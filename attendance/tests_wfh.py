from datetime import date
from pathlib import Path
from types import MethodType, SimpleNamespace
from unittest.mock import MagicMock, patch

from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import SimpleTestCase, override_settings
from rest_framework.test import APIRequestFactory, APITestCase, force_authenticate

from attendance.models import (
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchingHistory,
    AttendanceWorkMode,
    EmployeeWfhProfile,
    EmployeeWfhProfileHistory,
    PunchDecisionStatus,
)
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from attendance.views import clock_in_out
from base.worktype_display import normalize_work_type_label
from facedetection.models import EmployeeFaceDetection
from geofencing.models import GeoFencing
from geofencing.views import _can_reset_wfh_face, _can_reset_wfh_home
from horilla_api.api_serializers.employee.serializers import EmployeeSerializer
from horilla_api.api_views.attendance.views import (
    AdminResetWfhFaceAPIView,
    AdminResetWfhHomeAPIView,
    EmployeeWfhHomeSetupAPIView,
    MobileAttendanceSettingsAPIView,
    _has_wfh_face_reset_permission,
    _has_wfh_home_reset_permission,
    _validate_wfh_punch,
)
from attendance.services import monthly_recap
from attendance.services.work_type_request_rules import validate_work_type_request


class WfhSpecTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.employee = SimpleNamespace(
            get_company=lambda: SimpleNamespace(id=1, company="Example Co"),
        )

    def test_wfh_mode_and_label_exist(self):
        self.assertEqual(AttendanceWorkMode.WFH, "wfh")
        self.assertEqual(normalize_work_type_label("work from home"), "WFH")

    @patch("horilla_api.api_views.attendance.views._get_wfh_profile")
    @patch("horilla_api.api_views.attendance.views._get_company_geofencing")
    @patch("horilla_api.api_views.attendance.views.FaceDetection.objects.filter")
    def test_mobile_attendance_settings_include_wfh_fields(self, mock_face_filter, mock_geo, mock_profile):
        mock_face_filter.return_value.first.return_value = SimpleNamespace(start=True)
        mock_geo.return_value = SimpleNamespace(wfh_start=True, wfh_radius_in_meters=250)
        mock_profile.return_value = SimpleNamespace(
            requires_home_reconfiguration=False,
            requires_face_reenrollment=True,
            is_home_configured=True,
            home_latitude=-6.2,
            home_longitude=106.8,
        )
        request = self.factory.get("/api/attendance/mobile-attendance-settings/")
        user = SimpleNamespace(is_authenticated=True, employee_get=self.employee)
        force_authenticate(request, user=user)
        response = MobileAttendanceSettingsAPIView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertTrue(response.data["wfh_geofencing_enabled"])
        self.assertEqual(response.data["wfh_radius_in_meters"], 250)
        self.assertTrue(response.data["requires_face_reenrollment"])
        self.assertTrue(response.data["has_home_location_configured"])

    @patch("horilla_api.api_views.attendance.views._get_company_geofencing")
    @patch("horilla_api.api_views.attendance.views._get_wfh_profile")
    def test_validate_wfh_punch_blocks_outside_radius(self, mock_profile, mock_geo):
        mock_profile.return_value = SimpleNamespace(
            requires_face_reenrollment=False,
            requires_home_reconfiguration=False,
            is_home_configured=True,
            home_latitude=-6.2000,
            home_longitude=106.8166,
            home_radius_in_meters=250,
        )
        mock_geo.return_value = SimpleNamespace(wfh_start=True, wfh_radius_in_meters=250)
        error = _validate_wfh_punch(
            self.employee,
            AttendanceWorkMode.WFH,
            {"lat": -6.1900, "lng": 106.9000},
            direction="in",
            actor=self.employee,
        )
        self.assertIn("luar radius", error)

    @patch("horilla_api.api_views.attendance.views._get_company_geofencing")
    @patch("horilla_api.api_views.attendance.views._get_wfh_profile")
    def test_validate_wfh_punch_allows_inside_radius(self, mock_profile, mock_geo):
        mock_profile.return_value = SimpleNamespace(
            requires_face_reenrollment=False,
            requires_home_reconfiguration=False,
            is_home_configured=True,
            home_latitude=-6.2000,
            home_longitude=106.8166,
            home_radius_in_meters=250,
        )
        mock_geo.return_value = SimpleNamespace(wfh_start=True, wfh_radius_in_meters=250)
        error = _validate_wfh_punch(
            self.employee,
            AttendanceWorkMode.WFH,
            {"lat": -6.2001, "lng": 106.8167},
            direction="in",
            actor=self.employee,
        )
        self.assertIsNone(error)

    @patch("horilla_api.api_views.attendance.views._get_company_geofencing")
    @patch("horilla_api.api_views.attendance.views._get_wfh_profile")
    def test_validate_wfh_punch_still_requires_home_setup_when_geofence_disabled(self, mock_profile, mock_geo):
        mock_profile.return_value = SimpleNamespace(
            requires_face_reenrollment=False,
            requires_home_reconfiguration=True,
            is_home_configured=False,
            home_latitude=None,
            home_longitude=None,
            home_radius_in_meters=250,
        )
        mock_geo.return_value = SimpleNamespace(wfh_start=False, wfh_radius_in_meters=250)
        error = _validate_wfh_punch(
            self.employee,
            AttendanceWorkMode.WFH,
            {"lat": -6.2001, "lng": 106.8167},
            direction="in",
            actor=self.employee,
        )
        self.assertIn("setup ulang lokasi rumah", error)

    @patch("attendance.services.work_type_request_rules.WorkModeRequest.objects")
    @patch("attendance.services.work_type_request_rules.scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO)
    def test_validate_work_type_request_accepts_wfh(self, _mock_sched, mock_objects):
        mock_qs = MagicMock()
        mock_qs.filter.return_value = mock_qs
        mock_qs.exclude.return_value = mock_qs
        mock_qs.exists.return_value = False
        mock_objects.filter.return_value = mock_qs
        validate_work_type_request(
            employee=self.employee,
            mode=AttendanceWorkMode.WFH,
            scope="full",
            start_date=__import__("datetime").date.today(),
            end_date=__import__("datetime").date.today(),
            instance_id=None,
        )

    def test_monthly_recap_labels_wfh(self):
        self.assertEqual(monthly_recap._work_mode_label(AttendanceWorkMode.WFH), "WFH")
        self.assertEqual(monthly_recap._normalize_work_mode("work from home"), AttendanceWorkMode.WFH)


class _FakePermUser:
    def __init__(self, perms=None, superuser=False):
        self._perms = set(perms or [])
        self.is_superuser = superuser

    def has_perm(self, perm):
        return perm in self._perms


class WfhSpecRegressionTests(SimpleTestCase):
    def test_remote_alias_stays_wfa(self):
        self.assertEqual(normalize_work_type_label("remote"), "WFA")

    @patch("horilla_api.api_serializers.employee.serializers.EmployeeWfhProfileHistory.objects.filter")
    @patch("horilla_api.api_serializers.employee.serializers.EmployeeFaceDetection.objects.filter")
    @patch("horilla_api.api_serializers.employee.serializers.GeoFencing.objects.filter")
    def test_employee_serializer_returns_default_wfh_profile_without_row(self, mock_geo, mock_face, mock_history):
        mock_geo.return_value.first.return_value = SimpleNamespace(wfh_radius_in_meters=250)
        mock_face.return_value.first.return_value = None
        history_qs = MagicMock()
        history_qs.order_by.return_value.__getitem__.return_value = []
        mock_history.return_value = history_qs
        employee = SimpleNamespace(
            wfh_profile=None,
            get_company=lambda: SimpleNamespace(id=1),
            employee_work_info=SimpleNamespace(company_id=SimpleNamespace(id=1)),
        )
        payload = EmployeeSerializer().get_wfh_profile(employee)
        self.assertIsInstance(payload, dict)
        self.assertEqual(payload["radius_in_meters"], 250)
        self.assertFalse(payload["is_home_configured"])
        self.assertEqual(payload["history"], [])

    @patch("attendance.views.clock_in_out.update_punch_history")
    @patch("attendance.views.clock_in_out.resolve_biometric_work_mode")
    def test_non_mobile_raw_punch_sources_are_invalid_for_wfh(self, mock_resolve, mock_update):
        mock_resolve.return_value = SimpleNamespace(mode=AttendanceWorkMode.WFH, request=None)
        for source in (
            AttendancePunchSource.BIOMETRIC,
            AttendancePunchSource.API,
            AttendancePunchSource.UNKNOWN,
        ):
            with self.subTest(source=source):
                raw = SimpleNamespace(source=source, decision_status=None, reason=None, save=MagicMock())
                req = SimpleNamespace(raw_punch_history=raw)
                employee = SimpleNamespace()
                mode, request = clock_in_out._resolve_biometric_mode_context(req, employee, __import__("datetime").date.today())
                self.assertEqual(mode, AttendanceWorkMode.WFH)
                self.assertIsNone(request)
                self.assertEqual(raw.decision_status, PunchDecisionStatus.INVALID)
                self.assertEqual(raw.reason, "invalid_for_wfh_non_mobile_source")
        reasons = [call.kwargs.get("reason") for call in mock_update.mock_calls if call.kwargs.get("reason")]
        self.assertTrue(all(reason == "invalid_for_wfh_non_mobile_source" for reason in reasons))

    def test_web_permission_helpers_are_separate(self):
        face_only = _FakePermUser({"attendance.reset_wfh_face_detection"})
        home_only = _FakePermUser({"attendance.reset_wfh_home_geofence"})
        change_only = _FakePermUser({"employee.change_employee"})
        self.assertFalse(_can_reset_wfh_home(face_only))
        self.assertTrue(_can_reset_wfh_face(face_only))
        self.assertTrue(_can_reset_wfh_home(home_only))
        self.assertFalse(_can_reset_wfh_face(home_only))
        self.assertFalse(_can_reset_wfh_home(change_only))
        self.assertFalse(_can_reset_wfh_face(change_only))

    def test_api_permission_helpers_are_separate(self):
        face_only = _FakePermUser({"attendance.reset_wfh_face_detection"})
        home_only = _FakePermUser({"attendance.reset_wfh_home_geofence"})
        change_only = _FakePermUser({"employee.change_employee"})
        self.assertFalse(_has_wfh_home_reset_permission(face_only))
        self.assertTrue(_has_wfh_face_reset_permission(face_only))
        self.assertTrue(_has_wfh_home_reset_permission(home_only))
        self.assertFalse(_has_wfh_face_reset_permission(home_only))
        self.assertFalse(_has_wfh_home_reset_permission(change_only))
        self.assertFalse(_has_wfh_face_reset_permission(change_only))


class WfhTemplateSourceRegressionTests(SimpleTestCase):
    def test_employee_profile_template_matches_geo_face_info_card(self):
        backend_root = Path(__file__).resolve().parents[1]
        text = (backend_root / "employee" / "templates" / "employee" / "profile" / "profile_view.html").read_text()
        self.assertIn("Geo & Face Info", text)
        self.assertIn("wfh_profile_data.face_image_url", text)
        self.assertIn("Open in Google Maps", text)
        self.assertNotIn("WFH Home Location", text)
        self.assertNotIn("WFH History", text)
        self.assertNotIn("Requires Home Reconfiguration", text)
        self.assertNotIn("Requires Face Reenrollment", text)

    def test_employee_individual_template_contains_geo_face_info_card(self):
        backend_root = Path(__file__).resolve().parents[1]
        text = (backend_root / "employee" / "templates" / "employee" / "view" / "individual.html").read_text()
        self.assertIn("Geo & Face Info", text)
        self.assertIn("wfh_profile_data.face_image_url", text)
        self.assertIn("Open in Google Maps", text)

    def test_geofencing_template_contains_only_wfh_home_reset_controls(self):
        backend_root = Path(__file__).resolve().parents[1]
        text = (backend_root / "geofencing" / "templates" / "geo_config.html").read_text()
        self.assertIn("WFH Reset Actions", text)
        self.assertIn("{{ form.as_p }}", text)
        self.assertIn("reset_home", text)
        self.assertNotIn("reset_face", text)

    def test_face_detection_template_contains_face_reset_controls(self):
        backend_root = Path(__file__).resolve().parents[1]
        text = (backend_root / "facedetection" / "templates" / "face_config.html").read_text()
        self.assertIn("Reset Face Detection For", text)
        self.assertIn("reset_face", text)


@override_settings(MEDIA_ROOT="/tmp/horilla_wfh_test_media")
class WfhApiIntegrationTests(AttendanceApiIntegrationMixin, APITestCase):
    @classmethod
    def setUpTestData(cls):
        super().setUpTestData()

    def setUp(self):
        super().setUp()
        GeoFencing.objects.update_or_create(
            company_id=self.company,
            defaults={
                "latitude": -6.2,
                "longitude": 106.8,
                "radius_in_meters": 100,
                "start": False,
                "wfh_start": True,
                "wfh_radius_in_meters": 250,
            },
        )

    def _grant_only(self, user, *perms):
        allowed = set(perms)
        user.has_perm = MethodType(lambda self, perm: perm in allowed, user)
        return user

    def _json(self, response):
        try:
            return response.json()
        except Exception:
            return getattr(response, "data", None)

    def test_employee_profile_endpoint_returns_default_wfh_profile(self):
        user, employee = self.create_employee("Alice")
        response = self.auth_client(user).get(f"/api/employee/employees/{employee.id}/", format="json")
        data = self._json(response)
        self.assertEqual(response.status_code, 200)
        self.assertIn("wfh_profile", data)
        self.assertFalse(data["wfh_profile"]["is_home_configured"])
        self.assertEqual(data["wfh_profile"]["radius_in_meters"], 250)
        self.assertEqual(data["wfh_profile"]["history"], [])

    def test_home_setup_endpoint_persists_profile_and_history(self):
        user, employee = self.create_employee("Bob")
        request = self.factory.post(
            "/api/attendance/wfh/home-setup/",
            {"lat": -6.201, "lng": 106.817},
            format="json",
        )
        force_authenticate(request, user=user)
        response = EmployeeWfhHomeSetupAPIView.as_view()(request)
        profile = EmployeeWfhProfile.objects.get(employee=employee)
        history = EmployeeWfhProfileHistory.objects.filter(employee=employee).latest("id")
        self.assertEqual(response.status_code, 200)
        self.assertTrue(profile.is_home_configured)
        self.assertFalse(profile.requires_home_reconfiguration)
        self.assertEqual(float(profile.home_latitude), -6.201)
        self.assertEqual(float(profile.home_longitude), 106.817)
        self.assertEqual(profile.home_radius_in_meters, 250)
        self.assertEqual(history.action_type, EmployeeWfhProfileHistory.ActionType.HOME_INITIAL_SET)
        self.assertEqual(float(history.new_home_latitude), -6.201)
        self.assertEqual(float(history.new_home_longitude), 106.817)

    def test_home_setup_reconfiguration_clears_reset_flag_and_tracks_old_snapshot(self):
        user, employee = self.create_employee("Carla")
        profile = EmployeeWfhProfile.objects.create(
            employee=employee,
            home_latitude=-6.2,
            home_longitude=106.8,
            home_radius_in_meters=200,
            is_home_configured=True,
            requires_home_reconfiguration=True,
        )
        request = self.factory.post(
            "/api/attendance/wfh/home-setup/",
            {"lat": -6.21, "lng": 106.81},
            format="json",
        )
        force_authenticate(request, user=user)
        response = EmployeeWfhHomeSetupAPIView.as_view()(request)
        profile.refresh_from_db()
        history = EmployeeWfhProfileHistory.objects.filter(employee=employee).latest("id")
        self.assertEqual(response.status_code, 200)
        self.assertFalse(profile.requires_home_reconfiguration)
        self.assertEqual(history.action_type, EmployeeWfhProfileHistory.ActionType.HOME_RECONFIGURED)
        self.assertEqual(float(history.old_home_latitude), -6.2)
        self.assertEqual(float(history.old_home_longitude), 106.8)
        self.assertEqual(history.old_radius_in_meters, 200)

    def test_home_setup_endpoint_rejects_missing_location(self):
        user, _employee = self.create_employee("Dina")
        request = self.factory.post("/api/attendance/wfh/home-setup/", {}, format="json")
        force_authenticate(request, user=user)
        response = EmployeeWfhHomeSetupAPIView.as_view()(request)
        self.assertEqual(response.status_code, 400)
        self.assertIn("Location is required", str(response.data))

    def test_mobile_attendance_settings_endpoint_reads_real_flags(self):
        user, employee = self.create_employee("Eka")
        profile = EmployeeWfhProfile.objects.create(
            employee=employee,
            home_latitude=-6.21,
            home_longitude=106.82,
            is_home_configured=True,
            requires_home_reconfiguration=False,
            requires_face_reenrollment=True,
        )
        request = self.factory.get("/api/attendance/mobile-attendance-settings/")
        force_authenticate(request, user=user)
        response = MobileAttendanceSettingsAPIView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertTrue(response.data["wfh_geofencing_enabled"])
        self.assertEqual(response.data["wfh_radius_in_meters"], 250)
        self.assertTrue(response.data["requires_face_reenrollment"])
        self.assertTrue(response.data["has_home_location_configured"])
        self.assertFalse(response.data["requires_home_reconfiguration"])
        profile.delete()

    def test_admin_reset_home_endpoint_requires_home_permission_and_logs_snapshot(self):
        admin_user, admin_employee = self.create_employee("AdminHome")
        self._grant_only(admin_user, "attendance.reset_wfh_home_geofence")
        _target_user, employee = self.create_employee("Farah")
        EmployeeWfhProfile.objects.create(
            employee=employee,
            home_latitude=-6.22,
            home_longitude=106.83,
            home_radius_in_meters=300,
            is_home_configured=True,
        )
        request = self.factory.post(
            "/api/attendance/wfh/reset-home/",
            {"employee_id": employee.id},
            format="json",
        )
        force_authenticate(request, user=admin_user)
        response = AdminResetWfhHomeAPIView.as_view()(request)
        profile = EmployeeWfhProfile.objects.get(employee=employee)
        history = EmployeeWfhProfileHistory.objects.filter(employee=employee).latest("id")
        self.assertEqual(response.status_code, 200)
        self.assertTrue(profile.requires_home_reconfiguration)
        self.assertEqual(profile.last_home_reset_by, admin_employee)
        self.assertEqual(history.action_type, EmployeeWfhProfileHistory.ActionType.HOME_RESET)
        self.assertEqual(float(history.old_home_latitude), -6.22)
        self.assertEqual(float(history.old_home_longitude), 106.83)
        self.assertEqual(history.old_radius_in_meters, 300)

    def test_admin_reset_face_endpoint_requires_face_permission_and_logs_old_image(self):
        admin_user, admin_employee = self.create_employee("AdminFace")
        self._grant_only(admin_user, "attendance.reset_wfh_face_detection")
        _target_user, employee = self.create_employee("Gita")
        EmployeeWfhProfile.objects.create(employee=employee, is_home_configured=False)
        EmployeeFaceDetection.objects.create(
            employee_id=employee,
            image=SimpleUploadedFile("face.jpg", b"fake-image-bytes", content_type="image/jpeg"),
        )
        request = self.factory.post(
            "/api/attendance/wfh/reset-face/",
            {"employee_id": employee.id},
            format="json",
        )
        force_authenticate(request, user=admin_user)
        response = AdminResetWfhFaceAPIView.as_view()(request)
        profile = EmployeeWfhProfile.objects.get(employee=employee)
        history = EmployeeWfhProfileHistory.objects.filter(employee=employee).latest("id")
        self.assertEqual(response.status_code, 200)
        self.assertTrue(profile.requires_face_reenrollment)
        self.assertEqual(profile.last_face_reset_by, admin_employee)
        self.assertEqual(history.action_type, EmployeeWfhProfileHistory.ActionType.FACE_RESET)
        self.assertTrue(history.old_face_image)
        self.assertTrue(history.old_face_image.endswith(".jpg"))

    def test_reset_home_endpoint_rejects_face_only_permission(self):
        admin_user, _admin_employee = self.create_employee("AdminFaceOnly")
        self._grant_only(admin_user, "attendance.reset_wfh_face_detection")
        _target_user, employee = self.create_employee("Hani")
        request = self.factory.post(
            "/api/attendance/wfh/reset-home/",
            {"employee_id": employee.id},
            format="json",
        )
        force_authenticate(request, user=admin_user)
        response = AdminResetWfhHomeAPIView.as_view()(request)
        self.assertEqual(response.status_code, 403)

    def test_reset_face_endpoint_rejects_home_only_permission(self):
        admin_user, _admin_employee = self.create_employee("AdminHomeOnly")
        self._grant_only(admin_user, "attendance.reset_wfh_home_geofence")
        _target_user, employee = self.create_employee("Intan")
        request = self.factory.post(
            "/api/attendance/wfh/reset-face/",
            {"employee_id": employee.id},
            format="json",
        )
        force_authenticate(request, user=admin_user)
        response = AdminResetWfhFaceAPIView.as_view()(request)
        self.assertEqual(response.status_code, 403)

    def test_profile_serializer_includes_history_face_images(self):
        user, employee = self.create_employee("Joko")
        EmployeeWfhProfileHistory.objects.create(
            employee=employee,
            action_type=EmployeeWfhProfileHistory.ActionType.FACE_REENROLLED,
            old_face_image="/media/old-face.jpg",
            new_face_image="/media/new-face.jpg",
            acted_by=employee,
        )
        payload = EmployeeSerializer(employee).data["wfh_profile"]
        self.assertEqual(payload["history"][0]["old_face_image"], "/media/old-face.jpg")
        self.assertEqual(payload["history"][0]["new_face_image"], "/media/new-face.jpg")

    def test_non_mobile_invalid_source_is_reflected_in_history_serializer(self):
        user, employee = self.create_employee("Kiki")
        punch = AttendancePunchingHistory.objects.create(
            employee_id=employee,
            attendance_date=date(2026, 4, 6),
            punch_timestamp=self.aware_dt(2026, 4, 6, 8, 30),
            punch_direction=AttendancePunchDirection.IN,
            source=AttendancePunchSource.API,
            decision_status=PunchDecisionStatus.INVALID,
            reason="invalid_for_wfh_non_mobile_source",
        )
        from horilla_api.api_serializers.attendance.serializers import AttendancePunchingHistorySerializer

        payload = AttendancePunchingHistorySerializer(punch).data
        self.assertEqual(payload["decision_status"], PunchDecisionStatus.INVALID)
        self.assertEqual(payload["reason"], "invalid_for_wfh_non_mobile_source")

    def test_leave_profile_renderer_also_passes_wfh_profile_data(self):
        text = Path("leave/views.py").read_text()
        self.assertIn("employee/profile/profile_view.html", text)
        self.assertIn('"wfh_profile_data": _build_wfh_profile_data(employee)', text)
