from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.core.exceptions import ValidationError
from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import SimpleTestCase
from django.utils import timezone
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import AttendanceWorkMode
from employee.models import Employee
from horilla_api.api_views.attendance.views import (
    CheckingStatus,
    ClockInAPIView,
    ClockOutAPIView,
    MobileAttendanceSettingsAPIView,
)
from horilla_api.api_views.auth.views import LoginAPIView


class _AuthUser:
    is_authenticated = True
    is_superuser = False

    def __init__(self, employee):
        self.employee_get = employee


class _FirstSequence:
    def __init__(self, *values):
        self.values = list(values)

    def first(self):
        if not self.values:
            return None
        if len(self.values) == 1:
            return self.values[0]
        return self.values.pop(0)


class MobileAttendanceSettingsPolicyTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.company = SimpleNamespace(id=9, company="Policy Co")
        self.employee = Employee(
            employee_first_name="Policy",
            employee_last_name="User",
            email="policy-user@example.com",
            phone="8888888888",
        )
        self.employee.get_company = lambda: self.company
        self.user = _AuthUser(self.employee)

    def test_mobile_attendance_settings_always_report_geofencing_disabled(self):
        request = self.factory.get("/api/attendance/mobile-attendance-settings/")
        force_authenticate(request, user=self.user)

        face_detection = type(
            "FaceDetectionStub",
            (),
            {"start": True, "save": lambda self, **kwargs: None},
        )()

        with patch(
            "horilla_api.api_views.attendance.views.FaceDetection.objects.get_or_create",
            return_value=(face_detection, False),
        ):
            response = MobileAttendanceSettingsAPIView.as_view()(request)

        self.assertEqual(response.status_code, 200)
        self.assertTrue(response.data["face_detection_enabled"])
        self.assertTrue(response.data["location_capture_enabled"])
        self.assertFalse(response.data["geofencing_enabled"])

    def test_login_api_returns_geo_fencing_false_even_if_legacy_data_was_enabled(self):
        request = self.factory.post(
            "/api/auth/login/",
            {"username": "policy-user", "password": "testpass123"},
            format="json",
        )

        refresh = type("RefreshStub", (), {"access_token": "token-123"})()
        with patch("horilla_api.api_views.auth.views.authenticate", return_value=self.user), patch(
            "horilla_api.api_views.auth.views.RefreshToken.for_user",
            return_value=refresh,
        ):
            response = LoginAPIView.as_view()(request)

        self.assertEqual(response.status_code, 200)
        self.assertFalse(response.data["geo_fencing"])
        self.assertEqual(response.data["company_id"], self.company.id)


class MobileAttendanceActionParityTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.dt_now = timezone.make_aware(datetime(2026, 3, 20, 8, 5))
        self.attendance_date = date(2026, 3, 20)
        self.day = SimpleNamespace(id=1)
        self.company = SimpleNamespace(id=10, company="Parity Co")
        self.employee = SimpleNamespace(
            employee_first_name="Parity",
            employee_last_name="User",
            email="parity-user@example.com",
            phone="9999999999",
            employee_work_info=SimpleNamespace(shift_id="SHIFT-A"),
        )
        self.employee.get_company = lambda: self.company
        self.user = _AuthUser(self.employee)
        self.shift_rules = {
            "schedule": object(),
            "grace_seconds": 0,
            "clock_in_type": "after",
            "cutoff_in_dt": self.dt_now.replace(hour=10, minute=0),
            "cutoff_out_dt": self.dt_now.replace(hour=22, minute=0),
            "shift_start_dt": self.dt_now.replace(hour=8, minute=0),
            "shift_end_dt": self.dt_now.replace(hour=17, minute=0),
            "check_in_window_start_dt": self.dt_now.replace(hour=6, minute=0),
            "check_in_window_end_dt": self.dt_now.replace(hour=10, minute=0),
            "check_out_window_start_dt": self.dt_now.replace(hour=12, minute=0),
            "check_out_window_end_dt": self.dt_now.replace(hour=22, minute=0),
        }
        self.access = SimpleNamespace(
            allowed=True,
            message=None,
            reason_code=None,
            blocked_roles=(),
            is_reporting_manager=False,
            is_admin=False,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )

    def _status_request(self):
        request = self.factory.get("/api/attendance/checking-status/")
        force_authenticate(request, user=self.user)
        return request

    def _clock_request(self, path, *, image=True, location=True):
        payload = {}
        if location:
            payload.update({"latitude": "-6.2", "longitude": "106.8", "accuracy": "10"})
        if image:
            payload["image"] = SimpleUploadedFile("proof.jpg", b"image-bytes", content_type="image/jpeg")
        request = self.factory.post(path, payload, format="multipart")
        force_authenticate(request, user=self.user)
        return request

    def _status_patches(self, *, modes, allowed=None, attendance=None, committed_modes=None):
        if allowed is None:
            allowed = [True, True]
        if committed_modes is None:
            committed_modes = modes
        return [
            patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now),
            patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.access),
            patch(
                "horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day",
                return_value=(self.attendance_date, self.day, "08:00", 8 * 3600, 17 * 3600, "08:05", 8 * 3600 + 5 * 60),
            ),
            patch("horilla_api.api_views.attendance.views.cio.get_shift_rules", return_value=self.shift_rules),
            patch("horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date"),
            patch("horilla_api.api_views.attendance.views._resolve_punch_work_type", side_effect=modes),
            patch("horilla_api.api_views.attendance.views._resolve_committed_work_type", side_effect=committed_modes),
            patch("horilla_api.api_views.attendance.views._is_punch_allowed", side_effect=allowed),
            patch("horilla_api.api_views.attendance.views.Attendance.objects.filter", return_value=_FirstSequence(attendance)),
            patch("horilla_api.api_views.attendance.views.AttendanceActivity.objects.filter", return_value=_FirstSequence(None)),
            patch(
                "horilla_api.api_views.attendance.views._build_mobile_header_note_context",
                return_value={"header_note_effective_duration_seconds": None},
            ),
        ]

    def _clock_in_patches(self, *, mode_tuple, existing=None, final_attendance=None, parse_location=..., create_side_effect=None):
        if final_attendance is None:
            final_attendance = SimpleNamespace(
                attendance_clock_in=time(8, 5),
                attendance_clock_out=None,
                attendance_clock_in_date=self.attendance_date,
                in_attendance_status="VALID",
                out_attendance_status=None,
                in_attendance_reject_reason_code=None,
                out_attendance_reject_reason_code=None,
                in_related_work_type_request_id=None,
                out_related_work_type_request_id=None,
                reconciliation_source="mobile",
            )
        if parse_location is Ellipsis:
            parse_location = {"lat": -6.2, "lng": 106.8}
        if create_side_effect is None:
            create_side_effect = SimpleNamespace(id=99)
        mode_values = list(mode_tuple)
        mode_index = {"value": 0}

        def _mode_side_effect(*args, **kwargs):
            idx = min(mode_index["value"], len(mode_values) - 1)
            mode_index["value"] += 1
            return mode_values[idx]

        return [
            patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now),
            patch("horilla_api.api_views.attendance.views._parse_location_payload", return_value=parse_location),
            patch(
                "horilla_api.api_views.attendance.views.employee_exists",
                return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A")),
            ),
            patch(
                "horilla_api.api_views.attendance.views.create_mobile_punch_history",
                side_effect=create_side_effect,
            ),
            patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.access),
            patch("horilla_api.api_views.attendance.views._api_today", return_value=self.attendance_date),
            patch(
                "horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day",
                return_value=(self.attendance_date, self.day, "08:00", 8 * 3600, 17 * 3600, "08:05", 8 * 3600 + 5 * 60),
            ),
            patch("horilla_api.api_views.attendance.views.cio.get_shift_rules", return_value=self.shift_rules),
            patch("horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date"),
            patch("horilla_api.api_views.attendance.views._resolve_punch_work_type", side_effect=_mode_side_effect),
            patch("horilla_api.api_views.attendance.views._is_punch_allowed", return_value=True),
            patch("horilla_api.api_views.attendance.views._requires_proof", side_effect=lambda mode: mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.ON_DUTY}),
            patch(
                "horilla_api.api_views.attendance.views.Attendance.objects.filter",
                return_value=_FirstSequence(existing, final_attendance),
            ),
            patch("horilla_api.api_views.attendance.views.reconcile_attendance_punches"),
            patch(
                "horilla_api.api_views.attendance.views._build_mobile_header_note_context",
                return_value={"header_note_effective_duration_seconds": None},
            ),
            patch(
                "horilla_api.api_views.attendance.views._serialize_wfh_profile",
                return_value={
                    "home_latitude": None,
                    "home_longitude": None,
                    "google_maps_link": None,
                    "radius_in_meters": 250,
                    "is_home_configured": False,
                    "requires_home_reconfiguration": False,
                    "requires_face_reenrollment": False,
                    "face_image": None,
                    "history": [],
                },
            ),
        ]

    def test_checking_status_keeps_visible_mode_on_schedule_until_request_is_approved(self):
        waiting_req = SimpleNamespace(id=72, status="waiting_for_approval", scope="full", mode=AttendanceWorkMode.WFH)
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFH, "request", waiting_req), (AttendanceWorkMode.WFO, "schedule", None)],
            committed_modes=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.WFO, "schedule", None)],
            allowed=[False, True],
            attendance=None,
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertEqual(status_response.data["in_mode"], AttendanceWorkMode.WFO)
        self.assertEqual(status_response.data["in_work_type"], AttendanceWorkMode.WFO)
        self.assertEqual(status_response.data["in_work_type_source"], "schedule")
        self.assertEqual(status_response.data["in_work_type_request_status"], "waiting_for_approval")
        self.assertEqual(status_response.data["in_requested_work_type"], AttendanceWorkMode.WFH)
        self.assertFalse(status_response.data["can_clock_in"])
        self.assertEqual(status_response.data["check_in_block_reason"], "MODE_NOT_ALLOWED")

    def test_checking_status_matches_clock_in_allowance_for_approved_mobile_mode(self):
        approved_req = SimpleNamespace(id=71, status="approved", scope="full")
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFA, "request", approved_req), (AttendanceWorkMode.WFA, "request", approved_req)],
            allowed=[True, True],
            attendance=None,
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertTrue(status_response.data["can_clock_in"])
        self.assertIsNone(status_response.data["check_in_block_reason"])
        self.assertTrue(status_response.data["requires_photo_in"])
        self.assertTrue(status_response.data["requires_location_in"])

        punch_log = SimpleNamespace(id=101)
        clock_request = self._clock_request("/api/attendance/clock-in/", image=True, location=True)
        update_punch_history = MagicMock()
        clock_in_attendance = MagicMock()
        clock_patches = self._clock_in_patches(
            mode_tuple=[
                (AttendanceWorkMode.WFA, "request", approved_req),
                (AttendanceWorkMode.WFA, "request", approved_req),
            ],
            existing=None,
            create_side_effect=[punch_log],
        )
        clock_patches.extend(
            [
                patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history),
                patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity", clock_in_attendance),
            ]
        )

        for manager in clock_patches:
            manager.start()
        try:
            action_response = ClockInAPIView().post(clock_request)
        finally:
            for manager in reversed(clock_patches):
                manager.stop()

        self.assertEqual(action_response.status_code, 200)
        self.assertEqual(action_response.data["message"], "Clocked-In")
        self.assertEqual(action_response.data["in_mode"], AttendanceWorkMode.WFA)
        clock_in_attendance.assert_called_once()
        self.assertEqual(update_punch_history.call_args.kwargs["work_mode"], AttendanceWorkMode.WFA)
        self.assertIs(update_punch_history.call_args.kwargs["related_work_mode_request"], approved_req)

    def test_checking_status_verified_on_duty_in_hides_late_by_when_check_in_exists(self):
        approved_req = SimpleNamespace(
            id=811,
            status="approved",
            scope="in",
            document_status="verified",
            effective_document_status=lambda: "verified",
        )
        attendance = SimpleNamespace(
            attendance_clock_in=time(10, 15, 18),
            attendance_clock_out=None,
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=None,
            in_attendance_status="VALID",
            out_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=approved_req.id,
            out_related_work_type_request_id=None,
            reconciliation_source="SOURCE_ON_DUTY",
            attendance_worked_hour="00:00",
            is_presensi_only=False,
        )
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.ON_DUTY, "request", approved_req), (AttendanceWorkMode.WFO, "schedule", None)],
            allowed=[True, True],
            attendance=attendance,
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertEqual(status_response.data["in_mode"], AttendanceWorkMode.ON_DUTY)
        self.assertEqual(status_response.data["out_mode"], AttendanceWorkMode.WFO)
        self.assertIsNone(status_response.data["late_by"])
        self.assertEqual(status_response.data["header_state_code"], "CHECKED_IN")
        self.assertIn("Earliest Check Out", status_response.data["header_detail_message"])
        self.assertNotIn("Late by", status_response.data["header_detail_message"])

    def test_checking_status_verified_on_duty_out_hides_early_out_after_checkout_exists(self):
        approved_req = SimpleNamespace(
            id=812,
            status="approved",
            scope="out",
            document_status="verified",
            effective_document_status=lambda: "verified",
        )
        attendance = SimpleNamespace(
            attendance_clock_in=time(8, 0),
            attendance_clock_out=time(16, 44, 59),
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=self.attendance_date,
            in_attendance_status="VALID",
            out_attendance_status="VALID",
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=approved_req.id,
            reconciliation_source="SOURCE_ON_DUTY",
            attendance_worked_hour="08:44",
            is_presensi_only=False,
        )
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.ON_DUTY, "request", approved_req)],
            allowed=[True, True],
            attendance=attendance,
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertFalse(status_response.data["checked_out_early"])
        self.assertIsNone(status_response.data["checked_out_early_by"])
        self.assertEqual(status_response.data["out_mode"], AttendanceWorkMode.ON_DUTY)

    def test_checking_status_late_by_ignores_check_in_seconds(self):
        attendance = SimpleNamespace(
            attendance_clock_in=time(10, 15, 18),
            attendance_clock_out=None,
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=None,
            in_attendance_status="VALID",
            out_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source="mobile",
            attendance_worked_hour="00:00",
        )
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.WFO, "schedule", None)],
            allowed=[True, True],
            attendance=attendance,
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertEqual(status_response.data["late_by"], "135")

    def test_clock_out_response_early_out_ignores_checkout_seconds(self):
        attendance = SimpleNamespace(
            attendance_clock_in=time(8, 0),
            attendance_clock_out=time(16, 44, 59),
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=self.attendance_date,
            in_attendance_status="VALID",
            out_attendance_status="VALID",
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source="mobile",
            attendance_worked_hour="08:44",
        )
        request = self._clock_request("/api/attendance/clock-out/", image=False, location=False)
        update_punch_history = MagicMock()
        clock_out_attendance = MagicMock()
        patches = [
            patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now.replace(hour=16, minute=44, second=59)),
            patch("horilla_api.api_views.attendance.views._parse_location_payload", return_value=None),
            patch(
                "horilla_api.api_views.attendance.views.employee_exists",
                return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A")),
            ),
            patch(
                "horilla_api.api_views.attendance.views.create_mobile_punch_history",
                return_value=SimpleNamespace(id=301),
            ),
            patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.access),
            patch("horilla_api.api_views.attendance.views._api_today", return_value=self.attendance_date),
            patch(
                "horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day",
                return_value=(self.attendance_date, self.day, "16:44", 8 * 3600, 17 * 3600, "16:44", 16 * 3600 + 44 * 60 + 59),
            ),
            patch("horilla_api.api_views.attendance.views.cio.get_shift_rules", return_value=self.shift_rules),
            patch("horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date"),
            patch(
                "horilla_api.api_views.attendance.views._resolve_punch_work_type",
                side_effect=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.WFO, "schedule", None)],
            ),
            patch("horilla_api.api_views.attendance.views._is_punch_allowed", return_value=True),
            patch("horilla_api.api_views.attendance.views._requires_proof", return_value=False),
            patch("horilla_api.api_views.attendance.views.Attendance.objects.filter", return_value=_FirstSequence(attendance, attendance)),
            patch("horilla_api.api_views.attendance.views.AttendanceActivity.objects.filter", return_value=_FirstSequence(None)),
            patch("horilla_api.api_views.attendance.views.clock_out_attendance_and_activity", clock_out_attendance),
            patch("horilla_api.api_views.attendance.views.reconcile_attendance_punches"),
            patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history),
            patch(
                "horilla_api.api_views.attendance.views._build_mobile_header_note_context",
                return_value={"header_note_effective_duration_seconds": None},
            ),
        ]
        for manager in patches:
            manager.start()
        try:
            response = ClockOutAPIView().post(request)
        finally:
            for manager in reversed(patches):
                manager.stop()

        self.assertEqual(response.status_code, 403)

    def test_checking_status_with_existing_check_in_does_not_crash(self):
        attendance = SimpleNamespace(
            attendance_clock_in=time(8, 0),
            attendance_clock_out=None,
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=None,
            in_attendance_status="VALID",
            out_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source="mobile",
            attendance_worked_hour="00:05",
        )
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.WFO, "schedule", None)],
            allowed=[True, True],
            attendance=attendance,
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertFalse(status_response.data["missing_check_in"])
        self.assertEqual(status_response.data["earliest_check_out"], "17:00")
        self.assertFalse(status_response.data["can_clock_in"])
        self.assertFalse(status_response.data["can_clock_out"])

    def test_checking_status_with_late_existing_check_in_is_not_marked_missing(self):
        attendance = SimpleNamespace(
            attendance_clock_in=time(10, 15),
            attendance_clock_out=None,
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=None,
            in_attendance_status="VALID",
            out_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source="mobile",
            attendance_worked_hour="00:05",
        )
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.WFO, "schedule", None)],
            allowed=[True, True],
            attendance=attendance,
        )
        status_patches.append(
            patch(
                "horilla_api.api_views.attendance.views._compute_mobile_effective_start_and_earliest_checkout",
                return_value=(self.dt_now.replace(hour=10, minute=15), self.dt_now.replace(hour=17, minute=0), False),
            )
        )

        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertFalse(status_response.data["missing_check_in"])
        self.assertTrue(status_response.data["invalid_check_in"])
        self.assertEqual(status_response.data["first_check_in"], "10:15 AM")

    def test_checking_status_matches_clock_in_rejection_for_blocked_mobile_mode(self):
        status_request = self._status_request()
        status_patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFO, "schedule", None), (AttendanceWorkMode.WFO, "schedule", None)],
            allowed=[False, False],
            attendance=None,
        )
        for manager in status_patches:
            manager.start()
        try:
            status_response = CheckingStatus.as_view()(status_request)
        finally:
            for manager in reversed(status_patches):
                manager.stop()

        self.assertEqual(status_response.status_code, 200)
        self.assertFalse(status_response.data["can_clock_in"])
        self.assertEqual(status_response.data["check_in_block_reason"], "MODE_NOT_ALLOWED")

        update_punch_history = MagicMock()
        clock_in_attendance = MagicMock()
        request = self._clock_request("/api/attendance/clock-in/", image=True, location=True)
        clock_patches = self._clock_in_patches(
            mode_tuple=[(AttendanceWorkMode.WFO, "schedule", None)],
            existing=None,
            create_side_effect=[SimpleNamespace(id=201)],
        )
        clock_patches.extend(
            [
                patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history),
                patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity", clock_in_attendance),
            ]
        )
        # WFO is blocked before _is_punch_allowed matters.
        clock_patches.append(patch("horilla_api.api_views.attendance.views._is_punch_allowed", return_value=False))

        for manager in clock_patches:
            manager.start()
        try:
            action_response = ClockInAPIView().post(request)
        finally:
            for manager in reversed(clock_patches):
                manager.stop()

        self.assertEqual(action_response.status_code, 403)
        self.assertEqual(action_response.data["error"], "WFO attendance must be recorded via biometric device.")
        clock_in_attendance.assert_not_called()
        self.assertFalse(update_punch_history.call_args.kwargs["accepted"])
        self.assertIn("biometric", update_punch_history.call_args.kwargs["reason"].lower())

    def test_wfa_mobile_clock_in_rejects_missing_photo_when_proof_required(self):
        approved_req = SimpleNamespace(id=72, status="approved")
        request = self._clock_request("/api/attendance/clock-in/", image=False, location=True)
        update_punch_history = MagicMock()
        clock_in_attendance = MagicMock()
        patches = self._clock_in_patches(
            mode_tuple=[(AttendanceWorkMode.WFA, "request", approved_req)],
            existing=None,
            create_side_effect=[SimpleNamespace(id=301)],
        )
        patches.extend(
            [
                patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history),
                patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity", clock_in_attendance),
            ]
        )
        for manager in patches:
            manager.start()
        try:
            response = ClockInAPIView().post(request)
        finally:
            for manager in reversed(patches):
                manager.stop()

        self.assertEqual(response.status_code, 400)
        self.assertEqual(response.data["error"], "Photo is required.")
        clock_in_attendance.assert_not_called()
        self.assertIn("photo", update_punch_history.call_args.kwargs["reason"].lower())

    def test_on_duty_mobile_clock_in_rejects_missing_location_when_proof_required(self):
        approved_req = SimpleNamespace(id=73, status="approved")
        request = self._clock_request("/api/attendance/clock-in/", image=True, location=False)
        update_punch_history = MagicMock()
        clock_in_attendance = MagicMock()
        patches = self._clock_in_patches(
            mode_tuple=[(AttendanceWorkMode.ON_DUTY, "request", approved_req)],
            existing=None,
            parse_location=None,
            create_side_effect=[SimpleNamespace(id=302)],
        )
        patches.extend(
            [
                patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history),
                patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity", clock_in_attendance),
            ]
        )
        for manager in patches:
            manager.start()
        try:
            response = ClockInAPIView().post(request)
        finally:
            for manager in reversed(patches):
                manager.stop()

        self.assertEqual(response.status_code, 400)
        self.assertEqual(response.data["error"], "Location is required.")
        clock_in_attendance.assert_not_called()
        self.assertIn("location", update_punch_history.call_args.kwargs["reason"].lower())

    def test_invalid_image_upload_is_rejected_before_any_attendance_finalization(self):
        request = self._clock_request("/api/attendance/clock-in/", image=True, location=True)
        clock_in_attendance = MagicMock()
        with patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now), patch(
            "horilla_api.api_views.attendance.views._parse_location_payload",
            return_value={"lat": -6.2, "lng": 106.8},
        ), patch(
            "horilla_api.api_views.attendance.views.employee_exists",
            return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A")),
        ), patch(
            "horilla_api.api_views.attendance.views.evaluate_attendance_access",
            return_value=self.access,
        ), patch(
            "horilla_api.api_views.attendance.views.create_mobile_punch_history",
            side_effect=ValidationError("Invalid image file."),
        ), patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity", clock_in_attendance):
            response = ClockInAPIView().post(request)

        self.assertEqual(response.status_code, 400)
        self.assertIn("Invalid image file.", response.data["error"])
        clock_in_attendance.assert_not_called()

    def test_duplicate_mobile_clock_in_retry_keeps_single_final_checkin(self):
        approved_req = SimpleNamespace(id=74, status="approved")
        attendance_after = SimpleNamespace(
            attendance_clock_in=time(8, 5),
            attendance_clock_out=None,
            attendance_clock_in_date=self.attendance_date,
            in_attendance_status="VALID",
            out_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source="mobile",
        )
        qs = _FirstSequence(None, attendance_after, attendance_after)
        request_one = self._clock_request("/api/attendance/clock-in/", image=True, location=True)
        request_two = self._clock_request("/api/attendance/clock-in/", image=True, location=True)
        update_punch_history = MagicMock()
        clock_in_attendance = MagicMock()
        patches = [
            patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now),
            patch("horilla_api.api_views.attendance.views._parse_location_payload", return_value={"lat": -6.2, "lng": 106.8}),
            patch("horilla_api.api_views.attendance.views.employee_exists", return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A"))),
            patch("horilla_api.api_views.attendance.views.create_mobile_punch_history", side_effect=[SimpleNamespace(id=401), SimpleNamespace(id=402)]),
            patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.access),
            patch("horilla_api.api_views.attendance.views._api_today", return_value=self.attendance_date),
            patch("horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day", return_value=(self.attendance_date, self.day, "08:00", 8 * 3600, 17 * 3600, "08:05", 8 * 3600 + 5 * 60)),
            patch("horilla_api.api_views.attendance.views.cio.get_shift_rules", return_value=self.shift_rules),
            patch("horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date"),
            patch("horilla_api.api_views.attendance.views._resolve_punch_work_type", side_effect=(lambda *args, **kwargs: (AttendanceWorkMode.WFA, "request", approved_req))),
            patch("horilla_api.api_views.attendance.views._is_punch_allowed", return_value=True),
            patch("horilla_api.api_views.attendance.views._requires_proof", side_effect=lambda mode: mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.ON_DUTY}),
            patch("horilla_api.api_views.attendance.views.Attendance.objects.filter", return_value=qs),
            patch("horilla_api.api_views.attendance.views.reconcile_attendance_punches"),
            patch("horilla_api.api_views.attendance.views._build_mobile_header_note_context", return_value={"header_note_effective_duration_seconds": None}),
            patch("horilla_api.api_views.attendance.views._serialize_wfh_profile", return_value={"home_latitude": None, "home_longitude": None, "google_maps_link": None, "radius_in_meters": 250, "is_home_configured": False, "requires_home_reconfiguration": False, "requires_face_reenrollment": False, "face_image": None, "history": []}),
            patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history),
            patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity", clock_in_attendance),
        ]
        for manager in patches:
            manager.start()
        try:
            response_one = ClockInAPIView().post(request_one)
            response_two = ClockInAPIView().post(request_two)
        finally:
            for manager in reversed(patches):
                manager.stop()

        self.assertEqual(response_one.status_code, 200)
        self.assertEqual(response_two.status_code, 400)
        self.assertEqual(response_two.data["error"], "Already clocked-in")
        self.assertEqual(clock_in_attendance.call_count, 1)

    def test_duplicate_mobile_clock_out_retry_keeps_single_final_checkout(self):
        approved_req = SimpleNamespace(id=75, status="approved")
        existing_attendance = SimpleNamespace(
            attendance_clock_in=time(8, 5),
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out=None,
            out_attendance_status=None,
            reconciliation_source="mobile",
        )
        final_attendance = SimpleNamespace(
            attendance_clock_in=time(8, 5),
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out=time(17, 5),
            attendance_clock_out_date=self.attendance_date,
            attendance_worked_hour="09:00",
            out_attendance_status="VALID",
            in_attendance_status="VALID",
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source="mobile",
        )
        request_one = self._clock_request("/api/attendance/clock-out/", image=True, location=True)
        request_two = self._clock_request("/api/attendance/clock-out/", image=True, location=True)
        update_punch_history = MagicMock()
        clock_out_attendance = MagicMock(side_effect=[(final_attendance, False), ValidationError("Already clocked-out")])
        with patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now), patch(
            "horilla_api.api_views.attendance.views._parse_location_payload",
            return_value={"lat": -6.2, "lng": 106.8},
        ), patch(
            "horilla_api.api_views.attendance.views.employee_exists",
            return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A")),
        ), patch(
            "horilla_api.api_views.attendance.views.create_mobile_punch_history",
            side_effect=[SimpleNamespace(id=501), SimpleNamespace(id=502)],
        ), patch("horilla_api.api_views.attendance.views.update_punch_history", update_punch_history), patch(
            "horilla_api.api_views.attendance.views.evaluate_attendance_access",
            return_value=self.access,
        ), patch(
            "horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day",
            return_value=(self.attendance_date, self.day, "08:00", 8 * 3600, 17 * 3600, "17:05", 17 * 3600 + 5 * 60),
        ), patch(
            "horilla_api.api_views.attendance.views._resolve_punch_work_type",
            side_effect=[
                (AttendanceWorkMode.WFA, "request", approved_req),
                (AttendanceWorkMode.WFA, "request", approved_req),
                (AttendanceWorkMode.WFA, "request", approved_req),
                (AttendanceWorkMode.WFA, "request", approved_req),
            ],
        ), patch("horilla_api.api_views.attendance.views._is_punch_allowed", return_value=True), patch(
            "horilla_api.api_views.attendance.views.cio.get_shift_rules",
            return_value={"cutoff_in_dt": self.dt_now.replace(hour=10), "check_out_window_end_dt": self.dt_now.replace(hour=22)},
        ), patch("horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date"), patch(
            "horilla_api.api_views.attendance.views._requires_proof",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.Attendance.objects.filter",
            return_value=_FirstSequence(existing_attendance, final_attendance),
        ), patch(
            "horilla_api.api_views.attendance.views.cio.clock_out_attendance_and_activity",
            clock_out_attendance,
        ), patch("horilla_api.api_views.attendance.views.reconcile_attendance_punches"), patch(
            "horilla_api.api_views.attendance.views._build_mobile_header_note_context",
            return_value={"header_note_effective_duration_seconds": None},
        ), patch(
            "horilla_api.api_views.attendance.views._serialize_wfh_profile",
            return_value={"home_latitude": None, "home_longitude": None, "google_maps_link": None, "radius_in_meters": 250, "is_home_configured": False, "requires_home_reconfiguration": False, "requires_face_reenrollment": False, "face_image": None, "history": []},
        ):
            response_one = ClockOutAPIView().post(request_one)
            response_two = ClockOutAPIView().post(request_two)

        self.assertEqual(response_one.status_code, 200)
        self.assertEqual(response_two.status_code, 400)
        self.assertEqual(response_two.data["error"], "Already clocked-out")
        self.assertEqual(clock_out_attendance.call_count, 2)
