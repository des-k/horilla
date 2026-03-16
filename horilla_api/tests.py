from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from employee.models import Employee
from horilla_api.api_views.attendance.views import MobileAttendanceSettingsAPIView
from horilla_api.api_views.auth.views import LoginAPIView


class _AuthUser:
    is_authenticated = True
    is_superuser = False

    def __init__(self, employee):
        self.employee_get = employee


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
