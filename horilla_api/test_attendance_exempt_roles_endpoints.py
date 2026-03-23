from datetime import date, datetime
from types import SimpleNamespace
from unittest.mock import patch

from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import SimpleTestCase
from django.utils import timezone
from rest_framework.test import APIRequestFactory, force_authenticate

from horilla_api.api_views.attendance.views import CheckingStatus, ClockInAPIView, ClockOutAPIView


class _AuthUser:
    is_authenticated = True
    is_superuser = False

    def __init__(self, employee):
        self.employee_get = employee


class AttendanceExemptRolesEndpointTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.employee = SimpleNamespace(id=77, employee_first_name="Manager", employee_last_name="Only")
        self.user = _AuthUser(self.employee)
        self.dt_now = timezone.make_aware(datetime(2026, 3, 20, 8, 5))
        self.blocked_access = SimpleNamespace(
            allowed=False,
            message="Attendance is disabled for reporting managers.",
            reason_code="REPORTING_MANAGER_EXEMPT",
            blocked_roles=("reporting_manager",),
            is_reporting_manager=True,
            is_admin=False,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )
        self.admin_blocked_access = SimpleNamespace(
            allowed=False,
            message="Attendance is disabled for admins.",
            reason_code="ADMIN_EXEMPT",
            blocked_roles=("admin",),
            is_reporting_manager=False,
            is_admin=True,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )

    def test_reporting_manager_cannot_clock_in_when_exempt(self):
        request = self.factory.post(
            "/api/attendance/clock-in/",
            {
                "latitude": "-6.2",
                "longitude": "106.8",
                "image": SimpleUploadedFile("proof.jpg", b"image-bytes", content_type="image/jpeg"),
            },
            format="multipart",
        )
        force_authenticate(request, user=self.user)
        with patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now), \
             patch("horilla_api.api_views.attendance.views._parse_location_payload", return_value={"lat": -6.2, "lng": 106.8}), \
             patch("horilla_api.api_views.attendance.views.employee_exists", return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A"))), \
             patch("horilla_api.api_views.attendance.views.create_mobile_punch_history", return_value=SimpleNamespace(id=1)), \
             patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.blocked_access), \
             patch("horilla_api.api_views.attendance.views.update_punch_history") as update_mock:
            response = ClockInAPIView.as_view()(request)
        self.assertEqual(response.status_code, 403)
        self.assertIn("disabled", response.data["error"].lower())
        update_mock.assert_any_call(SimpleNamespace(id=1), attendance_date=date(2026, 3, 20))

    def test_reporting_manager_cannot_clock_out_when_exempt(self):
        request = self.factory.post(
            "/api/attendance/clock-out/",
            {
                "latitude": "-6.2",
                "longitude": "106.8",
                "image": SimpleUploadedFile("proof.jpg", b"image-bytes", content_type="image/jpeg"),
            },
            format="multipart",
        )
        force_authenticate(request, user=self.user)
        punch_log = SimpleNamespace(id=2)
        with patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now), \
             patch("horilla_api.api_views.attendance.views._parse_location_payload", return_value={"lat": -6.2, "lng": 106.8}), \
             patch("horilla_api.api_views.attendance.views.employee_exists", return_value=(self.employee, SimpleNamespace(shift_id="SHIFT-A"))), \
             patch("horilla_api.api_views.attendance.views.create_mobile_punch_history", return_value=punch_log), \
             patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.blocked_access), \
             patch("horilla_api.api_views.attendance.views.update_punch_history") as update_mock:
            response = ClockOutAPIView.as_view()(request)
        self.assertEqual(response.status_code, 403)
        self.assertIn("disabled", response.data["error"].lower())
        update_mock.assert_any_call(punch_log, attendance_date=date(2026, 3, 20))

    def test_exempt_role_status_endpoint_returns_attendance_disabled(self):
        request = self.factory.get("/api/attendance/checking-status/")
        force_authenticate(request, user=self.user)
        with patch("horilla_api.api_views.attendance.views._api_now", return_value=self.dt_now), \
             patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=self.admin_blocked_access):
            response = CheckingStatus.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertFalse(response.data["attendance_enabled"])
        self.assertEqual(response.data["attendance_exempt_reason"], "ADMIN_EXEMPT")
        self.assertTrue(response.data["role_flags"]["is_admin"])
