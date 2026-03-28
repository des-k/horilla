from __future__ import annotations

from datetime import date, time
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from django.core.paginator import Paginator
from django.template.loader import render_to_string
from django.test import SimpleTestCase, TestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import Attendance, AttendanceRequestActionType
from attendance.services.attendance_request_presentation import build_attendance_request_time_surface
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from horilla_api.api_serializers.attendance.serializers import AttendanceRequestSerializer
from horilla_api.api_views.attendance.permission_views import AttendanceRequestApprovePermissionCheck
from horilla_api.api_views.attendance.views import AttendanceRequestView


class AttendanceRequestHistoryPresentationTests(AttendanceApiIntegrationMixin, TestCase):
    databases = "__all__"

    def setUp(self):
        super().setUp()
        self.admin_user, self.admin_employee = self.create_employee("Admin", is_superuser=True)
        self.owner_user, self.owner_employee = self.create_employee("Owner")
        self.attendance = Attendance.objects.create(
            employee_id=self.owner_employee,
            attendance_date=date(2026, 3, 28),
            attendance_clock_in=time(8, 0),
            attendance_clock_in_date=date(2026, 3, 28),
            attendance_clock_out=time(17, 0),
            attendance_clock_out_date=date(2026, 3, 28),
            request_description="Need correction",
            request_type="reject_request",
            action_type=AttendanceRequestActionType.REJECTED,
            requested_data={
                "attendance_clock_in": "09:10:00",
                "attendance_clock_in_date": "2026-03-28",
                "attendance_clock_out": "17:20:00",
                "attendance_clock_out_date": "2026-03-28",
            },
        )

    def test_serializer_exposes_requested_and_final_time_fields(self):
        serializer = AttendanceRequestSerializer(
            self.attendance,
            context={"request": self.auth_request(self.admin_user)},
        )
        data = serializer.data
        self.assertEqual(data["proposed_attendance_clock_in"], "09:10")
        self.assertEqual(data["proposed_attendance_clock_out"], "17:20")
        self.assertEqual(data["final_attendance_clock_in"], "08:00")
        self.assertEqual(data["final_attendance_clock_out"], "17:00")
        self.assertEqual(data["effective_attendance_clock_in"], "09:10")
        self.assertEqual(data["effective_attendance_clock_out"], "17:20")

    def test_history_api_response_includes_proposed_time_fields(self):
        request = APIRequestFactory().get(
            "/api/attendance/attendance-request/",
            {
                "approval_view": "history",
                "month": "2026-03",
                "status": "rejected",
            },
        )
        force_authenticate(request, user=self.admin_user)
        with patch("horilla_api.api_views.attendance.views.AttendanceFilters") as filters_cls:
            filters_cls.return_value.qs = Attendance.objects.filter(id=self.attendance.id)
            response = AttendanceRequestView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertGreaterEqual(response.data["count"], 1)
        first = response.data["results"][0]
        self.assertEqual(first["proposed_attendance_clock_in"], "09:10")
        self.assertEqual(first["final_attendance_clock_in"], "08:00")
        self.assertIn("employee_options", response.data)

    def test_history_template_renders_proposed_and_final_labels(self):
        page = Paginator([self.attendance], 25).get_page(1)
        html = render_to_string(
            "attendance/attendance_requests/table_approval_history.html",
            {
                "approval_history": page,
                "search": "",
                "history_employees": [],
                "history_employee_id": "",
                "history_month": "2026-03",
                "history_status": "rejected",
                "history_status_options": [("rejected", "Rejected")],
                "pd_app_hist": "",
                "history_attach_counts": {self.attendance.id: 0},
                "history_shift_info": {self.attendance.id: None},
                "history_time_surface": {
                    self.attendance.id: build_attendance_request_time_surface(self.attendance)
                },
            },
        )
        self.assertIn("Proposed", html)
        self.assertIn("09:10", html)
        self.assertIn("Final", html)
        self.assertIn("08:00", html)

    def test_permission_check_uses_subordinate_scope_for_mobile_history_gate(self):
        request = APIRequestFactory().get("/api/attendance/permission-check/attendance-request-approve")
        force_authenticate(request, user=self.owner_user)
        with patch(
            "horilla_api.api_views.attendance.permission_views.get_subordinate_employee_ids",
            return_value=[self.owner_employee.id],
        ):
            response = AttendanceRequestApprovePermissionCheck.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertTrue(response.data["can_approve"])


class AttendanceRequestHistoryFilterSourceTests(SimpleTestCase):
    def test_history_templates_share_filter_classes_and_css_rules(self):
        attendance_template = Path(
            "attendance/templates/attendance/attendance_requests/table_approval_history.html"
        ).read_text(encoding="utf-8")
        work_type_template = Path(
            "attendance/templates/attendance/work_type_requests/table_approval_history.html"
        ).read_text(encoding="utf-8")
        css = Path("static/src/css/main.css").read_text(encoding="utf-8")

        for source in (attendance_template, work_type_template):
            self.assertIn("oh-history-filter-row", source)
            self.assertIn("oh-history-filter-field", source)
            self.assertIn("oh-history-filter-control", source)
            self.assertIn("oh-history-filter-button", source)

        self.assertIn(".oh-history-filter-row", css)
        self.assertIn(".oh-history-filter-control", css)
        self.assertIn(".oh-request-history-time__label", css)
