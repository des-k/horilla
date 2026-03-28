from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.test import RequestFactory, SimpleTestCase
from django.utils import timezone
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.forms import NewRequestForm
from attendance.services.activity_sync import validate_requested_data_with_windows
from attendance.views.requests import approve_validate_attendance_request
from horilla_api.api_views.attendance.views import AttendanceRequestApproveView, AttendanceRequestView


class AttendanceRequestWindowPolicyTests(SimpleTestCase):
    databases = "__all__"

    def test_new_request_form_collects_outside_window_warning_instead_of_raising(self):
        form = NewRequestForm.__new__(NewRequestForm)
        form.window_warnings = []
        form._validate_window(
            "attendance_clock_in",
            "Check In",
            time(5, 30),
            timezone.make_aware(datetime(2026, 3, 28, 8, 0)),
            timezone.make_aware(datetime(2026, 3, 28, 10, 0)),
        )
        self.assertEqual(len(form.window_warnings), 1)
        self.assertIn("manual approval review", form.window_warnings[0])

    def test_window_validation_helper_warns_but_allows_outside_window_approval(self):
        attendance = SimpleNamespace(
            requested_data={
                "attendance_date": "2026-03-28",
                "attendance_clock_in": "05:30",
                "shift_id": 7,
            },
            attendance_date=date(2026, 3, 28),
            shift_id=None,
            employee_id=SimpleNamespace(employee_work_info=SimpleNamespace(shift_id=SimpleNamespace(id=7))),
        )
        day_obj = SimpleNamespace(day="saturday")
        shift = SimpleNamespace(id=7)
        with patch("attendance.services.activity_sync.EmployeeShift.objects.filter") as shift_filter, \
             patch("attendance.services.activity_sync.EmployeeShiftDay.objects.filter") as day_filter, \
             patch("attendance.services.activity_sync.shift_schedule_today", return_value=(480, 8 * 3600, 17 * 3600)), \
             patch("attendance.views.clock_in_out.get_shift_rules", return_value={
                 "check_in_window_start_dt": timezone.make_aware(datetime(2026, 3, 28, 8, 0)),
                 "check_in_window_end_dt": timezone.make_aware(datetime(2026, 3, 28, 10, 0)),
             }):
            shift_filter.return_value.first.return_value = shift
            day_filter.return_value.first.return_value = day_obj
            is_valid, warning = validate_requested_data_with_windows(attendance)

        self.assertTrue(is_valid)
        self.assertIn("manual approval review", warning)

    def test_web_approve_allows_outside_window_warning_without_hard_fail(self):
        request = RequestFactory().post("/attendance/approve/77")
        request.user = SimpleNamespace(id=11, is_authenticated=True, is_active=True, employee_get=SimpleNamespace(id=502, is_active=True), has_perm=lambda perm: True)
        request.session = {}
        request.META["HTTP_REFERER"] = "/previous"
        attendance = SimpleNamespace(
            id=77,
            pk=77,
            employee_id=SimpleNamespace(id=101, employee_user_id=SimpleNamespace(id=10), employee_work_info=SimpleNamespace(reporting_manager_id=None)),
            attendance_date=date(2026, 3, 28),
            request_type="update_request",
            requested_data={"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}},
            is_validate_request=True,
            is_validate_request_approved=False,
            attendance_validated=False,
            action_by=None,
            action_type=None,
            action_at=None,
            save=lambda *args, **kwargs: None,
            refresh_from_db=lambda : None,
        )
        locked = MagicMock()
        locked.get.return_value = attendance
        filtered = MagicMock()
        with patch("attendance.views.requests.Attendance.objects.select_for_update", return_value=locked), \
             patch("attendance.views.requests.Attendance.objects.filter", return_value=filtered), \
             patch("attendance.views.requests.validate_requested_data_with_windows", return_value=(True, "Outside configured window")), \
             patch("attendance.views.requests.get_requested_sessions", return_value=(True, False)), \
             patch("attendance.views.requests._apply_request_override_snapshot"), \
             patch("attendance.views.requests._log_attendance_request_action"), \
             patch("attendance.views.requests._mark_approved_request_channels"), \
             patch("attendance.views.requests._detach_request_overridden_raw_links"), \
             patch("attendance.views.requests.recompute_attendance", return_value=SimpleNamespace(attendance=attendance)), \
             patch("attendance.views.requests.notify.send"), \
             patch("attendance.views.requests.messages.warning") as warning, \
             patch("attendance.views.requests.messages.success"), \
             patch("attendance.views.requests.messages.error") as error, \
             patch("employee.models.EmployeeWorkInformation.objects.filter") as mgr_filter:
            mgr_filter.return_value.exists.return_value = False
            import inspect
            response = inspect.unwrap(approve_validate_attendance_request)(request, attendance.id)

        self.assertEqual(response.status_code, 302)
        warning.assert_called_once()
        error.assert_not_called()

    def test_api_submit_returns_window_warning_but_still_creates_request(self):
        request = APIRequestFactory().post("/api/attendance/attendance-request/", {"attendance_date": "2026-03-28"}, format="json")
        user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=33))
        force_authenticate(request, user=user)

        attendance_obj = SimpleNamespace(id=91, save=lambda *args, **kwargs: None)
        serializer = SimpleNamespace(data={"id": 91, "request_type": "create_request"})
        form = MagicMock()
        form.is_valid.return_value = True
        form.cleaned_data = {"work_type_id": None}
        form.new_instance = attendance_obj
        form.window_warnings = ["Outside configured check-in window"]

        with patch("attendance.forms.NewRequestForm", return_value=form), \
             patch("horilla_api.api_views.attendance.views.NewRequestForm", return_value=form), \
             patch("horilla_api.api_views.attendance.views.WorkType.objects.filter") as wt_filter, \
             patch("horilla_api.api_views.attendance.views.AttendanceRequestSerializer", return_value=serializer), \
             patch("horilla_api.api_views.attendance.views.validate_uploaded_files"), \
             patch("horilla_api.api_views.attendance.views.Attendance.objects.filter") as att_filter:
            wt_filter.return_value.exists.return_value = False
            att_filter.return_value.first.return_value = attendance_obj
            response = AttendanceRequestView.as_view()(request)

        self.assertEqual(response.status_code, 201)
        self.assertEqual(response.data["window_warning"], "Outside configured check-in window")

    def test_api_approve_returns_window_warning_but_still_approves(self):
        request = APIRequestFactory().put("/api/attendance/attendance-request-approve/77", {}, format="json")
        user = SimpleNamespace(id=11, is_authenticated=True, is_active=True, employee_get=SimpleNamespace(id=502))
        force_authenticate(request, user=user)
        attendance = SimpleNamespace(
            id=77,
            pk=77,
            employee_id=SimpleNamespace(id=101),
            attendance_date=date(2026, 3, 28),
            request_type="update_request",
            requested_data={"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}},
            is_validate_request=True,
            is_validate_request_approved=False,
            attendance_validated=False,
            action_by=None,
            action_type=None,
            action_at=None,
            save=lambda *args, **kwargs: None,
            refresh_from_db=lambda : None,
        )
        locked = MagicMock()
        locked.get.return_value = attendance
        filtered = MagicMock()
        serializer = SimpleNamespace(data={"id": 77, "request_type": "approved"})
        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=locked), \
             patch("horilla_api.api_views.attendance.views.Attendance.objects.filter", return_value=filtered), \
             patch("horilla_api.api_views.attendance.views.user_can_approve_request", return_value=True), \
             patch("horilla_api.api_decorators.base.decorators.ManagerPermission.has_permission", return_value=True), \
             patch("horilla_api.api_views.attendance.views.validate_requested_data_with_windows", return_value=(True, "Outside configured window")), \
             patch("horilla_api.api_views.attendance.views.get_requested_sessions", return_value=(True, False)), \
             patch("horilla_api.api_views.attendance.views._apply_request_override_snapshot"), \
             patch("horilla_api.api_views.attendance.views._mark_approved_request_channels"), \
             patch("horilla_api.api_views.attendance.views._detach_request_overridden_raw_links"), \
             patch("horilla_api.api_views.attendance.views._log_attendance_request_status_change"), \
             patch("horilla_api.api_views.attendance.views.recompute_attendance", return_value=SimpleNamespace(attendance=attendance)), \
             patch("horilla_api.api_views.attendance.views.AttendanceRequestSerializer", return_value=serializer):
            response = AttendanceRequestApproveView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data["window_warning"], "Outside configured window")
