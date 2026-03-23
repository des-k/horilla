from __future__ import annotations

import inspect
from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.http import HttpResponseRedirect
from django.test import RequestFactory, SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import AttendanceRequestActionType
from attendance.views.requests import (
    cancel_attendance_request,
    revoke_validate_attendance_request,
)
from horilla_api.api_views.attendance.views import (
    AttendanceRequestCancelView,
    AttendanceRequestRejectView,
)


class FakeQuerySet:
    def __init__(self, attendance):
        self.attendance = attendance

    def get(self, *args, **kwargs):
        return self.attendance

    def filter(self, *args, **kwargs):
        return self

    def select_for_update(self):
        return self


class FakeAttendance(SimpleNamespace):
    def __init__(self, **overrides):
        owner_user = overrides.pop("owner_user", SimpleNamespace(id=10, is_authenticated=True, is_active=True, employee_get=SimpleNamespace(id=900, is_active=True)))
        employee = overrides.pop(
            "employee",
            SimpleNamespace(
                id=101,
                is_active=True,
                employee_user_id=owner_user,
                employee_work_info=SimpleNamespace(reporting_manager_id=None),
            ),
        )
        defaults = {
            "id": 88,
            "pk": 88,
            "employee_id": employee,
            "employee_id_id": employee.id,
            "attendance_date": date(2026, 3, 19),
            "attendance_clock_in_date": date(2026, 3, 19),
            "attendance_clock_in": time(9, 0),
            "attendance_clock_out_date": date(2026, 3, 19),
            "attendance_clock_out": time(17, 0),
            "request_type": "update_request",
            "requested_data": {"__meta": {"current_scope": "IN"}},
            "is_validate_request": True,
            "is_validate_request_approved": False,
            "action_by": None,
            "action_type": None,
            "action_at": None,
        }
        defaults.update(overrides)
        super().__init__(**defaults)
        self.refresh_count = 0
        self.save_calls = []

    def save(self, *args, **kwargs):
        self.save_calls.append(kwargs)

    def refresh_from_db(self):
        self.refresh_count += 1


class AttendanceRequestLifecycleRecomputeExecutableTests(SimpleTestCase):
    databases = "__all__"

    def setUp(self):
        self.web_factory = RequestFactory()
        self.api_factory = APIRequestFactory()
        self.owner_user = SimpleNamespace(id=10, is_authenticated=True, is_active=True, employee_get=SimpleNamespace(id=601, is_active=True), has_perm=lambda perm: True)
        self.manager_user = SimpleNamespace(id=11, is_authenticated=True, is_active=True, employee_get=SimpleNamespace(id=602, is_active=True), has_perm=lambda perm: True)

    def _unwrap(self, fn):
        return inspect.unwrap(fn)

    def test_web_cancel_recomputes_only_create_request_and_leaves_update_request_history_only(self):
        create_attendance = FakeAttendance(owner_user=self.owner_user, request_type="create_request")
        create_request = self.web_factory.post("/attendance/cancel/88")
        create_request.user = self.owner_user
        create_request.session = {}
        create_request.META["HTTP_REFERER"] = "/mine"

        with patch("attendance.views.requests.Attendance.objects.select_for_update", return_value=FakeQuerySet(create_attendance)), patch(
            "attendance.views.requests.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "attendance.views.requests.clear_request_override_and_recompute",
            return_value=create_attendance,
        ) as clear_reset, patch(
            "attendance.views.requests._log_attendance_request_action"
        ), patch(
            "attendance.views.requests.messages.success"
        ), patch(
            "attendance.views.requests.messages.error"
        ):
            response = self._unwrap(cancel_attendance_request)(create_request, create_attendance.id)

        self.assertIsInstance(response, HttpResponseRedirect)
        clear_reset.assert_called_once_with(create_attendance, include_in=True, include_out=False)
        self.assertEqual(create_attendance.request_type, "cancel_request")
        self.assertEqual(create_attendance.action_type, AttendanceRequestActionType.CANCELED)

        update_attendance = FakeAttendance(owner_user=self.owner_user, request_type="update_request")
        update_request = self.web_factory.post("/attendance/cancel/88")
        update_request.user = self.owner_user
        update_request.session = {}
        update_request.META["HTTP_REFERER"] = "/mine"

        with patch("attendance.views.requests.Attendance.objects.select_for_update", return_value=FakeQuerySet(update_attendance)), patch(
            "attendance.views.requests.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "attendance.views.requests.clear_request_override_and_recompute",
            return_value=update_attendance,
        ) as clear_reset, patch(
            "attendance.views.requests._log_attendance_request_action"
        ), patch(
            "attendance.views.requests.messages.success"
        ), patch(
            "attendance.views.requests.messages.error"
        ):
            response = self._unwrap(cancel_attendance_request)(update_request, update_attendance.id)

        self.assertIsInstance(response, HttpResponseRedirect)
        clear_reset.assert_not_called()
        self.assertEqual(update_attendance.request_type, "cancel_request")

    def test_web_revoke_restores_raw_then_recomputes(self):
        attendance = FakeAttendance(owner_user=self.owner_user, request_type="approved", is_validate_request=False, is_validate_request_approved=True)
        request = self.web_factory.post("/attendance/revoke/88")
        request.user = self.manager_user
        request.session = {}
        request.META["HTTP_REFERER"] = "/requests"
        sequence = []
        qs = FakeQuerySet(attendance)

        with patch("employee.models.EmployeeWorkInformation.objects.filter") as mgr_filter, patch("attendance.views.requests.Attendance.objects.filter", return_value=qs), patch(
            "attendance.views.requests.filtersubordinates",
            return_value=qs,
        ), patch(
            "attendance.views.requests.get_requested_sessions",
            return_value=(True, True),
        ), patch(
            "attendance.views.requests._restore_request_back_to_raw",
            side_effect=lambda *args, **kwargs: sequence.append("restore"),
        ), patch(
            "attendance.views.requests._log_attendance_request_action",
            side_effect=lambda *args, **kwargs: sequence.append("log"),
        ), patch(
            "attendance.views.requests.recompute_attendance",
            side_effect=lambda *args, **kwargs: sequence.append("recompute") or SimpleNamespace(attendance=attendance),
        ), patch(
            "attendance.views.requests.messages.success"
        ), patch(
            "attendance.views.requests.messages.error"
        ):
            mgr_filter.return_value.exists.return_value = False
            response = self._unwrap(revoke_validate_attendance_request)(request, attendance.id)

        self.assertIsInstance(response, HttpResponseRedirect)
        self.assertEqual(sequence, ["restore", "log", "recompute"])
        self.assertEqual(attendance.request_type, "revoke_request")
        self.assertEqual(attendance.action_type, AttendanceRequestActionType.REVOKED)

    def test_api_reject_recomputes_only_create_request(self):
        create_attendance = FakeAttendance(owner_user=self.owner_user, request_type="create_request")
        create_request = self.api_factory.put("/api/attendance/attendance-request-reject/88", {"reason": "invalid"}, format="json")
        force_authenticate(create_request, user=self.manager_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=FakeQuerySet(create_attendance)), patch(
            "horilla_api.api_views.attendance.views._can_act_on_employee",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "horilla_api.api_views.attendance.views.clear_request_override_and_recompute",
            return_value=create_attendance,
        ) as clear_reset, patch(
            "horilla_api.api_views.attendance.views._log_attendance_request_status_change"
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"request_type": "reject_request"}),
        ):
            response = AttendanceRequestRejectView.as_view()(create_request, pk=create_attendance.id)

        self.assertEqual(response.status_code, 200)
        clear_reset.assert_called_once_with(create_attendance, include_in=True, include_out=False)

        update_attendance = FakeAttendance(owner_user=self.owner_user, request_type="update_request")
        update_request = self.api_factory.put("/api/attendance/attendance-request-reject/88", {"reason": "invalid"}, format="json")
        force_authenticate(update_request, user=self.manager_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=FakeQuerySet(update_attendance)), patch(
            "horilla_api.api_views.attendance.views._can_act_on_employee",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "horilla_api.api_views.attendance.views.clear_request_override_and_recompute",
            return_value=update_attendance,
        ) as clear_reset, patch(
            "horilla_api.api_views.attendance.views._log_attendance_request_status_change"
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"request_type": "reject_request"}),
        ):
            response = AttendanceRequestRejectView.as_view()(update_request, pk=update_attendance.id)

        self.assertEqual(response.status_code, 200)
        clear_reset.assert_not_called()

    def test_api_cancel_returns_recomputed_attendance_object_when_create_request_is_canceled(self):
        attendance = FakeAttendance(owner_user=self.owner_user, request_type="create_request")
        request = self.api_factory.put("/api/attendance/attendance-request-cancel/88", {}, format="json")
        force_authenticate(request, user=self.owner_user)
        recomputed = FakeAttendance(owner_user=self.owner_user, request_type="cancel_request", is_validate_request=False)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=FakeQuerySet(attendance)), patch(
            "horilla_api.api_views.attendance.views.clear_request_override_and_recompute",
            return_value=recomputed,
        ), patch(
            "horilla_api.api_views.attendance.views._log_attendance_request_status_change"
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            side_effect=lambda obj, context=None: SimpleNamespace(data={"id": obj.id, "request_type": obj.request_type}),
        ):
            response = AttendanceRequestCancelView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data["request_type"], "cancel_request")
