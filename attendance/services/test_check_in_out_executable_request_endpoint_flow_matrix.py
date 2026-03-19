from __future__ import annotations

import inspect
from datetime import date, time
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.http import HttpResponseRedirect
from django.test import RequestFactory, SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import AttendanceRequestActionType
from attendance.views.requests import (
    approve_validate_attendance_request,
    reject_validate_attendance_request,
)
from horilla_api.api_views.attendance.views import (
    AttendanceRequestApproveView,
    AttendanceRequestCancelView,
    AttendanceRequestRevokeView,
)


class FakeQuerySet:
    def __init__(self, attendance):
        self.attendance = attendance
        self.updated = []

    def get(self, *args, **kwargs):
        return self.attendance

    def update(self, **kwargs):
        self.updated.append(kwargs)
        return 1

    def filter(self, *args, **kwargs):
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
                employee_first_name="Test",
                employee_work_info=SimpleNamespace(reporting_manager_id=None),
            ),
        )
        defaults = {
            "id": 77,
            "pk": 77,
            "employee_id": employee,
            "employee_id_id": employee.id,
            "attendance_date": date(2026, 3, 18),
            "attendance_clock_in_date": date(2026, 3, 18),
            "attendance_clock_in": time(9, 0),
            "attendance_clock_in_channel": "biometric",
            "attendance_clock_out_date": date(2026, 3, 18),
            "attendance_clock_out": time(17, 0),
            "attendance_clock_out_channel": "biometric",
            "request_type": "update_request",
            "request_description": "Fix attendance",
            "requested_data": {"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}},
            "is_validate_request": True,
            "is_validate_request_approved": False,
            "attendance_validated": False,
            "action_by": None,
            "action_type": None,
            "action_at": None,
        }
        defaults.update(overrides)
        super().__init__(**defaults)
        self.save_calls = []
        self.refresh_count = 0

    def save(self, *args, **kwargs):
        self.save_calls.append(kwargs)

    def refresh_from_db(self):
        self.refresh_count += 1


class AttendanceRequestEndpointFlowExecutableTests(SimpleTestCase):
    databases = "__all__"

    def setUp(self):
        self.web_factory = RequestFactory()
        self.api_factory = APIRequestFactory()
        self.owner_user = SimpleNamespace(
            id=10,
            is_authenticated=True,
            is_active=True,
            employee_get=SimpleNamespace(id=501, is_active=True),
            has_perm=lambda perm: True,
        )
        self.manager_user = SimpleNamespace(
            id=11,
            is_authenticated=True,
            is_active=True,
            employee_get=SimpleNamespace(id=502, is_active=True),
            has_perm=lambda perm: True,
        )
        self.attendance = FakeAttendance(owner_user=self.owner_user)

    def _unwrap(self, fn):
        return inspect.unwrap(fn)

    def test_web_approve_flow_applies_snapshot_logs_and_recomputes(self):
        request = self.web_factory.post("/attendance/approve/77")
        request.user = self.manager_user
        request.session = {}
        request.META["HTTP_REFERER"] = "/previous"
        sequence = []
        locked = FakeQuerySet(self.attendance)
        updated = FakeQuerySet(self.attendance)

        with patch("employee.models.EmployeeWorkInformation.objects.filter") as mgr_filter, patch("attendance.views.requests.Attendance.objects.select_for_update", return_value=locked), patch(
            "attendance.views.requests.Attendance.objects.filter",
            return_value=updated,
        ), patch(
            "attendance.views.requests.validate_requested_data_with_windows",
            return_value=(True, None),
        ), patch(
            "attendance.views.requests.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "attendance.views.requests._apply_request_override_snapshot",
            side_effect=lambda *args, **kwargs: sequence.append("snapshot"),
        ), patch(
            "attendance.views.requests._log_attendance_request_action",
            side_effect=lambda *args, **kwargs: sequence.append("log"),
        ), patch(
            "attendance.views.requests._mark_approved_request_channels",
            side_effect=lambda *args, **kwargs: sequence.append("mark"),
        ), patch(
            "attendance.views.requests._detach_request_overridden_raw_links",
            side_effect=lambda *args, **kwargs: sequence.append("detach"),
        ), patch(
            "attendance.views.requests.recompute_attendance",
            side_effect=lambda *args, **kwargs: sequence.append("recompute") or SimpleNamespace(attendance=self.attendance),
        ), patch(
            "attendance.views.requests.notify.send",
            side_effect=lambda *args, **kwargs: sequence.append("notify"),
        ), patch(
            "attendance.views.requests.reverse",
            return_value="/attendance/request-attendance-view",
        ), patch(
            "attendance.views.requests.messages.success"
        ) as success, patch(
            "attendance.views.requests.messages.error"
        ) as error:
            mgr_filter.return_value.exists.return_value = False
            response = self._unwrap(approve_validate_attendance_request)(request, self.attendance.id)

        self.assertIsInstance(response, HttpResponseRedirect)
        self.assertEqual(response.url, "/previous")
        self.assertFalse(self.attendance.is_validate_request)
        self.assertTrue(self.attendance.is_validate_request_approved)
        self.assertEqual(self.attendance.action_type, AttendanceRequestActionType.APPROVED)
        self.assertIn("snapshot", sequence)
        self.assertIn("mark", sequence)
        self.assertIn("detach", sequence)
        self.assertIn("recompute", sequence)
        self.assertIn("notify", sequence)
        self.assertEqual(updated.updated[-1], {"attendance_clock_in": "09:00:00"})
        success.assert_called_once()
        error.assert_not_called()

    def test_web_reject_flow_for_create_request_requires_reason_and_resets_canonical(self):
        attendance = FakeAttendance(owner_user=self.owner_user, request_type="create_request")
        request = self.web_factory.post("/attendance/reject/77", {"reason": "Invalid proof"})
        request.user = self.manager_user
        request.session = {}
        request.META["HTTP_REFERER"] = "/inbox"
        sequence = []
        locked = FakeQuerySet(attendance)

        with patch("employee.models.EmployeeWorkInformation.objects.filter") as mgr_filter, patch("attendance.views.requests.Attendance.objects.select_for_update", return_value=locked), patch(
            "attendance.views.requests.user_can_approve_request",
            return_value=True,
        ), patch(
            "attendance.views.requests.get_requested_sessions",
            return_value=(True, True),
        ), patch(
            "attendance.views.requests.clear_request_override_and_recompute",
            side_effect=lambda *args, **kwargs: sequence.append(("reset", kwargs)) or attendance,
        ), patch(
            "attendance.views.requests._log_attendance_request_action",
            side_effect=lambda *args, **kwargs: sequence.append(("log", kwargs.get("remark"))),
        ), patch(
            "attendance.views.requests.messages.success"
        ) as success, patch(
            "attendance.views.requests.messages.error"
        ) as error:
            mgr_filter.return_value.exists.return_value = False
            response = self._unwrap(reject_validate_attendance_request)(request, attendance.id)

        self.assertIsInstance(response, HttpResponseRedirect)
        self.assertEqual(attendance.request_type, "reject_request")
        self.assertFalse(attendance.is_validate_request)
        self.assertFalse(attendance.is_validate_request_approved)
        self.assertEqual(attendance.action_type, AttendanceRequestActionType.REJECTED)
        self.assertIn(("log", "Invalid proof"), sequence)
        self.assertIn(("reset", {"include_in": True, "include_out": True}), sequence)
        success.assert_called_once()
        error.assert_not_called()

    def test_api_approve_flow_marks_request_channels_and_serializes_recomputed_attendance(self):
        request = self.api_factory.put("/api/attendance/attendance-request-approve/77", {}, format="json")
        force_authenticate(request, user=self.manager_user)
        attendance = FakeAttendance(owner_user=self.owner_user)
        locked = FakeQuerySet(attendance)
        updated = FakeQuerySet(attendance)
        sequence = []
        final_attendance = FakeAttendance(owner_user=self.owner_user, attendance_clock_in_channel="approved_request")

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=locked), patch(
            "horilla_api.api_views.attendance.views.Attendance.objects.filter",
            return_value=updated,
        ), patch(
            "horilla_api.api_views.attendance.views.user_can_approve_request",
            return_value=True,
        ), patch(
            "horilla_api.api_decorators.base.decorators.ManagerPermission.has_permission",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.validate_requested_data_with_windows",
            return_value=(True, None),
        ), patch(
            "horilla_api.api_views.attendance.views.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "horilla_api.api_views.attendance.views._apply_request_override_snapshot",
            side_effect=lambda *args, **kwargs: sequence.append("snapshot"),
        ), patch(
            "horilla_api.api_views.attendance.views._mark_approved_request_channels",
            side_effect=lambda *args, **kwargs: sequence.append("mark"),
        ), patch(
            "horilla_api.api_views.attendance.views._detach_request_overridden_raw_links",
            side_effect=lambda *args, **kwargs: sequence.append("detach"),
        ), patch(
            "horilla_api.api_views.attendance.views._log_attendance_request_status_change",
            side_effect=lambda *args, **kwargs: sequence.append("log"),
        ), patch(
            "horilla_api.api_views.attendance.views.recompute_attendance",
            side_effect=lambda *args, **kwargs: sequence.append("recompute") or SimpleNamespace(attendance=final_attendance),
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"id": attendance.id, "request_type": "approved", "clock_in_channel": "approved_request"}),
        ):
            response = AttendanceRequestApproveView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data["clock_in_channel"], "approved_request")
        self.assertFalse(attendance.is_validate_request)
        self.assertTrue(attendance.is_validate_request_approved)
        self.assertEqual(attendance.action_type, AttendanceRequestActionType.APPROVED)
        self.assertEqual(updated.updated[-1], {"attendance_clock_in": "09:00:00"})
        self.assertEqual(sequence[:3], ["snapshot", "log", "mark"])
        self.assertIn("detach", sequence)
        self.assertIn("recompute", sequence)

    def test_api_cancel_and_revoke_endpoint_flows_drive_expected_recompute_helpers(self):
        cancel_request = self.api_factory.put("/api/attendance/attendance-request-cancel/77", {}, format="json")
        force_authenticate(cancel_request, user=self.owner_user)
        cancel_attendance = FakeAttendance(owner_user=self.owner_user, request_type="create_request")
        cancel_locked = FakeQuerySet(cancel_attendance)
        canceled_final = FakeAttendance(owner_user=self.owner_user, request_type="cancel_request", is_validate_request=False)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=cancel_locked), patch(
            "horilla_api.api_views.attendance.views.clear_request_override_and_recompute",
            return_value=canceled_final,
        ) as clear_reset, patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"request_type": "cancel_request"}),
        ):
            cancel_response = AttendanceRequestCancelView.as_view()(cancel_request, pk=cancel_attendance.id)

        self.assertEqual(cancel_response.status_code, 200)
        clear_reset.assert_called_once_with(cancel_attendance, include_in=True, include_out=False)

        revoke_request = self.api_factory.put("/api/attendance/attendance-request-revoke/77", {}, format="json")
        force_authenticate(revoke_request, user=self.manager_user)
        revoke_attendance = FakeAttendance(owner_user=self.owner_user, is_validate_request=False, is_validate_request_approved=True)
        revoke_locked = FakeQuerySet(revoke_attendance)
        revoke_sequence = []

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update", return_value=revoke_locked), patch(
            "horilla_api.api_decorators.base.decorators.ManagerPermission.has_permission",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views._can_act_on_employee",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.get_requested_sessions",
            return_value=(True, False),
        ), patch(
            "horilla_api.api_views.attendance.views._restore_request_back_to_raw",
            side_effect=lambda *args, **kwargs: revoke_sequence.append(("restore", kwargs)),
        ), patch(
            "horilla_api.api_views.attendance.views._log_attendance_request_status_change",
            side_effect=lambda *args, **kwargs: revoke_sequence.append(("log", kwargs.get("new_status"))),
        ), patch(
            "horilla_api.api_views.attendance.views.recompute_attendance",
            side_effect=lambda *args, **kwargs: revoke_sequence.append(("recompute", args[1])) or SimpleNamespace(attendance=revoke_attendance),
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"request_type": "revoke_request"}),
        ):
            revoke_response = AttendanceRequestRevokeView.as_view()(revoke_request, pk=revoke_attendance.id)

        self.assertEqual(revoke_response.status_code, 200)
        self.assertIn(("log", "revoke_request"), revoke_sequence)
        self.assertTrue(any(item[0] == "restore" for item in revoke_sequence))
        self.assertTrue(any(item[0] == "recompute" for item in revoke_sequence))
