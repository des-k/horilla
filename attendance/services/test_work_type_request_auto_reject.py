from __future__ import annotations

from datetime import date, datetime
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.test import SimpleTestCase

from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequestActionType,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)
from attendance.services import work_type_request_rules
from attendance.services.work_type_request_actions import WorkModeRequestActions


class WorkTypeAutoRejectCutoffTests(SimpleTestCase):
    def _request(self, *, scope=WorkModeRequestScope.FULL, mode=AttendanceWorkMode.WFA):
        return SimpleNamespace(
            id=81,
            mode=mode,
            scope=scope,
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            reason_code=None,
            approved_by='manager',
            approved_at='before',
            action_by=None,
            action_at=None,
            action_type=None,
            action_reason=None,
            employee_id='EMP-1',
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 14),
            save=MagicMock(),
        )

    def test_before_cutoff_request_not_auto_rejected(self):
        req = self._request(scope=WorkModeRequestScope.IN)
        now_dt = datetime(2026, 3, 14, 9, 0)
        due_dt = datetime(2026, 3, 14, 10, 0)

        with patch.object(WorkModeRequestActions, '_cutoff_due_datetime', return_value=due_dt), \
             patch.object(WorkModeRequestActions, '_now', return_value=now_dt), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance') as apply_rejection:
            result = WorkModeRequestActions._auto_reject_for_cutoff(req, actor=None, now_dt=now_dt)

        self.assertIsNone(result)
        self.assertEqual(req.status, WorkModeRequestStatus.WAITING_FOR_APPROVAL)
        apply_rejection.assert_not_called()

    def test_after_cutoff_in_scope_sets_in_reason_code(self):
        req = self._request(scope=WorkModeRequestScope.IN)
        now_dt = datetime(2026, 3, 14, 11, 0)
        due_dt = datetime(2026, 3, 14, 10, 0)

        with patch.object(WorkModeRequestActions, '_cutoff_due_datetime', return_value=due_dt), \
             patch.object(WorkModeRequestActions, '_now', return_value=now_dt), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance') as apply_rejection:
            result = WorkModeRequestActions._auto_reject_for_cutoff(req, actor=None, now_dt=now_dt)

        self.assertTrue(result.auto_rejected)
        self.assertEqual(req.status, WorkModeRequestStatus.REJECTED)
        self.assertEqual(req.reason_code, WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_IN_PASSED)
        self.assertEqual(req.action_type, WorkModeRequestActionType.AUTO_REJECTED)
        self.assertIsNone(req.approved_by)
        self.assertIsNone(req.approved_at)
        apply_rejection.assert_called_once_with(req)

    def test_after_cutoff_out_scope_sets_out_reason_code(self):
        req = self._request(scope=WorkModeRequestScope.OUT)
        now_dt = datetime(2026, 3, 14, 18, 0)
        due_dt = datetime(2026, 3, 14, 17, 0)

        with patch.object(WorkModeRequestActions, '_cutoff_due_datetime', return_value=due_dt), \
             patch.object(WorkModeRequestActions, '_now', return_value=now_dt), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance', return_value=1):
            WorkModeRequestActions._auto_reject_for_cutoff(req, actor=None, now_dt=now_dt)

        self.assertEqual(req.reason_code, WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_OUT_PASSED)

    def test_after_cutoff_full_scope_sets_full_reason_code(self):
        req = self._request(scope=WorkModeRequestScope.FULL)
        now_dt = datetime(2026, 3, 14, 13, 0)
        due_dt = datetime(2026, 3, 14, 12, 0)

        with patch.object(WorkModeRequestActions, '_cutoff_due_datetime', return_value=due_dt), \
             patch.object(WorkModeRequestActions, '_now', return_value=now_dt), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance', return_value=1):
            WorkModeRequestActions._auto_reject_for_cutoff(req, actor=None, now_dt=now_dt)

        self.assertEqual(req.reason_code, WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_FULL_PASSED)

    def test_non_wfa_request_not_auto_rejected(self):
        req = self._request(mode=AttendanceWorkMode.ON_DUTY)
        now_dt = datetime(2026, 3, 14, 13, 0)

        with patch.object(WorkModeRequestActions, '_cutoff_due_datetime', return_value=None), \
             patch.object(WorkModeRequestActions, '_now', return_value=now_dt), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance') as apply_rejection:
            result = WorkModeRequestActions._auto_reject_for_cutoff(req, actor=None, now_dt=now_dt)

        self.assertIsNone(result)
        self.assertEqual(req.status, WorkModeRequestStatus.WAITING_FOR_APPROVAL)
        apply_rejection.assert_not_called()

    def test_auto_reject_wfa_waiting_for_date_rejects_only_requests_past_scope_due(self):
        waiting_in = self._request(scope=WorkModeRequestScope.IN)
        waiting_out = self._request(scope=WorkModeRequestScope.OUT)
        current_time = datetime(2026, 3, 14, 12, 0)
        calls = []

        class FakeQS(list):
            pass

        with patch.object(
            work_type_request_rules.WorkModeRequest.objects,
            'select_for_update',
            return_value=SimpleNamespace(filter=lambda **kwargs: FakeQS([waiting_in, waiting_out])),
        ), patch.object(
            WorkModeRequestActions,
            '_auto_reject_for_cutoff',
            side_effect=lambda req, actor=None, now_dt=None: calls.append((req.scope, now_dt)) or (SimpleNamespace(auto_rejected=True) if req.scope == WorkModeRequestScope.IN else None),
        ):
            rejected = work_type_request_rules.auto_reject_wfa_waiting_for_date.__wrapped__(
                employee=SimpleNamespace(id=1),
                target_date=date(2026, 3, 14),
                now_dt=current_time,
                cutoff_in_dt=datetime(2026, 3, 14, 10, 0),
                cutoff_out_dt=datetime(2026, 3, 14, 15, 0),
            )

        self.assertEqual(rejected, 1)
        self.assertEqual(calls, [(WorkModeRequestScope.IN, current_time)])
