from __future__ import annotations

from datetime import date
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.core.exceptions import ValidationError
from django.test import SimpleTestCase

from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)
from attendance.services import work_type_request_rules


class WorkTypeRequestRuleTests(SimpleTestCase):
    def test_rejected_request_recomputes_affected_date_range(self):
        calls = []

        req = SimpleNamespace(
            employee_id="EMP-1",
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 16),
            status=WorkModeRequestStatus.REJECTED,
            reason_code=None,
            save=lambda update_fields=None: None,
        )

        with patch.object(
            work_type_request_rules,
            "recompute_attendance_range",
            lambda employee, start_date, end_date: calls.append((employee, start_date, end_date)),
        ):
            recomputed = work_type_request_rules.apply_rejection_to_attendance.__wrapped__(req)

        self.assertEqual(recomputed, 3)
        self.assertEqual(req.reason_code, WorkModeRequestRejectReasonCode.MANUAL_REJECT)
        self.assertEqual(calls, [("EMP-1", date(2026, 3, 14), date(2026, 3, 16))])


    def test_on_duty_request_requires_approval_before_punch(self):
        request = SimpleNamespace(mode="on_duty", status=WorkModeRequestStatus.PENDING)
        eff = work_type_request_rules.EffectiveWorkType(mode="on_duty", source="request", request=request)

        self.assertFalse(work_type_request_rules.punch_allowed(eff))

        request.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
        self.assertFalse(work_type_request_rules.punch_allowed(eff))

        request.status = WorkModeRequestStatus.APPROVED
        self.assertTrue(work_type_request_rules.punch_allowed(eff))

    def test_committed_work_type_ignores_waiting_request_and_keeps_schedule(self):
        employee = SimpleNamespace(id=10)

        with patch.object(work_type_request_rules, "pick_committed_request", return_value=None), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO):
            eff = work_type_request_rules.committed_work_type(employee, date(2026, 4, 7), "in")

        self.assertEqual(eff.mode, AttendanceWorkMode.WFO)
        self.assertEqual(eff.source, "schedule")
        self.assertIsNone(eff.request)

    def test_committed_work_type_prefers_approved_request(self):
        employee = SimpleNamespace(id=10)
        approved_req = SimpleNamespace(mode=AttendanceWorkMode.WFH, status=WorkModeRequestStatus.APPROVED)

        with patch.object(work_type_request_rules, "pick_committed_request", return_value=approved_req):
            eff = work_type_request_rules.committed_work_type(employee, date(2026, 4, 7), "in")

        self.assertEqual(eff.mode, AttendanceWorkMode.WFH)
        self.assertEqual(eff.source, "approved_request")
        self.assertIs(eff.request, approved_req)


class WorkTypeRequestValidationMatrixTests(SimpleTestCase):
    def _overlap_qs(self, *, range_exists=False, full_exists=False, same_scope_exists=False, capture=None):
        base = MagicMock(name="base_qs")
        active = MagicMock(name="active_qs")
        active_after_exclude = MagicMock(name="active_after_exclude")
        overlap = MagicMock(name="overlap_qs")
        full_scope = MagicMock(name="full_scope_qs")
        same_scope = MagicMock(name="same_scope_qs")

        base.filter.return_value = active

        def _active_filter(*args, **kwargs):
            if kwargs:
                return overlap
            return active

        active.filter.side_effect = _active_filter
        active.exclude.return_value = active_after_exclude
        active_after_exclude.filter.return_value = overlap
        if capture is not None:
            capture["active"] = active

        overlap.exists.return_value = range_exists

        def _overlap_filter(*args, **kwargs):
            if kwargs.get("scope") == WorkModeRequestScope.FULL:
                return full_scope
            if kwargs.get("scope") in (WorkModeRequestScope.IN, WorkModeRequestScope.OUT):
                return same_scope
            return overlap

        overlap.filter.side_effect = _overlap_filter
        full_scope.exists.return_value = full_exists
        same_scope.exists.return_value = same_scope_exists
        return base

    def test_create_rejects_backdated_request(self):
        employee = SimpleNamespace(id=10)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)):
            with self.assertRaisesMessage(ValidationError, "Start date cannot be in the past"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.WFA,
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 19),
                    end_date=date(2026, 3, 19),
                )

    def test_create_rejects_unknown_mode(self):
        employee = SimpleNamespace(id=10)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)):
            with self.assertRaisesMessage(ValidationError, "only supports WFA, WFH and ON DUTY"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode="hybrid",
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 20),
                )

    def test_create_accepts_wfh_mode(self):
        employee = SimpleNamespace(id=10)
        overlap_qs = self._overlap_qs()
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)),              patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO),              patch.object(work_type_request_rules.WorkModeRequest.objects, "filter", return_value=overlap_qs):
            work_type_request_rules.validate_work_type_request(
                employee=employee,
                mode=AttendanceWorkMode.WFH,
                scope=WorkModeRequestScope.FULL,
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 20),
            )

    def test_create_rejects_when_schedule_already_same_wfh_mode(self):
        employee = SimpleNamespace(id=10)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)),              patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFH):
            with self.assertRaisesMessage(ValidationError, "already WFH"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.WFH,
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 20),
                )

    def test_create_rejects_multiday_in_scope(self):
        employee = SimpleNamespace(id=10)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)):
            with self.assertRaisesMessage(ValidationError, "Scope IN/OUT must be a single day"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.WFA,
                    scope=WorkModeRequestScope.IN,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 21),
                )

    def test_create_rejects_full_scope_when_end_before_start(self):
        employee = SimpleNamespace(id=10)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)):
            with self.assertRaisesMessage(ValidationError, "End date must be on/after start date"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.WFA,
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 21),
                    end_date=date(2026, 3, 20),
                )

    def test_create_rejects_when_schedule_already_same_mode(self):
        employee = SimpleNamespace(id=10)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFA):
            with self.assertRaisesMessage(ValidationError, "already WFA"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.WFA,
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 20),
                )

    def test_create_allows_wfa_schedule_with_on_duty_request(self):
        employee = SimpleNamespace(id=10)
        overlap_qs = self._overlap_qs()
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFA), \
             patch.object(work_type_request_rules.WorkModeRequest.objects, "filter", return_value=overlap_qs):
            work_type_request_rules.validate_work_type_request(
                employee=employee,
                mode=AttendanceWorkMode.ON_DUTY,
                scope=WorkModeRequestScope.FULL,
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 20),
            )

    def test_overlap_full_vs_full_is_blocked(self):
        employee = SimpleNamespace(id=10)
        overlap_qs = self._overlap_qs(range_exists=True)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO), \
             patch.object(work_type_request_rules.WorkModeRequest.objects, "filter", return_value=overlap_qs):
            with self.assertRaisesMessage(ValidationError, "FULL request date range overlaps"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.WFA,
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 22),
                )

    def test_overlap_full_request_blocks_single_scope_request(self):
        employee = SimpleNamespace(id=10)
        overlap_qs = self._overlap_qs(full_exists=True)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO), \
             patch.object(work_type_request_rules.WorkModeRequest.objects, "filter", return_value=overlap_qs):
            with self.assertRaisesMessage(ValidationError, "Cannot create IN/OUT request when a FULL request covers the date"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.ON_DUTY,
                    scope=WorkModeRequestScope.IN,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 20),
                )

    def test_overlap_same_scope_same_day_is_blocked(self):
        employee = SimpleNamespace(id=10)
        overlap_qs = self._overlap_qs(same_scope_exists=True)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO), \
             patch.object(work_type_request_rules.WorkModeRequest.objects, "filter", return_value=overlap_qs):
            with self.assertRaisesMessage(ValidationError, "Only one request per scope"):
                work_type_request_rules.validate_work_type_request(
                    employee=employee,
                    mode=AttendanceWorkMode.ON_DUTY,
                    scope=WorkModeRequestScope.OUT,
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 20),
                )

    def test_update_excludes_current_request_from_overlap_detection(self):
        employee = SimpleNamespace(id=10)
        capture = {}
        overlap_qs = self._overlap_qs(capture=capture)
        with patch.object(work_type_request_rules.timezone, "localdate", return_value=date(2026, 3, 20)), \
             patch.object(work_type_request_rules, "scheduled_attendance_mode", return_value=AttendanceWorkMode.WFO), \
             patch.object(work_type_request_rules.WorkModeRequest.objects, "filter", return_value=overlap_qs):
            work_type_request_rules.validate_work_type_request(
                employee=employee,
                mode=AttendanceWorkMode.ON_DUTY,
                scope=WorkModeRequestScope.OUT,
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 20),
                instance_id=99,
            )

        capture["active"].exclude.assert_called_once_with(id=99)


class WorkTypeRequestActionServiceTests(SimpleTestCase):
    def test_rejection_preserves_explicit_reason_code(self):
        req = SimpleNamespace(
            employee_id="EMP-1",
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 15),
            status=WorkModeRequestStatus.REJECTED,
            reason_code=WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_IN_PASSED,
            save=MagicMock(),
        )
        calls = []

        with patch.object(
            work_type_request_rules,
            "recompute_attendance_range",
            lambda employee, start_date, end_date: calls.append((employee, start_date, end_date)),
        ):
            recomputed = work_type_request_rules.apply_rejection_to_attendance.__wrapped__(req)

        self.assertEqual(recomputed, 2)
        self.assertEqual(req.reason_code, WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_IN_PASSED)
        req.save.assert_not_called()
        self.assertEqual(calls, [("EMP-1", date(2026, 3, 14), date(2026, 3, 15))])

    def test_wfa_request_requires_approval_before_punch(self):
        request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.PENDING)
        eff = work_type_request_rules.EffectiveWorkType(mode=AttendanceWorkMode.WFA, source="request", request=request)

        self.assertFalse(work_type_request_rules.punch_allowed(eff))

        request.status = WorkModeRequestStatus.APPROVED
        self.assertTrue(work_type_request_rules.punch_allowed(eff))
