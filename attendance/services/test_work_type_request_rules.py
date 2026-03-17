from __future__ import annotations

from datetime import date
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.models import WorkModeRequestDocumentStatus, WorkModeRequestRejectReasonCode, WorkModeRequestScope, WorkModeRequestStatus
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

    def test_scheduled_on_duty_still_allows_punch(self):
        eff = work_type_request_rules.EffectiveWorkType(mode="on_duty", source="schedule", request=None)

        self.assertTrue(work_type_request_rules.punch_allowed(eff))


class WorkTypeRequestVersionedDocumentRuleTests(SimpleTestCase):
    databases = {"default"}
    def test_has_attachments_prefers_current_document_version(self):
        version = SimpleNamespace(file_links=SimpleNamespace(exists=lambda: True))
        req = SimpleNamespace(current_document_version=version, files=SimpleNamespace(exists=lambda: False))

        self.assertTrue(work_type_request_rules.has_attachments(req))

    def test_auto_reject_waiting_for_date_delegates_to_action_service(self):
        req = SimpleNamespace(id=7, scope=WorkModeRequestScope.IN)
        employee = SimpleNamespace(id=10)
        from datetime import datetime
        now_dt = datetime(2026, 3, 16, 9, 0)
        cutoff = datetime(2026, 3, 16, 8, 0)
        calls = []

        def _capture(target_req, *, actor=None, now_dt=None):
            calls.append((target_req, actor, now_dt))
            return 'ok'

        class FakeQS:
            def __iter__(self):
                return iter([req])

        manager = SimpleNamespace(select_for_update=lambda: SimpleNamespace(filter=lambda **kwargs: FakeQS()))

        with patch('attendance.models.WorkModeRequest.objects', manager),              patch('attendance.services.work_type_request_actions.WorkModeRequestActions._auto_reject_for_cutoff', side_effect=_capture):
            result = work_type_request_rules.auto_reject_wfa_waiting_for_date(
                employee=employee,
                target_date=date(2026, 3, 16),
                now_dt=now_dt,
                cutoff_in_dt=cutoff,
                cutoff_out_dt=None,
            )

        self.assertEqual(result, 1)
        self.assertEqual(calls, [(req, None, now_dt)])
