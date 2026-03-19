from __future__ import annotations

from types import SimpleNamespace

from django.test import SimpleTestCase

from attendance.models import AttendanceWorkMode, WorkModeRequestStatus
from attendance.services.check_in_out_test_blueprints import build_priority_scenarios
from attendance.services.work_type_request_rules import EffectiveWorkType, punch_allowed


class CheckInOutPolicyMatrixBlueprintTests(SimpleTestCase):
    def test_wfo_without_request_blocks_mobile_punch(self):
        eff = EffectiveWorkType(mode=AttendanceWorkMode.WFO, source="schedule", request=None)
        self.assertFalse(punch_allowed(eff))

    def test_wfa_request_only_unlocks_mobile_when_approved(self):
        request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.PENDING)
        eff = EffectiveWorkType(mode=AttendanceWorkMode.WFA, source="request", request=request)
        self.assertFalse(punch_allowed(eff))

        request.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
        self.assertFalse(punch_allowed(eff))

        request.status = WorkModeRequestStatus.APPROVED
        self.assertTrue(punch_allowed(eff))

    def test_on_duty_request_only_unlocks_mobile_when_approved(self):
        request = SimpleNamespace(mode=AttendanceWorkMode.ON_DUTY, status=WorkModeRequestStatus.PENDING)
        eff = EffectiveWorkType(mode=AttendanceWorkMode.ON_DUTY, source="request", request=request)
        self.assertFalse(punch_allowed(eff))

        request.status = WorkModeRequestStatus.APPROVED
        self.assertTrue(punch_allowed(eff))

    def test_scheduled_wfa_and_scheduled_on_duty_allow_mobile_punch(self):
        self.assertTrue(
            punch_allowed(EffectiveWorkType(mode=AttendanceWorkMode.WFA, source="schedule", request=None))
        )
        self.assertTrue(
            punch_allowed(EffectiveWorkType(mode=AttendanceWorkMode.ON_DUTY, source="schedule", request=None))
        )

    def test_priority_matrix_includes_mobile_duplicate_and_half_day_cases(self):
        priority = build_priority_scenarios()
        ids = {case.scenario_id for case in priority}
        self.assertTrue(any("MOB_MULTI_IN_ATTEMPT" in case_id for case_id in ids))
        self.assertTrue(any("LEAVE_FIRST_HALF_APPROVED" in case_id for case_id in ids))
        self.assertTrue(any("LEAVE_SECOND_HALF_APPROVED" in case_id for case_id in ids))
