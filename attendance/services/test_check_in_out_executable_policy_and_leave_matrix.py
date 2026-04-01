from __future__ import annotations

from dataclasses import dataclass
from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.models import AttendanceWorkMode, WorkModeRequestScope, WorkModeRequestStatus
from attendance.services import reconciliation
from attendance.services.work_type_request_rules import EffectiveWorkType, punch_allowed


@dataclass
class FakeLeaveRequest:
    employee_id: object
    status: str
    start_date: date
    end_date: date
    start_date_breakdown: str | None = None
    end_date_breakdown: str | None = None
    id: int = 1


class FakeLeaveQuerySet(list):
    def filter(self, **kwargs):
        def matches(obj, key, expected):
            if key.endswith("__lte"):
                return getattr(obj, key[:-5]) <= expected
            if key.endswith("__gte"):
                return getattr(obj, key[:-5]) >= expected
            return getattr(obj, key) == expected

        return FakeLeaveQuerySet([
            obj for obj in self if all(matches(obj, key, value) for key, value in kwargs.items())
        ])

    def order_by(self, *fields):
        data = list(self)
        for field in reversed(fields):
            reverse = field.startswith("-")
            attr = field[1:] if reverse else field
            data.sort(key=lambda obj: getattr(obj, attr), reverse=reverse)
        return FakeLeaveQuerySet(data)

    def first(self):
        return self[0] if self else None


class FakeLeaveManager:
    def __init__(self, rows):
        self.rows = FakeLeaveQuerySet(rows)

    def filter(self, **kwargs):
        return self.rows.filter(**kwargs)


class CheckInOutExecutablePolicyAndLeaveMatrixTests(SimpleTestCase):
    def test_mobile_punch_policy_matrix(self):
        cases = [
            {
                "label": "scheduled_wfo",
                "eff": EffectiveWorkType(mode=AttendanceWorkMode.WFO, source="schedule", request=None),
                "expected": False,
            },
            {
                "label": "scheduled_wfa",
                "eff": EffectiveWorkType(mode=AttendanceWorkMode.WFA, source="schedule", request=None),
                "expected": True,
            },
            {
                "label": "scheduled_on_duty",
                "eff": EffectiveWorkType(mode=AttendanceWorkMode.ON_DUTY, source="schedule", request=None),
                "expected": True,
            },
            {
                "label": "request_wfa_pending",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.WFA,
                    source="request",
                    request=SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.PENDING),
                ),
                "expected": False,
            },
            {
                "label": "request_wfa_waiting",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.WFA,
                    source="request",
                    request=SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.WAITING_FOR_APPROVAL),
                ),
                "expected": False,
            },
            {
                "label": "request_wfa_approved",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.WFA,
                    source="request",
                    request=SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED),
                ),
                "expected": True,
            },
            {
                "label": "request_on_duty_full_pending",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.ON_DUTY,
                    source="request",
                    request=SimpleNamespace(
                        mode=AttendanceWorkMode.ON_DUTY,
                        scope=WorkModeRequestScope.FULL,
                        status=WorkModeRequestStatus.PENDING,
                    ),
                ),
                "expected": False,
            },
            {
                "label": "request_on_duty_full_approved",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.ON_DUTY,
                    source="request",
                    request=SimpleNamespace(
                        mode=AttendanceWorkMode.ON_DUTY,
                        scope=WorkModeRequestScope.FULL,
                        status=WorkModeRequestStatus.APPROVED,
                    ),
                ),
                "expected": True,
            },
            {
                "label": "request_on_duty_in_approved",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.ON_DUTY,
                    source="request",
                    request=SimpleNamespace(
                        mode=AttendanceWorkMode.ON_DUTY,
                        scope=WorkModeRequestScope.IN,
                        status=WorkModeRequestStatus.APPROVED,
                    ),
                ),
                "expected": True,
            },
            {
                "label": "request_on_duty_out_revoked",
                "eff": EffectiveWorkType(
                    mode=AttendanceWorkMode.ON_DUTY,
                    source="request",
                    request=SimpleNamespace(
                        mode=AttendanceWorkMode.ON_DUTY,
                        scope=WorkModeRequestScope.OUT,
                        status=WorkModeRequestStatus.REVOKED,
                    ),
                ),
                "expected": False,
            },
        ]

        for case in cases:
            with self.subTest(case=case["label"]):
                self.assertEqual(punch_allowed(case["eff"]), case["expected"])

    def _ctx(self, *, target_date=None, schedule=None):
        target_date = target_date or date(2026, 3, 19)
        return reconciliation.ShiftContext(
            employee="EMP-1",
            attendance_date=target_date,
            day=None,
            shift=None,
            schedule=schedule,
            shift_start_dt=timezone.make_aware(datetime.combine(target_date, time(8, 0))),
            shift_end_dt=timezone.make_aware(datetime.combine(target_date, time(17, 0))),
            check_in_window_start_dt=timezone.make_aware(datetime.combine(target_date, time(6, 0))),
            check_in_window_end_dt=timezone.make_aware(datetime.combine(target_date, time(12, 0))),
            check_out_window_start_dt=timezone.make_aware(datetime.combine(target_date, time(12, 0))),
            check_out_window_end_dt=timezone.make_aware(datetime.combine(target_date, time(23, 0))),
            minimum_hour="08:00",
            grace_seconds=1800,
            grace_clock_in_type="after",
        )

    def test_leave_matrix_resolves_half_day_thresholds_for_session_windows(self):
        schedule = SimpleNamespace(
            enable_first_half_leave_rule=True,
            first_half_leave_latest_check_in_time=time(13, 0),
            enable_second_half_leave_rule=True,
            second_half_leave_earliest_check_out_time=time(12, 0),
            break_start_time=None,
            break_end_time=None,
        )
        first_half = FakeLeaveRequest(
            employee_id="EMP-1",
            status="approved",
            start_date=date(2026, 3, 19),
            end_date=date(2026, 3, 19),
            start_date_breakdown="first_half",
            end_date_breakdown="first_half",
            id=11,
        )
        second_half = FakeLeaveRequest(
            employee_id="EMP-1",
            status="approved",
            start_date=date(2026, 3, 20),
            end_date=date(2026, 3, 20),
            start_date_breakdown="second_half",
            end_date_breakdown="second_half",
            id=12,
        )
        full_day = FakeLeaveRequest(
            employee_id="EMP-1",
            status="approved",
            start_date=date(2026, 3, 21),
            end_date=date(2026, 3, 21),
            start_date_breakdown="full_day",
            end_date_breakdown="full_day",
            id=13,
        )

        with patch.object(reconciliation, "leave_breakdown_for_attendance_date", None):
            with patch.object(reconciliation, "LeaveRequest", SimpleNamespace(objects=FakeLeaveManager([first_half]))):
                first_ctx = reconciliation._resolve_leave_context("EMP-1", date(2026, 3, 19), self._ctx(target_date=date(2026, 3, 19), schedule=schedule))
            with patch.object(reconciliation, "LeaveRequest", SimpleNamespace(objects=FakeLeaveManager([second_half]))):
                second_ctx = reconciliation._resolve_leave_context("EMP-1", date(2026, 3, 20), self._ctx(target_date=date(2026, 3, 20), schedule=schedule))
            with patch.object(reconciliation, "LeaveRequest", SimpleNamespace(objects=FakeLeaveManager([full_day]))):
                full_ctx = reconciliation._resolve_leave_context("EMP-1", date(2026, 3, 21), self._ctx(target_date=date(2026, 3, 21), schedule=schedule))
            with patch.object(reconciliation, "LeaveRequest", SimpleNamespace(objects=FakeLeaveManager([]))):
                none_ctx = reconciliation._resolve_leave_context("EMP-1", date(2026, 3, 22), self._ctx(target_date=date(2026, 3, 22), schedule=schedule))

        self.assertEqual(first_ctx.kind, "first_half")
        self.assertEqual(first_ctx.minimum_hour, "04:00")
        self.assertEqual(first_ctx.late_reference_dt, timezone.make_aware(datetime(2026, 3, 19, 13, 0)))
        self.assertEqual(first_ctx.early_reference_dt, timezone.make_aware(datetime(2026, 3, 19, 17, 30)))

        self.assertEqual(second_ctx.kind, "second_half")
        self.assertEqual(second_ctx.minimum_hour, "04:00")
        self.assertEqual(second_ctx.late_reference_dt, timezone.make_aware(datetime(2026, 3, 20, 8, 0)))
        self.assertEqual(second_ctx.early_reference_dt, timezone.make_aware(datetime(2026, 3, 20, 12, 0)))

        self.assertEqual(full_ctx.kind, "full_day")
        self.assertEqual(full_ctx.minimum_hour, "08:00")
        self.assertTrue(full_ctx.is_full_day)

        self.assertIsNone(none_ctx.kind)
        self.assertEqual(none_ctx.minimum_hour, "08:00")

