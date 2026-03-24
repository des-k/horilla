from __future__ import annotations

from dataclasses import dataclass, field
from datetime import date, datetime, time
from types import SimpleNamespace

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.models import AttendancePunchDirection, AttendanceWorkMode, WorkModeRequestDocumentStatus, WorkModeRequestStatus
from attendance.services import reconciliation


@dataclass
class FakePunchLog:
    id: int
    punch_direction: str
    punch_timestamp: datetime
    source: str = "mobile"
    attendance_id: object | None = None
    attendance_date: date | None = None
    accepted_to_attendance: bool | None = None
    reason: str | None = None
    decision_status: str | None = None
    decision_source: str | None = None
    saved_update_fields: list[list[str]] = field(default_factory=list)

    def save(self, update_fields=None):
        self.saved_update_fields.append(list(update_fields or []))


class ReconciliationCanonicalTests(SimpleTestCase):


    def _default_ctx(self):
        return reconciliation.ShiftContext(
            employee="EMP-1",
            attendance_date=date(2026, 3, 14),
            day=None,
            shift=None,
            schedule=None,
            shift_start_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            shift_end_dt=timezone.make_aware(datetime(2026, 3, 14, 17, 0)),
            check_in_window_start_dt=timezone.make_aware(datetime(2026, 3, 14, 6, 0)),
            check_in_window_end_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            check_out_window_start_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            check_out_window_end_dt=timezone.make_aware(datetime(2026, 3, 14, 23, 0)),
            minimum_hour="08:00",
            grace_seconds=0,
            grace_clock_in_type="after",
        )

    def _apply_decisions_from_raw(self, attendance, logs, raw, source=reconciliation.SOURCE_NORMAL):
        decisions = {}
        if raw.get("final_in") is not None:
            decisions[raw["final_in"].id] = (True, reconciliation.NOTE_FINAL_IN)
        if raw.get("final_out") is not None:
            decisions[raw["final_out"].id] = (True, reconciliation.NOTE_FINAL_OUT)

        for log in logs:
            if raw.get("final_in") is not None and log.id == raw["final_in"].id:
                continue
            if raw.get("final_out") is not None and log.id == raw["final_out"].id:
                continue
            if log in raw.get("extra_in", []):
                decisions[log.id] = (False, reconciliation.NOTE_DUPLICATE_CHECKIN)
                continue
            if log in raw.get("extra_out", []):
                decisions[log.id] = (False, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
                continue
            if log in raw.get("invalid_in", []):
                decisions[log.id] = (False, reconciliation.NOTE_INVALID_IN_WINDOW)
                continue
            if log in raw.get("invalid_out", []):
                decisions[log.id] = (False, reconciliation.NOTE_INVALID_OUT_WINDOW)
                continue
            decisions[log.id] = (False, "Ignored: not used in final attendance")

        reconciliation._apply_punch_decisions(attendance, logs, decisions, source)
        return decisions
    def test_overnight_threshold_maps_to_next_calendar_day(self):
        shift_start = timezone.make_aware(datetime(2026, 3, 14, 22, 0))
        shift_end = timezone.make_aware(datetime(2026, 3, 15, 6, 0))

        threshold = reconciliation._time_to_shift_instance_dt(
            time(2, 0),
            shift_start_dt=shift_start,
            shift_end_dt=shift_end,
        )

        self.assertEqual(threshold, timezone.make_aware(datetime(2026, 3, 15, 2, 0)))

    def test_first_half_threshold_late_does_not_consume_grace(self):
        late_minutes, early_minutes = reconciliation._calculate_late_early(
            final_in_dt=timezone.make_aware(datetime(2026, 3, 14, 13, 15)),
            final_out_dt=None,
            late_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 13, 0)),
            early_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 17, 0)),
            grace_seconds=600,
            grace_clock_in_type="after",
            apply_grace_to_late=False,
        )

        self.assertEqual(late_minutes, 15)
        self.assertEqual(early_minutes, 0)

    def test_first_half_threshold_single_check_in_does_not_produce_early_out(self):
        late_minutes, early_minutes = reconciliation._calculate_late_early(
            final_in_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 50)),
            final_out_dt=None,
            late_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 13, 0)),
            early_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 17, 0)),
            grace_seconds=0,
            grace_clock_in_type="after",
            apply_grace_to_late=False,
        )

        self.assertEqual(late_minutes, 0)
        self.assertEqual(early_minutes, 0)

    def test_second_half_threshold_checkout_before_threshold_counts_as_early_out(self):
        late_minutes, early_minutes = reconciliation._calculate_late_early(
            final_in_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            final_out_dt=timezone.make_aware(datetime(2026, 3, 14, 11, 45)),
            late_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            early_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            grace_seconds=0,
            grace_clock_in_type="after",
        )

        self.assertEqual(late_minutes, 0)
        self.assertEqual(early_minutes, 15)

    def test_second_half_threshold_checkout_at_threshold_is_not_early_out(self):
        late_minutes, early_minutes = reconciliation._calculate_late_early(
            final_in_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            final_out_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            late_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            early_reference_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            grace_seconds=0,
            grace_clock_in_type="after",
        )

        self.assertEqual(late_minutes, 0)
        self.assertEqual(early_minutes, 0)


    def test_pick_raw_sessions_exposes_first_in_and_last_out_across_all_candidates(self):
        ctx = reconciliation.ShiftContext(
            employee="EMP-1",
            attendance_date=date(2026, 3, 14),
            day=None,
            shift=None,
            schedule=None,
            shift_start_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            shift_end_dt=timezone.make_aware(datetime(2026, 3, 14, 17, 0)),
            check_in_window_start_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            check_in_window_end_dt=timezone.make_aware(datetime(2026, 3, 14, 9, 0)),
            check_out_window_start_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            check_out_window_end_dt=timezone.make_aware(datetime(2026, 3, 14, 15, 0)),
            minimum_hour="08:00",
            grace_seconds=0,
            grace_clock_in_type="after",
        )
        logs = [
            FakePunchLog(10, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 7, 55))),
            FakePunchLog(11, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 20))),
            FakePunchLog(12, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 15, 5))),
            FakePunchLog(13, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 40))),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)

        self.assertEqual(raw["any_in"].id, 10)
        self.assertEqual(raw["final_in"].id, 11)
        self.assertEqual(raw["any_out"].id, 13)
        self.assertIsNone(raw["final_out"])

    def test_on_duty_raw_truth_selection_uses_first_and_last_punch_even_when_window_valid_selection_is_missing(self):
        raw = {
            "any_in": SimpleNamespace(id=21),
            "final_in": None,
            "any_out": SimpleNamespace(id=22),
            "final_out": None,
        }

        selected_in = reconciliation._select_raw_truth_punch(
            raw,
            AttendancePunchDirection.IN,
            preserve_raw_truth=True,
        )
        selected_out = reconciliation._select_raw_truth_punch(
            raw,
            AttendancePunchDirection.OUT,
            preserve_raw_truth=True,
        )

        self.assertEqual(selected_in.id, 21)
        self.assertEqual(selected_out.id, 22)

    def test_on_duty_status_variants_preserve_raw_truth_selection(self):
        for status, document_status in [
            (WorkModeRequestStatus.APPROVED, WorkModeRequestDocumentStatus.VERIFIED),
            (WorkModeRequestStatus.APPROVED, WorkModeRequestDocumentStatus.PENDING_VERIFICATION),
            (WorkModeRequestStatus.APPROVED, WorkModeRequestDocumentStatus.REJECTED),
            (WorkModeRequestStatus.REVOKED, WorkModeRequestDocumentStatus.REJECTED),
        ]:
            req = SimpleNamespace(
                mode=AttendanceWorkMode.ON_DUTY,
                status=status,
                effective_document_status=lambda ds=document_status: ds,
            )
            self.assertTrue(reconciliation._should_preserve_on_duty_raw_truth(req))

    def test_non_on_duty_or_non_active_requests_do_not_force_raw_truth_fallback(self):
        waiting_req = SimpleNamespace(mode=AttendanceWorkMode.ON_DUTY, status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)
        wfa_req = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)

        self.assertFalse(reconciliation._should_preserve_on_duty_raw_truth(waiting_req))
        self.assertFalse(reconciliation._should_preserve_on_duty_raw_truth(wfa_req))

    def test_multiple_valid_checkouts_choose_latest_and_supersede_older(self):
        ctx = reconciliation.ShiftContext(
            employee="EMP-1",
            attendance_date=date(2026, 3, 14),
            day=None,
            shift=None,
            schedule=None,
            shift_start_dt=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            shift_end_dt=timezone.make_aware(datetime(2026, 3, 14, 17, 0)),
            check_in_window_start_dt=timezone.make_aware(datetime(2026, 3, 14, 6, 0)),
            check_in_window_end_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            check_out_window_start_dt=timezone.make_aware(datetime(2026, 3, 14, 12, 0)),
            check_out_window_end_dt=timezone.make_aware(datetime(2026, 3, 14, 23, 0)),
            minimum_hour="08:00",
            grace_seconds=0,
            grace_clock_in_type="after",
        )
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0))),
            FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 0))),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 0))),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)

        self.assertEqual(raw["final_out"].id, 3)
        self.assertEqual([log.id for log in raw["extra_out"]], [2])



    def test_mixed_mobile_and_biometric_multiple_ins_and_outs_still_pick_first_in_and_last_out(self):
        ctx = self._default_ctx()
        attendance = SimpleNamespace(attendance_date=ctx.attendance_date)
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="biometric"),
            FakePunchLog(2, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 4)), source="mobile"),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 35)), source="mobile"),
            FakePunchLog(4, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 12)), source="biometric"),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)
        decisions = self._apply_decisions_from_raw(attendance, logs, raw)

        self.assertEqual(raw["any_in"].id, 1)
        self.assertEqual(raw["final_in"].id, 1)
        self.assertEqual(raw["any_out"].id, 4)
        self.assertEqual(raw["final_out"].id, 4)
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[1].decision_status, "not_accepted")
        self.assertEqual(logs[2].decision_status, "superseded")
        self.assertEqual(logs[2].decision_source, reconciliation.SOURCE_NORMAL)
        self.assertEqual(decisions[1], (True, reconciliation.NOTE_FINAL_IN))
        self.assertEqual(decisions[4], (True, reconciliation.NOTE_FINAL_OUT))

    def test_identical_minute_punches_prefer_stable_order_without_duplicate_acceptance(self):
        ctx = self._default_ctx()
        attendance = SimpleNamespace(attendance_date=ctx.attendance_date)
        same_minute = timezone.make_aware(datetime(2026, 3, 14, 8, 0))
        same_out_minute = timezone.make_aware(datetime(2026, 3, 14, 17, 0))
        logs = [
            FakePunchLog(5, AttendancePunchDirection.IN, same_minute, source="mobile"),
            FakePunchLog(1, AttendancePunchDirection.IN, same_minute, source="biometric"),
            FakePunchLog(8, AttendancePunchDirection.OUT, same_out_minute, source="mobile"),
            FakePunchLog(2, AttendancePunchDirection.OUT, same_out_minute, source="biometric"),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)
        self._apply_decisions_from_raw(attendance, logs, raw)

        self.assertEqual(raw["final_in"].id, 1)
        self.assertEqual([log.id for log in raw["extra_in"]], [5])
        self.assertEqual(raw["final_out"].id, 8)
        self.assertEqual([log.id for log in raw["extra_out"]], [2])
        self.assertTrue(next(log for log in logs if log.id == 1).accepted_to_attendance)
        self.assertFalse(next(log for log in logs if log.id == 5).accepted_to_attendance)
        self.assertTrue(next(log for log in logs if log.id == 8).accepted_to_attendance)
        self.assertFalse(next(log for log in logs if log.id == 2).accepted_to_attendance)

    def test_request_generated_punches_do_not_override_earlier_valid_in_or_later_valid_out_without_rule(self):
        ctx = self._default_ctx()
        attendance = SimpleNamespace(attendance_date=ctx.attendance_date)
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 5)), source="biometric"),
            FakePunchLog(2, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 20)), source="approved_request"),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 45)), source="approved_request"),
            FakePunchLog(4, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 10)), source="mobile"),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)
        self._apply_decisions_from_raw(attendance, logs, raw)

        self.assertEqual(raw["final_in"].id, 1)
        self.assertEqual(raw["final_out"].id, 4)
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)


    def test_first_in_and_last_out_win_with_mixed_sources_in_same_day(self):
        ctx = self._default_ctx()
        attendance = SimpleNamespace(attendance_date=ctx.attendance_date)
        logs = [
            FakePunchLog(11, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 7, 59)), source="biometric"),
            FakePunchLog(12, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 3)), source="mobile"),
            FakePunchLog(13, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 18)), source="approved_request"),
            FakePunchLog(14, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 55)), source="mobile"),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)
        self._apply_decisions_from_raw(attendance, logs, raw)

        self.assertEqual(raw["final_in"].id, 11)
        self.assertEqual(raw["final_out"].id, 14)
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)

    def test_tightly_clustered_in_punches_keep_earliest_as_final_in_and_single_acceptance(self):
        ctx = self._default_ctx()
        attendance = SimpleNamespace(attendance_date=ctx.attendance_date)
        logs = [
            FakePunchLog(21, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="mobile"),
            FakePunchLog(22, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 1)), source="approved_request"),
            FakePunchLog(23, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 1)), source="biometric"),
            FakePunchLog(24, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 0)), source="mobile"),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)
        self._apply_decisions_from_raw(attendance, logs, raw)

        accepted_ins = [log.id for log in logs if log.punch_direction == AttendancePunchDirection.IN and log.accepted_to_attendance]
        self.assertEqual(raw["final_in"].id, 21)
        self.assertEqual(accepted_ins, [21])
        self.assertEqual([log.id for log in raw["extra_in"]], [22, 23])
        self.assertEqual(logs[1].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)

    def test_interleaved_in_and_out_sequence_keeps_only_first_in_and_last_out_as_final_truth(self):
        ctx = self._default_ctx()
        attendance = SimpleNamespace(attendance_date=ctx.attendance_date)
        logs = [
            FakePunchLog(31, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="biometric"),
            FakePunchLog(32, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 10, 0)), source="mobile"),
            FakePunchLog(33, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 10, 5)), source="approved_request"),
            FakePunchLog(34, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 0)), source="biometric"),
        ]

        raw = reconciliation._pick_raw_sessions(logs, ctx)
        self._apply_decisions_from_raw(attendance, logs, raw)

        self.assertEqual(raw["final_in"].id, 31)
        self.assertEqual(raw["final_out"].id, 34)
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)

    def test_apply_punch_decisions_marks_duplicate_checkin_as_not_accepted(self):
        attendance = SimpleNamespace(attendance_date=date(2026, 3, 14))
        duplicate = FakePunchLog(2, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 5)))

        reconciliation._apply_punch_decisions(
            attendance,
            [duplicate],
            {duplicate.id: (False, reconciliation.NOTE_DUPLICATE_CHECKIN)},
            reconciliation.SOURCE_NORMAL,
        )

        self.assertFalse(duplicate.accepted_to_attendance)
        self.assertEqual(duplicate.reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(duplicate.decision_status, "not_accepted")
        self.assertEqual(duplicate.decision_source, reconciliation.SOURCE_NORMAL)

    def test_apply_punch_decisions_marks_superseded_checkout_and_is_idempotent(self):
        attendance = SimpleNamespace(attendance_date=date(2026, 3, 14))
        superseded = FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 0)))
        decisions = {superseded.id: (False, reconciliation.NOTE_SUPERSEDED_CHECKOUT)}

        reconciliation._apply_punch_decisions(
            attendance,
            [superseded],
            decisions,
            reconciliation.SOURCE_WFA,
        )
        first_state = (
            superseded.accepted_to_attendance,
            superseded.reason,
            superseded.decision_status,
            superseded.decision_source,
        )

        reconciliation._apply_punch_decisions(
            attendance,
            [superseded],
            decisions,
            reconciliation.SOURCE_WFA,
        )
        second_state = (
            superseded.accepted_to_attendance,
            superseded.reason,
            superseded.decision_status,
            superseded.decision_source,
        )

        self.assertEqual(first_state, second_state)
        self.assertEqual(superseded.decision_status, "superseded")
        self.assertEqual(len(superseded.saved_update_fields), 2)
