from __future__ import annotations

from pathlib import Path
from datetime import date, datetime, timedelta
import random

from django.utils import timezone

from attendance.models import AttendancePunchDirection
from attendance.services import reconciliation
from attendance.services.test_reconciliation_canonical import FakePunchLog
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.test import RequestFactory, SimpleTestCase, TestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequestActionType,
    WorkModeRequestDocumentStatus,
    WorkModeRequestStatus,
)


class LeaveSignalCanonicalRangeTests(SimpleTestCase):
    def test_reconcile_leave_related_punches_uses_impacted_date_range(self):
        from leave import signals as leave_signals

        instance = SimpleNamespace(
            employee_id="EMP-1",
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 16),
            requested_dates=lambda: [date(2026, 3, 14), date(2026, 3, 15), date(2026, 3, 16)],
        )
        calls = []

        with patch.object(
            leave_signals,
            "impacted_attendance_dates_for_leave_request",
            return_value=[date(2026, 3, 15), date(2026, 3, 16), date(2026, 3, 14)],
        ), patch(
            "attendance.services.reconciliation.recompute_attendance_range",
            lambda employee, start_date, end_date: calls.append((employee, start_date, end_date)),
        ):
            leave_signals._reconcile_leave_related_punches(instance)

        self.assertEqual(calls, [("EMP-1", date(2026, 3, 14), date(2026, 3, 16))])

    def test_reconcile_leave_related_punches_falls_back_to_requested_dates(self):
        from leave import signals as leave_signals

        instance = SimpleNamespace(
            employee_id="EMP-2",
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 16),
            requested_dates=lambda: [date(2026, 3, 16), date(2026, 3, 14)],
        )
        calls = []

        with patch.object(
            leave_signals,
            "impacted_attendance_dates_for_leave_request",
            side_effect=RuntimeError("fallback"),
        ), patch(
            "attendance.services.reconciliation.recompute_attendance_range",
            lambda employee, start_date, end_date: calls.append((employee, start_date, end_date)),
        ):
            leave_signals._reconcile_leave_related_punches(instance)

        self.assertEqual(calls, [("EMP-2", date(2026, 3, 14), date(2026, 3, 16))])


class CanonicalRecomputeDecisionFlowTests(SimpleTestCase):
    databases = {"default"}


    def _base_ctx(self, attendance_date):
        return reconciliation.ShiftContext(
            employee="EMP-CANONICAL",
            attendance_date=attendance_date,
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

    def _base_leave_ctx(self):
        return reconciliation.LeaveContext(
            request=None,
            kind=None,
            late_reference_dt=None,
            early_reference_dt=None,
            minimum_hour="08:00",
        )

    def _run_recompute_with_logs(self, attendance_date, logs, *, work_request=None, attendance=None):
        attendance = attendance or SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)
        activity = SimpleNamespace(save=lambda *args, **kwargs: None)
        ctx = self._base_ctx(attendance_date)
        sync_calls = []

        with patch.object(reconciliation, "_ensure_records", return_value=(attendance, activity)), \
             patch.object(reconciliation, "_resolve_shift_context", return_value=ctx), \
             patch.object(reconciliation, "_resolve_leave_context", return_value=self._base_leave_ctx()), \
             patch.object(reconciliation, "_approved_work_mode_request", return_value=work_request), \
             patch.object(reconciliation, "_approved_work_mode_request_for_session", side_effect=[work_request, work_request]), \
             patch.object(reconciliation, "_latest_revoked_request", return_value=None), \
             patch.object(reconciliation, "_candidate_logs", return_value=logs), \
             patch.object(reconciliation, "_sync_attendance_and_activity", lambda *args, **kwargs: sync_calls.append(kwargs)), \
             patch.object(reconciliation, "_set_late_early_rows", lambda *args, **kwargs: None), \
             patch("attendance.services.work_type_request_rules.resolve_biometric_work_mode", return_value=SimpleNamespace(mode=AttendanceWorkMode.WFA)):
            reconciliation.recompute_attendance("EMP-CANONICAL", attendance_date)

        return attendance, activity, sync_calls

    RANDOMIZED_SOURCES = ("biometric", "mobile", "approved_request")

    def _randomized_logs_for_recompute(self, rng: random.Random, scenario_id: int):
        attendance_date = date(2026, 3, 14)
        base_in = timezone.make_aware(datetime(2026, 3, 14, 8, 0))
        base_out = timezone.make_aware(datetime(2026, 3, 14, 12, 0))
        log_id = scenario_id * 1000 + 1
        logs = []

        def make_log(direction, dt, source):
            nonlocal log_id
            log = FakePunchLog(log_id, direction, dt, source=source)
            log_id += 1
            return log

        in_count = rng.randint(1, 4)
        out_count = rng.randint(1, 4)
        invalid_in_count = rng.randint(0, 2)
        invalid_out_count = rng.randint(0, 2)

        dense_minutes = [0, 0, 1, 1, 2, 5, 10, 20]
        out_minutes = [0, 0, 1, 5, 10, 40, 80, 120, 240]

        for _ in range(in_count):
            logs.append(make_log(AttendancePunchDirection.IN, base_in + timedelta(minutes=rng.choice(dense_minutes)), rng.choice(self.RANDOMIZED_SOURCES)))
        for _ in range(out_count):
            logs.append(make_log(AttendancePunchDirection.OUT, base_out + timedelta(minutes=rng.choice(out_minutes)), rng.choice(self.RANDOMIZED_SOURCES)))
        for _ in range(invalid_in_count):
            offset = rng.choice([1, 2, 5, 30, 90])
            dt = base_in - timedelta(hours=2, minutes=offset) if rng.random() < 0.5 else base_in + timedelta(hours=6, minutes=offset)
            logs.append(make_log(AttendancePunchDirection.IN, dt, rng.choice(self.RANDOMIZED_SOURCES)))
        for _ in range(invalid_out_count):
            offset = rng.choice([1, 2, 5, 30, 90])
            dt = base_out - timedelta(hours=2, minutes=offset) if rng.random() < 0.5 else base_out + timedelta(hours=12, minutes=offset)
            logs.append(make_log(AttendancePunchDirection.OUT, dt, rng.choice(self.RANDOMIZED_SOURCES)))

        rng.shuffle(logs)
        return attendance_date, logs



    def test_randomized_same_day_sequences_keep_db_truth_single_and_consistent(self):
        rng = random.Random(777331)
        work_request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)

        for scenario_id in range(1, 31):
            attendance_date, logs = self._randomized_logs_for_recompute(rng, scenario_id)
            attendance = SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)

            _attendance, activity, sync_calls = self._run_recompute_with_logs(
                attendance_date,
                logs,
                work_request=work_request,
                attendance=attendance,
            )

            accepted_in = [
                log for log in logs if log.punch_direction == AttendancePunchDirection.IN and log.accepted_to_attendance
            ]
            accepted_out = [
                log for log in logs if log.punch_direction == AttendancePunchDirection.OUT and log.accepted_to_attendance
            ]
            self.assertLessEqual(len(accepted_in), 1)
            self.assertLessEqual(len(accepted_out), 1)

            valid_in = sorted(
                [
                    log for log in logs
                    if log.punch_direction == AttendancePunchDirection.IN
                    and timezone.make_naive(log.punch_timestamp).hour < 12
                    and log.punch_timestamp >= timezone.make_aware(datetime(2026, 3, 14, 6, 0))
                    and log.punch_timestamp <= timezone.make_aware(datetime(2026, 3, 14, 12, 0))
                ],
                key=lambda log: (log.punch_timestamp, log.id),
            )
            valid_out = sorted(
                [
                    log for log in logs
                    if log.punch_direction == AttendancePunchDirection.OUT
                    and log.punch_timestamp >= timezone.make_aware(datetime(2026, 3, 14, 12, 0))
                    and log.punch_timestamp <= timezone.make_aware(datetime(2026, 3, 14, 23, 0))
                ],
                key=lambda log: (log.punch_timestamp, log.id),
            )

            if valid_in:
                self.assertEqual([log.id for log in accepted_in], [valid_in[0].id])
                self.assertEqual(sync_calls[-1]["final_in_dt"], valid_in[0].punch_timestamp)
            else:
                self.assertEqual(accepted_in, [])
            if valid_out:
                self.assertEqual([log.id for log in accepted_out], [valid_out[-1].id])
                self.assertEqual(sync_calls[-1]["final_out_dt"], valid_out[-1].punch_timestamp)
            else:
                self.assertEqual(accepted_out, [])

            self.assertIsNotNone(activity)
            for log in logs:
                self.assertEqual(log.attendance_id, attendance)
                self.assertEqual(log.attendance_date, attendance_date)
                self.assertIsNotNone(log.reason)
            for log in logs:
                if log not in accepted_out and log.punch_direction == AttendancePunchDirection.OUT and log in valid_out[:-1]:
                    self.assertEqual(log.reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)

    def test_superseded_middle_out_remains_visible_but_not_accepted(self):
        attendance_date = date(2026, 3, 14)
        attendance = SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="biometric"),
            FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 15, 15)), source="mobile"),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 10)), source="approved_request"),
            FakePunchLog(4, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 20)), source="biometric"),
        ]

        self._run_recompute_with_logs(attendance_date, logs, attendance=attendance)

        self.assertEqual(logs[3].reason, reconciliation.NOTE_FINAL_OUT)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[2].decision_status, "superseded")
        self.assertEqual(logs[2].attendance_id, attendance)
        self.assertEqual(logs[2].attendance_date, attendance_date)

    def test_multiple_out_candidates_keep_only_latest_as_final_and_mark_older_outs_superseded(self):
        attendance_date = date(2026, 3, 14)
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="mobile"),
            FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 14, 30)), source="mobile"),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 45)), source="approved_request"),
            FakePunchLog(4, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 30)), source="biometric"),
        ]
        work_request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)

        _attendance, _activity, sync_calls = self._run_recompute_with_logs(attendance_date, logs, work_request=work_request)

        self.assertEqual(sync_calls[0]["final_in_dt"], timezone.make_aware(datetime(2026, 3, 14, 8, 0)))
        self.assertEqual(sync_calls[0]["final_out_dt"], timezone.make_aware(datetime(2026, 3, 14, 17, 30)))
        self.assertEqual(sync_calls[0]["source"], reconciliation.SOURCE_WFA)
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[1].decision_status, "superseded")
        self.assertEqual(logs[2].decision_status, "superseded")

    def test_mixed_sources_same_day_keep_raw_visibility_for_all_nonfinal_punches(self):
        attendance_date = date(2026, 3, 14)
        attendance = SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 2)), source="biometric"),
            FakePunchLog(2, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 10)), source="mobile"),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 0)), source="approved_request"),
            FakePunchLog(4, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 8)), source="biometric"),
        ]

        self._run_recompute_with_logs(attendance_date, logs, attendance=attendance)

        for log in logs:
            self.assertEqual(log.attendance_id, attendance)
            self.assertEqual(log.attendance_date, attendance_date)
            self.assertIsNotNone(log.reason)
            self.assertEqual(log.decision_source, reconciliation.SOURCE_NORMAL)

        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)


    def test_latest_out_wins_even_when_request_generated_out_exists_earlier(self):
        attendance_date = date(2026, 3, 14)
        logs = [
            FakePunchLog(11, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 1)), source="biometric"),
            FakePunchLog(12, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 20)), source="approved_request"),
            FakePunchLog(13, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 55)), source="mobile"),
        ]
        work_request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)

        attendance, _activity, sync_calls = self._run_recompute_with_logs(attendance_date, logs, work_request=work_request)

        self.assertEqual(sync_calls[0]["final_in_dt"], timezone.make_aware(datetime(2026, 3, 14, 8, 1)))
        self.assertEqual(sync_calls[0]["final_out_dt"], timezone.make_aware(datetime(2026, 3, 14, 16, 55)))
        self.assertEqual(sync_calls[0]["source"], reconciliation.SOURCE_WFA)
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertTrue(logs[2].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_FINAL_OUT)
        self.assertEqual(logs[1].attendance_id, attendance)
        self.assertEqual(logs[2].attendance_id, attendance)

    def test_earliest_in_wins_even_when_mobile_or_request_generated_in_exists_later(self):
        attendance_date = date(2026, 3, 14)
        logs = [
            FakePunchLog(21, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="biometric"),
            FakePunchLog(22, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 4)), source="mobile"),
            FakePunchLog(23, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 6)), source="approved_request"),
            FakePunchLog(24, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 2)), source="mobile"),
        ]
        work_request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)

        attendance, _activity, sync_calls = self._run_recompute_with_logs(attendance_date, logs, work_request=work_request)

        self.assertEqual(sync_calls[0]["final_in_dt"], timezone.make_aware(datetime(2026, 3, 14, 8, 0)))
        self.assertEqual(sync_calls[0]["final_out_dt"], timezone.make_aware(datetime(2026, 3, 14, 17, 2)))
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertFalse(logs[2].accepted_to_attendance)
        self.assertTrue(logs[3].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[2].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[0].attendance_id, attendance)
        self.assertEqual(logs[3].attendance_id, attendance)

    def test_canonical_selection_remains_single_under_dense_same_day_punch_sequences(self):
        attendance_date = date(2026, 3, 14)
        logs = [
            FakePunchLog(31, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source="biometric"),
            FakePunchLog(32, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 1)), source="mobile"),
            FakePunchLog(33, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 12, 30)), source="mobile"),
            FakePunchLog(34, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 10, 5)), source="approved_request"),
            FakePunchLog(35, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 30)), source="approved_request"),
            FakePunchLog(36, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 10)), source="biometric"),
        ]
        work_request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)

        attendance, _activity, sync_calls = self._run_recompute_with_logs(attendance_date, logs, work_request=work_request)

        self.assertEqual(sync_calls[0]["final_in_dt"], timezone.make_aware(datetime(2026, 3, 14, 8, 0)))
        self.assertEqual(sync_calls[0]["final_out_dt"], timezone.make_aware(datetime(2026, 3, 14, 17, 10)))
        self.assertEqual([log.id for log in logs if log.accepted_to_attendance and log.punch_direction == AttendancePunchDirection.IN], [31])
        self.assertEqual([log.id for log in logs if log.accepted_to_attendance and log.punch_direction == AttendancePunchDirection.OUT], [36])
        for log in logs:
            self.assertEqual(log.attendance_id, attendance)
            self.assertEqual(log.attendance_date, attendance_date)
        self.assertEqual(logs[32 - 31].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[33 - 31].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[34 - 31].reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertEqual(logs[35 - 31].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)

    def test_full_day_leave_after_existing_raw_punches_keeps_logs_but_ignores_them(self):
        attendance_date = date(2026, 3, 14)
        attendance = SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)
        activity = SimpleNamespace(save=lambda *args, **kwargs: None)
        ctx = reconciliation.ShiftContext(
            employee="EMP-LEAVE",
            attendance_date=attendance_date,
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
        leave_ctx = reconciliation.LeaveContext(
            request=SimpleNamespace(id=55),
            kind="full_day",
            late_reference_dt=None,
            early_reference_dt=None,
            minimum_hour="00:00",
        )
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 5))),
            FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 1))),
        ]
        sync_calls = []

        with patch.object(reconciliation, "_ensure_records", return_value=(attendance, activity)), \
             patch.object(reconciliation, "_resolve_shift_context", return_value=ctx), \
             patch.object(reconciliation, "_resolve_leave_context", return_value=leave_ctx), \
             patch.object(reconciliation, "_approved_work_mode_request", return_value=None), \
             patch.object(reconciliation, "_latest_revoked_request", return_value=None), \
             patch.object(reconciliation, "_candidate_logs", return_value=logs), \
             patch.object(reconciliation, "_sync_attendance_and_activity", lambda *args, **kwargs: sync_calls.append(kwargs)), \
             patch.object(reconciliation, "_set_late_early_rows", lambda *args, **kwargs: None):
            reconciliation.recompute_attendance("EMP-LEAVE", attendance_date)

        self.assertIsNone(sync_calls[0]["final_in_dt"])
        self.assertIsNone(sync_calls[0]["final_out_dt"])
        self.assertEqual(sync_calls[0]["source"], reconciliation.SOURCE_LEAVE)
        self.assertEqual(sync_calls[0]["note"], reconciliation.NOTE_FULL_DAY_LEAVE)
        self.assertFalse(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertEqual(logs[0].reason, reconciliation.NOTE_IGNORED_FULL_DAY_LEAVE)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_IGNORED_FULL_DAY_LEAVE)

    def test_wfa_latest_checkout_wins_and_older_checkout_becomes_superseded(self):
        attendance_date = date(2026, 3, 14)
        attendance = SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)
        activity = SimpleNamespace(save=lambda *args, **kwargs: None)
        ctx = reconciliation.ShiftContext(
            employee="EMP-WFA",
            attendance_date=attendance_date,
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
        leave_ctx = reconciliation.LeaveContext(
            request=None,
            kind=None,
            late_reference_dt=None,
            early_reference_dt=None,
            minimum_hour="08:00",
        )
        work_request = SimpleNamespace(mode=AttendanceWorkMode.WFA, status=WorkModeRequestStatus.APPROVED)
        logs = [
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 14, 8, 0))),
            FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 16, 0))),
            FakePunchLog(3, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 14, 17, 5))),
        ]
        sync_calls = []

        with patch.object(reconciliation, "_ensure_records", return_value=(attendance, activity)), \
             patch.object(reconciliation, "_resolve_shift_context", return_value=ctx), \
             patch.object(reconciliation, "_resolve_leave_context", return_value=leave_ctx), \
             patch.object(reconciliation, "_approved_work_mode_request", return_value=work_request), \
             patch.object(reconciliation, "_approved_work_mode_request_for_session", side_effect=[work_request, work_request]), \
             patch.object(reconciliation, "_latest_revoked_request", return_value=None), \
             patch.object(reconciliation, "_candidate_logs", return_value=logs), \
             patch.object(reconciliation, "_sync_attendance_and_activity", lambda *args, **kwargs: sync_calls.append(kwargs)), \
             patch.object(reconciliation, "_set_late_early_rows", lambda *args, **kwargs: None), \
             patch("attendance.services.work_type_request_rules.resolve_biometric_work_mode", return_value=SimpleNamespace(mode=AttendanceWorkMode.WFA)):
            reconciliation.recompute_attendance("EMP-WFA", attendance_date)

        self.assertEqual(sync_calls[0]["source"], reconciliation.SOURCE_WFA)
        self.assertEqual(sync_calls[0]["note"], "WFA reconciled under normal attendance rules")
        self.assertEqual(sync_calls[0]["final_out_dt"], timezone.make_aware(datetime(2026, 3, 14, 17, 5)))
        self.assertTrue(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertTrue(logs[2].accepted_to_attendance)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(logs[1].decision_status, "superseded")
        self.assertEqual(logs[2].reason, reconciliation.NOTE_FINAL_OUT)


class WorkModeDocumentActionFlowTests(TestCase):
    def setUp(self):
        self.api_factory = APIRequestFactory()
        self.request_factory = RequestFactory()
        self.user = SimpleNamespace(is_authenticated=True, is_superuser=False)
        self.actor = SimpleNamespace(id=999)
        self.owner = SimpleNamespace(id=321, employee_user_id=SimpleNamespace(username="owner"))

    def _request_obj(self, *, document_status, status=WorkModeRequestStatus.APPROVED, mode=AttendanceWorkMode.ON_DUTY):
        saved = {}

        def _save(*, update_fields=None):
            saved["update_fields"] = list(update_fields or [])

        version_saved = {}

        def _save_version(*, update_fields=None):
            version_saved["update_fields"] = list(update_fields or [])

        version = SimpleNamespace(
            version_number=3,
            status=document_status,
            reviewed_by=None,
            reviewed_at=None,
            review_remark=None,
            save=_save_version,
            _saved=version_saved,
        )
        def _sync_root_document_fields():
            req.document_status = version.status
            req.document_verified_by = version.reviewed_by
            req.document_verified_at = version.reviewed_at
            req.document_remark = version.review_remark
        req = SimpleNamespace(
            id=77,
            employee_id=self.owner,
            employee_id_id=self.owner.id,
            status=status,
            mode=mode,
            document_status=document_status,
            document_verified_by=None,
            document_verified_at=None,
            action_by=None,
            action_at=None,
            action_type=None,
            action_reason=None,
            document_remark=None,
            current_document_version=version,
            resolve_current_document_version=lambda: version,
            sync_legacy_files_from_current_version=lambda: None,
            sync_root_document_fields_from_current_version=_sync_root_document_fields,
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 15),
            save=_save,
            _saved=saved,
            _version_saved=version_saved,
        )
        return req

    def test_api_verify_logs_actual_previous_document_status_and_recomputes(self):
        from horilla_api.api_views.attendance import views as api_views

        req_obj = self._request_obj(document_status=WorkModeRequestDocumentStatus.SUBMITTED)
        recompute_calls = []
        log_calls = []

        request = self.api_factory.put("/api/work-mode/77/verify", {"remark": "checked"}, format="json")
        force_authenticate(request, user=self.user)

        class DummySerializer:
            def __init__(self, obj, context=None):
                self.data = {"id": getattr(obj, "id", None), "document_status": getattr(obj, "document_status", None)}

        with patch.object(api_views, "get_object_or_404", return_value=req_obj), \
             patch.object(api_views, "_request_actor_employee", return_value=self.actor), \
             patch("attendance.services.work_type_request_actions.can_verify_document", return_value=True), \
             patch.object(api_views.WorkModeRequestActions, "_recompute", lambda req: recompute_calls.append((req.employee_id, req.start_date, req.end_date))), \
             patch.object(api_views.WorkModeRequestActions, "_audit", lambda req, **kwargs: log_calls.append(kwargs)), \
             patch.object(api_views.WorkModeRequestDocumentActionView, "serializer_class", DummySerializer):
            response = api_views.WorkModeRequestDocumentActionView.as_view()(request, pk=req_obj.id, action="verify")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(req_obj.document_status, WorkModeRequestDocumentStatus.VERIFIED)
        self.assertEqual(req_obj.action_type, WorkModeRequestActionType.VERIFIED)
        self.assertEqual(req_obj._saved["update_fields"], [
            "current_document_version",
            "document_status",
            "document_verified_by",
            "document_verified_at",
            "document_remark",
            "action_by",
            "action_at",
            "action_type",
            "action_reason",
        ])
        self.assertEqual(recompute_calls, [(self.owner, date(2026, 3, 14), date(2026, 3, 15))])
        self.assertEqual(log_calls[0]["old_status"], "document:submitted")
        self.assertEqual(log_calls[0]["new_status"], "document:verified")
        self.assertEqual(log_calls[0]["remark"], "checked")

    def test_web_reopen_sets_pending_verification_and_recomputes(self):
        from attendance.views import work_type_requests

        req_obj = self._request_obj(document_status=WorkModeRequestDocumentStatus.VERIFIED)
        log_calls = []
        recompute_calls = []
        self.actor.is_active = True
        web_user = SimpleNamespace(is_authenticated=True, is_active=True, is_superuser=False, employee_get=self.actor)
        request = self.request_factory.post(
            "/attendance/work-mode/77/reopen",
            {"remark": "reopen it"},
            HTTP_HX_REQUEST="true",
        )
        request.user = web_user
        request.session = {}

        with patch.object(work_type_requests, "get_object_or_404", return_value=req_obj), \
             patch.object(work_type_requests, "_request_actor_employee", return_value=self.actor), \
             patch("attendance.services.work_type_request_actions.can_reopen_document", return_value=True), \
             patch.object(work_type_requests.WorkModeRequestActions, "_recompute", lambda req: recompute_calls.append((req.employee_id, req.start_date, req.end_date))), \
             patch.object(work_type_requests.WorkModeRequestActions, "_audit", lambda req, **kwargs: log_calls.append(kwargs)), \
             patch.object(work_type_requests.messages, "success", lambda *args, **kwargs: None):
            response = work_type_requests.work_type_request_document_action(request, req_obj.id, "reopen")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(req_obj.document_status, WorkModeRequestDocumentStatus.PENDING_VERIFICATION)
        self.assertEqual(req_obj.action_type, "REOPENED")
        self.assertEqual(recompute_calls, [(self.owner, date(2026, 3, 14), date(2026, 3, 15))])
        self.assertEqual(log_calls[0]["old_status"], "document:verified")
        self.assertEqual(log_calls[0]["new_status"], "document:pending_verification")
        self.assertEqual(log_calls[0]["remark"], "reopen it")


class WorkTypeDocumentVersionLifecycleTests(SimpleTestCase):
    databases = {"default"}
    def _request_obj(self, *, status=WorkModeRequestStatus.APPROVED):
        current = SimpleNamespace(version_number=2, status=WorkModeRequestDocumentStatus.SUBMITTED)
        current.file_links = SimpleNamespace(exists=lambda: True)
        current.save = MagicMock()
        manager = MagicMock()
        manager.filter.return_value.update = MagicMock()
        req = SimpleNamespace(
            id=101,
            mode=AttendanceWorkMode.ON_DUTY,
            status=status,
            reason='site visit',
            duty_destination_location='Client Site',
            employee_id='EMP-1',
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 15),
            current_document_version=current,
            document_versions=manager,
            document_status=current.status,
            document_verified_by=None,
            document_verified_at=None,
            document_remark=None,
            action_by=None,
            action_at=None,
            action_type=None,
            action_reason=None,
            save=MagicMock(),
            sync_legacy_files_from_current_version=lambda: None,
            sync_root_document_fields_from_current_version=lambda: setattr(req, 'document_status', getattr(req.current_document_version, 'status', WorkModeRequestDocumentStatus.NOT_UPLOADED)),
        )
        return req, current, manager

    def test_reupload_creates_new_current_document_version_and_marks_previous_non_current(self):
        from attendance.services.work_type_request_actions import WorkModeRequestActions

        req, current, manager = self._request_obj()
        actor = SimpleNamespace(id=7)
        new_version = SimpleNamespace(version_number=3, status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION)
        new_version.file_links = SimpleNamespace(exists=lambda: True)

        with patch('attendance.services.work_type_request_actions.validate_uploaded_files', lambda uploads: None), \
             patch('attendance.services.work_type_request_actions.WorkModeRequestDocumentVersion.objects.create', return_value=new_version) as create_version, \
             patch('attendance.services.work_type_request_actions.AttendanceRequestFile.objects.create', return_value=SimpleNamespace(id=41)), \
             patch('attendance.services.work_type_request_actions.WorkModeRequestDocumentVersionFile.objects.create'), \
             patch.object(WorkModeRequestActions, '_touch_action', lambda *args, **kwargs: None), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None):
            created = WorkModeRequestActions._create_document_version(req, actor=actor, uploaded_files=[SimpleNamespace(name='proof.pdf')])

        manager.filter.assert_called_once_with(is_current=True)
        manager.filter.return_value.update.assert_called_once_with(is_current=False)
        create_version.assert_called_once()
        self.assertIs(created, new_version)
        self.assertIs(req.current_document_version, new_version)
        self.assertEqual(created.version_number, 3)
        self.assertEqual(created.status, WorkModeRequestDocumentStatus.PENDING_VERIFICATION)

    def test_update_request_reupload_recomputes_once_for_approved_on_duty(self):
        from attendance.services.work_type_request_actions import WorkModeRequestActions

        req, _current, _manager = self._request_obj()
        actor = SimpleNamespace(id=7)
        new_version = SimpleNamespace(version_number=4, status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION)
        recompute_calls = []

        with patch.object(WorkModeRequestActions, '_create_document_version', return_value=new_version), \
             patch.object(WorkModeRequestActions, '_recompute', lambda request_obj: recompute_calls.append(request_obj)), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None), \
             patch.object(WorkModeRequestActions, '_touch_action', lambda *args, **kwargs: None):
            result = WorkModeRequestActions.update_request(req, actor=actor, uploaded_files=[SimpleNamespace(name='proof.pdf')])

        self.assertTrue(result.recomputed)
        self.assertEqual(recompute_calls, [req])

    def test_verify_affects_only_current_document_version(self):
        from attendance.services.work_type_request_actions import WorkModeRequestActions

        req, current, _manager = self._request_obj()
        older = SimpleNamespace(
            status=WorkModeRequestDocumentStatus.REJECTED,
            reviewed_by='old-reviewer',
            reviewed_at='yesterday',
            review_remark='keep me',
        )
        current.reviewed_by = None
        current.reviewed_at = None
        current.review_remark = None
        actor = SimpleNamespace(id=88)
        recompute_calls = []

        with patch('attendance.services.work_type_request_actions.can_verify_document', return_value=True), \
             patch.object(WorkModeRequestActions, '_recompute', lambda request_obj: recompute_calls.append(request_obj)), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None):
            result = WorkModeRequestActions.verify_document(req, actor=actor, request=SimpleNamespace(user=SimpleNamespace()))

        self.assertTrue(result.recomputed)
        self.assertEqual(current.status, WorkModeRequestDocumentStatus.VERIFIED)
        self.assertIs(current.reviewed_by, actor)
        self.assertEqual(older.status, WorkModeRequestDocumentStatus.REJECTED)
        self.assertEqual(older.review_remark, 'keep me')
        self.assertEqual(recompute_calls, [req])

    def test_reject_affects_only_current_document_version(self):
        from attendance.services.work_type_request_actions import WorkModeRequestActions

        req, current, _manager = self._request_obj()
        current.reviewed_by = None
        current.reviewed_at = None
        current.review_remark = None
        older = SimpleNamespace(status=WorkModeRequestDocumentStatus.VERIFIED, reviewed_by='old', reviewed_at='old-at', review_remark='keep verified')
        actor = SimpleNamespace(id=44)

        with patch('attendance.services.work_type_request_actions.can_reject_document', return_value=True), \
             patch.object(WorkModeRequestActions, '_recompute', lambda *args, **kwargs: None), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None):
            WorkModeRequestActions.reject_document(req, actor=actor, request=SimpleNamespace(user=SimpleNamespace()), remark='blurred')

        self.assertEqual(current.status, WorkModeRequestDocumentStatus.REJECTED)
        self.assertEqual(current.review_remark, 'blurred')
        self.assertEqual(older.status, WorkModeRequestDocumentStatus.VERIFIED)
        self.assertEqual(older.review_remark, 'keep verified')

    def test_reopen_clears_review_metadata_and_restores_pending_verification(self):
        from attendance.services.work_type_request_actions import WorkModeRequestActions

        req, current, _manager = self._request_obj()
        current.status = WorkModeRequestDocumentStatus.VERIFIED
        current.reviewed_by = SimpleNamespace(id=5)
        current.reviewed_at = timezone.now()
        current.review_remark = 'verified before'
        recompute_calls = []

        with patch('attendance.services.work_type_request_actions.can_reopen_document', return_value=True), \
             patch.object(WorkModeRequestActions, '_recompute', lambda request_obj: recompute_calls.append(request_obj)), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None):
            result = WorkModeRequestActions.reopen_document(req, actor=SimpleNamespace(id=8), request=SimpleNamespace(user=SimpleNamespace()), remark='review again')

        self.assertTrue(result.recomputed)
        self.assertEqual(current.status, WorkModeRequestDocumentStatus.PENDING_VERIFICATION)
        self.assertIsNone(current.reviewed_by)
        self.assertIsNone(current.reviewed_at)
        self.assertIsNone(current.review_remark)
        self.assertEqual(recompute_calls, [req])


class MonthlyPdfExportParityTests(SimpleTestCase):
    def setUp(self):
        self.factory = RequestFactory()

    def test_pdf_export_passes_shared_recap_rows_and_summary_into_template(self):
        from attendance.views import views

        employee = SimpleNamespace(id=17, employee_work_info=SimpleNamespace())
        recap = {
            "rows": [SimpleNamespace(attendance_date=date(2026, 3, 14), note="Approved Full-Day Leave")],
            "summary": {"total_late_minutes": 15, "total_early_out_minutes": 5, "total_penalty_minutes": 20},
        }
        context_capture = {}
        recap_calls = []

        class FakeEmployeesQS:
            def __init__(self, items):
                self._items = list(items)

            def select_related(self, *_args, **_kwargs):
                return self

            def filter(self, **kwargs):
                if "id" in kwargs:
                    return FakeEmployeesQS([item for item in self._items if getattr(item, "id", None) == kwargs["id"]])
                return self

            def first(self):
                return self._items[0] if self._items else None

        def _render_to_string(template_name, context):
            context_capture["template_name"] = template_name
            context_capture["context"] = context
            return "<html>ok</html>"

        def _create_pdf(*, src, dest):
            dest.write(b"PDF")
            return SimpleNamespace(err=False)

        request = self.factory.get(
            "/attendance/attendances-recap/export-pdf/",
            {"employee_id": str(employee.id), "month": "2026-03", "lang": "id"},
        )
        viewer = SimpleNamespace(id=44, is_active=True)
        request.user = SimpleNamespace(
            is_authenticated=True,
            is_active=True,
            employee_get=viewer,
            has_perm=lambda perm: True,
        )
        request.session = {}

        with patch.object(views.Employee.objects, "filter", return_value=FakeEmployeesQS([employee])), \
             patch.object(views, "get_attendance_subject_employees", return_value=(FakeEmployeesQS([employee]), False, False, employee.id)), \
             patch.object(views, "get_monthly_attendance_recap", lambda emp, month, language=None: recap_calls.append((emp, month, language)) or recap), \
             patch.object(views, "render_to_string", _render_to_string), \
             patch.object(views.pisa, "CreatePDF", _create_pdf):
            response = views.attendance_employee_month_export_pdf(request)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response["Content-Type"], "application/pdf")
        self.assertIn('monthly_attendance_17_2026-03_id.pdf', response["Content-Disposition"])
        self.assertEqual(recap_calls, [(employee, "2026-03", "id")])
        self.assertEqual(context_capture["template_name"], "attendance/attendances/monthly_export_pdf.html")
        self.assertIs(context_capture["context"]["employee"], employee)
        self.assertEqual(context_capture["context"]["rows"], recap["rows"])
        self.assertEqual(context_capture["context"]["summary"], recap["summary"])
        self.assertEqual(context_capture["context"]["lang"], "id")


class ApiMonthlyRecapParityTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()

    def test_api_month_resolution_uses_shared_month_rules(self):
        from horilla_api.api_views.attendance import views as api_views

        view = api_views.AttendanceMonthlyRecapAPIView()

        with patch.object(api_views.dj_timezone, "localdate", return_value=date(2026, 3, 14)):
            malformed = self.factory.get("/api/attendance/recap", {"month": "2026-13"})
            future = self.factory.get("/api/attendance/recap", {"month": "2026-12"})
            blank = self.factory.get("/api/attendance/recap")

            self.assertEqual(view._resolve_month(malformed), "2026-03")
            self.assertEqual(view._resolve_month(future), "2026-03")
            self.assertEqual(view._resolve_month(blank), "2026-03")

    def test_api_pdf_export_uses_shared_recap_rows_and_summary_into_template(self):
        from horilla_api.api_views.attendance import views as api_views

        employee = SimpleNamespace(id=17, employee_work_info=SimpleNamespace())
        recap = {
            "rows": [SimpleNamespace(attendance_date=date(2026, 3, 14), note="Approved Full-Day Leave")],
            "summary": {"total_late_minutes": 15, "total_early_out_minutes": 5, "total_penalty_minutes": 20},
        }
        context_capture = {}
        recap_calls = []

        class FakeEmployeesQS:
            def __init__(self, items):
                self._items = list(items)

            def filter(self, **kwargs):
                if "id" in kwargs:
                    return FakeEmployeesQS([item for item in self._items if getattr(item, "id", None) == kwargs["id"]])
                return self

            def first(self):
                return self._items[0] if self._items else None

        def _render_to_string(template_name, context):
            context_capture["template_name"] = template_name
            context_capture["context"] = context
            return "<html>ok</html>"

        def _create_pdf(*, src, dest):
            dest.write(b"PDF")
            return SimpleNamespace(err=False)

        request = self.factory.get(
            "/api/attendance/monthly-recap/export-pdf/",
            {"employee_id": str(employee.id), "month": "2026-12", "lang": "id"},
            format="json",
        )
        force_authenticate(request, user=SimpleNamespace(is_authenticated=True))

        with patch.object(api_views.dj_timezone, "localdate", return_value=date(2026, 3, 14)), \
             patch.object(api_views.AttendanceMonthlyRecapExportPDFAPIView, "_allowed_employees_qs", return_value=(FakeEmployeesQS([employee]), False, False, employee.id)), \
             patch.object(api_views, "render_to_string", _render_to_string), \
             patch.object(api_views.pisa, "CreatePDF", _create_pdf), \
             patch("attendance.services.monthly_recap.get_monthly_attendance_recap", lambda emp, month, language=None: recap_calls.append((emp, month, language)) or recap):
            response = api_views.AttendanceMonthlyRecapExportPDFAPIView.as_view()(request)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response["Content-Type"], "application/pdf")
        self.assertIn('monthly_attendance_17_2026-03_id.pdf', response["Content-Disposition"])
        self.assertEqual(recap_calls, [(employee, "2026-03", "id")])
        self.assertEqual(context_capture["template_name"], "attendance/attendances/monthly_export_pdf.html")
        self.assertIs(context_capture["context"]["employee"], employee)
        self.assertEqual(context_capture["context"]["rows"], recap["rows"])
        self.assertEqual(context_capture["context"]["summary"], recap["summary"])
        self.assertEqual(context_capture["context"]["lang"], "id")

    def test_api_pdf_export_rejects_invalid_month_format(self):
        from horilla_api.api_views.attendance import views as api_views

        request = self.factory.get(
            "/api/attendance/monthly-recap/export-pdf/",
            {"employee_id": "17", "month": "2026-13", "lang": "en"},
            format="json",
        )
        force_authenticate(request, user=SimpleNamespace(is_authenticated=True))

        with patch.object(api_views.dj_timezone, "localdate", return_value=date(2026, 3, 14)):
            response = api_views.AttendanceMonthlyRecapExportPDFAPIView.as_view()(request)

        self.assertEqual(response.status_code, 400)
        self.assertEqual(response.data["error"], "Invalid month format. Expected YYYY-MM")


class WorkModePayloadParityTests(SimpleTestCase):
    def test_serializer_falls_back_action_reason_to_document_remark_for_mobile_clients(self):
        from horilla_api.api_serializers.attendance.serializers import WorkModeRequestSerializer

        instance = SimpleNamespace(
            employee_id=SimpleNamespace(
                pk=1,
                id=1,
                employee_first_name="Owner",
                employee_last_name="User",
                badge_id="B-1",
            ),
            action_reason=None,
            document_remark="doc verified from field audit",
            action_by=None,
            approved_by=None,
            approved_at=None,
            action_at=None,
            mode=AttendanceWorkMode.ON_DUTY,
            status=WorkModeRequestStatus.APPROVED,
            document_status=WorkModeRequestDocumentStatus.VERIFIED,
            reason="Visit customer site",
            files=SimpleNamespace(all=lambda: []),
            id=91,
            employee_id_id=1,
            scope="full",
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 14),
            reason_code=None,
            duty_destination_location="Site A",
        )

        data = WorkModeRequestSerializer(instance).data

        self.assertEqual(data["action_reason"], "doc verified from field audit")
        self.assertEqual(data["document_remark"], "doc verified from field audit")


class WorkModeDocumentActionReasonParityTests(TestCase):
    def setUp(self):
        self.api_factory = APIRequestFactory()
        self.request_factory = RequestFactory()
        self.user = SimpleNamespace(is_authenticated=True, is_superuser=False)
        self.actor = SimpleNamespace(id=777, is_active=True)
        self.owner = SimpleNamespace(id=322, employee_user_id=SimpleNamespace(username="owner"))

    def _request_obj(self, *, document_status):
        saved = {}

        def _save(*, update_fields=None):
            saved["update_fields"] = list(update_fields or [])

        version_saved = {}

        def _save_version(*, update_fields=None):
            version_saved["update_fields"] = list(update_fields or [])

        version = SimpleNamespace(
            version_number=2,
            status=document_status,
            reviewed_by=None,
            reviewed_at=None,
            review_remark=None,
            save=_save_version,
            _saved=version_saved,
        )
        def _sync_root_document_fields():
            req.document_status = version.status
            req.document_verified_by = version.reviewed_by
            req.document_verified_at = version.reviewed_at
            req.document_remark = version.review_remark
        req = SimpleNamespace(
            id=88,
            employee_id=self.owner,
            employee_id_id=self.owner.id,
            status=WorkModeRequestStatus.APPROVED,
            mode=AttendanceWorkMode.ON_DUTY,
            document_status=document_status,
            document_verified_by=None,
            document_verified_at=None,
            action_by=None,
            action_at=None,
            action_type=None,
            action_reason=None,
            document_remark=None,
            current_document_version=version,
            resolve_current_document_version=lambda: version,
            sync_legacy_files_from_current_version=lambda: None,
            sync_root_document_fields_from_current_version=_sync_root_document_fields,
            start_date=date(2026, 3, 14),
            end_date=date(2026, 3, 15),
            save=_save,
            _saved=saved,
            _version_saved=version_saved,
        )
        return req

    def test_api_reject_document_persists_action_reason_for_mobile_payload(self):
        from horilla_api.api_views.attendance import views as api_views

        req_obj = self._request_obj(document_status=WorkModeRequestDocumentStatus.SUBMITTED)
        request = self.api_factory.put("/api/work-mode/88/reject-document", {"remark": "document blurred"}, format="json")
        force_authenticate(request, user=self.user)

        class DummySerializer:
            def __init__(self, obj, context=None):
                self.data = {
                    "id": getattr(obj, "id", None),
                    "action_reason": getattr(obj, "action_reason", None),
                    "document_remark": getattr(obj, "document_remark", None),
                }

        with patch.object(api_views, "get_object_or_404", return_value=req_obj),              patch.object(api_views, "_request_actor_employee", return_value=self.actor),              patch("attendance.services.work_type_request_actions.can_reject_document", return_value=True),              patch.object(api_views.WorkModeRequestActions, "_recompute", lambda *args, **kwargs: None),              patch.object(api_views.WorkModeRequestActions, "_audit", lambda *args, **kwargs: None),              patch.object(api_views.WorkModeRequestDocumentActionView, "serializer_class", DummySerializer):
            response = api_views.WorkModeRequestDocumentActionView.as_view()(request, pk=req_obj.id, action="reject-document")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(req_obj.action_reason, "document blurred")
        self.assertEqual(req_obj.document_remark, "document blurred")
        self.assertIn("action_reason", req_obj._saved["update_fields"])
        self.assertEqual(response.data["action_reason"], "document blurred")

    def test_web_verify_persists_action_reason_for_mobile_payload(self):
        from attendance.views import work_type_requests

        req_obj = self._request_obj(document_status=WorkModeRequestDocumentStatus.SUBMITTED)
        web_user = SimpleNamespace(is_authenticated=True, is_active=True, is_superuser=False, employee_get=self.actor)
        request = self.request_factory.post(
            "/attendance/work-mode/88/verify",
            {"remark": "assignment letter valid"},
            HTTP_HX_REQUEST="true",
        )
        request.user = web_user
        request.session = {}

        with patch.object(work_type_requests, "get_object_or_404", return_value=req_obj),              patch.object(work_type_requests, "_request_actor_employee", return_value=self.actor),              patch("attendance.services.work_type_request_actions.can_verify_document", return_value=True),              patch.object(work_type_requests.WorkModeRequestActions, "_recompute", lambda *args, **kwargs: None),              patch.object(work_type_requests.WorkModeRequestActions, "_audit", lambda *args, **kwargs: None),              patch.object(work_type_requests.messages, "success", lambda *args, **kwargs: None):
            response = work_type_requests.work_type_request_document_action(request, req_obj.id, "verify")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(req_obj.action_reason, "assignment letter valid")
        self.assertEqual(req_obj.document_remark, "assignment letter valid")
        self.assertIn("action_reason", req_obj._saved["update_fields"])


class WorkTypeRequestFocusedParityTests(TestCase):
    def test_wfa_create_request_is_set_to_waiting_for_approval(self):
        source = Path('attendance/services/work_type_request_actions.py').read_text()
        self.assertIn('AttendanceWorkMode.WFA', source)
        self.assertIn('req.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL', source)

    def test_wfh_create_request_is_set_to_waiting_for_approval(self):
        source = Path('attendance/services/work_type_request_actions.py').read_text()
        self.assertIn('AttendanceWorkMode.WFH', source)
        self.assertIn('req.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL', source)

    def test_api_rejects_wfa_upload_after_approval_via_action_service_guard(self):
        from horilla_api.api_views.attendance import views as api_views

        req = SimpleNamespace(
            id=55,
            status=WorkModeRequestStatus.APPROVED,
            mode=AttendanceWorkMode.WFA,
            employee_id=SimpleNamespace(employee_user_id=SimpleNamespace(username='owner')),
            employee_id_id=1,
        )
        request = APIRequestFactory().put('/api/work-mode/55', {}, format='multipart')
        request.FILES['file'] = SimpleNamespace(name='evidence.pdf')
        force_authenticate(request, user=SimpleNamespace(is_authenticated=True, username='owner'))

        with patch.object(api_views, 'get_object_or_404', return_value=req), \
             patch.object(api_views, '_request_actor_employee', return_value=SimpleNamespace(id=1)), \
             patch.object(api_views.WorkModeRequestView, '_collect_uploaded_files', return_value=[SimpleNamespace(name='evidence.pdf')]):
            response = api_views.WorkModeRequestView.as_view()(request, pk=req.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn('cannot upload documents', str(response.data).lower())

    def test_serializer_wfa_upload_flag_is_waiting_only(self):
        source = Path('horilla_api/api_serializers/attendance/serializers.py').read_text()
        self.assertIn('get_can_upload_document', source)
        self.assertIn('WorkModeRequestStatus.WAITING_FOR_APPROVAL', source)
        self.assertIn('get_can_verify_document', source)

