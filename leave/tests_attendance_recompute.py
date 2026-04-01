from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.models import AttendancePunchDirection
from attendance.services import reconciliation
from attendance.services.test_reconciliation_canonical import FakePunchLog
from leave import half_day_rules


class LeaveAttendanceRecomputeTests(SimpleTestCase):
    databases = {"default"}
    def test_approve_full_day_leave_after_raw_punch_keeps_history_but_finalizes_leave_state(self):
        attendance_date = date(2026, 3, 20)
        attendance = SimpleNamespace(attendance_date=attendance_date, save=lambda *args, **kwargs: None)
        activity = SimpleNamespace(save=lambda *args, **kwargs: None)
        ctx = reconciliation.ShiftContext(
            employee="EMP-LEAVE",
            attendance_date=attendance_date,
            day=None,
            shift=None,
            schedule=None,
            shift_start_dt=timezone.make_aware(datetime(2026, 3, 20, 8, 0)),
            shift_end_dt=timezone.make_aware(datetime(2026, 3, 20, 17, 0)),
            check_in_window_start_dt=timezone.make_aware(datetime(2026, 3, 20, 6, 0)),
            check_in_window_end_dt=timezone.make_aware(datetime(2026, 3, 20, 12, 0)),
            check_out_window_start_dt=timezone.make_aware(datetime(2026, 3, 20, 12, 0)),
            check_out_window_end_dt=timezone.make_aware(datetime(2026, 3, 20, 23, 0)),
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
            FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 20, 8, 5))),
            FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 20, 17, 1))),
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

        self.assertEqual(sync_calls[0]["source"], reconciliation.SOURCE_LEAVE)
        self.assertEqual(sync_calls[0]["note"], reconciliation.NOTE_FULL_DAY_LEAVE)
        self.assertIsNone(sync_calls[0]["final_in_dt"])
        self.assertIsNone(sync_calls[0]["final_out_dt"])
        self.assertFalse(logs[0].accepted_to_attendance)
        self.assertFalse(logs[1].accepted_to_attendance)
        self.assertEqual(logs[0].reason, reconciliation.NOTE_IGNORED_FULL_DAY_LEAVE)
        self.assertEqual(logs[1].reason, reconciliation.NOTE_IGNORED_FULL_DAY_LEAVE)

    def test_cancel_approved_full_day_leave_restores_raw_attendance_result(self):
        from leave import signals as leave_signals

        attendance = SimpleNamespace(
            attendance_clock_in=None,
            attendance_clock_out=None,
            attendance_clock_in_channel=None,
            attendance_clock_out_channel=None,
            save=MagicMock(),
        )
        in_punch = SimpleNamespace(id=1, punch_direction=AttendancePunchDirection.IN, punch_timestamp=timezone.make_aware(datetime(2026, 3, 20, 8, 0)), delete=MagicMock())
        out_punch = SimpleNamespace(id=2, punch_direction=AttendancePunchDirection.OUT, punch_timestamp=timezone.make_aware(datetime(2026, 3, 20, 17, 0)), delete=MagicMock())
        assign_calls = []

        def _assign(att_obj, *, punch, direction):
            assign_calls.append((direction, punch.id))
            if direction == "in":
                att_obj.attendance_clock_in = time(8, 0)
            else:
                att_obj.attendance_clock_out = time(17, 0)

        with patch.object(leave_signals, "leave_breakdown_for_attendance_date", return_value=""), \
             patch.object(leave_signals, "_schedule_for_employee_attendance_date", return_value=None), \
             patch.object(leave_signals, "_raw_logs_for_attendance_date", return_value=[in_punch, out_punch]), \
             patch.object(leave_signals, "_ensure_attendance_shell", return_value=attendance), \
             patch("attendance.services.punching_history.assign_raw_punch_to_attendance", side_effect=_assign):
            result = leave_signals._materialize_attendance_for_leave_date("EMP-RESTORE", date(2026, 3, 20))

        self.assertIs(result, attendance)
        self.assertEqual(assign_calls, [("in", 1), ("out", 2)])
        attendance.save.assert_called_once_with()
        in_punch.delete.assert_not_called()
        out_punch.delete.assert_not_called()
        self.assertEqual(attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))

    def test_approve_leave_on_existing_attendance_row_recomputes_without_duplicate_range_calls(self):
        from leave import signals as leave_signals

        instance = SimpleNamespace(
            employee_id="EMP-RANGE",
            start_date=date(2026, 3, 20),
            end_date=date(2026, 3, 21),
            requested_dates=lambda: [date(2026, 3, 20), date(2026, 3, 21)],
        )
        calls = []
        with patch.object(
            leave_signals,
            "impacted_attendance_dates_for_leave_request",
            return_value=[date(2026, 3, 21), date(2026, 3, 20), date(2026, 3, 20)],
        ), patch(
            "attendance.services.reconciliation.recompute_attendance_range",
            lambda employee, start_date, end_date: calls.append((employee, start_date, end_date)),
        ):
            leave_signals._reconcile_leave_related_punches(instance)

        self.assertEqual(calls, [("EMP-RANGE", date(2026, 3, 20), date(2026, 3, 21))])


class LeaveAttendanceSyncRegressionTests(SimpleTestCase):
    def test_approve_first_half_leave_recomputes_late_thresholds(self):
        from leave import signals as leave_signals

        attendance = SimpleNamespace(
            employee_id="EMP-1",
            attendance_date=date(2026, 3, 20),
            attendance_clock_in_date=date(2026, 3, 20),
            attendance_clock_in=time(13, 5),
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            is_presensi_only=False,
        )
        schedule = SimpleNamespace(
            enable_first_half_leave_rule=True,
            first_half_leave_latest_check_in_time=time(13, 0),
            enable_second_half_leave_rule=False,
            start_time=time(8, 0),
            end_time=time(17, 0),
            is_night_shift=False,
            grace_time_id=None,
        )
        delete_calls = []
        get_or_create = MagicMock()

        with patch.object(leave_signals, "_schedule_for_attendance", return_value=schedule), \
             patch.object(leave_signals, "leave_breakdown_for_attendance_date", return_value=half_day_rules.HALF_DAY_FIRST), \
             patch("attendance.models.AttendanceLateComeEarlyOut.objects.filter") as filter_mock, \
             patch("attendance.models.AttendanceLateComeEarlyOut.objects.get_or_create", get_or_create):
            filter_mock.return_value.delete.side_effect = lambda: delete_calls.append(True)
            leave_signals._rebuild_late_early_records(attendance)

        self.assertTrue(delete_calls)
        get_or_create.assert_called_once()
        _args, kwargs = get_or_create.call_args
        self.assertEqual(kwargs["type"], "late_come")

    def test_approve_second_half_leave_recomputes_early_thresholds(self):
        from leave import signals as leave_signals

        attendance = SimpleNamespace(
            employee_id="EMP-2",
            attendance_date=date(2026, 3, 20),
            attendance_clock_in_date=None,
            attendance_clock_in=None,
            attendance_clock_out_date=date(2026, 3, 20),
            attendance_clock_out=time(11, 0),
            is_presensi_only=False,
        )
        schedule = SimpleNamespace(
            enable_first_half_leave_rule=False,
            first_half_leave_latest_check_in_time=None,
            enable_second_half_leave_rule=True,
            minimum_working_hour="08:00",
            start_time=time(8, 0),
            end_time=time(17, 0),
            is_night_shift=False,
            grace_time_id=None,
        )
        get_or_create = MagicMock()

        with patch.object(leave_signals, "_schedule_for_attendance", return_value=schedule), \
             patch.object(leave_signals, "leave_breakdown_for_attendance_date", return_value=half_day_rules.HALF_DAY_SECOND), \
             patch("attendance.models.AttendanceLateComeEarlyOut.objects.filter") as filter_mock, \
             patch("attendance.models.AttendanceLateComeEarlyOut.objects.get_or_create", get_or_create):
            filter_mock.return_value.delete.return_value = None
            leave_signals._rebuild_late_early_records(attendance)

        get_or_create.assert_called_once()
        _args, kwargs = get_or_create.call_args
        self.assertEqual(kwargs["type"], "early_out")

    def test_cancel_leave_never_deletes_punching_history(self):
        from leave import signals as leave_signals

        attendance = SimpleNamespace(
            attendance_clock_in=None,
            attendance_clock_out=None,
            attendance_clock_in_channel=None,
            attendance_clock_out_channel=None,
            save=MagicMock(),
        )
        in_punch = SimpleNamespace(id=11, punch_direction=AttendancePunchDirection.IN, punch_timestamp=timezone.make_aware(datetime(2026, 3, 20, 8, 0)), delete=MagicMock())
        out_punch = SimpleNamespace(id=12, punch_direction=AttendancePunchDirection.OUT, punch_timestamp=timezone.make_aware(datetime(2026, 3, 20, 17, 0)), delete=MagicMock())

        with patch.object(leave_signals, "leave_breakdown_for_attendance_date", return_value=""), \
             patch.object(leave_signals, "_schedule_for_employee_attendance_date", return_value=None), \
             patch.object(leave_signals, "_raw_logs_for_attendance_date", return_value=[in_punch, out_punch]), \
             patch.object(leave_signals, "_ensure_attendance_shell", return_value=attendance), \
             patch("attendance.services.punching_history.assign_raw_punch_to_attendance", return_value=None):
            leave_signals._materialize_attendance_for_leave_date("EMP-CANCEL", date(2026, 3, 20))

        in_punch.delete.assert_not_called()
        out_punch.delete.assert_not_called()
