from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.services import activity_sync
from attendance.services.punching_history import capture_request_restore_snapshot, clear_raw_links_for_request_override, restore_raw_state_after_request
from attendance.services.reconciliation import recompute_attendance_range


class _FakeActivity(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None

    def duration(self):
        if not (self.clock_in_date and self.clock_in and self.clock_out_date and self.clock_out):
            return 0
        from datetime import datetime
        return int((datetime.combine(self.clock_out_date, self.clock_out) - datetime.combine(self.clock_in_date, self.clock_in)).total_seconds())


class _FakeAttendance(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None


class CheckInOutExecutableOvernightMatrixTests(SimpleTestCase):
    databases = {"default"}
    def setUp(self):
        self.employee = SimpleNamespace(id=1)
        self.attendance = _FakeAttendance(
            employee_id=self.employee,
            attendance_date=date(2026, 3, 14),
            attendance_clock_in_date=date(2026, 3, 14),
            attendance_clock_in=time(22, 0),
            attendance_clock_out_date=date(2026, 3, 15),
            attendance_clock_out=time(6, 0),
            attendance_clock_in_channel="biometric",
            attendance_clock_out_channel="biometric",
            attendance_clock_in_image=None,
            attendance_clock_out_image=None,
            attendance_clock_in_mode="wfo",
            attendance_clock_out_mode="wfo",
            attendance_clock_in_location=None,
            attendance_clock_out_location=None,
            work_mode_request_id=None,
            request_restore_snapshot=None,
            attendance_clock_in_punch_id=10,
            attendance_clock_out_punch_id=11,
        )

    def test_overnight_biometric_in_out_finalizes_correct_attendance(self):
        fake_activity = _FakeActivity()
        with patch.object(activity_sync, "_locked_activity", return_value=fake_activity), \
             patch.object(activity_sync.EmployeeShiftDay.objects, "filter") as day_filter:
            day_filter.return_value.first.return_value = None
            activity = activity_sync.sync_single_session_activity(self.attendance)
        self.assertEqual(activity.attendance_date, date(2026, 3, 14))
        self.assertEqual(activity.clock_in_date, date(2026, 3, 14))
        self.assertEqual(activity.clock_out_date, date(2026, 3, 15))
        self.assertEqual(activity.clock_out, time(6, 0))
        self.assertEqual(activity.duration(), 8 * 60 * 60)

    def test_overnight_attendance_request_revoke_restores_raw_truth(self):
        capture_request_restore_snapshot(self.attendance, include_in=True, include_out=True)
        self.attendance.attendance_clock_in = time(23, 0)
        self.attendance.attendance_clock_out = time(7, 0)
        clear_raw_links_for_request_override(self.attendance, include_in=True, include_out=True)

        def _relink(attendance, *, include_in=False, include_out=False):
            if include_in:
                attendance.attendance_clock_in_punch_id = 10
            if include_out:
                attendance.attendance_clock_out_punch_id = 11
            return attendance

        with patch("attendance.services.punching_history.relink_attendance_to_raw_punches", side_effect=_relink):
            restore_raw_state_after_request(self.attendance, include_in=True, include_out=True)

        self.assertEqual(self.attendance.attendance_clock_in, time(22, 0))
        self.assertEqual(self.attendance.attendance_clock_out, time(6, 0))
        self.assertEqual(self.attendance.attendance_clock_out_date, date(2026, 3, 15))
        self.assertEqual(self.attendance.attendance_clock_in_punch_id, 10)
        self.assertEqual(self.attendance.attendance_clock_out_punch_id, 11)

    def test_overnight_recompute_range_expands_previous_and_next_day(self):
        with patch("attendance.services.reconciliation.recompute_attendance") as mocked:
            recompute_attendance_range(self.employee, date(2026, 3, 14), date(2026, 3, 14), expand_for_overnight=True)
        called_dates = [call.args[1] for call in mocked.call_args_list]
        self.assertEqual(called_dates, [date(2026, 3, 13), date(2026, 3, 14), date(2026, 3, 15)])
