from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.services import activity_sync
from attendance.services.punching_history import capture_request_restore_snapshot, clear_raw_links_for_request_override, restore_raw_state_after_request


class _FakeAttendance(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None


class _FakeActivity(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None


class CrossModuleAuditViewsConsistencyTests(SimpleTestCase):
    def setUp(self):
        self.employee = SimpleNamespace(id=55)
        self.in_punch = SimpleNamespace(id=201, source="biometric", accepted_to_attendance=True)
        self.out_punch = SimpleNamespace(id=202, source="biometric", accepted_to_attendance=True)
        self.attendance = _FakeAttendance(
            employee_id=self.employee,
            attendance_date=date(2026, 3, 14),
            attendance_clock_in_date=date(2026, 3, 14),
            attendance_clock_in=time(8, 0),
            attendance_clock_out_date=date(2026, 3, 14),
            attendance_clock_out=time(17, 0),
            attendance_clock_in_channel="biometric",
            attendance_clock_out_channel="biometric",
            attendance_clock_in_punch_id=self.in_punch.id,
            attendance_clock_out_punch_id=self.out_punch.id,
            attendance_clock_in_image=None,
            attendance_clock_out_image=None,
            attendance_clock_in_mode="wfo",
            attendance_clock_out_mode="wfo",
            attendance_clock_in_location=None,
            attendance_clock_out_location=None,
            work_mode_request_id=None,
            request_restore_snapshot=None,
        )

    def test_attendance_activity_and_punch_history_stay_consistent_after_correction_approve(self):
        self.attendance.attendance_clock_in = time(8, 30)
        self.attendance.attendance_clock_out = time(17, 30)
        self.attendance.attendance_clock_in_channel = "request"
        self.attendance.attendance_clock_out_channel = "request"
        clear_raw_links_for_request_override(self.attendance, include_in=True, include_out=True)

        activity = _FakeActivity()
        with patch.object(activity_sync, "_locked_activity", return_value=activity), \
             patch.object(activity_sync.EmployeeShiftDay.objects, "filter") as day_filter:
            day_filter.return_value.first.return_value = None
            synced = activity_sync.sync_single_session_activity(self.attendance)

        self.assertEqual(synced.clock_in, time(8, 30))
        self.assertEqual(synced.clock_out, time(17, 30))
        self.assertEqual(synced.clock_in_channel, "request")
        self.assertEqual(synced.clock_out_channel, "request")
        self.assertIsNone(self.attendance.attendance_clock_in_punch_id)
        self.assertIsNone(self.attendance.attendance_clock_out_punch_id)
        self.assertTrue(self.in_punch.accepted_to_attendance)
        self.assertTrue(self.out_punch.accepted_to_attendance)

    def test_attendance_activity_and_punch_history_stay_consistent_after_correction_revoke(self):
        capture_request_restore_snapshot(self.attendance, include_in=True, include_out=True)
        self.attendance.attendance_clock_in = time(8, 45)
        self.attendance.attendance_clock_out = time(17, 45)
        self.attendance.attendance_clock_in_channel = "request"
        self.attendance.attendance_clock_out_channel = "request"
        clear_raw_links_for_request_override(self.attendance, include_in=True, include_out=True)

        def _relink(attendance, *, include_in=False, include_out=False):
            if include_in:
                attendance.attendance_clock_in_punch_id = self.in_punch.id
            if include_out:
                attendance.attendance_clock_out_punch_id = self.out_punch.id
            return attendance

        with patch("attendance.services.punching_history.relink_attendance_to_raw_punches", side_effect=_relink):
            restore_raw_state_after_request(self.attendance, include_in=True, include_out=True)

        activity = _FakeActivity()
        with patch.object(activity_sync, "_locked_activity", return_value=activity), \
             patch.object(activity_sync.EmployeeShiftDay.objects, "filter") as day_filter:
            day_filter.return_value.first.return_value = None
            synced = activity_sync.sync_single_session_activity(self.attendance)

        self.assertEqual(self.attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(self.attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(self.attendance.attendance_clock_in_punch_id, self.in_punch.id)
        self.assertEqual(self.attendance.attendance_clock_out_punch_id, self.out_punch.id)
        self.assertEqual(synced.clock_in, time(8, 0))
        self.assertEqual(synced.clock_out, time(17, 0))
