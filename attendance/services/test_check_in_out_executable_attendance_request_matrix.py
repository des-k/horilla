from __future__ import annotations

from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.models import AttendanceChannel
from attendance.services.activity_sync import (
    CORRECTION_REQUEST_CHANNEL,
    mark_approved_request_channels,
    sync_single_session_activity,
)
from attendance.services.punching_history import (
    capture_request_restore_snapshot,
    restore_raw_state_after_request,
)


class _FakeAttendance:
    def __init__(self):
        self.employee_id = SimpleNamespace(id=501)
        self.attendance_date = date(2026, 3, 19)
        self.attendance_day = None
        self.attendance_clock_in_date = self.attendance_date
        self.attendance_clock_in = time(8, 2)
        self.attendance_clock_in_channel = AttendanceChannel.BIOMETRIC
        self.attendance_clock_in_mode = "wfo"
        self.attendance_clock_in_punch_id = 111
        self.attendance_clock_in_image = "raw-in.png"
        self.attendance_clock_in_location = {"lat": 1.0}
        self.in_attendance_status = "VALID"
        self.in_attendance_reject_reason_code = None
        self.in_related_work_type_request_id = None

        self.attendance_clock_out_date = self.attendance_date
        self.attendance_clock_out = time(17, 0)
        self.attendance_clock_out_channel = AttendanceChannel.BIOMETRIC
        self.attendance_clock_out_mode = "wfo"
        self.attendance_clock_out_punch_id = 222
        self.attendance_clock_out_image = "raw-out.png"
        self.attendance_clock_out_location = {"lat": 2.0}
        self.out_attendance_status = "VALID"
        self.out_attendance_reject_reason_code = None
        self.out_related_work_type_request_id = None

        self.work_mode_request_id_id = None
        self.request_restore_snapshot = None
        self.request_type = "update_request"
        self.requested_data = {
            "attendance_clock_in": "08:15",
            "__meta": {"approved_scopes": ["IN"], "current_scope": "IN"},
        }
        self.saved_update_fields = []

    def save(self, update_fields=None):
        self.saved_update_fields.append(list(update_fields or []))


class _FakeActivity(SimpleNamespace):
    def __init__(self):
        super().__init__(
            employee_id=None,
            attendance_date=None,
            shift_day=None,
            clock_in_date=None,
            clock_in=None,
            in_datetime=None,
            clock_out_date=None,
            clock_out=None,
            out_datetime=None,
            clock_in_channel=None,
            clock_out_channel=None,
            clock_in_location=None,
            clock_out_location=None,
            clock_in_mode=None,
            clock_out_mode=None,
            work_mode_request_id=None,
            saved=False,
        )

    def save(self):
        self.saved = True


class _FakeFilterResult:
    def __init__(self, value):
        self._value = value

    def first(self):
        return self._value


class AttendanceRequestExecutableMatrixTests(SimpleTestCase):
    def test_capture_and_restore_snapshot_round_trip_preserves_raw_biometric_state(self):
        attendance = _FakeAttendance()

        snapshot = capture_request_restore_snapshot(attendance, include_in=True, include_out=True)
        self.assertEqual(snapshot["in"]["channel"], AttendanceChannel.BIOMETRIC)
        self.assertEqual(snapshot["out"]["punch_id"], 222)

        attendance.attendance_clock_in = time(8, 15)
        attendance.attendance_clock_in_channel = AttendanceChannel.CORRECTION_REQUEST
        attendance.attendance_clock_in_mode = "wfa"
        attendance.attendance_clock_in_punch_id = None
        attendance.attendance_clock_in_image = None
        attendance.attendance_clock_in_location = None
        attendance.in_related_work_type_request_id = 77

        attendance.attendance_clock_out = time(16, 45)
        attendance.attendance_clock_out_channel = AttendanceChannel.CORRECTION_REQUEST
        attendance.attendance_clock_out_mode = "wfa"
        attendance.attendance_clock_out_punch_id = None
        attendance.attendance_clock_out_image = None
        attendance.attendance_clock_out_location = None
        attendance.out_related_work_type_request_id = 88

        restore_raw_state_after_request(attendance, include_in=True, include_out=True)

        self.assertEqual(attendance.attendance_clock_in, time(8, 2))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_in_mode, "wfo")
        self.assertEqual(attendance.attendance_clock_in_punch_id, 111)
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_mode, "wfo")
        self.assertEqual(attendance.attendance_clock_out_punch_id, 222)
        self.assertIsNone(attendance.request_restore_snapshot)

    def test_mark_approved_request_channels_only_updates_the_approved_session_scope(self):
        attendance = _FakeAttendance()
        attendance.attendance_clock_in_channel = AttendanceChannel.MOBILE
        attendance.attendance_clock_out_channel = AttendanceChannel.BIOMETRIC

        mark_approved_request_channels(attendance)

        self.assertEqual(attendance.attendance_clock_in_channel, CORRECTION_REQUEST_CHANNEL)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.saved_update_fields[-1], ["attendance_clock_in_channel"])

    def test_sync_single_session_activity_keeps_missing_checkout_null_for_correction_only_checkin(self):
        attendance = _FakeAttendance()
        attendance.attendance_clock_in_channel = AttendanceChannel.CORRECTION_REQUEST
        attendance.attendance_clock_in_mode = "wfa"
        attendance.attendance_clock_out_date = None
        attendance.attendance_clock_out = None
        attendance.attendance_clock_out_channel = None
        attendance.attendance_clock_out_location = None
        attendance.attendance_clock_out_mode = None

        activity = _FakeActivity()

        with patch("attendance.services.activity_sync._locked_activity", return_value=activity), \
             patch("attendance.services.activity_sync.EmployeeShiftDay.objects.filter", return_value=_FakeFilterResult(None)):
            synced = sync_single_session_activity(attendance)

        self.assertIs(synced, activity)
        self.assertEqual(activity.clock_in_date, attendance.attendance_date)
        self.assertEqual(activity.clock_in, time(8, 2))
        self.assertEqual(activity.clock_in_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(activity.clock_in_mode, "wfa")
        self.assertIsNone(activity.clock_out_date)
        self.assertIsNone(activity.clock_out)
        self.assertIsNone(activity.out_datetime)
        self.assertIsNone(activity.clock_out_channel)
        self.assertTrue(activity.saved)
