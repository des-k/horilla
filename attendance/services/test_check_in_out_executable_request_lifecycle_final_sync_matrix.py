from __future__ import annotations

from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.services.activity_sync import mark_approved_request_channels, sync_single_session_activity


class FakeAttendance(SimpleNamespace):
    def __init__(self, **overrides):
        employee = overrides.pop("employee", SimpleNamespace(id=301))
        defaults = {
            "id": 99,
            "employee_id": employee,
            "attendance_date": date(2026, 3, 19),
            "attendance_day": None,
            "attendance_clock_in_date": date(2026, 3, 19),
            "attendance_clock_in": time(9, 0),
            "attendance_clock_in_channel": "biometric",
            "attendance_clock_in_image": None,
            "attendance_clock_in_mode": None,
            "attendance_clock_in_location": None,
            "attendance_clock_out_date": date(2026, 3, 19),
            "attendance_clock_out": time(17, 0),
            "attendance_clock_out_channel": "biometric",
            "attendance_clock_out_image": None,
            "attendance_clock_out_mode": None,
            "attendance_clock_out_location": None,
            "request_type": "update_request",
            "requested_data": {"__meta": {"current_scope": "IN"}},
            "is_validate_request_approved": True,
            "work_mode_request_id": None,
        }
        defaults.update(overrides)
        super().__init__(**defaults)
        self.saved_update_fields = []

    def save(self, *args, **kwargs):
        self.saved_update_fields.append(list(kwargs.get("update_fields") or []))


class FakeActivity(SimpleNamespace):
    def __init__(self):
        super().__init__(save_calls=[])

    def save(self, *args, **kwargs):
        self.save_calls.append(kwargs)


class AttendanceRequestLifecycleFinalSyncExecutableTests(SimpleTestCase):
    databases = "__all__"

    def test_mark_approved_request_channels_only_marks_requested_scope_for_correction(self):
        attendance = FakeAttendance(
            request_type="update_request",
            requested_data={"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}},
            attendance_clock_out_channel="biometric",
        )

        result = mark_approved_request_channels(attendance)

        self.assertIs(result, attendance)
        self.assertEqual(attendance.attendance_clock_in_channel, "correction_request")
        self.assertEqual(attendance.attendance_clock_out_channel, "biometric")
        self.assertIn("attendance_clock_in_channel", attendance.saved_update_fields[-1])
        self.assertNotIn("attendance_clock_out_channel", attendance.saved_update_fields[-1])

    def test_mark_approved_request_channels_marks_both_sessions_for_create_request(self):
        attendance = FakeAttendance(
            request_type="create_request",
            requested_data={"attendance_clock_in": "09:00:00", "attendance_clock_out": "17:00:00", "__meta": {"current_scope": "FULL"}},
        )

        mark_approved_request_channels(attendance)

        self.assertEqual(attendance.attendance_clock_in_channel, "approved_request")
        self.assertEqual(attendance.attendance_clock_out_channel, "approved_request")
        self.assertIn("attendance_clock_in_channel", attendance.saved_update_fields[-1])
        self.assertIn("attendance_clock_out_channel", attendance.saved_update_fields[-1])

    def test_sync_single_session_activity_after_approve_keeps_request_in_and_raw_out_channels_aligned(self):
        attendance = FakeAttendance(
            request_type="update_request",
            attendance_clock_in_channel="correction_request",
            attendance_clock_out_channel="biometric",
        )
        activity = FakeActivity()

        with patch("attendance.services.activity_sync._locked_activity", return_value=activity), patch(
            "attendance.services.activity_sync.EmployeeShiftDay.objects.filter"
        ) as shift_filter:
            shift_filter.return_value.first.return_value = None
            result = sync_single_session_activity(attendance)

        self.assertIs(result, activity)
        self.assertEqual(activity.clock_in_channel, "correction_request")
        self.assertEqual(activity.clock_out_channel, "biometric")
        self.assertEqual(activity.clock_in, attendance.attendance_clock_in)
        self.assertEqual(activity.clock_out, attendance.attendance_clock_out)

    def test_sync_single_session_activity_after_revoke_restores_raw_channels(self):
        attendance = FakeAttendance(
            request_type="revoke_request",
            is_validate_request_approved=False,
            attendance_clock_in_channel="biometric",
            attendance_clock_out_channel="biometric",
        )
        activity = FakeActivity()

        with patch("attendance.services.activity_sync._locked_activity", return_value=activity), patch(
            "attendance.services.activity_sync.EmployeeShiftDay.objects.filter"
        ) as shift_filter:
            shift_filter.return_value.first.return_value = None
            result = sync_single_session_activity(attendance)

        self.assertIs(result, activity)
        self.assertEqual(activity.clock_in_channel, "biometric")
        self.assertEqual(activity.clock_out_channel, "biometric")
        self.assertEqual(activity.attendance_date, attendance.attendance_date)
