from __future__ import annotations

from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.services.request_override_recompute import clear_request_override_and_recompute


class FakeAttendance:
    def __init__(self):
        self.employee_id = SimpleNamespace(id=7)
        self.attendance_date = date(2026, 3, 14)
        self.attendance_clock_in_date = date(2026, 3, 14)
        self.attendance_clock_in = time(8, 0)
        self.attendance_clock_in_channel = "approved_request"
        self.attendance_clock_in_mode = "wfa"
        self.attendance_clock_in_punch = "PUNCH-IN"
        self.attendance_clock_in_image = "img-in"
        self.attendance_clock_in_location = "loc-in"
        self.in_attendance_status = "VALID"
        self.in_attendance_reject_reason_code = "CODE-IN"
        self.in_related_work_type_request_id = 11
        self.attendance_clock_out_date = date(2026, 3, 14)
        self.attendance_clock_out = time(17, 0)
        self.attendance_clock_out_channel = "approved_request"
        self.attendance_clock_out_mode = "wfa"
        self.attendance_clock_out_punch = "PUNCH-OUT"
        self.attendance_clock_out_image = "img-out"
        self.attendance_clock_out_location = "loc-out"
        self.out_attendance_status = "VALID"
        self.out_attendance_reject_reason_code = "CODE-OUT"
        self.out_related_work_type_request_id = 22
        self.work_mode_request_id = 33
        self.request_restore_snapshot = {"in": {"attendance_clock_in": "08:00"}}
        self.saved_update_fields = []

    def save(self, update_fields=None):
        self.saved_update_fields.append(list(update_fields or []))


class RequestOverrideRecomputeTests(SimpleTestCase):
    def test_clear_request_override_and_recompute_clears_both_sessions_and_recomputes(self):
        attendance = FakeAttendance()
        recomputed = SimpleNamespace(attendance="RECOMPUTED")

        with patch(
            "attendance.services.request_override_recompute.recompute_attendance",
            return_value=recomputed,
        ) as recompute:
            result = clear_request_override_and_recompute(
                attendance,
                include_in=True,
                include_out=True,
            )

        self.assertEqual(result, "RECOMPUTED")
        self.assertEqual(attendance.attendance_clock_in_date, None)
        self.assertEqual(attendance.attendance_clock_in, None)
        self.assertEqual(attendance.attendance_clock_out_date, None)
        self.assertEqual(attendance.attendance_clock_out, None)
        self.assertEqual(attendance.attendance_clock_in_channel, None)
        self.assertEqual(attendance.attendance_clock_out_channel, None)
        self.assertEqual(attendance.work_mode_request_id, None)
        self.assertEqual(attendance.request_restore_snapshot, None)
        recompute.assert_called_once_with(attendance.employee_id, attendance.attendance_date)
        saved_fields = set(attendance.saved_update_fields[-1])
        self.assertIn("attendance_clock_in", saved_fields)
        self.assertIn("attendance_clock_out", saved_fields)
        self.assertIn("work_mode_request_id", saved_fields)
        self.assertIn("request_restore_snapshot", saved_fields)
