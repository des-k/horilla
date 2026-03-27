from __future__ import annotations

from pathlib import Path
import unittest

from attendance.services.mobile_status_note import (
    ATTENDANCE_RECORDED,
    CHECKED_IN,
    CHECKED_OUT_EARLY,
    CHECK_OUT_REQUEST_REQUIRED,
    MISSING_CHECK_IN,
    READY_TO_CHECK_IN,
    build_mobile_header_state,
)


class MobileAttendanceHeaderStateTests(unittest.TestCase):
    def test_no_attendance_yet_returns_ready_to_check_in(self):
        payload = {
            "has_attendance": False,
            "can_clock_in": True,
            "can_clock_out": False,
            "attendance_enabled": True,
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], READY_TO_CHECK_IN)
        self.assertEqual(header["header_state_message"], "No record yet")
        self.assertEqual(header["header_detail_message"], "Please Check In")

    def test_checked_in_without_checkout_returns_checked_in_with_earliest_checkout_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:05 AM",
            "last_check_out": None,
            "earliest_check_out": "17:00",
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], CHECKED_IN)
        self.assertEqual(header["header_state_message"], "Checked In")
        self.assertEqual(header["header_detail_message"], "Earliest Check Out: 17:00")

    def test_checked_in_can_surface_late_by_and_earliest_checkout_in_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:20 AM",
            "last_check_out": None,
            "late_by": "00:15",
            "earliest_check_out": "17:20",
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], CHECKED_IN)
        self.assertEqual(header["header_detail_message"], "Late by 00:15 - Earliest Check Out: 17:20")

    def test_missing_check_in_state_is_canonical(self):
        payload = {
            "has_attendance": False,
            "missing_check_in": True,
            "can_clock_out": True,
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], MISSING_CHECK_IN)
        self.assertEqual(header["header_state_message"], "Missing Check In")
        self.assertEqual(header["header_detail_message"], "Check Out available")

    def test_invalid_check_in_is_treated_as_missing_check_in(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "05:00 AM",
            "invalid_check_in": True,
            "can_clock_out": True,
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], MISSING_CHECK_IN)
        self.assertEqual(header["header_state_message"], "Missing Check In")

    def test_missing_check_in_and_early_checkout_are_combined_consistently(self):
        payload = {
            "has_attendance": True,
            "missing_check_in": True,
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
            "checked_out_early_by": "00:45",
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], MISSING_CHECK_IN)
        self.assertEqual(header["header_state_message"], "Missing Check In, Check Out Early")
        self.assertEqual(header["header_detail_message"], "Short by 00:45 - Check Out saved")

    def test_missing_check_in_and_early_checkout_without_duration_keeps_saved_detail(self):
        payload = {
            "has_attendance": True,
            "missing_check_in": True,
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], MISSING_CHECK_IN)
        self.assertEqual(header["header_state_message"], "Missing Check In, Check Out Early")
        self.assertEqual(header["header_detail_message"], "Check Out saved")

    def test_checked_out_normally_returns_attendance_recorded(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:02 AM",
            "last_check_out": "05:16 PM",
            "checked_out_early": False,
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], ATTENDANCE_RECORDED)
        self.assertEqual(header["header_state_message"], "Attendance recorded")

    def test_checked_out_early_is_used_instead_of_below_minimum(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:00 AM",
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
            "checked_out_early_by": "00:15",
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], CHECKED_OUT_EARLY)
        self.assertEqual(header["header_state_message"], "Checked Out early")
        self.assertEqual(header["header_detail_message"], "Short by 00:15")

    def test_checked_out_early_can_surface_short_by_and_late_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:20 AM",
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
            "checked_out_early_by": "00:30",
            "late_by": "00:15",
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], CHECKED_OUT_EARLY)
        self.assertEqual(header["header_detail_message"], "Short by 00:30 - Late by 00:15")

    def test_check_out_request_required_after_cutoff_uses_canonical_message(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:00 AM",
            "last_check_out": None,
            "can_clock_out": False,
            "check_out_block_reason": "AFTER_WINDOW_END",
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], CHECK_OUT_REQUEST_REQUIRED)
        self.assertEqual(header["header_state_message"], "Check Out cutoff passed")
        self.assertEqual(header["header_detail_message"], "Please submit an attendance request")

    def test_attendance_recorded_can_still_surface_late_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:16 AM",
            "last_check_out": "05:16 PM",
            "late_by": "00:10",
            "checked_out_early": False,
        }
        header = build_mobile_header_state(payload)
        self.assertEqual(header["header_state_code"], ATTENDANCE_RECORDED)
        self.assertEqual(header["header_detail_message"], "Late by 00:10")


class MobileAttendanceHeaderSourceIntegrationTests(unittest.TestCase):
    def test_status_endpoint_injects_canonical_header_fields(self):
        source = Path('horilla_api/api_views/attendance/views.py').read_text()
        self.assertIn("payload.update(build_mobile_header_state(payload))", source)
        self.assertIn('"earliest_check_out": earliest_check_out_dt.strftime("%H:%M") if earliest_check_out_dt else None', source)
        self.assertIn("_compute_mobile_effective_start_and_earliest_checkout", source)

    def test_clock_actions_attach_header_state_alongside_action_message(self):
        source = Path('horilla_api/api_views/attendance/views.py').read_text()
        self.assertIn('"message": "Clocked-In"', source)
        self.assertIn('"earliest_check_out": earliest_check_out_hhmm', source)
        self.assertIn("response_payload.update(build_mobile_header_state(response_payload))", source)
        self.assertIn('"message": "Clocked-Out"', source)
        self.assertIn('"checked_out_early_by": checked_out_early_by', source)
        self.assertIn('"earliest_check_out": earliest_check_out_hhmm', source)


if __name__ == '__main__':
    unittest.main()
