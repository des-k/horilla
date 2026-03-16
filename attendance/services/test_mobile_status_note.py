from __future__ import annotations

import inspect

from django.test import SimpleTestCase

from attendance.services.mobile_status_note import (
    ATTENDANCE_RECORDED,
    BELOW_MINIMUM_HOURS,
    CHECKED_IN,
    CHECKED_OUT_EARLY,
    CHECK_OUT_REQUEST_REQUIRED,
    MISSING_CHECK_IN,
    READY_TO_CHECK_IN,
    build_mobile_header_state,
)


class MobileAttendanceHeaderStateTests(SimpleTestCase):
    def test_no_attendance_yet_returns_ready_to_check_in(self):
        payload = {
            "has_attendance": False,
            "can_clock_in": True,
            "can_clock_out": False,
            "attendance_enabled": True,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], READY_TO_CHECK_IN)
        self.assertEqual(header["header_state_message"], "No record yet • Please Check In")
        self.assertIsNone(header["header_detail_message"])

    def test_checked_in_without_checkout_returns_checked_in(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:05 AM",
            "last_check_out": None,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], CHECKED_IN)
        self.assertEqual(header["header_state_message"], "Checked In • Don’t forget to Check Out")


    def test_checked_in_can_surface_late_by_in_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:20 AM",
            "last_check_out": None,
            "late_by": "00:15",
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], CHECKED_IN)
        self.assertEqual(header["header_detail_message"], "Late by 00:15")

    def test_missing_check_in_state_is_canonical(self):
        payload = {
            "has_attendance": False,
            "missing_check_in": True,
            "can_clock_out": True,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], MISSING_CHECK_IN)
        self.assertEqual(header["header_state_message"], "Missing Check In • Check Out available")

    def test_checked_out_normally_returns_attendance_recorded(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:02 AM",
            "last_check_out": "05:16 PM",
            "work_hours_below_minimum": False,
            "checked_out_early": False,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], ATTENDANCE_RECORDED)
        self.assertEqual(header["header_state_message"], "Attendance recorded")

    def test_below_minimum_hours_returns_detail_from_note_specific_backend_truth(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:02 AM",
            "last_check_out": "03:30 PM",
            "work_hours_below_minimum": False,
            "header_note_work_hours_below_minimum": True,
            "header_note_work_hours_shortfall": "00:30",
            "header_note_effective_minimum_hour": "08:00",
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], BELOW_MINIMUM_HOURS)
        self.assertEqual(header["header_state_message"], "Below minimum hours")
        self.assertEqual(header["header_detail_message"], "Short by 00:30")

    def test_below_minimum_hours_has_priority_over_checked_out_early_when_both_true(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:00 AM",
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
            "header_note_work_hours_below_minimum": True,
            "header_note_work_hours_shortfall": "00:15",
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], BELOW_MINIMUM_HOURS)
        self.assertEqual(header["header_state_message"], "Below minimum hours")
        self.assertEqual(header["header_detail_message"], "Short by 00:15 • Checked out early")

    def test_checked_out_early_is_used_when_note_is_not_below_minimum(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:00 AM",
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
            "header_note_work_hours_below_minimum": False,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], CHECKED_OUT_EARLY)
        self.assertEqual(header["header_state_message"], "Checked Out early")


    def test_checked_out_early_can_surface_duration_and_late_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:20 AM",
            "last_check_out": "03:45 PM",
            "checked_out_early": True,
            "checked_out_early_by": "00:30",
            "late_by": "00:15",
            "header_note_work_hours_below_minimum": False,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], CHECKED_OUT_EARLY)
        self.assertEqual(
            header["header_detail_message"],
            "Checked out early by 00:30 • Late by 00:15",
        )

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
        self.assertEqual(
            header["header_state_message"],
            "Check Out cutoff passed • Please submit an attendance request",
        )

    def test_attendance_recorded_can_still_surface_late_detail(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "08:16 AM",
            "last_check_out": "05:16 PM",
            "late_by": "00:10",
            "work_hours_below_minimum": False,
            "checked_out_early": False,
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], ATTENDANCE_RECORDED)
        self.assertEqual(header["header_detail_message"], "Late by 00:10")

    def test_biometric_created_attendance_is_rendered_from_same_final_truth(self):
        payload = {
            "has_attendance": True,
            "first_check_in": "07:58 AM",
            "last_check_out": "05:01 PM",
            "work_hours_below_minimum": False,
            "checked_out_early": False,
            "reconciliation_source": "biometric",
        }

        header = build_mobile_header_state(payload)

        self.assertEqual(header["header_state_code"], ATTENDANCE_RECORDED)
        self.assertEqual(header["header_state_message"], "Attendance recorded")


class MobileAttendanceHeaderSourceIntegrationTests(SimpleTestCase):
    def test_status_endpoint_injects_canonical_header_fields(self):
        from horilla_api.api_views.attendance.views import CheckingStatus

        source = inspect.getsource(CheckingStatus.get)

        self.assertIn("payload.update(build_mobile_header_state(payload))", source)
        self.assertIn("header_note_work_hours_below_minimum", source)
        self.assertIn("_build_mobile_header_note_context", source)

    def test_clock_actions_attach_header_state_alongside_action_message(self):
        from horilla_api.api_views.attendance.views import ClockInAPIView, ClockOutAPIView

        in_source = inspect.getsource(ClockInAPIView.post)
        out_source = inspect.getsource(ClockOutAPIView.post)

        self.assertIn('"message": "Clocked-In"', in_source)
        self.assertIn("response_payload.update(build_mobile_header_state(response_payload))", in_source)
        self.assertIn('"message": "Clocked-Out"', out_source)
        self.assertIn("header_note_work_hours_below_minimum", out_source)
        self.assertIn('"late_by": late_by_hhmm', out_source)
        self.assertIn('"checked_out_early_by": checked_out_early_by', out_source)
        self.assertIn("response_payload.update(build_mobile_header_state(response_payload))", out_source)
