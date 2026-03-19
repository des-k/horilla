from __future__ import annotations

from datetime import datetime

from django.test import SimpleTestCase

from attendance.services.final_session_resolution import (
    APPROVED_REQUEST_CHANNEL,
    resolve_final_session,
    should_accept_raw_session,
)
from attendance.services.punching_history import humanize_mobile_error


class CheckInOutSourceMatrixBlueprintTests(SimpleTestCase):
    def test_multi_tap_biometric_in_keeps_earliest_valid_in(self):
        existing = datetime(2026, 3, 19, 8, 5)
        incoming_earlier = datetime(2026, 3, 19, 8, 1)
        incoming_later = datetime(2026, 3, 19, 8, 8)

        self.assertTrue(
            should_accept_raw_session(
                session="IN",
                existing_dt=existing,
                incoming_dt=incoming_earlier,
                existing_channel="biometric",
            )
        )
        self.assertFalse(
            should_accept_raw_session(
                session="IN",
                existing_dt=existing,
                incoming_dt=incoming_later,
                existing_channel="biometric",
            )
        )

    def test_multi_tap_biometric_out_keeps_latest_valid_out(self):
        existing = datetime(2026, 3, 19, 16, 55)
        incoming_later = datetime(2026, 3, 19, 17, 2)
        incoming_earlier = datetime(2026, 3, 19, 16, 40)

        self.assertTrue(
            should_accept_raw_session(
                session="OUT",
                existing_dt=existing,
                incoming_dt=incoming_later,
                existing_channel="biometric",
            )
        )
        self.assertFalse(
            should_accept_raw_session(
                session="OUT",
                existing_dt=existing,
                incoming_dt=incoming_earlier,
                existing_channel="biometric",
            )
        )

    def test_mixed_mobile_and_biometric_raw_punches_pick_earliest_in_and_latest_out(self):
        result_in = resolve_final_session(
            session="IN",
            approved_dt=None,
            raw_datetimes=[
                datetime(2026, 3, 19, 8, 7),
                datetime(2026, 3, 19, 8, 1),
                datetime(2026, 3, 19, 8, 3),
            ],
            raw_source="mixed",
        )
        result_out = resolve_final_session(
            session="OUT",
            approved_dt=None,
            raw_datetimes=[
                datetime(2026, 3, 19, 16, 57),
                datetime(2026, 3, 19, 17, 3),
                datetime(2026, 3, 19, 17, 1),
            ],
            raw_source="mixed",
        )

        self.assertEqual(result_in.final_dt, datetime(2026, 3, 19, 8, 1))
        self.assertEqual(result_out.final_dt, datetime(2026, 3, 19, 17, 3))
        self.assertEqual(result_in.final_source, "mixed")
        self.assertEqual(result_out.final_source, "mixed")

    def test_approved_request_still_overrides_raw_punches(self):
        approved_in = datetime(2026, 3, 19, 8, 15)
        resolved = resolve_final_session(
            session="IN",
            approved_dt=approved_in,
            raw_datetimes=[
                datetime(2026, 3, 19, 8, 1),
                datetime(2026, 3, 19, 8, 3),
            ],
            raw_source="biometric",
        )

        self.assertEqual(resolved.final_dt, approved_in)
        self.assertEqual(resolved.final_source, APPROVED_REQUEST_CHANNEL)
        self.assertEqual(resolved.raw_dt, datetime(2026, 3, 19, 8, 1))

    def test_duplicate_mobile_attempts_are_humanized_for_audit_history(self):
        self.assertEqual(
            humanize_mobile_error("Already clocked-in", direction="in"),
            "Rejected: valid Check-In already exists",
        )
        self.assertEqual(
            humanize_mobile_error("Already clocked-out", direction="out"),
            "Rejected: valid Check-Out already exists",
        )
