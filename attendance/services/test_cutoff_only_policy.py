from datetime import datetime

from django.test import SimpleTestCase

from attendance.services.attendance_window_rules import (
    WindowConfig,
    compute_checkin_window,
    compute_checkout_window_on_duty,
    compute_checkout_window_wfo_wfa,
    early_checkout_reject_reason,
)


class CutoffOnlyAttendanceWindowTests(SimpleTestCase):
    def test_checkin_window_ends_at_shift_start_when_no_cutoff_is_available(self):
        shift_start = datetime(2026, 3, 21, 8, 0)
        start, end = compute_checkin_window(
            shift_start_dt=shift_start,
            cutoff_in_dt=None,
            cfg=WindowConfig(early_checkin_minutes=90, early_checkout_minutes=0),
        )

        self.assertEqual(start, datetime(2026, 3, 21, 6, 30))
        self.assertEqual(end, shift_start)

    def test_checkout_window_ends_at_shift_end_when_no_cutoff_is_available(self):
        shift_end = datetime(2026, 3, 21, 17, 0)
        start, end = compute_checkout_window_wfo_wfa(
            shift_end_dt=shift_end,
            cutoff_out_dt=None,
            cfg=WindowConfig(early_checkin_minutes=120, early_checkout_minutes=15),
        )

        self.assertEqual(start, datetime(2026, 3, 21, 16, 45))
        self.assertEqual(end, shift_end)

    def test_on_duty_checkout_window_matches_normal_checkout_window(self):
        shift_end = datetime(2026, 3, 21, 17, 0)
        cfg = WindowConfig(early_checkin_minutes=120, early_checkout_minutes=10)

        normal = compute_checkout_window_wfo_wfa(
            shift_end_dt=shift_end,
            cutoff_out_dt=None,
            cfg=cfg,
        )
        on_duty = compute_checkout_window_on_duty(
            cutoff_in_dt=datetime(2026, 3, 21, 12, 30),
            shift_end_dt=shift_end,
            cutoff_out_dt=None,
            cfg=cfg,
        )

        self.assertEqual(on_duty, normal)

    def test_early_checkout_reason_is_uniform_for_on_duty(self):
        self.assertEqual(early_checkout_reject_reason(is_on_duty=False), "EARLY_CHECKOUT_BEFORE_SHIFT_END")
        self.assertEqual(early_checkout_reject_reason(is_on_duty=True), "EARLY_CHECKOUT_BEFORE_SHIFT_END")
