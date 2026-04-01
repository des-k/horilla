from __future__ import annotations

import importlib
import sys
import types
from typing import Any
import unittest
from datetime import datetime, time
from types import SimpleNamespace


_ORIGINAL_ATTENDANCE_METHODS: Any = sys.modules.get("attendance.methods")
_ORIGINAL_ATTENDANCE_METHODS_UTILS: Any = sys.modules.get("attendance.methods.utils")


def _install_stub_utils():
    utils = types.ModuleType("attendance.methods.utils")

    def format_time(seconds):
        seconds = int(seconds or 0)
        hours = seconds // 3600
        minutes = (seconds % 3600) // 60
        return f"{hours:02d}:{minutes:02d}"

    def strtime_seconds(value):
        parts = [int(p) for p in str(value).split(":")]
        if len(parts) == 2:
            hours, minutes = parts
            seconds = 0
        else:
            hours, minutes, seconds = (parts + [0, 0, 0])[:3]
        return (hours * 3600) + (minutes * 60) + seconds

    class Request:
        def __init__(self, *args, **kwargs):
            pass

    utils.format_time = format_time
    utils.strtime_seconds = strtime_seconds
    utils.Request = Request

    methods_pkg = types.ModuleType("attendance.methods")
    methods_pkg.utils = utils
    sys.modules["attendance.methods"] = methods_pkg
    sys.modules["attendance.methods.utils"] = utils


def _restore_original_utils_modules():
    if _ORIGINAL_ATTENDANCE_METHODS is None:
        sys.modules.pop("attendance.methods", None)
    else:
        sys.modules["attendance.methods"] = _ORIGINAL_ATTENDANCE_METHODS

    if _ORIGINAL_ATTENDANCE_METHODS_UTILS is None:
        sys.modules.pop("attendance.methods.utils", None)
    else:
        sys.modules["attendance.methods.utils"] = _ORIGINAL_ATTENDANCE_METHODS_UTILS


_install_stub_utils()
try:
    policy_module = importlib.import_module("attendance.services.canonical_attendance_policy")
finally:
    _restore_original_utils_modules()


def tearDownModule():
    _restore_original_utils_modules()


class CanonicalPolicyStandaloneTests(unittest.TestCase):
    def _dt(self, hour: int, minute: int = 0, *, day: int = 19):
        return datetime(2026, 3, day, hour, minute)

    def _schedule(self, **overrides):
        defaults = {
            "break_start_time": None,
            "break_end_time": None,
            "first_half_leave_latest_check_in_time": time(13, 0),
            "first_half_leave_early_checkout_minutes": 30,
            "second_half_leave_earliest_check_out_time": time(12, 0),
            "second_half_leave_early_checkout_minutes": 30,
        }
        defaults.update(overrides)
        return SimpleNamespace(**defaults)

    def test_break_is_excluded_from_worked_seconds(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(8, 0),
            final_out_dt=self._dt(17, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.worked_seconds, 8 * 3600)

    def test_missing_in_is_evidence_based_and_capped_to_half_minimum(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=None,
            final_out_dt=self._dt(15, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, 4 * 3600)
        self.assertEqual(metrics.early_out_seconds, 2 * 3600)

    def test_missing_in_uses_actual_evidence_when_less_than_half_minimum(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=None,
            final_out_dt=self._dt(11, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, 4 * 3600)
        self.assertEqual(metrics.early_out_seconds, 4 * 3600)

    def test_missing_out_is_evidence_based_and_capped_to_half_minimum(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(9, 0),
            final_out_dt=None,
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, 1 * 3600)
        self.assertEqual(metrics.early_out_seconds, 4 * 3600)

    def test_missing_both_uses_half_minimum_for_late_and_early_out(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="07:31",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=None,
            final_out_dt=None,
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, (225 * 60) + 30)
        self.assertEqual(metrics.early_out_seconds, (225 * 60) + 30)
        self.assertEqual(str(policy_module.seconds_to_decimal_minutes(metrics.late_seconds)), "225.5")

    def test_late_ignores_check_in_seconds_for_minute_precision(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="08:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=datetime(2026, 3, 19, 10, 15, 18),
            final_out_dt=self._dt(18, 45),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, 165 * 60)

    def test_early_out_ignores_check_out_seconds_for_minute_precision(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="08:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(7, 30),
            final_out_dt=datetime(2026, 3, 19, 15, 44, 59),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.early_out_seconds, 16 * 60)

    def test_first_half_missing_out_uses_policy_end_not_extended_target(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(
                break_start_time=time(12, 0),
                break_end_time=time(13, 0),
                first_half_leave_latest_check_in_time=time(13, 0),
            ),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind="first_half",
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(13, 30),
            final_out_dt=None,
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.early_out_seconds, (3 * 3600) + (30 * 60))

    def test_second_half_before_after_can_pull_policy_end_forward(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind="second_half",
            check_in_cutoff_dt=self._dt(12, 0),
        )
        effective_start_dt, earliest_checkout_dt, valid = policy_module.resolve_effective_check_in_and_earliest_checkout(
            policy,
            actual_check_in_dt=self._dt(7, 30),
            clock_in_type="before_after",
            flex_seconds=30 * 60,
        )
        self.assertTrue(valid)
        self.assertEqual(effective_start_dt, self._dt(7, 30))
        self.assertEqual(earliest_checkout_dt, self._dt(11, 30))

    def test_non_flex_full_day_uses_nominal_shift_end_for_early_out(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="07:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(9, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(10, 15),
            final_out_dt=self._dt(13, 6),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(16, 0))
        self.assertEqual(metrics.early_out_seconds, 174 * 60)
        self.assertEqual(metrics.worked_seconds, 111 * 60)

    def test_flex_after_within_window_uses_actual_flex_shift(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="07:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(9, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(8, 10),
            final_out_dt=self._dt(13, 6),
            grace_seconds=90 * 60,
            clock_in_type="after",
        )
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(16, 40))
        self.assertEqual(metrics.early_out_seconds, 214 * 60)

    def test_flex_after_beyond_window_clamps_to_max_flex_and_caps_early_out(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="07:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(9, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(10, 15),
            final_out_dt=self._dt(13, 6),
            grace_seconds=90 * 60,
            clock_in_type="after",
        )
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(17, 30))
        self.assertEqual(metrics.early_out_seconds, 264 * 60)

    def test_before_after_early_checkin_pulls_reference_end_forward(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="07:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(9, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(6, 50),
            final_out_dt=self._dt(13, 6),
            grace_seconds=90 * 60,
            clock_in_type="before_after",
        )
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(15, 20))
        self.assertEqual(metrics.early_out_seconds, 134 * 60)

    def test_grace_checkout_reduces_early_out(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="07:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(9, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(7, 30),
            final_out_dt=self._dt(15, 50),
            grace_seconds=0,
            clock_in_type="after",
            early_out_grace_seconds=15 * 60,
        )
        self.assertEqual(metrics.early_out_seconds, 0)

    def test_worked_seconds_truncates_timestamps_to_minute_before_break_deduction(self):
        policy = policy_module.build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(7, 30),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="07:30",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(9, 0),
        )
        metrics = policy_module.compute_attendance_metrics(
            policy,
            final_in_dt=datetime(2026, 3, 19, 10, 15, 59),
            final_out_dt=datetime(2026, 3, 19, 13, 6, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.worked_seconds, 111 * 60)


if __name__ == "__main__":
    unittest.main()
