from __future__ import annotations

from datetime import datetime, time
from types import SimpleNamespace

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.services.canonical_attendance_policy import (
    build_attendance_policy,
    compute_attendance_metrics,
)
from horilla_api.api_views.attendance.views import _compute_mobile_effective_start_and_earliest_checkout


class CanonicalBreakAwareEngineTests(SimpleTestCase):
    def _dt(self, hour: int, minute: int = 0):
        return timezone.make_aware(datetime(2026, 3, 19, hour, minute))

    def _schedule(self, **overrides):
        defaults = {
            "break_start_time": None,
            "break_end_time": None,
            "first_half_leave_latest_check_in_time": time(13, 0),
            "first_half_leave_new_shift_end_time": time(17, 0),
            "second_half_leave_earliest_check_out_time": time(12, 0),
        }
        defaults.update(overrides)
        return SimpleNamespace(**defaults)

    def test_normal_without_break_keeps_existing_required_duration(self):
        policy = build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(16, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(8, 0),
            final_out_dt=self._dt(16, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(policy.required_work_seconds, 8 * 3600)
        self.assertEqual(metrics.worked_seconds, 8 * 3600)
        self.assertEqual(metrics.early_out_seconds, 0)
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(16, 0))

    def test_normal_melewati_break_excludes_break_from_worked_hour(self):
        policy = build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(8, 0),
            final_out_dt=self._dt(17, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.worked_seconds, 8 * 3600)
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(17, 0))

    def test_normal_check_in_telat_yang_spannya_melewati_break_menggeser_target_checkout(self):
        policy = build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(9, 0),
            final_out_dt=self._dt(17, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(18, 0))
        self.assertEqual(metrics.early_out_seconds, 1 * 3600)

    def test_normal_late_excludes_break_interval(self):
        policy = build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(13, 30),
            final_out_dt=self._dt(18, 30),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, (4 * 3600) + (30 * 60))

    def test_second_half_datang_lebih_lambat_dan_melewati_break_menggeser_earliest_checkout(self):
        schedule = self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0))
        policy = build_attendance_policy(
            schedule=schedule,
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind="second_half",
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(9, 0),
            final_out_dt=self._dt(14, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(policy.minimum_hour, "04:00")
        self.assertEqual(policy.required_work_seconds, 4 * 3600)
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(14, 0))
        self.assertEqual(metrics.early_out_seconds, 0)

    def test_first_half_uses_new_shift_end_time_instead_of_half_normal_minimum(self):
        schedule = self._schedule(
            break_start_time=time(12, 0),
            break_end_time=time(13, 0),
            first_half_leave_latest_check_in_time=time(13, 0),
            first_half_leave_new_shift_end_time=time(18, 0),
        )
        policy = build_attendance_policy(
            schedule=schedule,
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind="first_half",
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(13, 0),
            final_out_dt=self._dt(18, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(policy.minimum_hour, "05:00")
        self.assertEqual(policy.required_work_seconds, 5 * 3600)
        self.assertEqual(metrics.earliest_checkout_dt, self._dt(18, 0))

    def test_missing_check_in_is_evidence_based_and_capped_to_half_minimum(self):
        policy = build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(13, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=None,
            final_out_dt=self._dt(17, 0),
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, 4 * 3600)
        self.assertEqual(metrics.early_out_seconds, 0)

    def test_missing_check_out_is_evidence_based_and_capped_to_half_minimum(self):
        policy = build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=self._dt(8, 0),
            final_out_dt=None,
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.early_out_seconds, 4 * 3600)

    def test_missing_in_and_out_uses_half_minimum_for_both_late_and_early_out(self):
        policy = build_attendance_policy(
            schedule=self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0)),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="08:00",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=None,
            final_out_dt=None,
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, 4 * 3600)
        self.assertEqual(metrics.early_out_seconds, 4 * 3600)

    def test_missing_both_can_produce_half_minimum_decimal_minutes(self):
        policy = build_attendance_policy(
            schedule=self._schedule(),
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            minimum_hour="07:31",
            leave_kind=None,
            check_in_cutoff_dt=self._dt(12, 0),
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=None,
            final_out_dt=None,
            grace_seconds=0,
            clock_in_type="after",
        )
        self.assertEqual(metrics.late_seconds, (225 * 60) + 30)
        self.assertEqual(metrics.early_out_seconds, (225 * 60) + 30)

    def test_mobile_helper_uses_same_canonical_second_half_threshold(self):
        schedule = self._schedule(break_start_time=time(12, 0), break_end_time=time(13, 0))
        effective_start_dt, earliest_checkout_dt, valid = _compute_mobile_effective_start_and_earliest_checkout(
            shift_start_dt=self._dt(8, 0),
            shift_end_dt=self._dt(17, 0),
            actual_check_in_dt=self._dt(9, 0),
            clock_in_type="after",
            flex_seconds=0,
            schedule=schedule,
            minimum_hour="08:00",
            leave_kind="second_half",
            check_in_cutoff_dt=self._dt(12, 0),
        )
        self.assertEqual(effective_start_dt, self._dt(9, 0))
        self.assertEqual(earliest_checkout_dt, self._dt(14, 0))
        self.assertFalse(valid)
