from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.core.exceptions import ValidationError
from django.test import SimpleTestCase

from leave import half_day_rules


class LeaveBreakdownAndImpactTests(SimpleTestCase):
    def test_leave_breakdown_single_day_first_half(self):
        target = date(2026, 3, 20)
        self.assertEqual(
            half_day_rules.leave_breakdown_for_date(
                start_date=target,
                end_date=target,
                start_date_breakdown=half_day_rules.HALF_DAY_FIRST,
                end_date_breakdown=half_day_rules.HALF_DAY_FIRST,
                target_date=target,
            ),
            half_day_rules.HALF_DAY_FIRST,
        )

    def test_leave_breakdown_single_day_second_half(self):
        target = date(2026, 3, 20)
        self.assertEqual(
            half_day_rules.leave_breakdown_for_date(
                start_date=target,
                end_date=target,
                start_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                target_date=target,
            ),
            half_day_rules.HALF_DAY_SECOND,
        )

    def test_leave_breakdown_multiday_start_middle_end(self):
        start = date(2026, 3, 20)
        end = date(2026, 3, 22)
        self.assertEqual(
            half_day_rules.leave_breakdown_for_date(
                start_date=start,
                end_date=end,
                start_date_breakdown=half_day_rules.HALF_DAY_FIRST,
                end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                target_date=start,
            ),
            half_day_rules.HALF_DAY_FIRST,
        )
        self.assertEqual(
            half_day_rules.leave_breakdown_for_date(
                start_date=start,
                end_date=end,
                start_date_breakdown=half_day_rules.HALF_DAY_FIRST,
                end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                target_date=date(2026, 3, 21),
            ),
            "full_day",
        )
        self.assertEqual(
            half_day_rules.leave_breakdown_for_date(
                start_date=start,
                end_date=end,
                start_date_breakdown=half_day_rules.HALF_DAY_FIRST,
                end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                target_date=end,
            ),
            half_day_rules.HALF_DAY_SECOND,
        )

    def test_impacted_attendance_dates_for_leave_request_deduplicates_and_sorts(self):
        employee = SimpleNamespace(id=99)
        with patch.object(
            half_day_rules,
            "impacted_attendance_dates_for_calendar_date",
            side_effect=[
                [date(2026, 3, 20), date(2026, 3, 19)],
                [date(2026, 3, 21), date(2026, 3, 20)],
            ],
        ):
            impacted = half_day_rules.impacted_attendance_dates_for_leave_request(
                employee=employee,
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 21),
            )

        self.assertEqual(
            impacted,
            [date(2026, 3, 19), date(2026, 3, 20), date(2026, 3, 21)],
        )

    def test_impacted_attendance_dates_for_overnight_shift_leave_includes_previous_attendance_date(self):
        employee = SimpleNamespace(id=100)
        target_date = date(2026, 3, 20)
        overnight_schedule = SimpleNamespace(id=77)
        shift_start = datetime(2026, 3, 19, 22, 0)
        shift_end = datetime(2026, 3, 20, 6, 0)

        with patch.object(
            half_day_rules,
            "resolve_shift_schedule_context",
            return_value={
                "shift": "SHIFT-NIGHT",
                "schedule": overnight_schedule,
                "attendance_date": date(2026, 3, 19),
                "shift_start": shift_start,
                "shift_end": shift_end,
            },
        ), patch.object(half_day_rules, "_employee_shift", return_value="SHIFT-NIGHT"), patch.object(
            half_day_rules,
            "_schedule_for_shift_date",
            return_value=overnight_schedule,
        ), patch.object(
            half_day_rules,
            "_schedule_bounds",
            return_value=(shift_start, shift_end),
        ):
            impacted = half_day_rules.impacted_attendance_dates_for_calendar_date(employee, target_date)

        self.assertEqual(impacted, [date(2026, 3, 19), date(2026, 3, 20)])


class LeaveHalfDaySubmissionValidationTests(SimpleTestCase):
    def test_validate_second_half_leave_requires_checkout_when_policy_enabled(self):
        with patch.object(
            half_day_rules,
            "get_half_day_schedule_config",
            return_value={"require_check_out_before_submit": True},
        ), patch.object(half_day_rules, "_current_day_check_state", return_value=(True, False)):
            with self.assertRaisesMessage(
                ValidationError,
                "You must check out first before submitting second half leave.",
            ):
                half_day_rules.validate_second_half_leave_submission(
                    employee=SimpleNamespace(id=1),
                    start_date=date(2026, 3, 20),
                    end_date=date(2026, 3, 20),
                    start_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                    end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                )

    def test_validate_second_half_leave_allows_when_checkout_rule_disabled(self):
        with patch.object(
            half_day_rules,
            "get_half_day_schedule_config",
            return_value={"require_check_out_before_submit": False},
        ), patch.object(half_day_rules, "_current_day_check_state", return_value=(True, False)):
            half_day_rules.validate_second_half_leave_submission(
                employee=SimpleNamespace(id=2),
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 20),
                start_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
            )

    def test_validate_second_half_leave_allows_when_employee_already_checked_out(self):
        with patch.object(
            half_day_rules,
            "get_half_day_schedule_config",
            return_value={"require_check_out_before_submit": True},
        ), patch.object(half_day_rules, "_current_day_check_state", return_value=(True, True)):
            half_day_rules.validate_second_half_leave_submission(
                employee=SimpleNamespace(id=3),
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 20),
                start_date_breakdown=half_day_rules.HALF_DAY_SECOND,
                end_date_breakdown=half_day_rules.HALF_DAY_SECOND,
            )

    def test_validate_second_half_leave_ignores_non_second_half_requests(self):
        with patch.object(half_day_rules, "get_half_day_schedule_config") as config, patch.object(
            half_day_rules,
            "_current_day_check_state",
        ) as current_state:
            half_day_rules.validate_second_half_leave_submission(
                employee=SimpleNamespace(id=4),
                start_date=date(2026, 3, 20),
                end_date=date(2026, 3, 20),
                start_date_breakdown=half_day_rules.HALF_DAY_FIRST,
                end_date_breakdown=half_day_rules.HALF_DAY_FIRST,
            )

        config.assert_not_called()
        current_state.assert_not_called()
