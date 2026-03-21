from datetime import time

from django.test import SimpleTestCase

from base.forms import EmployeeShiftScheduleForm, EmployeeShiftScheduleUpdateForm
from base.models import EmployeeShiftSchedule


class ShiftSchedulePolicyFormTests(SimpleTestCase):
    def test_shift_schedule_forms_hide_legacy_fallback_fields_and_reorder_cutoffs(self):
        form = EmployeeShiftScheduleForm()
        update_form = EmployeeShiftScheduleUpdateForm(instance=EmployeeShiftSchedule())

        for candidate in (form, update_form):
            self.assertNotIn("late_checkin_minutes", candidate.fields)
            self.assertNotIn("max_late_checkout_hours", candidate.fields)
            self.assertEqual(candidate.fields["early_checkin_minutes"].label, "Early Check In Minutes")
            self.assertEqual(candidate.fields["early_checkout_grace_minutes"].label, "Early Check Out Minutes")

            field_names = list(candidate.fields.keys())
            self.assertLess(field_names.index("early_checkin_minutes"), field_names.index("cutoff_check_in_offset"))
            self.assertLess(field_names.index("early_checkout_grace_minutes"), field_names.index("cutoff_check_out_offset"))

    def test_shift_schedule_forms_lock_policy_fields_read_only(self):
        form = EmployeeShiftScheduleForm()

        self.assertTrue(form.fields["enable_first_half_leave_rule"].disabled)
        self.assertTrue(form.fields["enable_second_half_leave_rule"].disabled)
        self.assertTrue(form.fields["enable_first_half_leave_rule"].initial)
        self.assertTrue(form.fields["enable_second_half_leave_rule"].initial)

        self.assertTrue(form.fields["is_auto_punch_out_enabled"].disabled)
        self.assertFalse(form.fields["is_auto_punch_out_enabled"].initial)
        self.assertTrue(form.fields["auto_punch_out_time"].disabled)

    def test_shift_schedule_clean_forces_locked_policy_flags(self):
        schedule = EmployeeShiftSchedule(
            start_time=time(8, 0),
            end_time=time(17, 0),
            cutoff_check_in_offset="04:30:00",
            cutoff_check_out_offset="07:00:00",
            enable_first_half_leave_rule=False,
            first_half_leave_latest_check_in_time=time(13, 0),
            enable_second_half_leave_rule=False,
            second_half_leave_earliest_check_out_time=time(12, 0),
            is_auto_punch_out_enabled=True,
            auto_punch_out_time=time(18, 0),
        )

        schedule.clean()

        self.assertTrue(schedule.enable_first_half_leave_rule)
        self.assertTrue(schedule.enable_second_half_leave_rule)
        self.assertFalse(schedule.is_auto_punch_out_enabled)
        self.assertIsNone(schedule.auto_punch_out_time)
