from datetime import time

from django.contrib.auth.models import Permission, User
from django.core.exceptions import ValidationError
from django.test import SimpleTestCase, TestCase
from django.urls import reverse
from rest_framework.test import APIClient

from base.forms import EmployeeShiftScheduleForm, EmployeeShiftScheduleUpdateForm
from base.models import Company, EmployeeShift, EmployeeShiftDay, EmployeeShiftSchedule
from horilla_api.api_serializers.base.serializers import EmployeeShiftScheduleSerializer


class ShiftScheduleSurfaceFormTests(SimpleTestCase):
    databases = {"default"}

    def test_shift_schedule_forms_include_new_surface_fields_in_expected_order(self):
        form = EmployeeShiftScheduleForm()
        update_form = EmployeeShiftScheduleUpdateForm(instance=EmployeeShiftSchedule())

        for candidate in (form, update_form):
            self.assertIn("break_start_time", candidate.fields)
            self.assertIn("break_end_time", candidate.fields)
            self.assertNotIn("first_half_leave_new_shift_end_time", candidate.fields)
            self.assertIn("first_half_leave_early_checkout_minutes", candidate.fields)
            self.assertIn("second_half_leave_early_checkout_minutes", candidate.fields)

            field_names = list(candidate.fields.keys())
            self.assertLess(field_names.index("end_time"), field_names.index("break_start_time"))
            self.assertLess(field_names.index("break_start_time"), field_names.index("break_end_time"))
            self.assertLess(
                field_names.index("first_half_leave_latest_check_in_time"),
                field_names.index("first_half_leave_early_checkout_minutes"),
            )
            self.assertLess(
                field_names.index("enable_second_half_leave_rule"),
                field_names.index("second_half_leave_early_checkout_minutes"),
            )

    def test_update_form_initializes_new_time_fields_from_instance(self):
        instance = EmployeeShiftSchedule(
            break_start_time=time(12, 0),
            break_end_time=time(13, 0),
        )
        instance.pk = 1

        form = EmployeeShiftScheduleUpdateForm(instance=instance)

        self.assertEqual(form.fields["break_start_time"].initial, "12:00")
        self.assertEqual(form.fields["break_end_time"].initial, "13:00")
        self.assertEqual(form.fields["first_half_leave_early_checkout_minutes"].initial, 30)
        self.assertEqual(form.fields["second_half_leave_early_checkout_minutes"].initial, 30)


class ShiftScheduleSurfaceModelAndApiTests(TestCase):
    def setUp(self):
        self.company = Company.objects.create(
            company="Test Company",
            address="Jl. Test 1",
            country="ID",
            state="Jakarta",
            city="Jakarta",
            zip="12345",
            is_default=True,
        )
        self.shift = EmployeeShift.objects.create(employee_shift="General Shift")
        self.shift.company_id.add(self.company)
        self.day = EmployeeShiftDay.objects.create(day="monday")
        self.day.company_id.add(self.company)

    def create_schedule(self, **overrides):
        payload = {
            "day": self.day,
            "shift_id": self.shift,
            "minimum_working_hour": "08:00",
            "start_time": time(8, 0),
            "end_time": time(17, 0),
            "first_half_leave_latest_check_in_time": time(13, 0),
        }
        payload.update(overrides)
        schedule = EmployeeShiftSchedule.objects.create(**payload)
        schedule.company_id.add(self.company)
        return schedule

    def test_new_fields_persist_and_serializer_exposes_them(self):
        schedule = self.create_schedule(
            break_start_time=time(12, 0),
            break_end_time=time(13, 0),
            first_half_leave_early_checkout_minutes=45,
            second_half_leave_early_checkout_minutes=20,
        )

        schedule.refresh_from_db()
        self.assertEqual(schedule.break_start_time, time(12, 0))
        self.assertEqual(schedule.break_end_time, time(13, 0))
        self.assertEqual(schedule.first_half_leave_early_checkout_minutes, 45)
        self.assertEqual(schedule.second_half_leave_early_checkout_minutes, 20)

        serialized = EmployeeShiftScheduleSerializer(schedule).data
        self.assertEqual(serialized["break_start_time"], "12:00:00")
        self.assertEqual(serialized["break_end_time"], "13:00:00")
        self.assertNotIn("first_half_leave_new_shift_end_time", serialized)
        self.assertEqual(serialized["first_half_leave_early_checkout_minutes"], 45)
        self.assertEqual(serialized["second_half_leave_early_checkout_minutes"], 20)

    def test_break_interval_requires_both_values(self):
        schedule = EmployeeShiftSchedule(
            day=self.day,
            shift_id=self.shift,
            minimum_working_hour="08:00",
            start_time=time(8, 0),
            end_time=time(17, 0),
            first_half_leave_latest_check_in_time=time(13, 0),
            break_start_time=time(12, 0),
        )

        with self.assertRaises(ValidationError) as ctx:
            schedule.clean()

        self.assertIn("break_start_time", ctx.exception.message_dict)
        self.assertIn("break_end_time", ctx.exception.message_dict)

    def test_break_end_must_be_after_break_start(self):
        schedule = EmployeeShiftSchedule(
            day=self.day,
            shift_id=self.shift,
            minimum_working_hour="08:00",
            start_time=time(8, 0),
            end_time=time(17, 0),
            first_half_leave_latest_check_in_time=time(13, 0),
            break_start_time=time(13, 0),
            break_end_time=time(12, 0),
        )

        with self.assertRaises(ValidationError) as ctx:
            schedule.clean()

        self.assertIn("break_end_time", ctx.exception.message_dict)

    def test_backward_compatibility_existing_rows_without_new_fields(self):
        schedule = self.create_schedule()

        schedule.refresh_from_db()
        self.assertIsNone(schedule.break_start_time)
        self.assertIsNone(schedule.break_end_time)
        self.assertEqual(schedule.first_half_leave_early_checkout_minutes, 30)
        self.assertEqual(schedule.second_half_leave_early_checkout_minutes, 30)

        serialized = EmployeeShiftScheduleSerializer(schedule).data
        self.assertIsNone(serialized["break_start_time"])
        self.assertIsNone(serialized["break_end_time"])
        self.assertEqual(serialized["first_half_leave_early_checkout_minutes"], 30)
        self.assertEqual(serialized["second_half_leave_early_checkout_minutes"], 30)

    def test_shift_schedule_detail_api_exposes_new_fields(self):
        schedule = self.create_schedule(
            break_start_time=time(12, 0),
            break_end_time=time(13, 0),
            first_half_leave_early_checkout_minutes=45,
            second_half_leave_early_checkout_minutes=20,
        )
        user = User.objects.create_user(username="viewer", password="pass1234")
        user.user_permissions.add(
            Permission.objects.get(codename="view_employeeshiftschedule")
        )
        client = APIClient()
        client.force_authenticate(user=user)

        response = client.get(
            reverse("api-employee_shift_schedule_detail_with_pk", args=[schedule.pk])
        )

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data["break_start_time"], "12:00:00")
        self.assertEqual(response.data["break_end_time"], "13:00:00")
        self.assertNotIn("first_half_leave_new_shift_end_time", response.data)
        self.assertEqual(response.data["first_half_leave_early_checkout_minutes"], 45)
        self.assertEqual(response.data["second_half_leave_early_checkout_minutes"], 20)
