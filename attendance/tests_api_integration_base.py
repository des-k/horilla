from __future__ import annotations

from datetime import datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.contrib.auth.models import Permission, User
from django.utils import timezone
from rest_framework.test import APIClient, APIRequestFactory

from base.models import Company, EmployeeShift, EmployeeShiftDay, EmployeeShiftSchedule
from employee.models import Employee, EmployeeWorkInformation
from horilla.horilla_middlewares import _thread_locals


class AttendanceApiIntegrationMixin:
    @staticmethod
    def _clear_request_context():
        if hasattr(_thread_locals, 'request'):
            delattr(_thread_locals, 'request')

    @classmethod
    def setUpTestData(cls):
        cls._clear_request_context()
        super_method = getattr(super(), 'setUpTestData', None)
        if callable(super_method):
            super_method()
        cls.company = Company.objects.create(
            company='Test Company',
            address='Jl. Test 1',
            country='ID',
            state='Jakarta',
            city='Jakarta',
            zip='12345',
            is_default=True,
        )
        cls._employee_seq = 0
        cls._shift_seq = 0
        cls._clear_request_context()

    def setUp(self):
        self._clear_request_context()
        super_method = getattr(super(), 'setUp', None)
        if callable(super_method):
            super_method()
        self.factory = APIRequestFactory()

    def tearDown(self):
        self._clear_request_context()
        super_method = getattr(super(), 'tearDown', None)
        if callable(super_method):
            super_method()

    @classmethod
    def _next_seq(cls) -> int:
        cls._employee_seq += 1
        return cls._employee_seq

    @classmethod
    def _next_shift_seq(cls) -> int:
        cls._shift_seq += 1
        return cls._shift_seq

    def create_employee(self, first_name, *, manager=None, is_superuser=False, permissions=None):
        self._clear_request_context()
        seq = self.__class__._next_seq()
        username = f'{first_name.lower()}_{seq}'
        user = User.objects.create_user(
            username=username,
            password='pass1234',
            email=f'{username}@example.com',
        )
        user.is_staff = is_superuser
        user.is_superuser = is_superuser
        user.save(update_fields=['is_staff', 'is_superuser'])
        if permissions:
            for codename in permissions:
                user.user_permissions.add(Permission.objects.get(codename=codename))

        employee = Employee.objects.create(
            employee_user_id=user,
            employee_first_name=first_name,
            employee_last_name='User',
            email=f'{username}@example.com',
            phone=f'08{seq:08d}',
        )
        EmployeeWorkInformation.objects.update_or_create(
            employee_id=employee,
            defaults={
                'company_id': self.company,
                'reporting_manager_id': manager,
            },
        )
        self._clear_request_context()
        return user, employee

    def create_shift_with_schedule(
        self,
        *,
        employee,
        day_key: str,
        start_time: time,
        end_time: time,
        minimum_working_hour: str = '08:00',
        is_night_shift: bool = False,
        first_half_latest_check_in_time: time | None = None,
        second_half_earliest_check_out_time: time | None = None,
    ):
        seq = self.__class__._next_shift_seq()
        day_obj = EmployeeShiftDay.objects.create(day=day_key)
        day_obj.company_id.add(self.company)

        shift = EmployeeShift.objects.create(employee_shift=f'SHIFT-{seq}')
        shift.company_id.add(self.company)

        def _seconds(value: time) -> int:
            return value.hour * 3600 + value.minute * 60 + value.second

        start_sec = _seconds(start_time)
        end_sec = _seconds(end_time)
        if end_sec <= start_sec:
            end_sec += 24 * 3600
        midpoint = (start_sec + end_sec) // 2
        midpoint = midpoint % (24 * 3600)
        midpoint_time = time(midpoint // 3600, (midpoint % 3600) // 60, midpoint % 60)

        first_half_latest_check_in_time = first_half_latest_check_in_time or midpoint_time
        second_half_earliest_check_out_time = second_half_earliest_check_out_time or midpoint_time

        schedule = EmployeeShiftSchedule.objects.create(
            day=day_obj,
            shift_id=shift,
            minimum_working_hour=minimum_working_hour,
            start_time=start_time,
            end_time=end_time,
            is_night_shift=is_night_shift,
            first_half_leave_latest_check_in_time=first_half_latest_check_in_time,
            second_half_leave_earliest_check_out_time=second_half_earliest_check_out_time,
        )

        work_info = employee.employee_work_info
        work_info.shift_id = shift
        work_info.company_id = self.company
        work_info.save(update_fields=['shift_id', 'company_id'])
        return shift, day_obj, schedule

    def auth_client(self, user):
        self._clear_request_context()
        client = APIClient()
        client.force_authenticate(user=user)
        return client

    def auth_request(self, user, *, selected_company='all'):
        self._clear_request_context()
        request = SimpleNamespace(
            user=user,
            session={'selected_company': selected_company},
            is_filtering=False,
        )
        _thread_locals.request = request
        return request

    def patch_reconciliation_shift_rules(
        self,
        *,
        target_date,
        schedule,
        shift_start_dt: datetime,
        shift_end_dt: datetime,
        check_in_window_start_dt: datetime,
        check_in_window_end_dt: datetime,
        check_out_window_start_dt: datetime,
        check_out_window_end_dt: datetime,
        grace_seconds: int = 0,
        grace_clock_in_type: str = 'after',
        minimum_hour: str = '08:00',
    ):
        def _get_shift_rules(day, shift, day_obj, **kwargs):
            if day != target_date or shift != schedule.shift_id or day_obj != schedule.day:
                return {'schedule': None, 'start_time': None, 'end_time': None}
            return {
                'schedule': schedule,
                'start_time': schedule.start_time,
                'end_time': schedule.end_time,
                'shift_start_dt': shift_start_dt,
                'shift_end_dt': shift_end_dt,
                'check_in_window_start_dt': check_in_window_start_dt,
                'check_in_window_end_dt': check_in_window_end_dt,
                'check_out_window_start_dt': check_out_window_start_dt,
                'check_out_window_end_dt': check_out_window_end_dt,
                'grace_seconds': grace_seconds,
                'clock_in_type': grace_clock_in_type,
            }

        def _resolve_grace_time(_schedule, _shift):
            return SimpleNamespace(clock_in_type=grace_clock_in_type, allowed_clock_out=False, allowed_time_in_secs=grace_seconds)

        return patch.multiple(
            'attendance.services.reconciliation',
            shift_schedule_today=lambda day, shift: (minimum_hour, None, None),
            _get_shift_rule_helpers=lambda: (_get_shift_rules, _resolve_grace_time),
        )

    def patch_monthly_recap_shift_rules(
        self,
        *,
        target_date,
        schedule,
        shift_start_dt: datetime,
        shift_end_dt: datetime,
        check_in_window_start_dt: datetime,
        check_in_window_end_dt: datetime,
        check_out_window_start_dt: datetime,
        check_out_window_end_dt: datetime,
        grace_seconds: int = 0,
        grace_clock_in_type: str = 'after',
    ):
        def _get_shift_rules(day, shift, day_obj, **kwargs):
            if day != target_date or shift != schedule.shift_id or day_obj != schedule.day:
                return {'schedule': None, 'start_time': None, 'end_time': None}
            return {
                'schedule': schedule,
                'start_time': schedule.start_time,
                'end_time': schedule.end_time,
                'shift_start_dt': shift_start_dt,
                'shift_end_dt': shift_end_dt,
                'check_in_window_start_dt': check_in_window_start_dt,
                'check_in_window_end_dt': check_in_window_end_dt,
                'check_out_window_start_dt': check_out_window_start_dt,
                'check_out_window_end_dt': check_out_window_end_dt,
                'grace_seconds': grace_seconds,
                'clock_in_type': grace_clock_in_type,
            }

        def _resolve_grace_time(_schedule, _shift):
            return SimpleNamespace(clock_in_type=grace_clock_in_type, allowed_clock_out=False, allowed_time_in_secs=grace_seconds)

        return patch.multiple(
            'attendance.views.clock_in_out',
            get_shift_rules=_get_shift_rules,
            _resolve_grace_time=_resolve_grace_time,
        )

    @staticmethod
    def aware_dt(year, month, day, hour, minute=0, second=0):
        value = datetime(year, month, day, hour, minute, second)
        if timezone.is_naive(value):
            return timezone.make_aware(value, timezone.get_current_timezone())
        return timezone.localtime(value, timezone.get_current_timezone())
