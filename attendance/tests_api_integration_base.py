from __future__ import annotations

from django.contrib.auth.models import Permission, User
from rest_framework.test import APIRequestFactory

from base.models import Company
from employee.models import Employee, EmployeeWorkInformation


class AttendanceApiIntegrationMixin:
    @classmethod
    def setUpTestData(cls):
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

    def setUp(self):
        super_method = getattr(super(), 'setUp', None)
        if callable(super_method):
            super_method()
        self.factory = APIRequestFactory()

    @classmethod
    def _next_seq(cls) -> int:
        cls._employee_seq += 1
        return cls._employee_seq

    def create_employee(self, first_name, *, manager=None, is_superuser=False, permissions=None):
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
        return user, employee
