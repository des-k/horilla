from __future__ import annotations

from types import SimpleNamespace

from django.contrib.auth.models import Permission, User
from rest_framework.test import APIClient, APIRequestFactory

from base.models import Company
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

