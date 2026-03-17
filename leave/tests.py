from unittest import SkipTest
from datetime import date

from django.contrib.auth.models import User
from django.db import connection
from django.test import TestCase

from employee.models import Employee
from horilla_api.api_serializers.leave.serializers import (
    LeaveRequestCreateUpdateSerializer,
    UpdateLeaveRequestSerializer,
)
from leave.models import AvailableLeave, LeaveRequest, LeaveType


class LeaveOverlapValidationTests(TestCase):
    @classmethod
    def setUpTestData(cls):
        if "employee_employee" not in connection.introspection.table_names():
            raise SkipTest("employee_employee table is unavailable in this test snapshot")
        cls.user = User.objects.create_user(
            username="leave-owner",
            email="leave-owner@example.com",
            password="testpass123",
        )
        cls.employee = Employee.objects.create(
            employee_user_id=cls.user,
            employee_first_name="Leave",
            employee_last_name="Owner",
            email="leave-owner@example.com",
            phone="1234567890",
        )
        cls.leave_type = LeaveType.objects.create(name="Annual Leave")
        AvailableLeave.objects.create(
            employee_id=cls.employee,
            leave_type_id=cls.leave_type,
            available_days=10,
            carryforward_days=0,
            total_leave_days=10,
        )

    def _create_leave_request(self, *, status, start_date=date(2026, 3, 10), end_date=date(2026, 3, 10)):
        return LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=self.leave_type,
            start_date=start_date,
            end_date=end_date,
            start_date_breakdown="full_day",
            end_date_breakdown="full_day",
            requested_days=1,
            description=f"Existing {status} leave",
            status=status,
        )

    def _create_payload(self, *, start_date=date(2026, 3, 10), end_date=date(2026, 3, 10)):
        return {
            "employee_id": self.employee.id,
            "leave_type_id": self.leave_type.id,
            "start_date": start_date,
            "end_date": end_date,
            "start_date_breakdown": "full_day",
            "end_date_breakdown": "full_day",
            "description": "New leave request",
        }

    def test_create_allows_overlap_when_existing_leave_is_rejected(self):
        self._create_leave_request(status="rejected")

        serializer = LeaveRequestCreateUpdateSerializer(data=self._create_payload())

        self.assertTrue(serializer.is_valid(), serializer.errors)

    def test_create_allows_overlap_when_existing_leave_is_cancelled(self):
        self._create_leave_request(status="cancelled")

        serializer = LeaveRequestCreateUpdateSerializer(data=self._create_payload())

        self.assertTrue(serializer.is_valid(), serializer.errors)

    def test_create_blocks_overlap_when_existing_leave_is_requested(self):
        self._create_leave_request(status="requested")

        serializer = LeaveRequestCreateUpdateSerializer(data=self._create_payload())

        self.assertFalse(serializer.is_valid())
        self.assertIn("There is already a leave request for this date range.", str(serializer.errors))

    def test_create_blocks_overlap_when_existing_leave_is_approved(self):
        self._create_leave_request(status="approved")

        serializer = LeaveRequestCreateUpdateSerializer(data=self._create_payload())

        self.assertFalse(serializer.is_valid())
        self.assertIn("There is already a leave request for this date range.", str(serializer.errors))

    def test_update_serializer_excludes_current_record_from_overlap_check(self):
        leave_request = self._create_leave_request(status="requested")

        serializer = UpdateLeaveRequestSerializer(
            leave_request,
            data={
                "start_date": leave_request.start_date,
                "end_date": leave_request.end_date,
                "start_date_breakdown": leave_request.start_date_breakdown,
                "end_date_breakdown": leave_request.end_date_breakdown,
                "description": "Updated description",
            },
        )

        self.assertTrue(serializer.is_valid(), serializer.errors)
