from datetime import date
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from horilla_api.api_serializers.leave import serializers as leave_serializers


class _FakeAvailableLeaveQuerySet:
    def __init__(self, available_leave=None):
        self.available_leave = available_leave

    def exists(self):
        return self.available_leave is not None

    def __getitem__(self, index):
        if index != 0 or self.available_leave is None:
            raise IndexError(index)
        return self.available_leave


class _FakeLeaveQuerySet:
    def __init__(self, items):
        self.items = list(items)

    def exclude(self, **kwargs):
        if "status__in" in kwargs:
            excluded = set(kwargs["status__in"])
            return _FakeLeaveQuerySet([item for item in self.items if getattr(item, "status", None) not in excluded])
        if "id" in kwargs:
            excluded_id = kwargs["id"]
            return _FakeLeaveQuerySet([item for item in self.items if getattr(item, "id", None) != excluded_id])
        return self

    def filter(self, **kwargs):
        start_date = kwargs.get("start_date__lte")
        end_date = kwargs.get("end_date__gte")
        filtered = [
            item
            for item in self.items
            if getattr(item, "start_date", None) <= start_date and getattr(item, "end_date", None) >= end_date
        ]
        return _FakeLeaveQuerySet(filtered)

    def __bool__(self):
        return bool(self.items)


class LeaveOverlapValidationTests(SimpleTestCase):
    def setUp(self):
        self.leave_type = SimpleNamespace(id=1, require_attachment="no")
        self.available_leave = SimpleNamespace(available_days=10, carryforward_days=0)

    def _employee(self, existing_requests=None):
        return SimpleNamespace(leaverequest_set=_FakeLeaveQuerySet(existing_requests or []))

    def _existing_request(self, *, status, request_id=1, start_date=date(2026, 3, 10), end_date=date(2026, 3, 10)):
        return SimpleNamespace(
            id=request_id,
            status=status,
            start_date=start_date,
            end_date=end_date,
        )

    def _payload(self, employee, *, start_date=date(2026, 3, 10), end_date=date(2026, 3, 10)):
        return {
            "employee_id": employee,
            "leave_type_id": self.leave_type,
            "start_date": start_date,
            "end_date": end_date,
            "start_date_breakdown": "full_day",
            "end_date_breakdown": "full_day",
            "description": "New leave request",
        }

    def _patch_validation_dependencies(self):
        return patch.multiple(
            leave_serializers,
            calculate_requested_days=lambda *args, **kwargs: 1,
            cal_effective_requested_days=lambda *args, **kwargs: 1,
            validate_second_half_leave_submission=lambda **kwargs: None,
        )

    def test_create_allows_overlap_when_existing_leave_is_rejected(self):
        employee = self._employee([self._existing_request(status="rejected")])
        data = self._payload(employee)
        serializer = SimpleNamespace(instance=None)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies():
            leave_serializers.leave_Validations(serializer, data)

    def test_create_allows_overlap_when_existing_leave_is_cancelled(self):
        employee = self._employee([self._existing_request(status="cancelled")])
        data = self._payload(employee)
        serializer = SimpleNamespace(instance=None)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies():
            leave_serializers.leave_Validations(serializer, data)

    def test_create_blocks_overlap_when_existing_leave_is_requested(self):
        employee = self._employee([self._existing_request(status="requested")])
        data = self._payload(employee)
        serializer = SimpleNamespace(instance=None)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies():
            with self.assertRaisesMessage(Exception, "There is already a leave request for this date range."):
                leave_serializers.leave_Validations(serializer, data)

    def test_create_blocks_overlap_when_existing_leave_is_approved(self):
        employee = self._employee([self._existing_request(status="approved")])
        data = self._payload(employee)
        serializer = SimpleNamespace(instance=None)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies():
            with self.assertRaisesMessage(Exception, "There is already a leave request for this date range."):
                leave_serializers.leave_Validations(serializer, data)

    def test_update_serializer_excludes_current_record_from_overlap_check(self):
        current = self._existing_request(status="requested", request_id=55)
        employee = self._employee([current])
        instance = SimpleNamespace(
            id=current.id,
            start_date=current.start_date,
            end_date=current.end_date,
            start_date_breakdown="full_day",
            end_date_breakdown="full_day",
            employee_id=employee,
            leave_type_id=self.leave_type,
            attachment=None,
        )
        data = {
            "start_date": current.start_date,
            "end_date": current.end_date,
            "start_date_breakdown": "full_day",
            "end_date_breakdown": "full_day",
            "description": "Updated description",
        }
        serializer = SimpleNamespace(instance=instance)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies():
            leave_serializers.leave_Validations(serializer, data)
