from datetime import date
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from horilla_api.api_serializers.leave import serializers as leave_serializers
from leave import methods as leave_methods


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
        items = self.items
        if "status__in" in kwargs:
            excluded = set(kwargs["status__in"])
            items = [item for item in items if getattr(item, "status", None) not in excluded]
        if "id" in kwargs:
            excluded_id = kwargs["id"]
            items = [item for item in items if getattr(item, "id", None) != excluded_id]
        return _FakeLeaveQuerySet(items)

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

    def exists(self):
        return bool(self.items)


class LeaveSameDayOverlapPolicyTests(SimpleTestCase):
    def setUp(self):
        self.leave_type = SimpleNamespace(id=1, require_attachment="no")
        self.available_leave = SimpleNamespace(available_days=10, carryforward_days=0)
        self.target_date = date(2026, 3, 28)

    def _employee(self, existing_requests=None):
        return SimpleNamespace(leaverequest_set=_FakeLeaveQuerySet(existing_requests or []))

    def _existing_request(self, *, status="requested", request_id=1, breakdown="full_day"):
        return SimpleNamespace(
            id=request_id,
            status=status,
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown=breakdown,
            end_date_breakdown=breakdown,
        )

    def _payload(self, employee, *, breakdown="full_day"):
        return {
            "employee_id": employee,
            "leave_type_id": self.leave_type,
            "start_date": self.target_date,
            "end_date": self.target_date,
            "start_date_breakdown": breakdown,
            "end_date_breakdown": breakdown,
            "description": "New leave request",
        }

    def _patch_validation_dependencies(self):
        return patch.multiple(
            leave_serializers,
            calculate_requested_days=lambda *args, **kwargs: 1,
            cal_effective_requested_days=lambda *args, **kwargs: 1,
            validate_second_half_leave_submission=lambda **kwargs: None,
        )

    def test_helper_treats_opposite_half_day_same_date_as_overlap(self):
        employee = self._employee([self._existing_request(breakdown="first_half")])
        overlaps = leave_methods.active_overlapping_leave_requests(
            employee=employee,
            start_date=self.target_date,
            end_date=self.target_date,
        )
        self.assertTrue(overlaps.exists())

    def test_serializer_blocks_all_same_day_active_combinations(self):
        combinations = [
            ("full_day", "first_half"),
            ("full_day", "second_half"),
            ("first_half", "second_half"),
            ("first_half", "first_half"),
            ("second_half", "second_half"),
        ]
        for existing_breakdown, incoming_breakdown in combinations:
            with self.subTest(existing=existing_breakdown, incoming=incoming_breakdown):
                employee = self._employee([self._existing_request(breakdown=existing_breakdown)])
                data = self._payload(employee, breakdown=incoming_breakdown)
                serializer = SimpleNamespace(instance=None)
                with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies():
                    with self.assertRaisesMessage(Exception, "There is already a leave request for this date range."):
                        leave_serializers.leave_Validations(serializer, data)
