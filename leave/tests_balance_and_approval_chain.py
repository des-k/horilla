from datetime import date
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.test import SimpleTestCase

from horilla_api.api_serializers.leave import serializers as leave_serializers
from horilla_api.api_views.leave.views import LeaveRequestApproveAPIView
from leave.methods import calculate_requested_days
from leave.models import LeaveRequest
from leave import views as leave_views


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


class _FakeConditionApprovalQuerySet(list):
    def filter(self, **kwargs):
        data = list(self)
        for key, expected in kwargs.items():
            data = [item for item in data if getattr(item, key) == expected]
        return _FakeConditionApprovalQuerySet(data)

    def order_by(self, *_fields):
        return _FakeConditionApprovalQuerySet(sorted(self, key=lambda item: item.sequence))

    def exists(self):
        return bool(self)

    def first(self):
        return self[0] if self else None


class LeaveBalanceValidationTests(SimpleTestCase):
    def setUp(self):
        self.leave_type = SimpleNamespace(id=1, require_attachment="no")
        self.available_leave = SimpleNamespace(available_days=10, carryforward_days=0)

    def _employee(self, existing_requests=None):
        return SimpleNamespace(leaverequest_set=_FakeLeaveQuerySet(existing_requests or []))

    def _payload(self, employee, *, start_date=date(2026, 3, 20), end_date=date(2026, 3, 20), leave_type=None, attachment=None):
        return {
            "employee_id": employee,
            "leave_type_id": leave_type or self.leave_type,
            "start_date": start_date,
            "end_date": end_date,
            "start_date_breakdown": "full_day",
            "end_date_breakdown": "full_day",
            "description": "Leave request",
            "attachment": attachment,
        }

    def _patch_validation_dependencies(self, *, requested_days=1, effective_days=1):
        return patch.multiple(
            leave_serializers,
            calculate_requested_days=lambda *args, **kwargs: requested_days,
            cal_effective_requested_days=lambda *args, **kwargs: effective_days,
            validate_second_half_leave_submission=lambda **kwargs: None,
        )

    def test_insufficient_balance_rejects_request(self):
        employee = self._employee()
        data = self._payload(employee)
        serializer = SimpleNamespace(instance=None)
        available_leave = SimpleNamespace(available_days=0.5, carryforward_days=0)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(available_leave)), self._patch_validation_dependencies(requested_days=1, effective_days=1):
            with self.assertRaisesMessage(Exception, "Employee doesn't have enough leave days"):
                leave_serializers.leave_Validations(serializer, data)

    def test_carryforward_consumed_after_regular_balance(self):
        available_leave = SimpleNamespace(available_days=2, carryforward_days=4, save=MagicMock())
        leave_request = SimpleNamespace(
            employee_id="EMP-1",
            leave_type_id="TYPE-1",
            requested_days=5,
            approved_available_days=0,
            approved_carryforward_days=0,
            status="requested",
        )

        with patch("leave.models.AvailableLeave.objects.get", return_value=available_leave):
            LeaveRequest.no_approval(leave_request)

        self.assertEqual(leave_request.status, "approved")
        self.assertEqual(leave_request.approved_available_days, 2)
        self.assertEqual(leave_request.approved_carryforward_days, 3)
        self.assertEqual(available_leave.available_days, 0)
        self.assertEqual(available_leave.carryforward_days, 1)
        available_leave.save.assert_called_once_with()

    def test_requested_days_first_half_is_half_day(self):
        target = date(2026, 3, 20)
        self.assertEqual(
            calculate_requested_days(target, target, "first_half", "first_half"),
            0.5,
        )

    def test_requested_days_second_half_is_half_day(self):
        target = date(2026, 3, 20)
        self.assertEqual(
            calculate_requested_days(target, target, "second_half", "second_half"),
            0.5,
        )

    def test_requested_days_multiday_mixed_breakdown_is_correct(self):
        self.assertEqual(
            calculate_requested_days(
                date(2026, 3, 20),
                date(2026, 3, 22),
                "first_half",
                "second_half",
            ),
            2.0,
        )

    def test_attachment_required_leave_type_rejects_without_file(self):
        employee = self._employee()
        leave_type = SimpleNamespace(id=2, require_attachment="yes")
        data = self._payload(employee, leave_type=leave_type, attachment=None)
        serializer = SimpleNamespace(instance=None)

        with patch.object(leave_serializers.AvailableLeave.objects, "filter", return_value=_FakeAvailableLeaveQuerySet(self.available_leave)), self._patch_validation_dependencies(requested_days=1, effective_days=1):
            with self.assertRaisesMessage(Exception, "This field is required"):
                leave_serializers.leave_Validations(serializer, data)


class LeaveApprovalChainTests(SimpleTestCase):
    def _manager(self, name, user_obj=None):
        return SimpleNamespace(employee_user_id=user_obj if user_obj is not None else name)

    def test_multiple_approvals_check_returns_expected_sequence(self):
        manager1 = self._manager("mgr1")
        manager2 = self._manager("mgr2")
        leave_request = SimpleNamespace(id=55)
        approvals = _FakeConditionApprovalQuerySet(
            [
                SimpleNamespace(sequence=1, is_approved=False, leave_request_id=leave_request, manager_id=manager1),
                SimpleNamespace(sequence=2, is_approved=True, leave_request_id=leave_request, manager_id=manager2),
            ]
        )

        with patch.object(leave_views.LeaveRequestConditionApproval.objects, "filter", return_value=approvals):
            result = leave_views.multiple_approvals_check(leave_request.id)

        self.assertEqual(result["managers"], [manager1, manager2])
        self.assertEqual([item.sequence for item in result["requested"]], [1])
        self.assertEqual([item.sequence for item in result["approved"]], [2])

    def test_first_level_approval_does_not_finalize_request(self):
        view = LeaveRequestApproveAPIView()
        user1 = SimpleNamespace(is_superuser=False)
        manager1 = self._manager("mgr1", user1)
        manager2 = self._manager("mgr2")
        condition_approval = SimpleNamespace(sequence=1, is_approved=False, save=MagicMock())
        leave_request = SimpleNamespace(
            status="requested",
            multiple_approvals=lambda: {"managers": [manager1, manager2]},
            save=MagicMock(),
        )
        user1.employee_get = manager1
        request = SimpleNamespace(user=user1)

        with patch.object(
            leave_views.LeaveRequestConditionApproval.objects,
            "filter",
            return_value=_FakeConditionApprovalQuerySet([condition_approval]),
        ), patch.object(view, "leave_approve_calculation") as calc:
            view.leave_multiple_approve(request, leave_request, available_leave=SimpleNamespace())

        self.assertTrue(condition_approval.is_approved)
        condition_approval.save.assert_called_once_with()
        calc.assert_not_called()
        leave_request.save.assert_not_called()
        self.assertEqual(leave_request.status, "requested")

    def test_last_level_approval_finalizes_request(self):
        view = LeaveRequestApproveAPIView()
        manager1 = self._manager("mgr1")
        user2 = SimpleNamespace(is_superuser=False)
        manager2 = self._manager("mgr2", user2)
        condition_approval = SimpleNamespace(sequence=2, is_approved=False, save=MagicMock())
        leave_request = SimpleNamespace(
            status="requested",
            multiple_approvals=lambda: {"managers": [manager1, manager2]},
            save=MagicMock(),
        )
        user2.employee_get = manager2
        request = SimpleNamespace(user=user2)

        with patch.object(
            leave_views.LeaveRequestConditionApproval.objects,
            "filter",
            return_value=_FakeConditionApprovalQuerySet([condition_approval]),
        ), patch.object(view, "leave_approve_calculation") as calc:
            view.leave_multiple_approve(request, leave_request, available_leave=SimpleNamespace())

        self.assertTrue(condition_approval.is_approved)
        condition_approval.save.assert_called_once_with()
        calc.assert_called_once()
        leave_request.save.assert_called_once_with()
        self.assertEqual(leave_request.status, "approved")
