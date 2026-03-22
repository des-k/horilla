from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from horilla_api.api_views.leave.views import LeaveRequestRejectAPIView


class LeaveRejectOptionalReasonTests(SimpleTestCase):
    def test_leave_reject_can_store_optional_reason_when_present(self):
        available_leave = SimpleNamespace(available_days=5, carryforward_days=2)
        available_leave.save = lambda: None
        leave_request = SimpleNamespace(
            leave_type_id=SimpleNamespace(id=11),
            approved_available_days=1,
            approved_carryforward_days=0,
            status='approved',
            reject_reason='',
        )
        leave_request.save = lambda: None

        with patch(
            'horilla_api.api_views.leave.views.AvailableLeave.objects.get',
            return_value=available_leave,
        ):
            LeaveRequestRejectAPIView().leave_calculation(
                leave_request,
                employee_id=SimpleNamespace(id=4),
                reject_reason='Insufficient business justification',
            )

        self.assertEqual(leave_request.status, 'rejected')
        self.assertEqual(leave_request.reject_reason, 'Insufficient business justification')
        self.assertEqual(available_leave.available_days, 6)

    def test_leave_reject_without_reason_stays_valid_and_blank(self):
        available_leave = SimpleNamespace(available_days=3, carryforward_days=1)
        available_leave.save = lambda: None
        leave_request = SimpleNamespace(
            leave_type_id=SimpleNamespace(id=12),
            approved_available_days=2,
            approved_carryforward_days=1,
            status='approved',
            reject_reason='should reset',
        )
        leave_request.save = lambda: None

        with patch(
            'horilla_api.api_views.leave.views.AvailableLeave.objects.get',
            return_value=available_leave,
        ):
            LeaveRequestRejectAPIView().leave_calculation(
                leave_request,
                employee_id=SimpleNamespace(id=4),
                reject_reason='',
            )

        self.assertEqual(leave_request.status, 'rejected')
        self.assertEqual(leave_request.reject_reason, '')
        self.assertEqual(available_leave.available_days, 5)
        self.assertEqual(available_leave.carryforward_days, 2)
