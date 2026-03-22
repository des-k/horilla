from unittest.mock import patch

from django.test import RequestFactory, SimpleTestCase

from attendance.models import AttendanceRequestActionType
from horilla_api.api_views.attendance.views import _log_attendance_request_status_change


class AttendanceRequestApiAuditGuardTests(SimpleTestCase):
    def test_attendance_request_audit_logging_raises_instead_of_silent_pass(self):
        request = RequestFactory().post('/api/attendance/request/approve/77/')
        request.user = type('U', (), {'employee_get': object()})()
        attendance = type('AttendanceStub', (), {'id': 77})()

        with patch(
            'horilla_api.api_views.attendance.views.log_request_action',
            side_effect=RuntimeError('audit unavailable'),
        ):
            with self.assertRaises(RuntimeError):
                _log_attendance_request_status_change(
                    attendance,
                    request,
                    action_type=AttendanceRequestActionType.APPROVED,
                    old_status='requested',
                    new_status='approved',
                )
