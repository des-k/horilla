from datetime import date, time

from django.test import Client, TestCase, override_settings

from attendance.models import AttendanceCorrectionRequest, AttendanceCorrectionRequestStatus
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


@override_settings(ALLOWED_HOSTS=['testserver', 'localhost', '127.0.0.1'])
class AttendanceCorrectionWebSmokeTests(AttendanceApiIntegrationMixin, TestCase):
    target_date = date(2026, 4, 3)

    def setUp(self):
        super().setUp()
        self.manager_user, self.manager_employee = self.create_employee('WebManager')
        self.owner_user, self.employee = self.create_employee('WebOwner', manager=self.manager_employee)
        self.client = Client()

    def test_request_pages_render_and_owner_can_cancel_waiting_request(self):
        request_obj = AttendanceCorrectionRequest.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            scope='FULL',
            requested_check_in_date=self.target_date,
            requested_check_in_time=time(8, 0),
            requested_check_out_date=self.target_date,
            requested_check_out_time=time(16, 0),
            reason='Web smoke',
            status=AttendanceCorrectionRequestStatus.WAITING,
        )
        self.client.force_login(self.owner_user)

        listing = self.client.get('/attendance/request-attendance-view/')
        self.assertEqual(listing.status_code, 200)
        self.assertContains(listing, 'Attendance Requests')

        detail = self.client.get(f'/attendance/validate-attendance-request/{request_obj.id}/', HTTP_HX_REQUEST='true')
        self.assertEqual(detail.status_code, 200)
        self.assertContains(detail, 'Requested Value')

        cancel = self.client.get(f'/attendance/cancel-validate-attendance-request/{request_obj.id}/')
        self.assertEqual(cancel.status_code, 302)
        request_obj.refresh_from_db()
        self.assertEqual(request_obj.status, AttendanceCorrectionRequestStatus.CANCELED)
