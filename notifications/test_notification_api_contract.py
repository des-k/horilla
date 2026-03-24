from datetime import date

from django.test import TestCase

from attendance.models import Attendance
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from notifications.domain_notifications import send_attendance_request_notification
from notifications.models import Notification


class NotificationApiContractTests(AttendanceApiIntegrationMixin, TestCase):
    def setUp(self):
        super().setUp()
        self.manager_user, self.manager = self.create_employee('Manager')
        self.owner_user, self.owner = self.create_employee('Owner', manager=self.manager)

    def _create_notification(self):
        attendance = Attendance.objects.create(
            employee_id=self.owner,
            attendance_date=date(2026, 3, 29),
            request_type='update_request',
            is_validate_request=True,
        )
        send_attendance_request_notification(
            actor=self.owner_user,
            recipient=self.manager_user,
            attendance=attendance,
            event='attendance_request_created',
            recipient_role='approver',
        )
        return Notification.objects.latest('id')

    def test_unread_notifications_api_returns_data_payload(self):
        notification = self._create_notification()
        client = self.auth_client(self.manager_user)

        response = client.get('/api/notifications/notifications/list/unread')

        self.assertEqual(response.status_code, 200)
        payload = response.json()['results']
        self.assertEqual(len(payload), 1)
        self.assertEqual(payload[0]['id'], notification.id)
        self.assertEqual(payload[0]['data']['event'], 'attendance_request_created')
        self.assertEqual(payload[0]['data']['mobile_route'], '/attendance_request')

    def test_all_notifications_api_serializes_null_data_safely(self):
        notification = self._create_notification()
        notification.data = None
        notification.verb = 'Legacy notification'
        notification.save(update_fields=['data', 'verb'])
        client = self.auth_client(self.manager_user)

        response = client.get('/api/notifications/notifications/list/all')

        self.assertEqual(response.status_code, 200)
        payload = response.json()['results']
        self.assertEqual(len(payload), 1)
        self.assertEqual(payload[0]['id'], notification.id)
        self.assertIsNone(payload[0]['data'])
        self.assertEqual(payload[0]['verb'], 'Legacy notification')
