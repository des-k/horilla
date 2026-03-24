from datetime import date

from django.test import TestCase

from attendance.models import Attendance
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from horilla_api.api_serializers.notifications.serializers import NotificationSerializer
from notifications.domain_notifications import send_attendance_request_notification
from notifications.models import Notification


class NotificationSerializerPayloadTests(AttendanceApiIntegrationMixin, TestCase):
    def setUp(self):
        super().setUp()
        self.manager_user, self.manager = self.create_employee('Manager')
        self.owner_user, self.owner = self.create_employee('Owner', manager=self.manager)

    def test_serializer_keeps_data_payload_fields(self):
        attendance = Attendance.objects.create(
            employee_id=self.owner,
            attendance_date=date(2026, 3, 24),
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

        data = NotificationSerializer(Notification.objects.latest('id')).data
        self.assertEqual(data['data']['event'], 'attendance_request_created')
        self.assertEqual(data['data']['mobile_route'], '/attendance_request')
        self.assertEqual(data['data']['mobile_args']['request_id'], attendance.id)

    def test_serializer_handles_null_data(self):
        attendance = Attendance.objects.create(
            employee_id=self.owner,
            attendance_date=date(2026, 3, 25),
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
        notification = Notification.objects.latest('id')
        notification.data = None
        notification.verb = 'Legacy notification'
        notification.save(update_fields=['data', 'verb'])
        data = NotificationSerializer(notification).data
        self.assertIsNone(data['data'])
        self.assertEqual(data['verb'], 'Legacy notification')
