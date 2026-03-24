from datetime import date
from types import SimpleNamespace

from django.test import TestCase

from attendance.models import Attendance
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from notifications.domain_notifications import send_attendance_request_notification
from notifications.models import Notification


class DomainNotificationHelperSafetyTests(AttendanceApiIntegrationMixin, TestCase):
    def setUp(self):
        super().setUp()
        self.manager_user, self.manager = self.create_employee('Manager')
        self.owner_user, self.owner = self.create_employee('Owner', manager=self.manager)

    def _attendance(self, when: date) -> Attendance:
        return Attendance.objects.create(
            employee_id=self.owner,
            attendance_date=when,
            request_type='update_request',
            is_validate_request=True,
        )

    def test_non_model_actor_falls_back_to_real_recipient_as_sender(self):
        attendance = self._attendance(date(2026, 3, 27))

        send_attendance_request_notification(
            actor=SimpleNamespace(name='actor double'),
            recipient=self.manager_user,
            attendance=attendance,
            event='attendance_request_created',
            recipient_role='approver',
        )

        notification = Notification.objects.latest('id')
        self.assertEqual(notification.recipient, self.manager_user)
        self.assertEqual(str(notification.actor_object_id), str(self.manager_user.id))
        self.assertEqual(notification.data['event'], 'attendance_request_created')

    def test_non_model_recipient_short_circuits_without_persisting(self):
        attendance = self._attendance(date(2026, 3, 28))

        send_attendance_request_notification(
            actor=self.owner_user,
            recipient=SimpleNamespace(name='recipient double'),
            attendance=attendance,
            event='attendance_request_created',
            recipient_role='approver',
        )

        self.assertEqual(Notification.objects.count(), 0)
