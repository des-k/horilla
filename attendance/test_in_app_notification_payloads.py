from datetime import date
from unittest.mock import patch

from django.test import TestCase

from attendance.models import Attendance, AttendanceWorkMode, WorkModeRequestScope, WorkModeRequestStatus
from attendance.services.work_type_request_actions import WorkModeRequestActions
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from notifications.domain_notifications import (
    send_attendance_request_notification,
    send_leave_request_notification,
)
from notifications.models import Notification
from leave.models import LeaveRequest, LeaveType


class InAppNotificationPayloadTests(AttendanceApiIntegrationMixin, TestCase):
    def setUp(self):
        super().setUp()
        self.manager_user, self.manager = self.create_employee('Manager')
        self.owner_user, self.owner = self.create_employee('Owner', manager=self.manager)

    def test_attendance_notification_persists_standard_payload(self):
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

        notification = Notification.objects.latest('id')
        self.assertEqual(notification.recipient, self.manager_user)
        self.assertEqual(notification.data['category'], 'attendance')
        self.assertEqual(notification.data['event'], 'attendance_request_created')
        self.assertEqual(notification.data['entity_id'], attendance.id)
        self.assertEqual(notification.data['mobile_route'], '/attendance_request')
        self.assertEqual(notification.data['mobile_args']['tab'], 'attendance_request')

    def test_leave_notification_persists_standard_payload(self):
        leave_type = LeaveType.objects.create(name='Annual Leave', require_approval='yes')
        leave_request = LeaveRequest.objects.create(
            employee_id=self.owner,
            leave_type_id=leave_type,
            start_date=date(2026, 3, 24),
            end_date=date(2026, 3, 24),
            description='Family event',
            requested_days=1,
            created_by=self.owner,
        )

        send_leave_request_notification(
            actor=self.manager,
            recipient=self.owner_user,
            leave_request=leave_request,
            event='leave_request_approved',
            recipient_role='requester',
        )

        notification = Notification.objects.latest('id')
        self.assertEqual(notification.recipient, self.owner_user)
        self.assertEqual(notification.data['category'], 'leave')
        self.assertEqual(notification.data['event'], 'leave_request_approved')
        self.assertEqual(notification.data['entity_id'], leave_request.id)
        self.assertEqual(notification.data['mobile_route'], '/leave_request')
        self.assertEqual(notification.data['mobile_args']['request_id'], leave_request.id)

    def test_work_mode_create_and_approve_emit_notifications(self):
        with patch('attendance.services.work_type_request_actions.validate_work_type_request', lambda **kwargs: None),              patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            req = WorkModeRequestActions.create_request(
                actor=self.owner,
                mode=AttendanceWorkMode.WFA,
                scope=WorkModeRequestScope.FULL,
                start_date=date(2026, 3, 24),
                end_date=date(2026, 3, 24),
                reason='Need remote work',
            )
            WorkModeRequestActions.approve_request(req, actor=self.manager)

        notifications = list(Notification.objects.order_by('id'))
        events = [((notification.data or {}).get('event')) for notification in notifications]
        recipients = [notification.recipient_id for notification in notifications]
        self.assertIn('work_mode_request_created', events)
        self.assertIn('work_mode_request_approved', events)
        self.assertIn(self.manager_user.id, recipients)
        self.assertIn(self.owner_user.id, recipients)
        req.refresh_from_db()
        self.assertEqual(req.status, WorkModeRequestStatus.APPROVED)
