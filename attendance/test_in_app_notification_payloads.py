from datetime import date
from types import SimpleNamespace
from unittest.mock import patch

from django.test import TestCase

from attendance.models import Attendance, AttendanceWorkMode, WorkModeRequestScope, WorkModeRequestStatus
from attendance.services.work_type_request_actions import WorkModeRequestActions
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from leave.models import LeaveRequest, LeaveType
from notifications.domain_notifications import (
    send_attendance_request_notification,
    send_leave_request_notification,
)
from notifications.models import Notification


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

    def test_attendance_reject_cancel_and_revoke_payloads_include_reason_and_route_contract(self):
        attendance = Attendance.objects.create(
            employee_id=self.owner,
            attendance_date=date(2026, 3, 25),
            request_type='update_request',
            is_validate_request=True,
        )

        send_attendance_request_notification(
            actor=self.manager,
            recipient=self.owner_user,
            attendance=attendance,
            event='attendance_request_rejected',
            recipient_role='requester',
            reason='Outside attendance window',
        )
        send_attendance_request_notification(
            actor=self.owner,
            recipient=self.owner_user,
            attendance=attendance,
            event='attendance_request_canceled',
            recipient_role='requester',
            reason='Requester canceled',
        )
        send_attendance_request_notification(
            actor=self.manager,
            recipient=self.owner_user,
            attendance=attendance,
            event='attendance_request_revoked',
            recipient_role='requester',
            reason='Correction superseded by raw punch',
        )

        notifications = list(Notification.objects.order_by('id'))
        events = [n.data['event'] for n in notifications]
        self.assertEqual(events, ['attendance_request_rejected', 'attendance_request_canceled', 'attendance_request_revoked'])
        rejected, canceled, revoked = notifications
        self.assertEqual(rejected.data['reason'], 'Outside attendance window')
        self.assertEqual(rejected.data['status'], 'rejected')
        self.assertEqual(canceled.data['reason'], 'Requester canceled')
        self.assertEqual(canceled.data['status'], 'canceled')
        self.assertEqual(canceled.data['mobile_args']['request_id'], attendance.id)
        self.assertEqual(revoked.data['reason'], 'Correction superseded by raw punch')
        self.assertEqual(revoked.data['status'], 'revoked')
        self.assertEqual(revoked.data['mobile_route'], '/attendance_request')

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

    def test_leave_created_rejected_and_canceled_payloads_are_consistent(self):
        leave_type = LeaveType.objects.create(name='Emergency Leave', require_approval='yes')
        leave_request = LeaveRequest.objects.create(
            employee_id=self.owner,
            leave_type_id=leave_type,
            start_date=date(2026, 3, 25),
            end_date=date(2026, 3, 25),
            description='Medical',
            requested_days=1,
            created_by=self.owner,
        )

        send_leave_request_notification(
            actor=self.owner,
            recipient=self.manager_user,
            leave_request=leave_request,
            event='leave_request_created',
            recipient_role='approver',
        )
        send_leave_request_notification(
            actor=self.manager,
            recipient=self.owner_user,
            leave_request=leave_request,
            event='leave_request_rejected',
            recipient_role='requester',
            reason='Insufficient staffing',
        )
        send_leave_request_notification(
            actor=self.owner,
            recipient=self.owner_user,
            leave_request=leave_request,
            event='leave_request_canceled',
            recipient_role='requester',
            reason='Trip postponed',
        )

        notifications = list(Notification.objects.order_by('id'))
        self.assertEqual([n.data['event'] for n in notifications], [
            'leave_request_created',
            'leave_request_rejected',
            'leave_request_canceled',
        ])
        self.assertEqual(notifications[0].recipient, self.manager_user)
        self.assertEqual(notifications[1].data['reason'], 'Insufficient staffing')
        self.assertEqual(notifications[2].data['reason'], 'Trip postponed')
        self.assertEqual(notifications[2].data['mobile_route'], '/leave_request')

    def test_helper_tolerates_non_model_sender_without_persisting_notification(self):
        attendance = Attendance.objects.create(
            employee_id=self.owner,
            attendance_date=date(2026, 3, 26),
            request_type='update_request',
            is_validate_request=True,
        )

        send_attendance_request_notification(
            actor=SimpleNamespace(name='non-model actor'),
            recipient=SimpleNamespace(name='non-model recipient'),
            attendance=attendance,
            event='attendance_request_created',
            recipient_role='approver',
        )

        self.assertEqual(Notification.objects.count(), 0)

    def test_work_mode_create_and_approve_emit_notifications(self):
        with patch('attendance.services.work_type_request_actions.validate_work_type_request', lambda **kwargs: None), \
             patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
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
