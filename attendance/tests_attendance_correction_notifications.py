from datetime import date
from unittest.mock import patch

from django.test import TestCase

from attendance.models import AttendanceCorrectionRequestStatus
from attendance.services.attendance_correction_requests import (
    approve_request,
    cancel_request,
    create_request,
    reject_request,
    revoke_request,
)
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from notifications.models import Notification


class AttendanceCorrectionNotificationTests(AttendanceApiIntegrationMixin, TestCase):
    def setUp(self):
        super().setUp()
        self.manager_user, self.manager = self.create_employee('Manager')
        self.owner_user, self.owner = self.create_employee('Owner', manager=self.manager)
        self.payload = {
            'attendance_date': date(2026, 4, 7),
            'scope': 'IN',
            'reason': 'Forgot device punch',
            'requested_check_in_date': date(2026, 4, 7),
            'requested_check_in_time': '08:30',
            'requested_check_out_date': None,
            'requested_check_out_time': None,
        }

    def _create_waiting_request(self):
        return create_request(
            employee=self.owner,
            actor_user=self.owner_user,
            payload=dict(self.payload),
            uploaded_files=[],
        )

    def test_create_request_notifies_reporting_manager(self):
        req = self._create_waiting_request()

        notification = Notification.objects.latest('id')
        self.assertEqual(notification.recipient, self.manager_user)
        self.assertEqual(notification.data['event'], 'attendance_request_created')
        self.assertEqual(notification.data['entity_id'], req.id)
        self.assertEqual(notification.data['recipient_role'], 'approver')
        self.assertEqual(notification.data['mobile_route'], '/attendance_request')
        self.assertEqual(notification.data['mobile_args']['tab'], 'attendance_request')

    def test_approve_reject_cancel_and_revoke_notify_requester(self):
        with patch('attendance.services.attendance_correction_requests.recompute_attendance', lambda *args, **kwargs: None):
            approved_req = self._create_waiting_request()
            Notification.objects.all().delete()
            approve_request(request_obj=approved_req, actor_user=self.manager_user)
            approved_notice = Notification.objects.latest('id')
            self.assertEqual(approved_notice.recipient, self.owner_user)
            self.assertEqual(approved_notice.data['event'], 'attendance_request_approved')
            approved_req.refresh_from_db()
            self.assertEqual(approved_req.status, AttendanceCorrectionRequestStatus.APPROVED)

            revoked_reason = 'Manual review override'
            Notification.objects.all().delete()
            revoke_request(request_obj=approved_req, actor_user=self.manager_user, reason=revoked_reason)
            revoked_notice = Notification.objects.latest('id')
            self.assertEqual(revoked_notice.recipient, self.owner_user)
            self.assertEqual(revoked_notice.data['event'], 'attendance_request_revoked')
            self.assertEqual(revoked_notice.data['reason'], revoked_reason)
            approved_req.refresh_from_db()
            self.assertEqual(approved_req.status, AttendanceCorrectionRequestStatus.REVOKED)

        rejected_req = self._create_waiting_request()
        reject_reason = 'Outside allowed window'
        Notification.objects.all().delete()
        reject_request(request_obj=rejected_req, actor_user=self.manager_user, reason=reject_reason)
        rejected_notice = Notification.objects.latest('id')
        self.assertEqual(rejected_notice.recipient, self.owner_user)
        self.assertEqual(rejected_notice.data['event'], 'attendance_request_rejected')
        self.assertEqual(rejected_notice.data['reason'], reject_reason)
        rejected_req.refresh_from_db()
        self.assertEqual(rejected_req.status, AttendanceCorrectionRequestStatus.REJECTED)

        canceled_req = self._create_waiting_request()
        Notification.objects.all().delete()
        cancel_request(request_obj=canceled_req, actor_user=self.owner_user)
        canceled_notice = Notification.objects.latest('id')
        self.assertEqual(canceled_notice.recipient, self.owner_user)
        self.assertEqual(canceled_notice.data['event'], 'attendance_request_canceled')
        canceled_req.refresh_from_db()
        self.assertEqual(canceled_req.status, AttendanceCorrectionRequestStatus.CANCELED)
