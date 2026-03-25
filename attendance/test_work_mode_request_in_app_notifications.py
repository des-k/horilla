from __future__ import annotations

from datetime import date
from unittest.mock import patch

from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import TestCase

from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequestDocumentStatus,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)
from attendance.services.work_type_request_actions import (
    WorkModeRequestActionError,
    WorkModeRequestActions,
)
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from notifications.models import Notification


class WorkModeInAppNotificationTests(AttendanceApiIntegrationMixin, TestCase):
    def setUp(self):
        super().setUp()
        self.manager_user, self.manager = self.create_employee('Manager')
        self.owner_user, self.owner = self.create_employee('Owner', manager=self.manager)

    @staticmethod
    def _pdf_file(name='proof.pdf'):
        return SimpleUploadedFile(name, b'PDF', content_type='application/pdf')

    def _notification_events(self):
        return [((notification.data or {}).get('event')) for notification in Notification.objects.order_by('id')]

    def _notifications_for(self, user):
        return Notification.objects.filter(recipient=user).order_by('id')

    def _create_wfa(self):
        with patch('attendance.services.work_type_request_actions.validate_work_type_request', lambda **kwargs: None), \
             patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            return WorkModeRequestActions.create_request(
                actor=self.owner,
                mode=AttendanceWorkMode.WFA,
                scope=WorkModeRequestScope.FULL,
                start_date=date(2026, 3, 24),
                end_date=date(2026, 3, 24),
                reason='Need remote work',
            )

    def _create_on_duty(self, *, uploaded_files=None):
        with patch('attendance.services.work_type_request_actions.validate_work_type_request', lambda **kwargs: None), \
             patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            return WorkModeRequestActions.create_request(
                actor=self.owner,
                mode=AttendanceWorkMode.ON_DUTY,
                scope=WorkModeRequestScope.FULL,
                start_date=date(2026, 3, 24),
                end_date=date(2026, 3, 24),
                reason='Client visit',
                duty_destination_location='Client HQ',
                uploaded_files=uploaded_files or [],
            )

    def test_reject_wfa_notifies_requester_once_and_keeps_reason(self):
        req = self._create_wfa()
        Notification.objects.all().delete()

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance', lambda req: None):
            WorkModeRequestActions.reject_request(req, actor=self.manager, remark='Need office presence')

        notifications = list(self._notifications_for(self.owner_user))
        self.assertEqual(len(notifications), 1)
        payload = notifications[0].data
        self.assertEqual(payload['event'], 'work_mode_request_rejected')
        self.assertEqual(payload['category'], 'work_mode')
        self.assertEqual(payload['entity_id'], req.id)
        self.assertEqual(payload['status'], 'rejected')
        self.assertEqual(payload['mobile_route'], '/attendance_request')
        self.assertEqual(payload['mobile_args']['tab'], 'work_mode_request')
        self.assertEqual(payload['reason'], 'Need office presence')

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None), \
             patch('attendance.services.work_type_request_actions.apply_rejection_to_attendance', lambda req: None):
            with self.assertRaises(WorkModeRequestActionError):
                WorkModeRequestActions.reject_request(req, actor=self.manager, remark='Duplicate reject')

        self.assertEqual(self._notifications_for(self.owner_user).count(), 1)

    def test_cancel_and_revoke_do_not_duplicate_notifications_on_invalid_repeat(self):
        cancel_req = self._create_wfa()
        Notification.objects.all().delete()

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            WorkModeRequestActions.cancel_request(cancel_req, actor=self.owner, remark='No longer needed')

        canceled = list(self._notifications_for(self.owner_user))
        self.assertEqual(len(canceled), 1)
        self.assertEqual(canceled[0].data['event'], 'work_mode_request_canceled')
        self.assertEqual(canceled[0].data['reason'], 'No longer needed')

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            with self.assertRaises(WorkModeRequestActionError):
                WorkModeRequestActions.cancel_request(cancel_req, actor=self.owner, remark='Repeat cancel')

        self.assertEqual(self._notifications_for(self.owner_user).count(), 1)

        revoke_req = self._create_wfa()
        Notification.objects.all().delete()
        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            WorkModeRequestActions.approve_request(revoke_req, actor=self.manager)
            WorkModeRequestActions.revoke_request(revoke_req, actor=self.manager, remark='Trip ended')

        events = self._notification_events()
        self.assertEqual(events, ['work_mode_request_approved', 'work_mode_request_revoked'])
        revoked_notification = self._notifications_for(self.owner_user).latest('id')
        self.assertEqual(revoked_notification.data['reason'], 'Trip ended')
        self.assertEqual(revoked_notification.data['status'], 'revoked')

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            with self.assertRaises(WorkModeRequestActionError):
                WorkModeRequestActions.revoke_request(revoke_req, actor=self.manager, remark='Repeat revoke')

        self.assertEqual(self._notifications_for(self.owner_user).count(), 2)

    def test_on_duty_document_upload_verify_and_reject_emit_expected_notifications(self):
        req = self._create_on_duty(uploaded_files=[self._pdf_file('initial.pdf')])
        Notification.objects.all().delete()

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            WorkModeRequestActions.update_request(
                req,
                actor=self.owner,
                uploaded_files=[self._pdf_file('updated.pdf')],
                remark='Initial evidence',
            )

        upload_notification = self._notifications_for(self.manager_user).latest('id')
        self.assertEqual(upload_notification.data['event'], 'work_mode_document_uploaded')
        self.assertEqual(upload_notification.data['mobile_args']['tab'], 'work_mode_request')
        req.refresh_from_db()
        self.assertEqual(req.status, WorkModeRequestStatus.WAITING_FOR_APPROVAL)
        self.assertEqual(req.document_status, WorkModeRequestDocumentStatus.SUBMITTED)

        Notification.objects.all().delete()
        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            WorkModeRequestActions.approve_request(req, actor=self.manager)
            WorkModeRequestActions.verify_document(req, actor=self.manager, remark='Looks valid')

        events = self._notification_events()
        self.assertEqual(events, ['work_mode_request_approved', 'work_mode_document_verified'])
        verified = self._notifications_for(self.owner_user).latest('id')
        self.assertEqual(verified.data['event'], 'work_mode_document_verified')
        self.assertEqual(verified.data['reason'], 'Looks valid')
        req.refresh_from_db()
        self.assertEqual(req.document_status, WorkModeRequestDocumentStatus.VERIFIED)

        reject_req = self._create_on_duty(uploaded_files=[self._pdf_file('evidence.pdf')])
        Notification.objects.all().delete()
        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            WorkModeRequestActions.approve_request(reject_req, actor=self.manager)
            WorkModeRequestActions.reject_document(reject_req, actor=self.manager, remark='File is blurry')

        rejected = self._notifications_for(self.owner_user).latest('id')
        self.assertEqual(rejected.data['event'], 'work_mode_document_rejected')
        self.assertEqual(rejected.data['reason'], 'File is blurry')
        self.assertEqual(rejected.data['status'], 'document_rejected')
        reject_req.refresh_from_db()
        self.assertEqual(reject_req.document_status, WorkModeRequestDocumentStatus.REJECTED)

    def test_no_op_update_without_files_does_not_emit_document_notification(self):
        req = self._create_on_duty(uploaded_files=[self._pdf_file()])
        Notification.objects.all().delete()

        with patch.object(WorkModeRequestActions, '_recompute', lambda req: None):
            WorkModeRequestActions.update_request(req, actor=self.owner, reason='Client visit updated note')

        self.assertEqual(Notification.objects.count(), 0)
