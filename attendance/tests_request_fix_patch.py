import inspect
from io import BytesIO
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.core.exceptions import ValidationError
from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import RequestFactory, SimpleTestCase
from django.urls import reverse

from attendance.models import (
    Attendance,
    AttendanceWorkMode,
    WorkModeRequestActionType,
    WorkModeRequestDocumentStatus,
    WorkModeRequestStatus,
)
from attendance.services.attachment_validation import validate_uploaded_files
from attendance.services.attendance_request_files import (
    build_attachment_token,
    build_attachment_url,
    verify_attachment_token,
)
from attendance.services.work_type_request_exceptions import WorkModeRequestConsistencyError
from attendance.services.work_type_request_permissions import _effective_document_status, can_verify_document
from attendance.services.work_type_request_rules import classify_work_mode_request_queue, work_mode_request_approval_q, work_mode_request_document_review_q
from attendance.views.work_type_requests import work_type_request_attachment_download
from horilla_api.api_serializers.attendance.serializers import AttendanceRequestSerializer, WorkModeRequestSerializer
from horilla_api.api_views.attendance.views import AttendanceRequestAttachmentDownloadView, WorkModeRequestDocumentActionView


class WorkModeActionTypeTests(SimpleTestCase):
    def test_required_action_types_exist(self):
        values = {choice.value for choice in WorkModeRequestActionType}
        self.assertIn("CREATED", values)
        self.assertIn("UPDATED", values)
        self.assertIn("DOCUMENT_UPLOADED", values)


class AttachmentValidationTests(SimpleTestCase):
    def test_rejects_removed_extensions(self):
        for ext, content_type in (
            ("webp", "image/webp"),
            ("xlsx", "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"),
            ("csv", "text/csv"),
            ("txt", "text/plain"),
        ):
            upload = SimpleUploadedFile(f"proof.{ext}", b"x", content_type=content_type)
            with self.assertRaises(ValidationError):
                validate_uploaded_files([upload])

    def test_accepts_supported_extensions(self):
        upload = SimpleUploadedFile("proof.pdf", b"%PDF-1.4", content_type="application/pdf")
        validate_uploaded_files([upload])

    def test_rejects_mime_mismatch(self):
        upload = SimpleUploadedFile("proof.pdf", b"not really pdf", content_type="text/plain")
        with self.assertRaises(ValidationError):
            validate_uploaded_files([upload])


class AttendanceRequestSerializerStatusTests(SimpleTestCase):
    def test_cancel_and_revoke_statuses_are_explicit(self):
        serializer = AttendanceRequestSerializer()

        canceled = Attendance(request_type="cancel_request")
        revoked = Attendance(request_type="revoke_request")

        self.assertEqual(serializer.get_status(canceled), "CANCELED")
        self.assertEqual(serializer.get_status(revoked), "REVOKED")
        self.assertEqual(serializer.get_action_type(canceled), "CANCELED")
        self.assertEqual(serializer.get_action_type(revoked), "REVOKED")


class AttendanceAttachmentUrlTests(SimpleTestCase):
    def test_build_and_verify_signed_attachment_url(self):
        request = RequestFactory().get("/")
        attendance = SimpleNamespace(id=77)
        file_obj = SimpleNamespace(id=15)

        url = build_attachment_url(request, attendance, file_obj)
        self.assertIn("/api/attendance/attendance-request-attachment/77/15", url)
        token = url.split("token=", 1)[1]
        self.assertTrue(verify_attachment_token(77, 15, token))

    def test_serializer_uses_protected_attendance_urls(self):
        request = RequestFactory().get("/")
        serializer = AttendanceRequestSerializer(context={"request": request})
        fake_file = SimpleNamespace(id=1)
        fake_comment = SimpleNamespace(files=SimpleNamespace(all=lambda: [fake_file]))
        fake_qs = SimpleNamespace(prefetch_related=lambda *args, **kwargs: [fake_comment])
        attendance = Attendance(id=5)

        with patch("attendance.models.AttendanceRequestComment.objects.filter", return_value=fake_qs), patch(
            "horilla_api.api_serializers.attendance.serializers.build_attendance_attachment_url",
            return_value="https://example.test/protected/attendance/5/1?token=abc",
        ):
            urls = serializer.get_attachment_urls(attendance)

        self.assertEqual(urls, ["https://example.test/protected/attendance/5/1?token=abc"])


class WorkModeSerializerTests(SimpleTestCase):
    def test_queue_type_is_explicit(self):
        serializer = WorkModeRequestSerializer()
        approval_req = SimpleNamespace(
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            mode=AttendanceWorkMode.WFA,
            effective_document_status=lambda: WorkModeRequestDocumentStatus.SUBMITTED,
        )
        review_req = SimpleNamespace(
            status=WorkModeRequestStatus.APPROVED,
            mode=AttendanceWorkMode.ON_DUTY,
            effective_document_status=lambda: WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )

        self.assertEqual(serializer.get_queue_type(approval_req), "approval")
        self.assertEqual(serializer.get_queue_type(review_req), "document_review")

    def test_file_links_use_protected_work_mode_url(self):
        request = RequestFactory().get("/")
        serializer = WorkModeRequestSerializer(context={"request": request})
        dummy_req = SimpleNamespace(id=9)
        dummy_file = SimpleNamespace(id=4, file=SimpleNamespace(name="media/private/proof.pdf"))

        with patch(
            "horilla_api.api_serializers.attendance.serializers.build_work_mode_attachment_url",
            return_value="https://example.test/protected/work-mode/9/4?token=def",
        ):
            payload = serializer._serialize_file_links(dummy_req, [dummy_file])

        self.assertEqual(payload[0]["url"], "https://example.test/protected/work-mode/9/4?token=def")
        self.assertEqual(payload[0]["id"], 4)


class PermissionFallbackTests(SimpleTestCase):
    def test_effective_document_status_raises_consistency_error(self):
        req = SimpleNamespace(
            id=11,
            effective_document_status=lambda: (_ for _ in ()).throw(RuntimeError("boom")),
            document_status=WorkModeRequestDocumentStatus.VERIFIED,
        )
        with self.assertRaises(WorkModeRequestConsistencyError):
            _effective_document_status(req)

    def test_verify_permission_hard_fails_when_version_resolution_breaks(self):
        request = SimpleNamespace(user=SimpleNamespace(is_superuser=True, has_perm=lambda perm: True))
        req = SimpleNamespace(
            id=22,
            mode=AttendanceWorkMode.ON_DUTY,
            status=WorkModeRequestStatus.APPROVED,
            employee_id=SimpleNamespace(employee_user_id=object()),
            employee_id_id=123,
            effective_document_status=lambda: (_ for _ in ()).throw(RuntimeError("boom")),
        )
        with self.assertRaises(WorkModeRequestConsistencyError):
            can_verify_document(request, req)


class AttachmentSecurityTests(SimpleTestCase):
    def setUp(self):
        self.factory = RequestFactory()

    def test_attendance_download_denies_token_only_bypass(self):
        request = self.factory.get('/api/attendance/attendance-request-attachment/1/2?token=valid')
        request.user = SimpleNamespace(is_authenticated=False)
        attendance = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(id=2, file=SimpleNamespace(open=MagicMock()))

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', side_effect=[attendance, file_obj]), \
             patch('horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request', return_value=True), \
             patch('horilla_api.api_views.attendance.views.attendance_request_can_view_attachment', return_value=False), \
             patch('horilla_api.api_views.attendance.views.verify_attendance_attachment_token', return_value=True):
            response = AttendanceRequestAttachmentDownloadView().get(request, 1, 2)

        self.assertEqual(response.status_code, 403)

    def test_attendance_download_requires_valid_token_for_authorized_user(self):
        request = self.factory.get('/api/attendance/attendance-request-attachment/1/2?token=bad')
        request.user = SimpleNamespace(is_authenticated=True)
        attendance = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(id=2, file=SimpleNamespace(open=MagicMock()))

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', side_effect=[attendance, file_obj]), \
             patch('horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request', return_value=True), \
             patch('horilla_api.api_views.attendance.views.attendance_request_can_view_attachment', return_value=True), \
             patch('horilla_api.api_views.attendance.views.verify_attendance_attachment_token', return_value=False):
            response = AttendanceRequestAttachmentDownloadView().get(request, 1, 2)

        self.assertEqual(response.status_code, 403)

    def test_attendance_download_allows_authorized_user_with_valid_token(self):
        request = self.factory.get('/api/attendance/attendance-request-attachment/1/2?token=valid')
        request.user = SimpleNamespace(is_authenticated=True)
        file_obj = SimpleNamespace(id=2, file=SimpleNamespace(open=MagicMock(return_value=BytesIO(b'proof'))))
        attendance = SimpleNamespace(id=1)

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', side_effect=[attendance, file_obj]), \
             patch('horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request', return_value=True), \
             patch('horilla_api.api_views.attendance.views.attendance_request_can_view_attachment', return_value=True), \
             patch('horilla_api.api_views.attendance.views.verify_attendance_attachment_token', return_value=True), \
             patch('horilla_api.api_views.attendance.views.FileResponse', return_value=SimpleNamespace(status_code=200)):
            response = AttendanceRequestAttachmentDownloadView().get(request, 1, 2)

        self.assertEqual(response.status_code, 200)

    def test_work_mode_download_source_requires_auth_and_valid_token(self):
        from pathlib import Path

        source = Path('attendance/views/work_type_requests.py').read_text()
        self.assertIn('if not allowed:\n        return HttpResponseForbidden("Not allowed")', source)
        self.assertIn('verify_attachment_token(req.id, file_obj.id, token)', source)
        self.assertNotIn('if not allowed and not verify_attachment_token', source)


class RemainingGapSourceTests(SimpleTestCase):
    def test_bulk_reject_no_longer_wipes_requested_data(self):
        from attendance.views.requests import bulk_reject_attendance_request

        source = inspect.getsource(bulk_reject_attendance_request)
        self.assertNotIn('requested_data = None', source)

    def test_critical_audit_helpers_no_longer_silently_pass(self):
        from attendance.views.requests import _log_attendance_request_action
        from horilla_api.api_views.attendance.views import _log_work_mode_status_change

        self.assertNotIn('except Exception:\n        pass', inspect.getsource(_log_attendance_request_action))
        self.assertNotIn('except Exception:\n        pass', inspect.getsource(_log_work_mode_status_change))


class QueueSemanticsTests(SimpleTestCase):
    def test_queue_classification_separates_approval_and_document_review(self):
        approval_req = SimpleNamespace(
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            mode=AttendanceWorkMode.WFA,
            effective_document_status=lambda: WorkModeRequestDocumentStatus.SUBMITTED,
        )
        review_req = SimpleNamespace(
            status=WorkModeRequestStatus.APPROVED,
            mode=AttendanceWorkMode.ON_DUTY,
            effective_document_status=lambda: WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )
        approved_wfa = SimpleNamespace(
            status=WorkModeRequestStatus.APPROVED,
            mode=AttendanceWorkMode.WFA,
            effective_document_status=lambda: WorkModeRequestDocumentStatus.SUBMITTED,
        )

        self.assertEqual(classify_work_mode_request_queue(approval_req), 'approval')
        self.assertEqual(classify_work_mode_request_queue(review_req), 'document_review')
        self.assertIsNone(classify_work_mode_request_queue(approved_wfa))

    def test_approval_q_only_targets_waiting_requests(self):
        q = work_mode_request_approval_q()
        q_repr = repr(q)
        self.assertIn('WAITING_FOR_APPROVAL', q_repr)
        self.assertNotIn('APPROVED', q_repr)

    def test_document_review_q_targets_approved_on_duty_candidates(self):
        q = work_mode_request_document_review_q()
        q_repr = repr(q)
        self.assertIn('APPROVED', q_repr)
        self.assertIn('on_duty', q_repr.lower())

    def test_document_action_view_handles_consistency_error_explicitly(self):
        source = inspect.getsource(WorkModeRequestDocumentActionView.put)
        self.assertIn('except WorkModeRequestConsistencyError as exc', source)
        self.assertIn('status=409', source)
class ApiUrlTests(SimpleTestCase):
    def test_new_aliases_and_download_url_exist(self):
        self.assertEqual(
            reverse("api-attendance-request-attachment-download", kwargs={"attendance_id": 1, "file_id": 2}),
            "/api/attendance/attendance-request-attachment/1/2",
        )
        self.assertEqual(
            reverse("api-work-type-request-revoke", kwargs={"pk": 1}),
            "/api/attendance/work-type-request-revoke/1",
        )
        self.assertEqual(
            reverse("api-work-mode-request-revoke", kwargs={"pk": 1}),
            "/api/attendance/work-mode-request-revoke/1",
        )
