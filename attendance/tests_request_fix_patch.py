from types import SimpleNamespace
from unittest.mock import patch

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
from attendance.services.work_type_request_permissions import _effective_document_status, can_verify_document
from horilla_api.api_serializers.attendance.serializers import AttendanceRequestSerializer, WorkModeRequestSerializer


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
    def test_effective_document_status_does_not_fallback_to_stale_root_value(self):
        req = SimpleNamespace(
            id=11,
            effective_document_status=lambda: (_ for _ in ()).throw(RuntimeError("boom")),
            document_status=WorkModeRequestDocumentStatus.VERIFIED,
        )
        self.assertIsNone(_effective_document_status(req))

    def test_verify_permission_fails_safe_when_version_resolution_breaks(self):
        request = SimpleNamespace(user=SimpleNamespace(is_superuser=True, has_perm=lambda perm: True))
        req = SimpleNamespace(
            id=22,
            mode=AttendanceWorkMode.ON_DUTY,
            status=WorkModeRequestStatus.APPROVED,
            employee_id=SimpleNamespace(employee_user_id=object()),
            employee_id_id=123,
            effective_document_status=lambda: (_ for _ in ()).throw(RuntimeError("boom")),
        )
        self.assertFalse(can_verify_document(request, req))


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
