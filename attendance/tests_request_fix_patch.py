import inspect
import shutil
import tempfile
from datetime import date
from pathlib import Path
from io import BytesIO
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.core.exceptions import ValidationError
from django.core.files.uploadedfile import SimpleUploadedFile
from django.db import connection
from django.db import models as django_models
from django.http import Http404
from django.test import RequestFactory, SimpleTestCase, TestCase, override_settings
from django.urls import reverse
from rest_framework.test import APIRequestFactory, force_authenticate

from django.contrib.auth.models import User
from employee.models import Employee

from attendance.models import (
    Attendance,
    AttendanceRequestFile,
    AttendanceWorkMode,
    WorkModeRequest,
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
from attendance.services.attendance_correction_scope_rules import (
    load_requested_data,
    record_approved_scope_on_requested_data,
)
from attendance.services.attendance_request_access import (
    hard_delete_request_attachment,
    user_can_delete_attachment,
)
from attendance.services.work_type_request_exceptions import WorkModeRequestConsistencyError
from attendance.services.work_type_request_permissions import _effective_document_status, can_verify_document
from attendance.services.work_type_request_rules import classify_work_mode_request_queue, work_mode_request_approval_q, work_mode_request_document_review_q
from attendance.views.work_type_requests import work_type_request_attachment_download
from horilla_api.api_views.attendance.views import (
    AttendanceRequestCancelView,
    AttendanceRequestRejectView,
    AttendanceRequestRevokeView,
    AttendanceRequestView,
)
from horilla_api.api_serializers.attendance.serializers import AttendanceRequestSerializer, WorkModeRequestSerializer
from horilla_api.api_views.attendance.views import AttendanceRequestAttachmentDownloadView, WorkModeRequestApproveView, WorkModeRequestCancelView, WorkModeRequestDocumentActionView, WorkModeRequestView


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
        attendance = Attendance(id=5)

        with patch("attendance.services.attendance_request_access.iter_request_attachments", return_value=[fake_file]), patch(
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


class AttendanceRequestDirectAttachmentSourceTests(SimpleTestCase):
    def test_attendance_model_has_direct_attachment_field(self):
        source = Path("attendance/models.py").read_text()
        self.assertIn("request_attachments = models.ManyToManyField", source)

    def test_requested_data_new_writes_are_not_stringified(self):
        forms_source = Path("attendance/forms.py").read_text()
        self.assertNotIn("requested_data = json.dumps(meta_wrapped)", forms_source)

    def test_comment_flows_disabled_for_attendance_request(self):
        source = Path("attendance/views/views.py").read_text()
        self.assertIn("Attendance request comments are disabled.", source)


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


class AttendanceRequestedDataNormalizationTests(SimpleTestCase):
    def test_load_requested_data_accepts_legacy_string(self):
        payload = load_requested_data('{"attendance_clock_in": "08:05", "__meta": {"current_scope": "IN"}}')
        self.assertEqual(payload["attendance_clock_in"], "08:05")
        self.assertEqual(payload["__meta"]["current_scope"], "IN")

    def test_record_approved_scope_returns_native_dict_and_preserves_meta(self):
        payload = record_approved_scope_on_requested_data({
            "attendance_clock_in": "08:05",
            "__meta": {"current_scope": "IN", "approved_scopes": []},
        })
        self.assertIsInstance(payload, dict)
        self.assertEqual(payload["__meta"]["approved_scopes"], ["IN"])


class AttendanceRequestAttachmentAccessTests(SimpleTestCase):
    def test_owner_can_delete_attachment_only_while_waiting(self):
        owner = object()
        attendance = SimpleNamespace(
            employee_id=SimpleNamespace(employee_user_id=owner),
            is_validate_request=True,
            is_validate_request_approved=False,
        )
        self.assertTrue(user_can_delete_attachment(owner, attendance))

        attendance.is_validate_request_approved = True
        self.assertFalse(user_can_delete_attachment(owner, attendance))

    def test_hard_delete_request_attachment_deletes_relation_model_and_blob(self):
        attendance = SimpleNamespace(request_attachments=SimpleNamespace(remove=MagicMock()))
        storage = SimpleNamespace(delete=MagicMock())
        file_obj = SimpleNamespace(
            file=SimpleNamespace(storage=storage, name="media/private/proof.pdf"),
            delete=MagicMock(),
        )

        hard_delete_request_attachment(attendance, file_obj)

        attendance.request_attachments.remove.assert_called_once_with(file_obj)
        file_obj.delete.assert_called_once()
        storage.delete.assert_called_once_with("media/private/proof.pdf")


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


class AttendanceRequestApiFlowTests(SimpleTestCase):
    databases = {"default"}

    def setUp(self):
        self.factory = APIRequestFactory()
        self.owner_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=10), has_perm=lambda perm: False)
        self.manager_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=11), has_perm=lambda perm: False)
        self.other_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=12), has_perm=lambda perm: False)

    def _attendance(self, **overrides):
        employee = SimpleNamespace(id=10, employee_user_id=self.owner_user)
        defaults = {
            "id": 77,
            "employee_id": employee,
            "employee_id_id": employee.id,
            "attendance_date": date(2026, 3, 10),
            "request_type": "update_request",
            "request_description": "Fix attendance",
            "is_validate_request": True,
            "is_validate_request_approved": False,
            "requested_data": {"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}},
            "request_attachments": SimpleNamespace(add=MagicMock(), remove=MagicMock()),
            "save": MagicMock(),
            "refresh_from_db": MagicMock(),
        }
        defaults.update(overrides)
        return SimpleNamespace(**defaults)

    def test_api_update_request_forbidden_for_unrelated_actor(self):
        attendance = self._attendance()
        request = self.factory.put(
            "/api/attendance/attendance-request/77",
            {"request_description": "edited"},
            format="json",
        )
        force_authenticate(request, user=self.other_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select:
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 403)

    def test_api_update_request_rejects_approved_request_even_for_owner(self):
        attendance = self._attendance(is_validate_request=False, is_validate_request_approved=True)
        request = self.factory.put(
            "/api/attendance/attendance-request/77",
            {"request_description": "edited"},
            format="json",
        )
        force_authenticate(request, user=self.owner_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select:
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn("Approved requests cannot be edited", str(response.data))

    def test_api_reject_requires_reason(self):
        attendance = self._attendance()
        request = self.factory.put(
            "/api/attendance/attendance-request-reject/77",
            {},
            format="json",
        )
        force_authenticate(request, user=self.manager_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select, patch(
            "horilla_api.api_views.attendance.views._can_act_on_employee",
            return_value=True,
        ), patch(
            "horilla_api.api_decorators.base.decorators.ManagerPermission.has_permission",
            return_value=True,
        ):
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestRejectView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn("Reject reason is required", str(response.data))

    def test_api_cancel_rejects_approved_request_for_owner(self):
        attendance = self._attendance(is_validate_request=False, is_validate_request_approved=True)
        request = self.factory.put(
            "/api/attendance/attendance-request-cancel/77",
            {},
            format="json",
        )
        force_authenticate(request, user=self.owner_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select:
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestCancelView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn("Only waiting requests can be canceled", str(response.data))

    def test_api_revoke_allows_valid_approver_for_approved_request(self):
        attendance = self._attendance(is_validate_request=False, is_validate_request_approved=True)
        request = self.factory.put(
            "/api/attendance/attendance-request-revoke/77",
            {},
            format="json",
        )
        force_authenticate(request, user=self.manager_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select, patch(
            "horilla_api.api_views.attendance.views._can_act_on_employee",
            return_value=True,
        ), patch(
            "horilla_api.api_decorators.base.decorators.ManagerPermission.has_permission",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views._restore_request_back_to_raw",
            return_value=None,
        ), patch(
            "horilla_api.api_views.attendance.views.recompute_attendance",
            return_value=None,
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"status": "REVOKED"}),
        ):
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestRevokeView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(attendance.request_type, "revoke_request")
        self.assertFalse(attendance.is_validate_request_approved)

    def test_api_revoke_rejects_owner_even_when_permission_layer_is_green(self):
        attendance = self._attendance(is_validate_request=False, is_validate_request_approved=True)
        request = self.factory.put(
            "/api/attendance/attendance-request-revoke/77",
            {},
            format="json",
        )
        force_authenticate(request, user=self.owner_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select, patch(
            "horilla_api.api_decorators.base.decorators.ManagerPermission.has_permission",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views._can_act_on_employee",
            return_value=True,
        ):
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestRevokeView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 403)
        self.assertIn("cannot revoke your own approved request", str(response.data).lower())

    def test_api_cancel_is_owner_only_even_for_manager_actor(self):
        attendance = self._attendance()
        request = self.factory.put(
            "/api/attendance/attendance-request-cancel/77",
            {},
            format="json",
        )
        force_authenticate(request, user=self.manager_user)

        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select:
            mocked_select.return_value.get.return_value = attendance
            response = AttendanceRequestCancelView.as_view()(request, pk=attendance.id)

        self.assertEqual(response.status_code, 403)
        self.assertIn("only the requester can cancel", str(response.data).lower())

    def test_api_attachment_delete_is_owner_only_and_invokes_hard_delete(self):
        attendance = self._attendance()
        file_obj = SimpleNamespace(id=5)

        denied = self.factory.delete("/api/attendance/attendance-request-attachment/77/5")
        force_authenticate(denied, user=self.manager_user)
        with patch(
            "horilla_api.api_views.attendance.views.get_object_or_404",
            side_effect=[attendance, file_obj],
        ), patch(
            "horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.hard_delete_request_attachment"
        ) as hard_delete:
            denied_response = AttendanceRequestAttachmentDownloadView.as_view()(denied, attendance_id=attendance.id, file_id=file_obj.id)
        self.assertEqual(denied_response.status_code, 403)
        hard_delete.assert_not_called()

        allowed = self.factory.delete("/api/attendance/attendance-request-attachment/77/5")
        force_authenticate(allowed, user=self.owner_user)
        with patch(
            "horilla_api.api_views.attendance.views.get_object_or_404",
            side_effect=[attendance, file_obj],
        ), patch(
            "horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.hard_delete_request_attachment"
        ) as hard_delete:
            allowed_response = AttendanceRequestAttachmentDownloadView.as_view()(allowed, attendance_id=attendance.id, file_id=file_obj.id)
        self.assertEqual(allowed_response.status_code, 204)
        hard_delete.assert_called_once_with(attendance, file_obj)


class AttendanceRequestDirectAttachmentApiViewTests(SimpleTestCase):
    databases = {"default"}

    def setUp(self):
        self.factory = APIRequestFactory()
        self.view = AttendanceRequestView.as_view()
        self.owner_user = SimpleNamespace(
            is_authenticated=True,
            employee_get=SimpleNamespace(id=10),
            has_perm=lambda perm: False,
        )
        self.other_user = SimpleNamespace(
            is_authenticated=True,
            employee_get=SimpleNamespace(id=11),
            has_perm=lambda perm: False,
        )

    def _attendance(self, **overrides):
        employee = SimpleNamespace(id=10, employee_user_id=self.owner_user)
        defaults = {
            "id": 77,
            "pk": 77,
            "employee_id": employee,
            "employee_id_id": employee.id,
            "attendance_date": date(2026, 3, 10),
            "request_type": "update_request",
            "request_description": "Fix attendance",
            "is_validate_request": True,
            "is_validate_request_approved": False,
            "requested_data": {"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}},
            "request_attachments": SimpleNamespace(add=MagicMock(), remove=MagicMock()),
            "save": MagicMock(),
            "refresh_from_db": MagicMock(),
            "serialize": MagicMock(return_value={"attendance_clock_in": "09:00:00", "__meta": {"current_scope": "IN"}}),
        }
        defaults.update(overrides)
        return SimpleNamespace(**defaults)

    def test_api_create_request_attaches_uploaded_files_directly(self):
        attendance = self._attendance(request_type="create_request")
        upload = SimpleUploadedFile("create-proof.pdf", b"%PDF-1.4\ncreate", content_type="application/pdf")
        form = MagicMock()
        form.is_valid.return_value = True
        form.cleaned_data = {"work_type_id": None}
        form.new_instance = attendance
        form.errors = {}
        arf = SimpleNamespace(id=5, file=SimpleNamespace(url="/media/private/create-proof.pdf"))

        request = self.factory.post(
            "/api/attendance/attendance-request/",
            {"attendance_date": "2026-03-10", "request_description": "Need fix", "files": upload},
            format="multipart",
        )
        force_authenticate(request, user=self.owner_user)

        worktype_filter = MagicMock()
        worktype_filter.exists.return_value = False
        with patch("attendance.forms.NewRequestForm", return_value=form), patch(
            "horilla_api.api_views.attendance.views.WorkType.objects.filter",
            return_value=worktype_filter,
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestFile.objects.create",
            return_value=arf,
        ) as create_file, patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"id": attendance.id, "attachment_urls": ["protected-url"]}),
        ):
            response = self.view(request)

        self.assertEqual(response.status_code, 201)
        create_file.assert_called_once()
        attendance.request_attachments.add.assert_called_once_with(arf)

    def test_api_update_request_attaches_uploaded_files_directly(self):
        attendance = self._attendance(request_type="update_request")
        upload = SimpleUploadedFile("update-proof.pdf", b"%PDF-1.4\nupdate", content_type="application/pdf")
        form = MagicMock()
        form.is_valid.return_value = True
        form.cleaned_data = {"work_type_id": None}
        form.instance = SimpleNamespace(pk=attendance.id)
        form.save.return_value = attendance
        form.errors = {}
        arf = SimpleNamespace(id=8, file=SimpleNamespace(url="/media/private/update-proof.pdf"))

        request = self.factory.put(
            f"/api/attendance/attendance-request/{attendance.id}",
            {"request_description": "Edited reason", "files": upload},
            format="multipart",
        )
        force_authenticate(request, user=self.owner_user)

        worktype_filter = MagicMock()
        worktype_filter.exists.return_value = False
        with patch("horilla_api.api_views.attendance.views.Attendance.objects.select_for_update") as mocked_select, patch(
            "attendance.forms.AttendanceRequestForm",
            return_value=form,
        ), patch(
            "horilla_api.api_views.attendance.views.WorkType.objects.filter",
            return_value=worktype_filter,
        ), patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestFile.objects.create",
            return_value=arf,
        ) as create_file, patch(
            "horilla_api.api_views.attendance.views.AttendanceRequestSerializer",
            return_value=SimpleNamespace(data={"id": attendance.id, "attachment_urls": ["protected-url"]}),
        ):
            mocked_select.return_value.get.return_value = attendance
            response = self.view(request, pk=attendance.id)

        self.assertEqual(response.status_code, 200)
        create_file.assert_called_once()
        attendance.request_attachments.add.assert_called_once_with(arf)



class WorkModeRequestPermissionApiRegressionTests(SimpleTestCase):
    databases = {"default"}
    def setUp(self):
        self.factory = APIRequestFactory()
        self.owner_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=10), has_perm=lambda perm: False, is_superuser=False)
        self.manager_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=20), has_perm=lambda perm: False, is_superuser=False)

    def _work_request(self, **overrides):
        employee = SimpleNamespace(id=10, employee_user_id=self.owner_user)
        current_version = SimpleNamespace(status=WorkModeRequestDocumentStatus.SUBMITTED)
        defaults = {
            "id": 55,
            "pk": 55,
            "employee_id": employee,
            "employee_id_id": employee.id,
            "status": WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            "mode": AttendanceWorkMode.ON_DUTY,
            "reason": "Need field visit",
            "document_status": WorkModeRequestDocumentStatus.SUBMITTED,
            "current_document_version": current_version,
            "resolve_current_document_version": lambda: current_version,
            "effective_document_status": lambda: WorkModeRequestDocumentStatus.SUBMITTED,
            "sync_legacy_files_from_current_version": lambda: None,
            "sync_root_document_fields_from_current_version": lambda: None,
            "save": MagicMock(),
            "start_date": date(2026, 3, 14),
            "end_date": date(2026, 3, 14),
        }
        defaults.update(overrides)
        return SimpleNamespace(**defaults)

    def test_manager_cannot_cancel_employee_work_type_request(self):
        req = self._work_request(status=WorkModeRequestStatus.PENDING)
        request = self.factory.put('/api/attendance/work-mode-request-cancel/55', {}, format='json')
        force_authenticate(request, user=self.manager_user)

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', return_value=req), \
             patch('horilla_api.api_views.attendance.views._request_actor_employee', return_value=self.manager_user.employee_get):
            response = WorkModeRequestCancelView.as_view()(request, pk=req.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn('permission to cancel this request', str(response.data).lower())

    def test_owner_cannot_revoke_own_approved_work_type_request(self):
        req = self._work_request(status=WorkModeRequestStatus.APPROVED)
        request = self.factory.put('/api/attendance/work-mode-request-revoke/55', {'remark': 'undo'}, format='json')
        force_authenticate(request, user=self.owner_user)

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', return_value=req), \
             patch('horilla_api.api_views.attendance.views._request_actor_employee', return_value=self.owner_user.employee_get):
            response = WorkModeRequestDocumentActionView.as_view()(request, pk=req.id, action='revoke')

        self.assertEqual(response.status_code, 400)
        self.assertIn('permission to revoke this request', str(response.data).lower())

    def test_unrelated_manager_cannot_approve_work_type_request(self):
        req = self._work_request(status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)
        request = self.factory.put('/api/attendance/work-mode-request-approve/55', {}, format='json')
        force_authenticate(request, user=self.manager_user)

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', return_value=req), \
             patch('horilla_api.api_views.attendance.views._request_actor_employee', return_value=self.manager_user.employee_get), \
             patch('attendance.services.work_type_request_permissions.get_subordinate_employee_ids', return_value=[]):
            response = WorkModeRequestApproveView.as_view()(request, pk=req.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn('permission to approve this request', str(response.data).lower())

    def test_self_approval_is_rejected_for_work_type_request(self):
        req = self._work_request(status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)
        request = self.factory.put('/api/attendance/work-mode-request-approve/55', {}, format='json')
        force_authenticate(request, user=self.owner_user)

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', return_value=req), \
             patch('horilla_api.api_views.attendance.views._request_actor_employee', return_value=self.owner_user.employee_get):
            response = WorkModeRequestApproveView.as_view()(request, pk=req.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn('permission to approve this request', str(response.data).lower())

    def test_owner_cannot_update_approved_work_type_request(self):
        req = self._work_request(status=WorkModeRequestStatus.APPROVED, mode=AttendanceWorkMode.WFA)
        request = self.factory.put('/api/attendance/work-mode-request/55', {'reason': 'edited note'}, format='json')
        force_authenticate(request, user=self.owner_user)

        with patch('horilla_api.api_views.attendance.views.get_object_or_404', return_value=req), \
             patch.object(WorkModeRequestView, '_collect_uploaded_files', return_value=[]), \
             patch('horilla_api.api_views.attendance.views._request_actor_employee', return_value=self.owner_user.employee_get):
            response = WorkModeRequestView.as_view()(request, pk=req.id)

        self.assertEqual(response.status_code, 400)
        self.assertIn('can no longer be updated', str(response.data).lower())


class WorkModeAttachmentSecurityRegressionTests(SimpleTestCase):
    def setUp(self):
        self.factory = RequestFactory()
        self.owner_user = SimpleNamespace(is_authenticated=True, is_active=True, is_superuser=False, employee_get=SimpleNamespace(is_active=True))

    def _req_and_file(self):
        req = SimpleNamespace(id=91)
        file_obj = SimpleNamespace(id=7, file=SimpleNamespace(open=MagicMock(return_value=BytesIO(b'data')), name='media/private/proof.pdf'))
        return req, file_obj

    def test_attachment_download_rejects_when_authorization_fails_even_with_valid_token(self):
        req, file_obj = self._req_and_file()
        request = self.factory.get('/attendance/work-mode/91/attachment/7?token=valid')
        request.user = self.owner_user
        request.session = {}

        with patch('attendance.views.work_type_requests.get_object_or_404', side_effect=lambda model, **kwargs: req if getattr(model, '__name__', '') == 'WorkModeRequest' else file_obj), \
             patch('attendance.views.work_type_requests.attachment_belongs_to_request', return_value=True), \
             patch('attendance.views.work_type_requests.request_can_view_attachment', return_value=False), \
             patch('attendance.views.work_type_requests.verify_attachment_token', return_value=True):
            response = work_type_request_attachment_download(request, req.id, file_obj.id)

        self.assertEqual(response.status_code, 403)
        self.assertIn('Not allowed', response.content.decode())

    def test_old_attachment_token_cannot_access_replaced_current_version(self):
        req, file_obj = self._req_and_file()
        request = self.factory.get('/attendance/work-mode/91/attachment/7?token=stale')
        request.user = self.owner_user
        request.session = {}

        with patch('attendance.views.work_type_requests.get_object_or_404', side_effect=lambda model, **kwargs: req if getattr(model, '__name__', '') == 'WorkModeRequest' else file_obj), \
             patch('attendance.views.work_type_requests.attachment_belongs_to_request', return_value=True), \
             patch('attendance.views.work_type_requests.request_can_view_attachment', return_value=True), \
             patch('attendance.views.work_type_requests.verify_attachment_token', return_value=False):
            response = work_type_request_attachment_download(request, req.id, file_obj.id)

        self.assertEqual(response.status_code, 403)
        self.assertIn('Invalid or expired attachment token', response.content.decode())

    def test_non_current_document_version_cannot_be_used_as_current_download_target(self):
        req, file_obj = self._req_and_file()
        request = self.factory.get('/attendance/work-mode/91/attachment/7?token=valid')
        request.user = self.owner_user
        request.session = {}

        with patch('attendance.views.work_type_requests.get_object_or_404', side_effect=lambda model, **kwargs: req if getattr(model, '__name__', '') == 'WorkModeRequest' else file_obj), \
             patch('attendance.views.work_type_requests.attachment_belongs_to_request', return_value=False), \
             patch('attendance.views.work_type_requests.request_can_view_attachment', return_value=True), \
             patch('attendance.views.work_type_requests.verify_attachment_token', return_value=True):
            with self.assertRaises(Http404):
                work_type_request_attachment_download(request, req.id, file_obj.id)
