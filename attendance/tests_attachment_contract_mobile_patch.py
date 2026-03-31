from io import BytesIO
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from django.urls import reverse
from rest_framework.test import APIRequestFactory, force_authenticate

from horilla_api.api_views.attendance.views import (
    AttendanceRequestAttachmentDownloadView,
    WorkModeRequestAttachmentAccessView,
)


class AttachmentContractUrlTests(SimpleTestCase):
    def test_attendance_attachment_view_and_download_urls_exist(self):
        self.assertEqual(
            reverse("api-attendance-request-attachment-view", kwargs={"attendance_id": 1, "file_id": 2}),
            "/api/attendance/attendance-request-attachments/1/2/view",
        )
        self.assertEqual(
            reverse("api-attendance-request-attachment-download-v2", kwargs={"attendance_id": 1, "file_id": 2}),
            "/api/attendance/attendance-request-attachments/1/2/download",
        )

    def test_work_mode_attachment_view_and_download_urls_exist(self):
        self.assertEqual(
            reverse("api-work-mode-request-attachment-view", kwargs={"pk": 1, "file_id": 2}),
            "/api/attendance/work-mode-request-attachments/1/2/view",
        )
        self.assertEqual(
            reverse("api-work-mode-request-attachment-download", kwargs={"pk": 1, "file_id": 2}),
            "/api/attendance/work-mode-request-attachments/1/2/download",
        )


class AttachmentAccessResponseTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.user = SimpleNamespace(is_authenticated=True, is_superuser=False)

    def test_attendance_view_endpoint_streams_pdf_inline(self):
        request = self.factory.get("/api/attendance/attendance-request-attachments/1/2/view?token=ok")
        force_authenticate(request, user=self.user)

        attendance = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(
            id=2,
            file=SimpleNamespace(
                name="proof.pdf",
                open=lambda mode='rb': BytesIO(b"%PDF-1.4"),
            ),
        )

        with patch("horilla_api.api_views.attendance.views.get_object_or_404", side_effect=[attendance, file_obj]), patch(
            "horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.attendance_request_can_view_attachment",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.verify_attendance_attachment_token",
            return_value=True,
        ):
            response = AttendanceRequestAttachmentDownloadView.as_view()(request, attendance_id=1, file_id=2, disposition="view")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response["Content-Type"], "application/pdf")
        self.assertIn("inline", response["Content-Disposition"].lower())
        self.assertIn("private", response["Cache-Control"].lower())


    def test_attendance_view_endpoint_allows_valid_token_without_authentication(self):
        request = self.factory.get("/api/attendance/attendance-request-attachments/1/2/view?token=ok")

        attendance = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(
            id=2,
            file=SimpleNamespace(
                name="proof.pdf",
                open=lambda mode='rb': BytesIO(b"%PDF-1.4"),
            ),
        )

        with patch("horilla_api.api_views.attendance.views.get_object_or_404", side_effect=[attendance, file_obj]), patch(
            "horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.attendance_request_can_view_attachment",
            return_value=False,
        ), patch(
            "horilla_api.api_views.attendance.views.verify_attendance_attachment_token",
            return_value=True,
        ):
            response = AttendanceRequestAttachmentDownloadView.as_view()(request, attendance_id=1, file_id=2, disposition="view")

        self.assertEqual(response.status_code, 200)

    def test_attendance_download_endpoint_forces_attachment_for_docx(self):
        request = self.factory.get("/api/attendance/attendance-request-attachments/1/2/download?token=ok")
        force_authenticate(request, user=self.user)

        attendance = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(
            id=2,
            file=SimpleNamespace(
                name="letter.docx",
                open=lambda mode='rb': BytesIO(b"docx"),
            ),
        )

        with patch("horilla_api.api_views.attendance.views.get_object_or_404", side_effect=[attendance, file_obj]), patch(
            "horilla_api.api_views.attendance.views.attendance_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.attendance_request_can_view_attachment",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.verify_attendance_attachment_token",
            return_value=True,
        ):
            response = AttendanceRequestAttachmentDownloadView.as_view()(request, attendance_id=1, file_id=2, disposition="download")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(
            response["Content-Type"],
            "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
        )
        self.assertIn("attachment", response["Content-Disposition"].lower())


    def test_work_mode_attachment_view_allows_valid_token_without_authentication(self):
        request = self.factory.get("/api/attendance/work-mode-request-attachments/1/2/view?token=ok")

        req = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(
            id=2,
            file=SimpleNamespace(
                name="proof.pdf",
                open=lambda mode='rb': BytesIO(b"%PDF-1.4"),
            ),
        )

        with patch("horilla_api.api_views.attendance.views.get_object_or_404", side_effect=[req, file_obj]), patch(
            "horilla_api.api_views.attendance.views.work_mode_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.work_mode_request_can_view_attachment",
            return_value=False,
        ), patch(
            "horilla_api.api_views.attendance.views.verify_work_mode_attachment_token",
            return_value=True,
        ):
            response = WorkModeRequestAttachmentAccessView.as_view()(request, pk=1, file_id=2, disposition="view")

        self.assertEqual(response.status_code, 200)

    def test_work_mode_attachment_requires_permission(self):
        request = self.factory.get("/api/attendance/work-mode-request-attachments/1/2/view?token=ok")
        force_authenticate(request, user=self.user)

        req = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(
            id=2,
            file=SimpleNamespace(name="proof.pdf", open=lambda mode='rb': BytesIO(b"%PDF-1.4")),
        )

        with patch("horilla_api.api_views.attendance.views.get_object_or_404", side_effect=[req, file_obj]), patch(
            "horilla_api.api_views.attendance.views.work_mode_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.work_mode_request_can_view_attachment",
            return_value=False,
        ), patch(
            "horilla_api.api_views.attendance.views.verify_work_mode_attachment_token",
            return_value=True,
        ):
            response = WorkModeRequestAttachmentAccessView.as_view()(request, pk=1, file_id=2, disposition="view")

        self.assertEqual(response.status_code, 200)

    def test_work_mode_attachment_view_streams_inline_for_authorized_user(self):
        request = self.factory.get("/api/attendance/work-mode-request-attachments/1/2/view?token=ok")
        force_authenticate(request, user=self.user)

        req = SimpleNamespace(id=1)
        file_obj = SimpleNamespace(
            id=2,
            file=SimpleNamespace(
                name="proof.pdf",
                open=lambda mode='rb': BytesIO(b"%PDF-1.4"),
            ),
        )

        with patch("horilla_api.api_views.attendance.views.get_object_or_404", side_effect=[req, file_obj]), patch(
            "horilla_api.api_views.attendance.views.work_mode_attachment_belongs_to_request",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.work_mode_request_can_view_attachment",
            return_value=True,
        ), patch(
            "horilla_api.api_views.attendance.views.verify_work_mode_attachment_token",
            return_value=True,
        ):
            response = WorkModeRequestAttachmentAccessView.as_view()(request, pk=1, file_id=2, disposition="view")

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response["Content-Type"], "application/pdf")
        self.assertIn("inline", response["Content-Disposition"].lower())
