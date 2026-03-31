from __future__ import annotations

from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import SimpleTestCase
from django.utils import timezone
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.services.attachment_validation import validate_uploaded_files
from attendance.services.monthly_recap import _canonical_row_from_attendance
from horilla_api.api_serializers.attendance.serializers import WorkModeRequestSerializer
from horilla_api.api_views.attendance.views import WorkModeRequestView
from attendance.models import AttendanceWorkMode, WorkModeRequestScope


class WorkModeRequestBackendSelfBindingTests(SimpleTestCase):
    databases = {"default"}

    def test_serializer_employee_id_not_required(self):
        serializer = WorkModeRequestSerializer(context={"request": None})
        self.assertFalse(serializer.fields["employee_id"].required)

    def test_view_injects_actor_employee_id_before_validation(self):
        captured = {}

        class FakeSerializer:
            def __init__(self, *args, **kwargs):
                candidate = kwargs.get("data") if kwargs.get("data") is not None else (args[0] if args else None)
                if isinstance(candidate, dict):
                    captured["data"] = candidate
                self.validated_data = {
                    "mode": AttendanceWorkMode.WFA,
                    "scope": WorkModeRequestScope.IN,
                    "start_date": date(2026, 3, 26),
                    "end_date": date(2026, 3, 26),
                    "reason": "Need WFA",
                }

            def is_valid(self):
                return True

            @property
            def errors(self):
                return {}

            @property
            def data(self):
                return {"id": 1}

        factory = APIRequestFactory()
        user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=77))
        request = factory.post(
            "/api/attendance/work-type-request/",
            {
                "mode": "wfa",
                "scope": "in",
                "start_date": "2026-03-26",
                "end_date": "2026-03-26",
                "reason": "Need WFA",
            },
            format="json",
        )
        force_authenticate(request, user=user)

        with patch.object(WorkModeRequestView, "serializer_class", FakeSerializer), \
             patch.object(WorkModeRequestView, "_collect_uploaded_files", return_value=[]), \
             patch("horilla_api.api_views.attendance.views.WorkModeRequestActions.create_request", return_value=SimpleNamespace(id=1)):
            response = WorkModeRequestView.as_view()(request)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(captured["data"]["employee_id"], 77)

    def test_view_accepts_multipart_create_with_uploaded_file_without_deepcopy_crash(self):
        captured = {}

        class FakeSerializer:
            def __init__(self, *args, **kwargs):
                candidate = kwargs.get("data") if kwargs.get("data") is not None else (args[0] if args else None)
                if isinstance(candidate, dict):
                    captured["data"] = candidate
                self.validated_data = {
                    "mode": AttendanceWorkMode.WFA,
                    "scope": WorkModeRequestScope.IN,
                    "start_date": date(2026, 3, 26),
                    "end_date": date(2026, 3, 26),
                    "reason": "Need WFA",
                    "duty_destination_location": "HQ",
                }

            def is_valid(self):
                return True

            @property
            def errors(self):
                return {}

            @property
            def data(self):
                return {"id": 1}

        factory = APIRequestFactory()
        user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=77))
        upload = SimpleUploadedFile("proof.jpg", b"jpg", content_type="image/jpeg")
        request = factory.post(
            "/api/attendance/work-type-request/",
            {
                "mode": "wfa",
                "scope": "in",
                "start_date": "2026-03-26",
                "end_date": "2026-03-26",
                "reason": "Need WFA",
                "file": upload,
            },
            format="multipart",
        )
        force_authenticate(request, user=user)

        with patch.object(WorkModeRequestView, "serializer_class", FakeSerializer), \
             patch("horilla_api.api_views.attendance.views.WorkModeRequestActions.create_request", return_value=SimpleNamespace(id=1)) as create_request:
            response = WorkModeRequestView.as_view()(request)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(captured["data"]["employee_id"], 77)
        self.assertEqual(captured["data"]["mode"], "wfa")
        self.assertNotIn("file", captured["data"])
        self.assertEqual(len(create_request.call_args.kwargs["uploaded_files"]), 1)

    def test_view_accepts_multipart_update_with_uploaded_file_without_deepcopy_crash(self):
        factory = APIRequestFactory()
        user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=77))
        upload = SimpleUploadedFile("proof.jpg", b"jpg", content_type="image/jpeg")
        request = factory.put(
            "/api/attendance/work-type-request/5",
            {
                "reason": "Updated note",
                "remark": "Need review",
                "duty_destination_location": "Client Site",
                "file": upload,
            },
            format="multipart",
        )
        force_authenticate(request, user=user)

        target = SimpleNamespace(id=5)
        with patch("horilla_api.api_views.attendance.views.get_object_or_404", return_value=target), \
             patch("horilla_api.api_views.attendance.views.WorkModeRequestActions.update_request") as update_request, \
             patch.object(WorkModeRequestView, "serializer_class", lambda *args, **kwargs: SimpleNamespace(data={"id": 5})):
            response = WorkModeRequestView.as_view()(request, pk=5)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(update_request.call_args.kwargs["reason"], "Updated note")
        self.assertEqual(update_request.call_args.kwargs["remark"], "Need review")
        self.assertEqual(update_request.call_args.kwargs["duty_destination_location"], "Client Site")
        self.assertEqual(len(update_request.call_args.kwargs["uploaded_files"]), 1)


class AttachmentValidationRegressionTests(SimpleTestCase):
    def test_accepts_jpg_with_image_jpg_mime(self):
        uploaded = SimpleUploadedFile("sample.jpg", b"jpg", content_type="image/jpg")
        validate_uploaded_files([uploaded])

    def test_accepts_jpg_with_octet_stream_when_extension_is_valid(self):
        uploaded = SimpleUploadedFile("sample.jpg", b"jpg", content_type="application/octet-stream")
        validate_uploaded_files([uploaded])


class MonthlyRecapIncompleteAttendanceRegressionTests(SimpleTestCase):
    def _dt(self, hour: int, minute: int) -> datetime:
        return timezone.make_aware(datetime(2026, 3, 26, hour, minute), timezone.get_current_timezone())

    def test_incomplete_missing_checkout_uses_canonical_missing_metrics(self):
        best_att = SimpleNamespace(
            reconciliation_note="Missing Check Out",
            reconciliation_source="Normal",
            attendance_clock_in_date=date(2026, 3, 26),
            attendance_clock_in=time(8, 0),
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            late_minutes=0,
            early_out_minutes=0,
            work_type_id=None,
        )
        row = _canonical_row_from_attendance(
            best_att=best_att,
            attendance_date=date(2026, 3, 26),
            row_no=1,
            shift_information="09:00 - 18:00",
            language="en",
            is_off=False,
            shift_start_dt=self._dt(9, 0),
            shift_end_dt=self._dt(18, 0),
            minimum_hour="08:00",
        )
        self.assertIsNotNone(row)
        self.assertEqual(row.check_in, "08:00")
        self.assertEqual(row.check_out, "-")
        self.assertIn("Missing Check Out", row.note)
        self.assertEqual(row.late_minutes, 0)
        self.assertEqual(row.early_out_minutes, 240)
        self.assertEqual(row.late, "00:00")
        self.assertEqual(row.early_out, "04:00")

    def test_incomplete_missing_checkin_uses_canonical_missing_metrics(self):
        best_att = SimpleNamespace(
            reconciliation_note="Missing Check In",
            reconciliation_source="Normal",
            attendance_clock_in_date=None,
            attendance_clock_in=None,
            attendance_clock_out_date=date(2026, 3, 26),
            attendance_clock_out=time(18, 0),
            late_minutes=0,
            early_out_minutes=0,
            work_type_id=None,
        )
        row = _canonical_row_from_attendance(
            best_att=best_att,
            attendance_date=date(2026, 3, 26),
            row_no=1,
            shift_information="09:00 - 18:00",
            language="en",
            is_off=False,
            shift_start_dt=self._dt(9, 0),
            shift_end_dt=self._dt(18, 0),
            minimum_hour="08:00",
        )
        self.assertIsNotNone(row)
        self.assertEqual(row.check_in, "-")
        self.assertEqual(row.check_out, "18:00")
        self.assertIn("Missing Check In", row.note)
        self.assertEqual(row.late_minutes, 240)
        self.assertEqual(row.early_out_minutes, 0)
        self.assertEqual(row.late, "04:00")
        self.assertEqual(row.early_out, "00:00")
