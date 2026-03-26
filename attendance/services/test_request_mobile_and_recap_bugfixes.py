from __future__ import annotations

from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import SimpleTestCase
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


class AttachmentValidationRegressionTests(SimpleTestCase):
    def test_accepts_jpg_with_image_jpg_mime(self):
        uploaded = SimpleUploadedFile("sample.jpg", b"jpg", content_type="image/jpg")
        validate_uploaded_files([uploaded])

    def test_accepts_jpg_with_octet_stream_when_extension_is_valid(self):
        uploaded = SimpleUploadedFile("sample.jpg", b"jpg", content_type="application/octet-stream")
        validate_uploaded_files([uploaded])


class MonthlyRecapIncompleteAttendanceRegressionTests(SimpleTestCase):
    def test_incomplete_missing_checkout_does_not_trust_persisted_zero_minutes(self):
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
        )
        self.assertIsNone(row)

    def test_incomplete_missing_checkin_does_not_trust_persisted_zero_minutes(self):
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
        )
        self.assertIsNone(row)
