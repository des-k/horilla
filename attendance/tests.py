from io import BytesIO
import datetime as dt
import os
import unittest

from django.core.exceptions import ValidationError
from django.core.files.uploadedfile import SimpleUploadedFile

from types import SimpleNamespace

from attendance.services.image_compression import (
    MAX_IMAGE_DIMENSION,
    compress_attendance_image,
    compress_model_image_field,
)
from attendance.services.punching_history import (
    _clone_uploaded_file,
    canonical_punch_image_reference,
)

try:
    from PIL import Image
except Exception:  # pragma: no cover
    Image = None


@unittest.skipIf(Image is None, "Pillow is required")
class AttendanceImageCompressionTests(unittest.TestCase):
    def _make_image_bytes(self, size=(2400, 1800), fmt="JPEG", mode="RGB", color=None):
        color = color or ((255, 0, 0, 128) if "A" in mode else (255, 0, 0))
        image = Image.new(mode, size, color)
        output = BytesIO()
        save_kwargs = {}
        if fmt == "JPEG":
            save_kwargs["quality"] = 95
        image.save(output, format=fmt, **save_kwargs)
        return output.getvalue()

    def test_large_jpeg_is_resized_and_saved_as_jpeg(self):
        uploaded = SimpleUploadedFile("selfie.jpg", self._make_image_bytes(size=(3200, 2400), fmt="JPEG"), content_type="image/jpeg")
        compressed = compress_attendance_image(uploaded)
        self.assertTrue(compressed.name.endswith(".jpg"))
        image = Image.open(BytesIO(compressed.read()))
        self.assertLessEqual(max(image.size), MAX_IMAGE_DIMENSION)

    def test_transparent_png_stays_png(self):
        uploaded = SimpleUploadedFile("selfie.png", self._make_image_bytes(size=(1200, 1200), fmt="PNG", mode="RGBA"), content_type="image/png")
        compressed = compress_attendance_image(uploaded)
        self.assertTrue(compressed.name.endswith(".png"))
        image = Image.open(BytesIO(compressed.read()))
        self.assertEqual(image.format, "PNG")

    def test_small_opaque_png_does_not_silently_become_larger_jpeg(self):
        uploaded_bytes = self._make_image_bytes(size=(64, 64), fmt="PNG", mode="RGB")
        uploaded = SimpleUploadedFile("selfie.png", uploaded_bytes, content_type="image/png")
        compressed = compress_attendance_image(uploaded)
        self.assertTrue(compressed.name.endswith(".png"))
        self.assertLessEqual(len(compressed.read()), len(uploaded_bytes))

    def test_large_photo_like_opaque_png_can_switch_to_jpeg_when_materially_smaller(self):
        random_bytes = os.urandom(512 * 512 * 3)
        image = Image.frombytes("RGB", (512, 512), random_bytes)
        output = BytesIO()
        image.save(output, format="PNG")
        uploaded = SimpleUploadedFile("photo.png", output.getvalue(), content_type="image/png")
        compressed = compress_attendance_image(uploaded)
        self.assertTrue(compressed.name.endswith((".jpg", ".png")))
        if compressed.name.endswith(".jpg"):
            self.assertLess(len(compressed.read()), len(output.getvalue()))

    def test_cmyk_jpeg_is_normalized_to_rgb_jpeg(self):
        image = Image.new("CMYK", (900, 600), (0, 128, 128, 0))
        output = BytesIO()
        image.save(output, format="JPEG", quality=95)
        uploaded = SimpleUploadedFile("cmyk.jpg", output.getvalue(), content_type="image/jpeg")
        compressed = compress_attendance_image(uploaded)
        normalized = Image.open(BytesIO(compressed.read()))
        self.assertEqual(normalized.format, "JPEG")
        self.assertEqual(normalized.mode, "RGB")

    def test_invalid_image_raises_validation_error(self):
        uploaded = SimpleUploadedFile("broken.jpg", b"not-an-image", content_type="image/jpeg")
        with self.assertRaises(ValidationError):
            compress_attendance_image(uploaded)

    def test_clone_uploaded_file_reads_from_start_even_if_stream_was_advanced(self):
        uploaded = SimpleUploadedFile("selfie.jpg", self._make_image_bytes(size=(800, 600), fmt="JPEG"), content_type="image/jpeg")
        uploaded.read(10)
        cloned = _clone_uploaded_file(uploaded)
        self.assertIsNotNone(cloned)
        self.assertGreater(len(cloned.read()), 10)

    def test_existing_storage_string_is_not_recompressed(self):
        instance = SimpleNamespace(photo="attendance/photo.jpg")
        changed = compress_model_image_field(instance, "photo")
        self.assertFalse(changed)
        self.assertEqual(instance.photo, "attendance/photo.jpg")

    def test_canonical_punch_reference_prefers_saved_punch_photo(self):
        uploaded = SimpleUploadedFile("fresh.jpg", self._make_image_bytes(size=(640, 480), fmt="JPEG"), content_type="image/jpeg")
        punch = SimpleNamespace(photo=SimpleNamespace(name="attendance/stored.jpg", _committed=True))
        chosen = canonical_punch_image_reference(punch=punch, uploaded=uploaded)
        self.assertEqual(getattr(chosen, "name", None), "attendance/stored.jpg")

    def test_canonical_punch_reference_falls_back_to_uploaded_file(self):
        uploaded = SimpleUploadedFile("fresh.jpg", self._make_image_bytes(size=(640, 480), fmt="JPEG"), content_type="image/jpeg")
        chosen = canonical_punch_image_reference(punch=None, uploaded=uploaded)
        self.assertIs(chosen, uploaded)

from unittest.mock import Mock, patch

from attendance.models import Attendance


class AttendanceSaveUpdateFieldsTests(unittest.TestCase):
    def test_request_restore_snapshot_only_save_skips_recalculation(self):
        attendance = Attendance(request_restore_snapshot={"in": {"dummy": True}})

        with patch("attendance.models.compress_model_image_field") as compress_mock, \
             patch("attendance.models.Attendance.update_attendance_overtime") as update_ot_mock, \
             patch("attendance.models.Attendance.adjust_minimum_hour") as adjust_min_mock, \
             patch("attendance.models.Attendance.handle_overtime_conditions") as handle_ot_mock, \
             patch.object(__import__("attendance.models", fromlist=["EmployeeShiftDay"]).EmployeeShiftDay.objects, "get", create=True) as shift_day_get_mock, \
             patch("attendance.models.HorillaModel.save", autospec=True, return_value=None) as super_save_mock:
            attendance.save(update_fields=["request_restore_snapshot"])

        compress_mock.assert_not_called()
        update_ot_mock.assert_not_called()
        adjust_min_mock.assert_not_called()
        handle_ot_mock.assert_not_called()
        shift_day_get_mock.assert_not_called()
        super_save_mock.assert_called_once()

    def test_other_partial_update_still_uses_existing_save_flow(self):
        attendance = Attendance()
        attendance.attendance_date = dt.date(2026, 3, 14)
        attendance.attendance_overtime_approve = False
        attendance.approved_overtime_second = 0
        attendance.overtime_second = 0
        attendance.is_validate_request = False
        attendance.is_presensi_only = False
        overtime_account = Mock()
        overtime_account.overtime_second = 0
        employee_overtime_qs = Mock()
        employee_overtime_qs.first.return_value = overtime_account
        employee = Mock()
        employee.employee_overtime.filter.return_value = employee_overtime_qs
        attendance.employee_id_id = 1
        attendance._state.fields_cache["employee_id"] = employee

        with patch("attendance.models.compress_model_image_field") as compress_mock, \
             patch("attendance.models.Attendance.update_attendance_overtime") as update_ot_mock, \
             patch("attendance.models.Attendance.adjust_minimum_hour") as adjust_min_mock, \
             patch("attendance.models.Attendance.handle_overtime_conditions") as handle_ot_mock, \
             patch.object(__import__("attendance.models", fromlist=["EmployeeShiftDay"]).EmployeeShiftDay.objects, "get", create=True, return_value=__import__("attendance.models", fromlist=["EmployeeShiftDay"]).EmployeeShiftDay(day="saturday")) as shift_day_get_mock, \
             patch("attendance.models.Attendance.update_ot") as update_ot_account_mock, \
             patch("attendance.models.HorillaModel.save", autospec=True, return_value=None) as super_save_mock:
            attendance.save(update_fields=["request_description"])

        compress_mock.assert_any_call(attendance, "attendance_clock_in_image")
        compress_mock.assert_any_call(attendance, "attendance_clock_out_image")
        update_ot_mock.assert_called_once()
        adjust_min_mock.assert_called_once()
        handle_ot_mock.assert_called_once()
        overtime_account.save.assert_called_once()
        super_save_mock.assert_called_once()
