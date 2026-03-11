from io import BytesIO
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
