from __future__ import annotations

import os
from io import BytesIO
from pathlib import Path

from django.core.exceptions import ValidationError
from django.core.files.base import ContentFile
from django.utils.translation import gettext_lazy as _

from PIL import Image, ImageOps, UnidentifiedImageError

try:
    RESAMPLE = Image.Resampling.LANCZOS
except AttributeError:  # Pillow < 9.1
    RESAMPLE = Image.LANCZOS

MAX_IMAGE_DIMENSION = 1600
JPEG_QUALITY = 78
SMALL_FILE_THRESHOLD = 256 * 1024
PNG_TO_JPEG_SAVINGS_RATIO = 0.85


def _extract_error_message(error: ValidationError) -> str:
    if hasattr(error, "message_dict") and error.message_dict:
        for value in error.message_dict.values():
            if isinstance(value, (list, tuple)) and value:
                return str(value[0])
            return str(value)
    if hasattr(error, "messages") and error.messages:
        return str(error.messages[0])
    return str(error)


def _safe_basename(filename: str | None, fallback: str = "attendance-photo") -> str:
    stem = Path(filename or fallback).stem.strip() or fallback
    return os.path.basename(stem)


def _read_file_bytes(file_obj) -> bytes:
    if file_obj is None:
        return b""

    start_pos = None
    if hasattr(file_obj, "tell"):
        try:
            start_pos = file_obj.tell()
        except Exception:
            start_pos = None

    if hasattr(file_obj, "seek"):
        try:
            file_obj.seek(0)
        except Exception:
            pass

    data = file_obj.read() if hasattr(file_obj, "read") else b""

    if start_pos is not None and hasattr(file_obj, "seek"):
        try:
            file_obj.seek(start_pos)
        except Exception:
            pass

    return data or b""


def _has_transparency(image: Image.Image) -> bool:
    if image.mode in ("RGBA", "LA"):
        alpha = image.getchannel("A")
        return alpha.getextrema()[0] < 255

    if image.mode == "P":
        transparency = image.info.get("transparency")
        if transparency is not None:
            return True
        try:
            return "transparency" in image.palette.info
        except Exception:
            return False

    return False


def _should_keep_original(
    *,
    original_bytes: bytes,
    candidate_bytes: bytes,
    original_format: str,
    output_format: str,
    original_mode: str,
    resized: bool,
    orientation_fixed: bool,
) -> bool:
    if resized or orientation_fixed:
        return False
    if len(original_bytes) > SMALL_FILE_THRESHOLD:
        return False
    if output_format == "JPEG":
        if original_format not in {"JPEG", "JPG"}:
            return False
        if original_mode not in {"RGB", "L"}:
            return False
    if output_format == "PNG" and original_format != "PNG":
        return False
    return len(candidate_bytes) >= len(original_bytes)


def _png_bytes(image: Image.Image, *, preserve_alpha: bool) -> bytes:
    output = BytesIO()
    if preserve_alpha:
        save_image = image if image.mode in ("RGBA", "LA", "P") else image.convert("RGBA")
    else:
        save_image = image if image.mode in ("RGB", "L", "P") else image.convert("RGB")
    save_image.save(output, format="PNG", optimize=True)
    return output.getvalue()


def _jpeg_bytes(image: Image.Image) -> bytes:
    output = BytesIO()
    save_image = image if image.mode == "RGB" else image.convert("RGB")
    save_image.save(
        output,
        format="JPEG",
        quality=JPEG_QUALITY,
        optimize=True,
        progressive=True,
    )
    return output.getvalue()


def _choose_output_for_opaque_png(
    *,
    normalized: Image.Image,
    original_bytes: bytes,
    resized: bool,
    orientation_fixed: bool,
):
    png_bytes = _png_bytes(normalized, preserve_alpha=False)
    jpeg_bytes = _jpeg_bytes(normalized)

    # Only switch an opaque PNG to JPEG when the JPEG artifact is materially
    # smaller. Otherwise keep PNG to avoid needless format changes and lossy
    # degradation for already-efficient PNG inputs.
    png_baseline = min(len(original_bytes), len(png_bytes)) if original_bytes else len(png_bytes)
    if jpeg_bytes and len(jpeg_bytes) <= int(png_baseline * PNG_TO_JPEG_SAVINGS_RATIO):
        return jpeg_bytes, "JPEG", ".jpg"

    if _should_keep_original(
        original_bytes=original_bytes,
        candidate_bytes=png_bytes,
        original_format="PNG",
        output_format="PNG",
        original_mode=normalized.mode,
        resized=resized,
        orientation_fixed=orientation_fixed,
    ):
        return original_bytes, "PNG", ".png"

    return png_bytes, "PNG", ".png"


def compress_attendance_image(uploaded, *, fallback_name: str = "attendance-photo.jpg"):
    if not uploaded:
        return uploaded

    raw_bytes = _read_file_bytes(uploaded)
    if not raw_bytes:
        raise ValidationError(_("Uploaded image is empty or unreadable."))

    try:
        with Image.open(BytesIO(raw_bytes)) as original:
            original.load()
            original_format = (original.format or "").upper()
            original_orientation = None
            try:
                original_orientation = original.getexif().get(274)
            except Exception:
                original_orientation = None

            normalized = ImageOps.exif_transpose(original)
            orientation_fixed = original_orientation not in (None, 1)
            original_size = original.size

            if max(normalized.size) > MAX_IMAGE_DIMENSION:
                normalized.thumbnail((MAX_IMAGE_DIMENSION, MAX_IMAGE_DIMENSION), RESAMPLE)
            resized = normalized.size != original_size

            transparent = _has_transparency(normalized)
            base_name = _safe_basename(getattr(uploaded, "name", None), fallback="attendance-photo")

            if transparent:
                candidate_bytes = _png_bytes(normalized, preserve_alpha=True)
                output_format = "PNG"
                extension = ".png"
            elif original_format == "PNG":
                candidate_bytes, output_format, extension = _choose_output_for_opaque_png(
                    normalized=normalized,
                    original_bytes=raw_bytes,
                    resized=resized,
                    orientation_fixed=orientation_fixed,
                )
            else:
                candidate_bytes = _jpeg_bytes(normalized)
                output_format = "JPEG"
                extension = ".jpg"

            if _should_keep_original(
                original_bytes=raw_bytes,
                candidate_bytes=candidate_bytes,
                original_format=original_format,
                output_format=output_format,
                original_mode=original.mode,
                resized=resized,
                orientation_fixed=orientation_fixed,
            ):
                preserved_ext = Path(getattr(uploaded, "name", fallback_name)).suffix or extension
                preserved = ContentFile(raw_bytes)
                preserved.name = f"{base_name}{preserved_ext.lower()}"
                return preserved

            compressed = ContentFile(candidate_bytes)
            compressed.name = f"{base_name}{extension}"
            return compressed
    except (UnidentifiedImageError, OSError, ValueError) as exc:
        raise ValidationError(_("Invalid image upload.")) from exc


def compress_model_image_field(instance, field_name: str) -> bool:
    file_value = getattr(instance, field_name, None)
    if not file_value:
        return False

    # Plain strings / stored names are already canonical storage references and
    # must not be re-opened or re-compressed. This matters for flows that reuse
    # one stored punch image across multiple models by pointing them at the same
    # storage path.
    if isinstance(file_value, str):
        return False

    if getattr(file_value, "_committed", False):
        return False

    compressed = compress_attendance_image(
        file_value,
        fallback_name=getattr(file_value, "name", f"{field_name}.jpg"),
    )
    setattr(instance, field_name, compressed)
    return True


__all__ = [
    "MAX_IMAGE_DIMENSION",
    "JPEG_QUALITY",
    "compress_attendance_image",
    "compress_model_image_field",
    "_extract_error_message",
]
