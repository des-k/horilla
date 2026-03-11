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


def _should_keep_original(*, original_bytes: bytes, recompressed_bytes: bytes, original_format: str, output_format: str, original_mode: str, resized: bool, orientation_fixed: bool) -> bool:
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
    return len(recompressed_bytes) >= len(original_bytes)


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
            output = BytesIO()
            base_name = _safe_basename(getattr(uploaded, "name", None), fallback="attendance-photo")

            if transparent:
                save_image = normalized if normalized.mode in ("RGBA", "LA", "P") else normalized.convert("RGBA")
                save_image.save(output, format="PNG", optimize=True)
                output_format = "PNG"
                final_name = f"{base_name}.png"
            else:
                if normalized.mode != "RGB":
                    save_image = normalized.convert("RGB")
                else:
                    save_image = normalized
                save_image.save(
                    output,
                    format="JPEG",
                    quality=JPEG_QUALITY,
                    optimize=True,
                    progressive=True,
                )
                output_format = "JPEG"
                final_name = f"{base_name}.jpg"

            recompressed = output.getvalue()
            if _should_keep_original(
                original_bytes=raw_bytes,
                recompressed_bytes=recompressed,
                original_format=original_format,
                output_format=output_format,
                original_mode=original.mode,
                resized=resized,
                orientation_fixed=orientation_fixed,
            ):
                preserved_ext = Path(getattr(uploaded, "name", fallback_name)).suffix or (".png" if output_format == "PNG" else ".jpg")
                preserved = ContentFile(raw_bytes)
                preserved.name = f"{base_name}{preserved_ext.lower()}"
                return preserved

            compressed = ContentFile(recompressed)
            compressed.name = final_name
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

    compressed = compress_attendance_image(file_value, fallback_name=getattr(file_value, "name", f"{field_name}.jpg"))
    setattr(instance, field_name, compressed)
    return True


__all__ = [
    "MAX_IMAGE_DIMENSION",
    "JPEG_QUALITY",
    "compress_attendance_image",
    "compress_model_image_field",
    "_extract_error_message",
]
