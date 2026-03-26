from __future__ import annotations

import mimetypes
from pathlib import Path
from typing import Iterable

from django.core.exceptions import ValidationError
from django.utils.translation import gettext_lazy as _

MAX_ATTACHMENT_SIZE_BYTES = 20 * 1024 * 1024
MAX_ATTACHMENT_SIZE_MB = MAX_ATTACHMENT_SIZE_BYTES // (1024 * 1024)
ALLOWED_ATTACHMENT_EXTENSIONS = (
    ".jpg",
    ".jpeg",
    ".png",
    ".pdf",
    ".doc",
    ".docx",
)

ALLOWED_ATTACHMENT_MIME_TYPES = {
    ".jpg": {"image/jpeg", "image/jpg"},
    ".jpeg": {"image/jpeg"},
    ".png": {"image/png"},
    ".pdf": {"application/pdf"},
    ".doc": {"application/msword"},
    ".docx": {"application/vnd.openxmlformats-officedocument.wordprocessingml.document"},
}


def allowed_attachment_extensions_text() -> str:
    return ", ".join(ext.lstrip(".").upper() for ext in ALLOWED_ATTACHMENT_EXTENSIONS)


def validate_uploaded_files(uploaded_files: Iterable) -> None:
    allowed_text = allowed_attachment_extensions_text()
    for uploaded in uploaded_files or []:
        name = getattr(uploaded, "name", "") or "file"
        size = int(getattr(uploaded, "size", 0) or 0)
        ext = Path(name).suffix.lower()
        if ext not in ALLOWED_ATTACHMENT_EXTENSIONS:
            raise ValidationError(
                _("Unsupported attachment type for %(name)s. Allowed types: %(allowed)s."),
                params={"name": name, "allowed": allowed_text},
            )
        content_type = (getattr(uploaded, "content_type", None) or "").lower().strip()
        guessed_type, guessed_encoding = mimetypes.guess_type(name)
        guessed_type = (guessed_type or "").lower().strip()
        allowed_mime_types = ALLOWED_ATTACHMENT_MIME_TYPES.get(ext, set())
        generic_types = {"application/octet-stream", "binary/octet-stream"}
        effective_type = content_type
        if not effective_type or effective_type in generic_types:
            effective_type = guessed_type
        if allowed_mime_types and effective_type and effective_type not in allowed_mime_types:
            raise ValidationError(
                _("MIME type mismatch for %(name)s. Allowed types: %(allowed)s."),
                params={"name": name, "allowed": allowed_text},
            )
        if size > MAX_ATTACHMENT_SIZE_BYTES:
            raise ValidationError(
                _("Attachment %(name)s exceeds the maximum allowed size of %(max_size)s MB."),
                params={"name": name, "max_size": MAX_ATTACHMENT_SIZE_MB},
            )
