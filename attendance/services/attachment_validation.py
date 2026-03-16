from __future__ import annotations

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
    ".webp",
    ".pdf",
    ".doc",
    ".docx",
    ".xls",
    ".xlsx",
    ".csv",
    ".txt",
)


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
        if size > MAX_ATTACHMENT_SIZE_BYTES:
            raise ValidationError(
                _("Attachment %(name)s exceeds the maximum allowed size of %(max_size)s MB."),
                params={"name": name, "max_size": MAX_ATTACHMENT_SIZE_MB},
            )
