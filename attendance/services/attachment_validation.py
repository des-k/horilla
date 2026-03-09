from __future__ import annotations

from pathlib import Path
from typing import Iterable

from django.core.exceptions import ValidationError
from django.utils.translation import gettext_lazy as _

MAX_ATTACHMENT_SIZE_BYTES = 10 * 1024 * 1024
ALLOWED_ATTACHMENT_EXTENSIONS = {
    ".jpg", ".jpeg", ".png", ".webp", ".pdf",
    ".doc", ".docx", ".xls", ".xlsx", ".csv", ".txt",
}


def validate_uploaded_files(uploaded_files: Iterable) -> None:
    for uploaded in uploaded_files or []:
        name = getattr(uploaded, "name", "") or "file"
        size = int(getattr(uploaded, "size", 0) or 0)
        ext = Path(name).suffix.lower()
        if ext not in ALLOWED_ATTACHMENT_EXTENSIONS:
            allowed = ", ".join(sorted(ALLOWED_ATTACHMENT_EXTENSIONS))
            raise ValidationError(
                _("Unsupported attachment type: %(name)s. Allowed: %(allowed)s"),
                params={"name": name, "allowed": allowed},
            )
        if size > MAX_ATTACHMENT_SIZE_BYTES:
            raise ValidationError(
                _("Attachment %(name)s exceeds the maximum allowed size of 10 MB."),
                params={"name": name},
            )
