from __future__ import annotations

import mimetypes
import os
from typing import Any

INLINE_VIEWABLE_MIME_TYPES = {
    "application/pdf",
    "image/jpeg",
    "image/jpg",
    "image/png",
    "image/gif",
    "image/webp",
}


def attachment_name(file_obj: Any) -> str:
    try:
        raw_name = getattr(getattr(file_obj, "file", None), "name", "") or ""
        name = os.path.basename(raw_name.strip())
        return name or "attachment"
    except Exception:
        return "attachment"


def attachment_mime_type(file_obj: Any) -> str:
    file_field = getattr(file_obj, "file", None)
    explicit = (
        getattr(file_field, "content_type", None)
        or getattr(file_obj, "content_type", None)
        or ""
    )
    explicit = str(explicit).strip().lower()
    if explicit and explicit not in {"application/octet-stream", "binary/octet-stream"}:
        return explicit

    guessed, _encoding = mimetypes.guess_type(attachment_name(file_obj))
    guessed = (guessed or "").strip().lower()
    return guessed or "application/octet-stream"


def attachment_size(file_obj: Any) -> int | None:
    file_field = getattr(file_obj, "file", None)
    try:
        size = getattr(file_field, "size", None)
        if size is not None:
            return int(size)
    except Exception:
        pass
    try:
        storage = getattr(file_field, "storage", None)
        file_name = getattr(file_field, "name", None)
        if storage is not None and file_name:
            return int(storage.size(file_name))
    except Exception:
        pass
    return None


def is_inline_viewable_mime_type(mime_type: str | None) -> bool:
    normalized = (mime_type or "").strip().lower()
    if not normalized:
        return False
    if normalized in INLINE_VIEWABLE_MIME_TYPES:
        return True
    return normalized.startswith("image/")


def preferred_attachment_url(metadata: dict[str, Any] | None) -> str | None:
    if not metadata:
        return None
    mime_type = metadata.get("mime_type")
    if is_inline_viewable_mime_type(mime_type):
        return metadata.get("view_url") or metadata.get("download_url")
    return metadata.get("download_url") or metadata.get("view_url")
