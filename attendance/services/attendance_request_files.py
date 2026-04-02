from __future__ import annotations

from dataclasses import dataclass

import logging

from django.core.signing import BadSignature, SignatureExpired, TimestampSigner
from django.urls import reverse

from attendance.models import Attendance
from attendance.services.attachment_contract import (
    attachment_mime_type,
    attachment_name,
    attachment_size,
    preferred_attachment_url,
)
from attendance.services.attendance_request_access import iter_request_attachments, user_can_view_request
from attendance.services.attendance_correction_requests import (
    build_permission_flags as build_correction_permission_flags,
    user_is_request_owner as correction_user_is_request_owner,
)

logger = logging.getLogger(__name__)

SIGNER_SALT = "attendance.attendance_request_attachment"
DEFAULT_MAX_AGE_SECONDS = 60 * 60 * 24


@dataclass
class AttachmentLink:
    file_id: int
    file_name: str
    url: str


def _iter_generic_attachments(request_obj):
    if isinstance(request_obj, Attendance):
        yield from iter_request_attachments(request_obj)
        return
    try:
        for link in request_obj.attachment_links.select_related("attendance_request_file").all():
            file_obj = getattr(link, "attendance_request_file", None)
            if file_obj:
                yield file_obj
    except Exception:
        return


def attachment_belongs_to_request(request_obj, file_obj) -> bool:
    try:
        return any(getattr(f, "id", None) == getattr(file_obj, "id", None) for f in _iter_generic_attachments(request_obj))
    except Exception:
        return False


def build_attachment_token(request_id: int, file_id: int) -> str:
    signer = TimestampSigner(salt=SIGNER_SALT)
    return signer.sign(f"{request_id}:{file_id}")


def verify_attachment_token(request_id: int, file_id: int, token: str | None, *, max_age: int = DEFAULT_MAX_AGE_SECONDS) -> bool:
    if not token:
        return False
    signer = TimestampSigner(salt=SIGNER_SALT)
    try:
        value = signer.unsign(token, max_age=max_age)
    except (BadSignature, SignatureExpired):
        return False
    return value == f"{request_id}:{file_id}"


def build_attachment_url(request, request_obj, file_obj, *, kind: str = "preferred") -> str:
    if kind == "view":
        route_name = "api-attendance-request-attachment-view"
    elif kind == "download":
        route_name = "api-attendance-request-attachment-download"
    else:
        route_name = None

    token = build_attachment_token(request_obj.id, file_obj.id)
    if route_name:
        path = reverse(route_name, kwargs={"attendance_id": request_obj.id, "file_id": file_obj.id})
        url = f"{path}?token={token}"
    else:
        metadata = build_attachment_metadata(request, request_obj, file_obj)
        url = preferred_attachment_url(metadata) or metadata.get("download_url") or metadata.get("view_url") or ""

    try:
        return request.build_absolute_uri(url)
    except Exception:
        return url


def build_attachment_metadata(request, request_obj, file_obj, *, include_delete_url: bool = False) -> dict:
    view_url = build_attachment_url(request, request_obj, file_obj, kind="view")
    download_url = build_attachment_url(request, request_obj, file_obj, kind="download")
    metadata = {
        "id": getattr(file_obj, "id", None),
        "name": attachment_name(file_obj),
        "mime_type": attachment_mime_type(file_obj),
        "size": attachment_size(file_obj),
        "view_url": view_url,
        "download_url": download_url,
    }
    metadata["url"] = preferred_attachment_url(metadata) or download_url or view_url
    if include_delete_url:
        try:
            delete_path = reverse(
                "api-attendance-request-attachment-download",
                kwargs={"attendance_id": request_obj.id, "file_id": file_obj.id},
            )
            delete_url = f"{delete_path}?token={build_attachment_token(request_obj.id, file_obj.id)}"
            try:
                delete_url = request.build_absolute_uri(delete_url)
            except Exception:
                pass
            metadata["delete_url"] = delete_url
        except Exception:
            metadata["delete_url"] = None
    return metadata


def request_can_view_attachment(request, request_obj) -> bool:
    if not request or not request_obj:
        return False
    try:
        if isinstance(request_obj, Attendance):
            return user_can_view_request(request.user, request_obj)
        flags = build_correction_permission_flags(request_obj, request.user)
        return bool(
            getattr(request.user, "is_superuser", False)
            or correction_user_is_request_owner(request.user, request_obj)
            or any(flags.values())
        )
    except Exception:
        logger.exception("Failed to resolve attendance attachment permissions for request %s", getattr(request_obj, "id", None))
        return False
