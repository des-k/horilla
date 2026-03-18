from __future__ import annotations

import logging
import os
from dataclasses import dataclass
from typing import Iterable

from django.core.signing import BadSignature, SignatureExpired, TimestampSigner
from django.urls import reverse

from attendance.models import WorkModeRequest
from attendance.services.work_type_request_permissions import can_manage_as_approver, is_owner


SIGNER_SALT = "attendance.work_type_request_attachment"
DEFAULT_MAX_AGE_SECONDS = 60 * 60 * 24

logger = logging.getLogger(__name__)


@dataclass
class AttachmentLink:
    file_id: int
    file_name: str
    url: str


def _attachment_name(file_obj) -> str:
    try:
        return os.path.basename(getattr(file_obj.file, "name", "") or "attachment")
    except Exception:
        return "attachment"


def attachment_belongs_to_request(req: WorkModeRequest, file_obj) -> bool:
    try:
        if req.files.filter(id=file_obj.id).exists():
            return True
    except Exception:
        pass
    try:
        return req.document_versions.filter(file_links__attendance_request_file=file_obj).exists()
    except Exception:
        return False


def build_attachment_token(req_id: int, file_id: int) -> str:
    signer = TimestampSigner(salt=SIGNER_SALT)
    return signer.sign(f"{req_id}:{file_id}")


def verify_attachment_token(req_id: int, file_id: int, token: str | None, *, max_age: int = DEFAULT_MAX_AGE_SECONDS) -> bool:
    if not token:
        return False
    signer = TimestampSigner(salt=SIGNER_SALT)
    try:
        value = signer.unsign(token, max_age=max_age)
    except (BadSignature, SignatureExpired):
        return False
    return value == f"{req_id}:{file_id}"


def build_attachment_url(request, req: WorkModeRequest, file_obj) -> str:
    path = reverse(
        "attendance-work-type-request-attachment-download",
        kwargs={"obj_id": req.id, "file_id": file_obj.id},
    )
    token = build_attachment_token(req.id, file_obj.id)
    url = f"{path}?token={token}"
    try:
        return request.build_absolute_uri(url)
    except Exception:
        return url


def request_can_view_attachment(request, req: WorkModeRequest) -> bool:
    try:
        if is_owner(request, req):
            return True
    except Exception:
        logger.exception("Failed to resolve work-mode attachment owner for request %s", getattr(req, "id", None))
        return False
    try:
        return can_manage_as_approver(request, req)
    except Exception:
        logger.exception("Failed to resolve work-mode attachment access for request %s", getattr(req, "id", None))
        return False


def build_attachment_links(request, req: WorkModeRequest, files: Iterable) -> list[AttachmentLink]:
    links: list[AttachmentLink] = []
    seen: set[int] = set()
    for file_obj in files or []:
        try:
            file_id = int(file_obj.id)
        except Exception:
            continue
        if file_id in seen:
            continue
        seen.add(file_id)
        links.append(
            AttachmentLink(
                file_id=file_id,
                file_name=_attachment_name(file_obj),
                url=build_attachment_url(request, req, file_obj),
            )
        )
    return links
