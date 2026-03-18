from __future__ import annotations

import os
from dataclasses import dataclass

from django.core.signing import BadSignature, SignatureExpired, TimestampSigner
from django.urls import reverse

import logging

from attendance.models import Attendance, AttendanceRequestComment
from base.methods import get_subordinate_employee_ids

logger = logging.getLogger(__name__)

SIGNER_SALT = "attendance.attendance_request_attachment"
DEFAULT_MAX_AGE_SECONDS = 60 * 60 * 24


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


def attachment_belongs_to_request(attendance: Attendance, file_obj) -> bool:
    try:
        return AttendanceRequestComment.objects.filter(
            request_id=attendance,
            files=file_obj,
        ).exists()
    except Exception:
        return False


def build_attachment_token(attendance_id: int, file_id: int) -> str:
    signer = TimestampSigner(salt=SIGNER_SALT)
    return signer.sign(f"{attendance_id}:{file_id}")


def verify_attachment_token(attendance_id: int, file_id: int, token: str | None, *, max_age: int = DEFAULT_MAX_AGE_SECONDS) -> bool:
    if not token:
        return False
    signer = TimestampSigner(salt=SIGNER_SALT)
    try:
        value = signer.unsign(token, max_age=max_age)
    except (BadSignature, SignatureExpired):
        return False
    return value == f"{attendance_id}:{file_id}"


def build_attachment_url(request, attendance: Attendance, file_obj) -> str:
    path = reverse(
        "api-attendance-request-attachment-download",
        kwargs={"attendance_id": attendance.id, "file_id": file_obj.id},
    )
    token = build_attachment_token(attendance.id, file_obj.id)
    url = f"{path}?token={token}"
    try:
        return request.build_absolute_uri(url)
    except Exception:
        return url


def request_can_view_attachment(request, attendance: Attendance) -> bool:
    if not request or not attendance:
        return False
    try:
        if attendance.employee_id.employee_user_id == request.user:
            return True
    except Exception:
        logger.exception("Failed to resolve attendance attachment owner for attendance %s", getattr(attendance, "id", None))
        return False
    try:
        if request.user.has_perm("attendance.change_attendance") or request.user.has_perm("attendance.view_attendance"):
            return True
    except Exception:
        logger.exception("Failed to resolve attendance attachment permissions for attendance %s", getattr(attendance, "id", None))
        return False
    try:
        employee_id = int(getattr(attendance, "employee_id_id", 0) or 0)
        subordinate_ids = {int(v) for v in (get_subordinate_employee_ids(request) or [])}
        return employee_id in subordinate_ids
    except Exception:
        logger.exception("Failed to resolve subordinate scope for attendance attachment %s", getattr(attendance, "id", None))
        return False
