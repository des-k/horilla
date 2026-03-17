from __future__ import annotations

from typing import Any

from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestDocumentStatus,
    WorkModeRequestStatus,
)
from base.methods import get_subordinate_employee_ids


TERMINAL_STATUSES = {
    WorkModeRequestStatus.REJECTED,
    WorkModeRequestStatus.CANCELED,
    WorkModeRequestStatus.REVOKED,
}


def _effective_document_status(req: WorkModeRequest) -> str | None:
    resolver = getattr(req, "effective_document_status", None)
    if callable(resolver):
        try:
            return resolver()
        except Exception:
            pass
    return getattr(req, "document_status", None)


def request_actor_employee(request) -> Any | None:
    try:
        return request.user.employee_get
    except Exception:
        return None


def is_global_work_type_approver(user) -> bool:
    try:
        if getattr(user, "is_superuser", False):
            return True
        return bool(
            user.has_perm("attendance.change_workmoderequest")
            or user.has_perm("attendance.change_attendance")
        )
    except Exception:
        return False


def subordinate_employee_ids(request) -> set[int]:
    try:
        return {int(v) for v in (get_subordinate_employee_ids(request) or [])}
    except Exception:
        return set()


def is_owner(request, req: WorkModeRequest) -> bool:
    try:
        return req.employee_id.employee_user_id == request.user
    except Exception:
        return False


def is_self_request(request, req: WorkModeRequest) -> bool:
    return is_owner(request, req)


def can_manage_as_approver(request, req: WorkModeRequest) -> bool:
    if not request or not req:
        return False
    if is_self_request(request, req):
        return False
    if is_global_work_type_approver(request.user):
        return True
    return int(getattr(req, "employee_id_id", 0) or 0) in subordinate_employee_ids(request)


def update_allowed(req: WorkModeRequest) -> bool:
    if req.status in TERMINAL_STATUSES:
        return False
    if req.mode != AttendanceWorkMode.ON_DUTY:
        return req.status in {
            WorkModeRequestStatus.PENDING,
            WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        }
    if req.status in {
        WorkModeRequestStatus.PENDING,
        WorkModeRequestStatus.WAITING_FOR_APPROVAL,
    }:
        return True
    if req.status != WorkModeRequestStatus.APPROVED:
        return False
    return _effective_document_status(req) != WorkModeRequestDocumentStatus.VERIFIED


def can_update_request(request, req: WorkModeRequest) -> bool:
    return bool(request and is_owner(request, req) and update_allowed(req))


def cancel_allowed(req: WorkModeRequest) -> bool:
    return req.status in {
        WorkModeRequestStatus.PENDING,
        WorkModeRequestStatus.WAITING_FOR_APPROVAL,
    }


def can_cancel_request(request, req: WorkModeRequest) -> bool:
    return bool(request and is_owner(request, req) and cancel_allowed(req))


def can_upload_document(request, req: WorkModeRequest) -> bool:
    if not request or not is_owner(request, req):
        return False
    if req.status in TERMINAL_STATUSES:
        return False
    if req.mode == AttendanceWorkMode.WFA:
        return req.status in {
            WorkModeRequestStatus.PENDING,
            WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            WorkModeRequestStatus.APPROVED,
        }
    return update_allowed(req)


def can_approve_request(request, req: WorkModeRequest) -> bool:
    return bool(
        request
        and req.status == WorkModeRequestStatus.WAITING_FOR_APPROVAL
        and can_manage_as_approver(request, req)
    )


def can_reject_request(request, req: WorkModeRequest) -> bool:
    if not request or not can_manage_as_approver(request, req):
        return False
    if req.status == WorkModeRequestStatus.WAITING_FOR_APPROVAL:
        return True
    return bool(
        req.status == WorkModeRequestStatus.PENDING
        and req.mode == AttendanceWorkMode.ON_DUTY
        and is_global_work_type_approver(request.user)
    )


def can_revoke_request(request, req: WorkModeRequest) -> bool:
    return bool(
        request
        and req.status == WorkModeRequestStatus.APPROVED
        and can_manage_as_approver(request, req)
    )


def can_verify_document(request, req: WorkModeRequest) -> bool:
    return bool(
        request
        and req.mode == AttendanceWorkMode.ON_DUTY
        and req.status == WorkModeRequestStatus.APPROVED
        and _effective_document_status(req) in {
            WorkModeRequestDocumentStatus.SUBMITTED,
            WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        }
        and can_manage_as_approver(request, req)
    )


def can_reject_document(request, req: WorkModeRequest) -> bool:
    return can_verify_document(request, req)


def can_reopen_document(request, req: WorkModeRequest) -> bool:
    return bool(
        request
        and req.mode == AttendanceWorkMode.ON_DUTY
        and req.status == WorkModeRequestStatus.APPROVED
        and _effective_document_status(req) in {
            WorkModeRequestDocumentStatus.VERIFIED,
            WorkModeRequestDocumentStatus.REJECTED,
        }
        and can_manage_as_approver(request, req)
    )


def build_permission_flags(request, req: WorkModeRequest) -> dict[str, bool]:
    return {
        "can_update": can_update_request(request, req),
        "can_cancel": can_cancel_request(request, req),
        "can_upload_document": can_upload_document(request, req),
        "can_approve": can_approve_request(request, req),
        "can_reject": can_reject_request(request, req),
        "can_revoke": can_revoke_request(request, req),
        "can_verify_document": can_verify_document(request, req),
        "can_reject_document": can_reject_document(request, req),
        "can_reopen_document": can_reopen_document(request, req),
    }
