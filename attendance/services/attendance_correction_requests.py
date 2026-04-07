from __future__ import annotations

from datetime import datetime
from typing import Iterable, Optional

from django.core.exceptions import ValidationError
from django.db import IntegrityError, transaction
from django.utils import timezone
from django.utils.dateparse import parse_date, parse_time

from attendance.models import (
    Attendance,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestAttachment,
    AttendanceCorrectionRequestScope,
    AttendanceCorrectionRequestSession,
    AttendanceCorrectionRequestStatus,
    AttendanceRequestActionType,
    AttendanceRequestFile,
)
from attendance.services.reconciliation import recompute_attendance
from notifications.domain_notifications import send_attendance_request_notification
from base.methods import get_subordinate_employee_ids
from employee.models import Employee

ACTIVE_STATUSES = (
    AttendanceCorrectionRequestStatus.WAITING,
    AttendanceCorrectionRequestStatus.APPROVED,
)
TERMINAL_STATUSES = (
    AttendanceCorrectionRequestStatus.REJECTED,
    AttendanceCorrectionRequestStatus.REVOKED,
    AttendanceCorrectionRequestStatus.CANCELED,
)


class AttendanceCorrectionError(ValidationError):
    pass


def _normalize_scope(scope: str | None) -> str:
    raw = (scope or "").strip().upper()
    if raw == "BOTH":
        raw = "FULL"
    if raw not in {
        AttendanceCorrectionRequestScope.IN,
        AttendanceCorrectionRequestScope.OUT,
        AttendanceCorrectionRequestScope.FULL,
    }:
        raise AttendanceCorrectionError({"scope": "Invalid scope."})
    return raw




def _coerce_date(value):
    if value in (None, "", "null"):
        return None
    if hasattr(value, "year") and hasattr(value, "month") and hasattr(value, "day") and not isinstance(value, str):
        return value
    return parse_date(str(value))


def _coerce_time(value):
    if value in (None, "", "null"):
        return None
    if hasattr(value, "hour") and hasattr(value, "minute") and not isinstance(value, str):
        return value
    parsed = parse_time(str(value))
    return parsed

def _combine(d, t):
    if d and t:
        return datetime.combine(d, t)
    return None


def _sessions_for_scope(scope: str) -> list[str]:
    if scope == AttendanceCorrectionRequestScope.FULL:
        return ["IN", "OUT"]
    return [scope]


def _active_request_for_slot(employee: Employee, attendance_date, session: str, exclude_request_id: int | None = None):
    qs = AttendanceCorrectionRequest.objects.filter(
        employee_id=employee,
        attendance_date=attendance_date,
        status__in=ACTIVE_STATUSES,
        sessions__session=session,
        sessions__is_active_lock=True,
    ).distinct()
    if exclude_request_id:
        qs = qs.exclude(id=exclude_request_id)
    return qs.order_by("-id").first()


def _effective_attendance(employee: Employee, attendance_date):
    return Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()


def _owner_user(request_obj: AttendanceCorrectionRequest):
    try:
        return request_obj.employee_id.employee_user_id
    except Exception:
        return None


def _approver_user(request_obj: AttendanceCorrectionRequest):
    employee = getattr(request_obj, 'employee_id', None)
    work_info = None
    if employee is not None:
        try:
            work_info = employee.employee_work_info
        except Exception:
            work_info = None
    manager = getattr(work_info, 'reporting_manager_id', None)
    if manager is None:
        try:
            from employee.models import EmployeeWorkInformation

            employee_id = getattr(request_obj, 'employee_id_id', None) or getattr(employee, 'id', None)
            if employee_id:
                work_info = EmployeeWorkInformation.objects.filter(employee_id=employee_id).select_related('reporting_manager_id__employee_user_id').first()
                manager = getattr(work_info, 'reporting_manager_id', None)
        except Exception:
            manager = None
    return getattr(manager, 'employee_user_id', None)


def _notify_request_event(*, request_obj: AttendanceCorrectionRequest, actor_user, event: str, recipient_role: str, reason: str | None = None):
    recipient = _approver_user(request_obj) if recipient_role == 'approver' else _owner_user(request_obj)
    if recipient is None:
        return
    send_attendance_request_notification(
        actor=actor_user,
        recipient=recipient,
        attendance=request_obj,
        event=event,
        recipient_role=recipient_role,
        reason=reason,
    )


def user_is_request_owner(user, request_obj: AttendanceCorrectionRequest) -> bool:
    return bool(user and _owner_user(request_obj) == user)


def user_can_approve_request(user, request_obj: AttendanceCorrectionRequest) -> bool:
    if not user or user_is_request_owner(user, request_obj):
        return False
    try:
        if getattr(user, "is_superuser", False):
            return True
    except Exception:
        pass
    try:
        subordinate_ids = {int(v) for v in (get_subordinate_employee_ids(type("R", (), {"user": user})()) or [])}
    except Exception:
        subordinate_ids = set()
    return int(request_obj.employee_id_id) in subordinate_ids


def build_permission_flags(request_obj: AttendanceCorrectionRequest, user) -> dict:
    status_value = getattr(request_obj, "status", None)
    is_owner = user_is_request_owner(user, request_obj)
    can_approve = user_can_approve_request(user, request_obj) and status_value == AttendanceCorrectionRequestStatus.WAITING
    can_reject = can_approve
    can_revoke = user_can_approve_request(user, request_obj) and status_value == AttendanceCorrectionRequestStatus.APPROVED
    return {
        "can_edit": bool(is_owner and status_value == AttendanceCorrectionRequestStatus.WAITING),
        "can_cancel": bool(is_owner and status_value == AttendanceCorrectionRequestStatus.WAITING),
        "can_approve": bool(can_approve),
        "can_reject": bool(can_reject),
        "can_revoke": bool(can_revoke),
    }


def _validate_payload(*, employee: Employee, attendance_date, scope: str, requested_check_in_date=None, requested_check_in_time=None, requested_check_out_date=None, requested_check_out_time=None, exclude_request_id: int | None = None):
    scope = _normalize_scope(scope)
    errors = {}
    in_dt = _combine(requested_check_in_date, requested_check_in_time)
    out_dt = _combine(requested_check_out_date, requested_check_out_time)

    if scope in (AttendanceCorrectionRequestScope.IN, AttendanceCorrectionRequestScope.FULL) and not in_dt:
        errors["requested_check_in_time"] = "Requested check-in is required."
    if scope in (AttendanceCorrectionRequestScope.OUT, AttendanceCorrectionRequestScope.FULL) and not out_dt:
        errors["requested_check_out_time"] = "Requested check-out is required."
    if scope == AttendanceCorrectionRequestScope.FULL and in_dt and out_dt and out_dt <= in_dt:
        errors["requested_check_out_time"] = "Requested check-out must be after requested check-in."

    for session in _sessions_for_scope(scope):
        conflict = _active_request_for_slot(employee, attendance_date, session, exclude_request_id=exclude_request_id)
        if conflict is not None:
            errors["scope"] = f"Another active attendance correction request already locks slot {session} for this date."
            break

    effective = _effective_attendance(employee, attendance_date)
    current_in_dt = _combine(getattr(effective, "attendance_clock_in_date", None), getattr(effective, "attendance_clock_in", None)) if effective else None
    current_out_dt = _combine(getattr(effective, "attendance_clock_out_date", None), getattr(effective, "attendance_clock_out", None)) if effective else None
    active_in_req = _active_request_for_slot(employee, attendance_date, "IN", exclude_request_id=exclude_request_id)
    active_out_req = _active_request_for_slot(employee, attendance_date, "OUT", exclude_request_id=exclude_request_id)
    other_in_dt = active_in_req.requested_check_in_dt if active_in_req else None
    other_out_dt = active_out_req.requested_check_out_dt if active_out_req else None

    if scope == AttendanceCorrectionRequestScope.IN and in_dt:
        compare_out = current_out_dt
        if other_out_dt and (compare_out is None or other_out_dt < compare_out):
            compare_out = other_out_dt
        if compare_out and in_dt >= compare_out:
            errors["requested_check_in_time"] = "Requested check-in must be earlier than the effective check-out."
    if scope == AttendanceCorrectionRequestScope.OUT and out_dt:
        compare_in = current_in_dt
        if other_in_dt and (compare_in is None or other_in_dt > compare_in):
            compare_in = other_in_dt
        if compare_in and out_dt <= compare_in:
            errors["requested_check_out_time"] = "Requested check-out must be later than the effective check-in."

    if errors:
        raise AttendanceCorrectionError(errors)


def _sync_session_locks(request_obj: AttendanceCorrectionRequest):
    AttendanceCorrectionRequestSession.objects.filter(request=request_obj, is_active_lock=True).update(is_active_lock=False)
    if request_obj.status not in ACTIVE_STATUSES:
        return
    for session in _sessions_for_scope(request_obj.scope):
        AttendanceCorrectionRequestSession.objects.create(
            request=request_obj,
            employee_id=request_obj.employee_id,
            attendance_date=request_obj.attendance_date,
            session=session,
            is_active_lock=True,
        )


def _create_attachment_links(request_obj: AttendanceCorrectionRequest, uploaded_files: Iterable):
    for up in uploaded_files or []:
        arf = AttendanceRequestFile.objects.create(file=up)
        AttendanceCorrectionRequestAttachment.objects.create(
            request=request_obj,
            attendance_request_file=arf,
        )


@transaction.atomic
def create_request(*, employee: Employee, actor_user, payload: dict, uploaded_files: Optional[Iterable] = None) -> AttendanceCorrectionRequest:
    scope = _normalize_scope(payload.get("scope"))
    attendance_date = _coerce_date(payload.get("attendance_date"))
    reason = (payload.get("reason") or "").strip()
    if not reason:
        raise AttendanceCorrectionError({"reason": "Reason is required."})
    _validate_payload(
        employee=employee,
        attendance_date=attendance_date,
        scope=scope,
        requested_check_in_date=_coerce_date(payload.get("requested_check_in_date") or payload.get("attendance_clock_in_date")),
        requested_check_in_time=_coerce_time(payload.get("requested_check_in_time") or payload.get("attendance_clock_in")),
        requested_check_out_date=_coerce_date(payload.get("requested_check_out_date") or payload.get("attendance_clock_out_date")),
        requested_check_out_time=_coerce_time(payload.get("requested_check_out_time") or payload.get("attendance_clock_out")),
    )
    request_obj = AttendanceCorrectionRequest.objects.create(
        employee_id=employee,
        attendance_date=attendance_date,
        scope=scope,
        requested_check_in_date=_coerce_date(payload.get("requested_check_in_date") or payload.get("attendance_clock_in_date")),
        requested_check_in_time=_coerce_time(payload.get("requested_check_in_time") or payload.get("attendance_clock_in")),
        requested_check_out_date=_coerce_date(payload.get("requested_check_out_date") or payload.get("attendance_clock_out_date")),
        requested_check_out_time=_coerce_time(payload.get("requested_check_out_time") or payload.get("attendance_clock_out")),
        reason=reason,
        status=AttendanceCorrectionRequestStatus.WAITING,
    )
    try:
        request_obj.created_by = actor_user
        request_obj.save(update_fields=["created_by"])
    except Exception:
        pass
    try:
        _sync_session_locks(request_obj)
    except IntegrityError:
        raise AttendanceCorrectionError({"scope": "Another active attendance correction request already exists for this slot."})
    _create_attachment_links(request_obj, uploaded_files)
    _notify_request_event(
        request_obj=request_obj,
        actor_user=actor_user,
        event='attendance_request_created',
        recipient_role='approver',
    )
    return request_obj


@transaction.atomic
def update_request(*, request_obj: AttendanceCorrectionRequest, actor_user, payload: dict, uploaded_files: Optional[Iterable] = None) -> AttendanceCorrectionRequest:
    if request_obj.status != AttendanceCorrectionRequestStatus.WAITING:
        raise AttendanceCorrectionError({"status": "Only waiting requests can be edited."})
    scope = _normalize_scope(payload.get("scope") or request_obj.scope)
    attendance_date = _coerce_date(payload.get("attendance_date")) or request_obj.attendance_date
    reason = (payload.get("reason") or request_obj.reason or "").strip()
    if not reason:
        raise AttendanceCorrectionError({"reason": "Reason is required."})
    _validate_payload(
        employee=request_obj.employee_id,
        attendance_date=attendance_date,
        scope=scope,
        requested_check_in_date=_coerce_date(payload.get("requested_check_in_date") or payload.get("attendance_clock_in_date")),
        requested_check_in_time=_coerce_time(payload.get("requested_check_in_time") or payload.get("attendance_clock_in")),
        requested_check_out_date=_coerce_date(payload.get("requested_check_out_date") or payload.get("attendance_clock_out_date")),
        requested_check_out_time=_coerce_time(payload.get("requested_check_out_time") or payload.get("attendance_clock_out")),
        exclude_request_id=request_obj.id,
    )
    request_obj.attendance_date = attendance_date
    request_obj.scope = scope
    request_obj.requested_check_in_date = _coerce_date(payload.get("requested_check_in_date") or payload.get("attendance_clock_in_date"))
    request_obj.requested_check_in_time = _coerce_time(payload.get("requested_check_in_time") or payload.get("attendance_clock_in"))
    request_obj.requested_check_out_date = _coerce_date(payload.get("requested_check_out_date") or payload.get("attendance_clock_out_date"))
    request_obj.requested_check_out_time = _coerce_time(payload.get("requested_check_out_time") or payload.get("attendance_clock_out"))
    request_obj.reason = reason
    try:
        request_obj.modified_by = actor_user
    except Exception:
        pass
    request_obj.save()
    try:
        _sync_session_locks(request_obj)
    except IntegrityError:
        raise AttendanceCorrectionError({"scope": "Another active attendance correction request already exists for this slot."})
    _create_attachment_links(request_obj, uploaded_files)
    return request_obj


def _actor_employee(user):
    try:
        return user.employee_get
    except Exception:
        return None


@transaction.atomic
def approve_request(*, request_obj: AttendanceCorrectionRequest, actor_user):
    if request_obj.status != AttendanceCorrectionRequestStatus.WAITING:
        raise AttendanceCorrectionError({"status": "Only waiting requests can be approved."})
    request_obj.status = AttendanceCorrectionRequestStatus.APPROVED
    request_obj.approved_by = _actor_employee(actor_user)
    request_obj.approved_at = timezone.now()
    request_obj.action_by = request_obj.approved_by
    request_obj.action_at = request_obj.approved_at
    request_obj.action_type = AttendanceRequestActionType.APPROVED
    request_obj.save()
    _sync_session_locks(request_obj)
    recompute_attendance(request_obj.employee_id, request_obj.attendance_date)
    _notify_request_event(
        request_obj=request_obj,
        actor_user=actor_user,
        event='attendance_request_approved',
        recipient_role='requester',
    )
    return request_obj


@transaction.atomic
def reject_request(*, request_obj: AttendanceCorrectionRequest, actor_user, reason: str):
    if request_obj.status != AttendanceCorrectionRequestStatus.WAITING:
        raise AttendanceCorrectionError({"status": "Only waiting requests can be rejected."})
    reason = (reason or "").strip()
    if not reason:
        raise AttendanceCorrectionError({"reason": "Reject reason is required."})
    request_obj.status = AttendanceCorrectionRequestStatus.REJECTED
    request_obj.action_reason = reason
    request_obj.rejected_by = _actor_employee(actor_user)
    request_obj.rejected_at = timezone.now()
    request_obj.action_by = request_obj.rejected_by
    request_obj.action_at = request_obj.rejected_at
    request_obj.action_type = AttendanceRequestActionType.REJECTED
    request_obj.save()
    _sync_session_locks(request_obj)
    _notify_request_event(
        request_obj=request_obj,
        actor_user=actor_user,
        event='attendance_request_rejected',
        recipient_role='requester',
        reason=reason,
    )
    return request_obj


@transaction.atomic
def revoke_request(*, request_obj: AttendanceCorrectionRequest, actor_user, reason: str):
    if request_obj.status != AttendanceCorrectionRequestStatus.APPROVED:
        raise AttendanceCorrectionError({"status": "Only approved requests can be revoked."})
    reason = (reason or "").strip()
    if not reason:
        raise AttendanceCorrectionError({"reason": "Revoke reason is required."})
    request_obj.status = AttendanceCorrectionRequestStatus.REVOKED
    request_obj.action_reason = reason
    request_obj.revoked_by = _actor_employee(actor_user)
    request_obj.revoked_at = timezone.now()
    request_obj.action_by = request_obj.revoked_by
    request_obj.action_at = request_obj.revoked_at
    request_obj.action_type = AttendanceRequestActionType.REVOKED
    request_obj.save()
    _sync_session_locks(request_obj)
    recompute_attendance(request_obj.employee_id, request_obj.attendance_date)
    _notify_request_event(
        request_obj=request_obj,
        actor_user=actor_user,
        event='attendance_request_revoked',
        recipient_role='requester',
        reason=reason,
    )
    return request_obj


@transaction.atomic
def cancel_request(*, request_obj: AttendanceCorrectionRequest, actor_user):
    if request_obj.status != AttendanceCorrectionRequestStatus.WAITING:
        raise AttendanceCorrectionError({"status": "Only waiting requests can be canceled."})
    request_obj.status = AttendanceCorrectionRequestStatus.CANCELED
    request_obj.canceled_by = _actor_employee(actor_user)
    request_obj.canceled_at = timezone.now()
    request_obj.action_by = request_obj.canceled_by
    request_obj.action_at = request_obj.canceled_at
    request_obj.action_type = AttendanceRequestActionType.CANCELED
    request_obj.save()
    _sync_session_locks(request_obj)
    _notify_request_event(
        request_obj=request_obj,
        actor_user=actor_user,
        event='attendance_request_canceled',
        recipient_role='requester',
    )
    return request_obj
