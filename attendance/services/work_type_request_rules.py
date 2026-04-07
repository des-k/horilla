"""attendance.services.work_type_request_rules

Centralized business rules for **Work Type Requests (Attendance)**.

Terminology:
- UI/UX uses **Work Type**.
- DB model remains ``attendance.WorkModeRequest`` for backwards compatibility.

This module enforces the FINAL spec:
- Allowed request depends on scheduled work type for the *attendance_date*.
- Scopes: IN / OUT (single day), FULL (range).
- Overlap rules: FULL blocks any other request on covered days; otherwise max 1 IN and max 1 OUT per date.
- Status flow:
  - ON_DUTY requires attachment at create and goes to WAITING_FOR_APPROVAL once submitted.
  - WFA goes directly to WAITING_FOR_APPROVAL.
- Punch permission:
  - Schedule WFA/WFH/ON_DUTY => mobile punch allowed without request.
  - Schedule WFO => punch allowed only via relevant request:
    - WFA => only if APPROVED
    - ON_DUTY => only if APPROVED
- On Duty finalization:
  - Approval only unlocks punch permission for request-based ON_DUTY.
  - Late/early-out benefit remains normal until the supporting document is VERIFIED.
- Auto reject:
  - WFA WAITING_FOR_APPROVAL that passes cutoff is auto REJECTED with reason_code.
- Option B audit:
  - If a request that has been used for punch becomes REJECTED, mark attendance IN/OUT status as REJECTED
    (attendance row is kept).
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import date, datetime, timedelta
from typing import Optional, Tuple

from django.core.exceptions import ValidationError
from django.db import transaction
from django.db.models import Q
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceWorkMode,
    AttendancePunchStatus,
    WorkModeRequest,
    WorkModeRequestDocumentStatus,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestScope,
    WorkModeRequestStatus,
    EmployeeShiftDay,
)

from attendance.services.reconciliation import recompute_attendance_range
from attendance.methods.utils import shift_schedule_today


# -----------------------------------------------------------------------------
# Schedule resolver
# -----------------------------------------------------------------------------

def _normalize(s: str) -> str:
    return (s or "").strip().lower().replace("-", " ").replace("_", " ")


def _scheduled_attendance_mode_or_none(employee, target_date: date) -> Optional[str]:
    """Resolve scheduled/default work mode without forcing WFO on unknown data.

    ``target_date`` is currently informational; the deployment still derives the
    default work type from ``employee.employee_work_info.work_type_id``.
    """

    wt_obj = None
    try:
        wt_obj = employee.employee_work_info.work_type_id
    except Exception:
        wt_obj = None

    if wt_obj is None:
        try:
            wt_obj = employee.get_work_type()
        except Exception:
            wt_obj = None

    wt_name = ""
    try:
        wt_name = getattr(wt_obj, "work_type", "") or ""
    except Exception:
        wt_name = ""

    n = _normalize(wt_name)

    if "on duty" in n or "onduty" in n:
        return AttendanceWorkMode.ON_DUTY
    if "wfh" in n or "work from home" in n:
        return AttendanceWorkMode.WFH
    if "wfa" in n or "work from anywhere" in n or "remote" in n:
        return AttendanceWorkMode.WFA
    if "wfo" in n or "office" in n:
        return AttendanceWorkMode.WFO

    if n in (AttendanceWorkMode.WFO, AttendanceWorkMode.WFA, AttendanceWorkMode.WFH, AttendanceWorkMode.ON_DUTY):
        return n

    return None


def scheduled_attendance_mode(employee, target_date: date) -> str:
    """Resolve scheduled attendance mode with legacy WFO fallback."""

    return _scheduled_attendance_mode_or_none(employee, target_date) or AttendanceWorkMode.WFO


def _resolve_shift_rules_for_employee_date(employee, target_date: date) -> tuple[Optional[dict], Optional[datetime], Optional[datetime], Optional[datetime], Optional[datetime]]:
    """Return shift rules + key window datetimes for *target_date*.

    Validation is intentionally best-effort. If shift metadata cannot be resolved,
    callers should fall back to allowing the request and let other validations run.
    """

    shift = getattr(getattr(employee, "employee_work_info", None), "shift_id", None)
    if not shift:
        return None, None, None, None, None

    day = EmployeeShiftDay.objects.filter(day=target_date.strftime("%A").lower()).first()
    if not day:
        return None, None, None, None, None

    try:
        _min_hour, start_sec, end_sec = shift_schedule_today(day=day, shift=shift)
    except Exception:
        start_sec, end_sec = 0, 0

    try:
        from attendance.views.clock_in_out import get_shift_rules

        rules = get_shift_rules(target_date, shift, day, start_time_sec=start_sec, end_time_sec=end_sec)
    except Exception:
        return None, None, None, None, None

    now_dt = timezone.localtime(timezone.now())

    def _coerce(dt):
        if dt is None:
            return None
        try:
            return timezone.localtime(dt) if timezone.is_aware(dt) else timezone.make_aware(dt, timezone.get_current_timezone())
        except Exception:
            return dt

    check_in_end_dt = _coerce(rules.get("check_in_window_end_dt") or rules.get("cutoff_in_dt"))
    check_out_start_dt = _coerce(rules.get("check_out_window_start_dt"))
    check_out_end_dt = _coerce(rules.get("check_out_window_end_dt") or rules.get("cutoff_out_dt"))
    return rules, now_dt, check_in_end_dt, check_out_start_dt, check_out_end_dt


def _validate_current_day_scope_window(*, employee, scope: str, start_date: date, end_date: date, instance_id: Optional[int]) -> None:
    """Enforce live create-time scope rules against today's attendance windows.

    Only applies during create and only when today's date is covered by the request.
    Future-only ranges remain allowed.
    """

    if instance_id is not None:
        return

    today = timezone.localdate()
    if not (start_date <= today <= end_date):
        return

    _rules, now_dt, check_in_end_dt, check_out_start_dt, check_out_end_dt = _resolve_shift_rules_for_employee_date(employee, today)
    if now_dt is None:
        return

    check_in_passed = bool(check_in_end_dt and now_dt > check_in_end_dt)
    check_out_open = bool(check_out_start_dt and check_out_end_dt and check_out_start_dt <= now_dt <= check_out_end_dt)
    check_out_passed = bool(check_out_end_dt and now_dt > check_out_end_dt)

    if check_out_passed:
        raise ValidationError("Check-out window has ended. Work Type Request can no longer be created for today.")

    if scope == WorkModeRequestScope.OUT:
        # OUT requests for today remain allowed until the check-out window has ended.
        # The expired case is already handled above by `check_out_passed`.
        return

    if check_in_passed:
        if check_out_open:
            raise ValidationError("Check-in window has passed. Only OUT scope may be requested while the check-out window remains open.")
        raise ValidationError("Check-in window has passed. IN and FULL scopes are no longer allowed for today.")


# -----------------------------------------------------------------------------
# Request pickers & effective mode
# -----------------------------------------------------------------------------

TERMINAL_WORK_MODE_REQUEST_STATUSES = {
    WorkModeRequestStatus.REJECTED,
    WorkModeRequestStatus.CANCELED,
    WorkModeRequestStatus.REVOKED,
}



DOCUMENT_REVIEW_DOCUMENT_STATUSES = {
    WorkModeRequestDocumentStatus.SUBMITTED,
    WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
    WorkModeRequestDocumentStatus.REJECTED,
}


def work_mode_request_document_review_q() -> Q:
    return Q(
        status=WorkModeRequestStatus.APPROVED,
        mode=AttendanceWorkMode.ON_DUTY,
    )


def classify_work_mode_request_queue(req: WorkModeRequest) -> str | None:
    status_value = getattr(req, "status", None)
    if status_value == WorkModeRequestStatus.WAITING_FOR_APPROVAL:
        return "approval"
    if (
        getattr(req, "mode", None) == AttendanceWorkMode.ON_DUTY
        and status_value == WorkModeRequestStatus.APPROVED
        and req.effective_document_status() in DOCUMENT_REVIEW_DOCUMENT_STATUSES
    ):
        return "document_review"
    return None

def is_terminal_work_mode_request_status(status_val: str | None) -> bool:
    return status_val in TERMINAL_WORK_MODE_REQUEST_STATUSES


def is_active_work_mode_request_status(status_val: str | None) -> bool:
    return not is_terminal_work_mode_request_status(status_val)


def _is_active_status(status_val: str) -> bool:
    return is_active_work_mode_request_status(status_val)


def active_work_mode_request_status_q() -> Q:
    return ~Q(status__in=list(TERMINAL_WORK_MODE_REQUEST_STATUSES))


def work_mode_request_approval_q(*, include_pending_on_duty: bool = False) -> Q:
    _ = include_pending_on_duty  # kept for backward-compatible callers
    return Q(status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)


def pick_relevant_request(employee, target_date: date, want: str) -> Optional[WorkModeRequest]:
    """Pick *relevant* request for response/gating.

    Priority: IN/OUT (matching want) > FULL. Newest first.

    We intentionally include PENDING/WAITING requests so the API can:
    - show the request in response
    - block punch for WFA until APPROVED
    """

    if want not in ("in", "out"):
        raise ValueError("want must be 'in' or 'out'")

    base_qs = (
        WorkModeRequest.objects.filter(
            employee_id=employee,
            start_date__lte=target_date,
            end_date__gte=target_date,
        )
        .filter(active_work_mode_request_status_q())
        .order_by("-id")
    )

    scope_first = WorkModeRequestScope.IN if want == "in" else WorkModeRequestScope.OUT

    exact = base_qs.filter(scope=scope_first)
    if exact.exists():
        return exact.first()

    full = base_qs.filter(scope=WorkModeRequestScope.FULL)
    if full.exists():
        return full.first()

    return None


@dataclass
class EffectiveWorkType:
    mode: str
    source: str  # schedule|request
    request: Optional[WorkModeRequest]


def effective_work_type(employee, target_date: date, want: str) -> EffectiveWorkType:
    req = pick_relevant_request(employee, target_date, want)
    if req is not None:
        return EffectiveWorkType(mode=req.mode, source="request", request=req)

    sched = scheduled_attendance_mode(employee, target_date)
    return EffectiveWorkType(mode=sched, source="schedule", request=None)




def pick_committed_request(employee, target_date: date, want: str) -> Optional[WorkModeRequest]:
    """Pick the approved request that is already committed for read/display surfaces.

    Unlike :func:`pick_relevant_request`, this helper ignores waiting/pending requests.
    It is used by response payloads that must continue showing the scheduled mode until
    a request is actually approved.
    """

    if want not in ("in", "out"):
        raise ValueError("want must be 'in' or 'out'")

    base_qs = (
        WorkModeRequest.objects.filter(
            employee_id=employee,
            start_date__lte=target_date,
            end_date__gte=target_date,
            status=WorkModeRequestStatus.APPROVED,
        )
        .order_by("-id")
    )

    scope_first = WorkModeRequestScope.IN if want == "in" else WorkModeRequestScope.OUT

    exact = base_qs.filter(scope=scope_first)
    if exact.exists():
        return exact.first()

    full = base_qs.filter(scope=WorkModeRequestScope.FULL)
    if full.exists():
        return full.first()

    return None


def committed_work_type(employee, target_date: date, want: str) -> EffectiveWorkType:
    """Resolve the committed/visible work mode for a single session.

    Priority:
    1. approved request matching the requested session scope
    2. scheduled/default work mode for that date
    3. legacy WFO fallback when the schedule cannot be resolved

    This is distinct from :func:`effective_work_type`, which intentionally exposes
    waiting requests so the API can communicate request state and gate punch
    permissions.
    """

    req = pick_committed_request(employee, target_date, want)
    if req is not None:
        return EffectiveWorkType(mode=req.mode, source="approved_request", request=req)

    sched = scheduled_attendance_mode(employee, target_date)
    return EffectiveWorkType(mode=sched, source="schedule", request=None)

def resolve_biometric_work_mode(employee, target_date: date) -> EffectiveWorkType:
    """Resolve work mode for biometric punches.

    Priority:
    1. approved WorkModeRequest covering the date
    2. scheduled/default work type for that date
    3. WFO only when no business truth can be resolved
    """

    approved_request = (
        WorkModeRequest.objects.filter(
            employee_id=employee,
            start_date__lte=target_date,
            end_date__gte=target_date,
            status=WorkModeRequestStatus.APPROVED,
        )
        .order_by("-id")
        .first()
    )
    if approved_request is not None:
        return EffectiveWorkType(
            mode=approved_request.mode,
            source="approved_request",
            request=approved_request,
        )

    scheduled_mode = _scheduled_attendance_mode_or_none(employee, target_date)
    if scheduled_mode:
        return EffectiveWorkType(mode=scheduled_mode, source="schedule", request=None)

    return EffectiveWorkType(mode=AttendanceWorkMode.WFO, source="fallback_wfo", request=None)


def punch_allowed(eff: EffectiveWorkType) -> bool:
    """Whether mobile punch is allowed."""

    if eff.mode == AttendanceWorkMode.WFO:
        return False

    if eff.source == "schedule":
        return eff.mode in (AttendanceWorkMode.WFA, AttendanceWorkMode.WFH, AttendanceWorkMode.ON_DUTY)

    req = eff.request
    if not req:
        return False

    if not _is_active_status(req.status):
        return False

    # WFA/WFH require APPROVED
    if req.mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH}:
        return req.status == WorkModeRequestStatus.APPROVED

    # ON_DUTY request requires approval before punch.
    # Benefit finalization is handled later by reconciliation based on document verification.
    if req.mode == AttendanceWorkMode.ON_DUTY:
        return req.status == WorkModeRequestStatus.APPROVED

    return False


# -----------------------------------------------------------------------------
# Validation rules
# -----------------------------------------------------------------------------

def _active_status_q() -> Q:
    return active_work_mode_request_status_q()


def validate_work_type_request(
    *,
    employee,
    mode: str,
    scope: str,
    start_date: date,
    end_date: date,
    instance_id: Optional[int] = None,
) -> None:
    """Validate payload for create/update against business rules."""

    # Disallow backdated requests (creation only).
    # NOTE: allow editing existing records (attachments/note) even if they're in the past.
    if instance_id is None:
        today = timezone.localdate()
        if start_date < today:
            raise ValidationError("Start date cannot be in the past.")

    if mode not in (AttendanceWorkMode.WFA, AttendanceWorkMode.WFH, AttendanceWorkMode.ON_DUTY):
        raise ValidationError("Work Type Request only supports WFA, WFH and ON DUTY.")

    if scope in (WorkModeRequestScope.IN, WorkModeRequestScope.OUT) and start_date != end_date:
        raise ValidationError("Scope IN/OUT must be a single day (end_date = start_date).")

    if scope == WorkModeRequestScope.FULL and end_date < start_date:
        raise ValidationError("End date must be on/after start date.")

    # Allowed based on default schedule for each date in range
    d = start_date
    while d <= end_date:
        sched = scheduled_attendance_mode(employee, d)
        if sched == AttendanceWorkMode.ON_DUTY:
            raise ValidationError(
                "Default schedule is ON DUTY for this date; Work Type Request is not allowed."
            )
        if sched == AttendanceWorkMode.WFA and mode == AttendanceWorkMode.WFA:
            raise ValidationError("Default schedule is already WFA for this date.")
        if sched == AttendanceWorkMode.WFH and mode == AttendanceWorkMode.WFH:
            raise ValidationError("Default schedule is already WFH for this date.")
        # sched WFO: WFA/ON_DUTY allowed
        # sched WFA: ON_DUTY allowed for any scope (IN/OUT/FULL)
        d += timedelta(days=1)

    _validate_current_day_scope_window(
        employee=employee,
        scope=scope,
        start_date=start_date,
        end_date=end_date,
        instance_id=instance_id,
    )

    # Overlap rules
    qs = WorkModeRequest.objects.filter(employee_id=employee).filter(_active_status_q())
    if instance_id:
        qs = qs.exclude(id=instance_id)

    overlap_range = qs.filter(start_date__lte=end_date, end_date__gte=start_date)

    if scope == WorkModeRequestScope.FULL:
        if overlap_range.exists():
            raise ValidationError("FULL request date range overlaps with another request.")
        return

    # IN/OUT: single day
    day = start_date
    if overlap_range.filter(scope=WorkModeRequestScope.FULL).exists():
        raise ValidationError("Cannot create IN/OUT request when a FULL request covers the date.")

    if overlap_range.filter(scope=scope).exists():
        raise ValidationError("Only one request per scope (IN/OUT) is allowed per day.")


def coerce_work_type_payload(data: dict) -> Tuple[Optional[str], dict]:
    """Support UI using `work_type` instead of legacy `mode`."""

    if data.get("mode"):
        return data.get("mode"), data

    if data.get("work_type"):
        new_data = {**data}
        new_data["mode"] = new_data.get("work_type")
        return new_data.get("mode"), new_data

    return None, data


def has_attachments(req: WorkModeRequest) -> bool:
    try:
        resolver = getattr(req, "resolve_current_document_version", None)
        current = resolver() if callable(resolver) else getattr(req, "current_document_version", None)
        if current is not None:
            return current.file_links.exists()
    except Exception:
        pass
    try:
        return req.files.exists()
    except Exception:
        return False


# -----------------------------------------------------------------------------
# Auto reject cutoff (WFA waiting)
# -----------------------------------------------------------------------------

def _reject_reason_for_scope(scope: str) -> str:
    if scope == WorkModeRequestScope.IN:
        return WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_IN_PASSED
    if scope == WorkModeRequestScope.OUT:
        return WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_OUT_PASSED
    return WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_FULL_PASSED


@transaction.atomic
def auto_reject_wfa_waiting_for_date(
    *,
    employee,
    target_date: date,
    now_dt: datetime,
    cutoff_in_dt: Optional[datetime],
    cutoff_out_dt: Optional[datetime],
) -> int:
    """Auto reject WFA WAITING_FOR_APPROVAL when cutoff passed.

    Returns number of requests auto-rejected.
    """

    qs = WorkModeRequest.objects.select_for_update().filter(
        employee_id=employee,
        mode=AttendanceWorkMode.WFA,
        status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        start_date__lte=target_date,
        end_date__gte=target_date,
    )

    rejected = 0
    for req in qs:
        due_dt = None
        if req.scope == WorkModeRequestScope.IN:
            due_dt = cutoff_in_dt
        elif req.scope == WorkModeRequestScope.OUT:
            due_dt = cutoff_out_dt
        else:
            due_dt = cutoff_in_dt

        if due_dt and now_dt > due_dt:
            from attendance.services.work_type_request_actions import WorkModeRequestActions

            result = WorkModeRequestActions._auto_reject_for_cutoff(req, actor=None, now_dt=now_dt)
            if result is not None:
                rejected += 1

    return rejected


# -----------------------------------------------------------------------------
# Option B: mark attendance punches when request rejected
# -----------------------------------------------------------------------------

def _daterange(start: date, end: date):
    d = start
    while d <= end:
        yield d
        d += timedelta(days=1)


@transaction.atomic
def apply_rejection_to_attendance(req: WorkModeRequest) -> int:
    """Recompute final attendance after a rejected work type request.

    Raw punches remain stored; canonical reconciliation decides the restored final state.
    Returns the number of attendance dates recomputed.
    """

    if req.status != WorkModeRequestStatus.REJECTED:
        return 0
    if not req.reason_code:
        req.reason_code = WorkModeRequestRejectReasonCode.MANUAL_REJECT
        req.save(update_fields=["reason_code"])

    recompute_attendance_range(req.employee_id, req.start_date, req.end_date)
    return sum(1 for _ in _daterange(req.start_date, req.end_date))

