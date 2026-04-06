from __future__ import annotations

from dataclasses import dataclass
from datetime import date, datetime, time, timedelta
from typing import Iterable, Optional

from django.apps import apps
from django.conf import settings
from django.db import transaction
from django.db.models import Q
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceChannel,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestScope,
    AttendanceCorrectionRequestStatus,
    AttendanceLateComeEarlyOut,
    AttendancePunchDirection,
    AttendancePunchingHistory,
    AttendancePunchStatus,
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestDocumentStatus,
    WorkModeRequestStatus,
)
from attendance.methods.utils import format_time, strtime_seconds, shift_schedule_today
from attendance.services.canonical_attendance_policy import (
    AttendancePolicy,
    build_attendance_policy,
    compute_attendance_metrics,
    compute_worked_seconds,
    seconds_to_decimal_minutes,
    truncate_datetime_to_minute,
)
from base.models import EmployeeShiftDay

try:
    from leave.models import LeaveRequest
except Exception:  # pragma: no cover
    LeaveRequest = None  # type: ignore

try:
    from leave.half_day_rules import leave_breakdown_for_attendance_date
except Exception:  # pragma: no cover
    leave_breakdown_for_attendance_date = None  # type: ignore


SOURCE_NORMAL = "Normal"
SOURCE_LEAVE = "Leave"
SOURCE_WFA = "WFA"
SOURCE_ON_DUTY = "On Duty"
SOURCE_PROVISIONAL_ON_DUTY = "Provisional On Duty"
SOURCE_ATTENDANCE_REQUEST = "Attendance Request Override"
SOURCE_RECOMPUTED_AFTER_REVOKE = "Recomputed Normal After Revoke"

NOTE_FULL_DAY_LEAVE = "Approved Full-Day Leave"
NOTE_HALF_DAY_FIRST = "Approved First-Half Leave"
NOTE_HALF_DAY_SECOND = "Approved Second-Half Leave"
NOTE_ON_DUTY_FINAL = "On Duty Final"
NOTE_ON_DUTY_PROVISIONAL = "On Duty approved; benefit not final"
NOTE_ON_DUTY_NOT_GRANTED = "On Duty benefit not granted; normal attendance rules applied"
NOTE_RECOMPUTED_AFTER_REVOKE = "Recomputed using normal attendance rules after revoke"
NOTE_APPROVED_ATTENDANCE_REQUEST = "Approved Attendance Request Override"
NOTE_DUPLICATE_CHECKIN = "Duplicate check-in not used as final"
NOTE_SUPERSEDED_CHECKOUT = "Superseded by later valid check-out"
NOTE_IGNORED_FULL_DAY_LEAVE = "Ignored due to approved full-day leave"
NOTE_FINAL_IN = "Used as final Check-In"
NOTE_FINAL_OUT = "Used as final Check-Out"
NOTE_NOT_USED_REQUEST = {
    AttendancePunchDirection.IN: "Not used because final Check-In came from approved request",
    AttendancePunchDirection.OUT: "Not used because final Check-Out came from approved request",
}
NOTE_INVALID_IN_WINDOW = "Rejected: outside Check-In window"
NOTE_INVALID_OUT_WINDOW = "Rejected: outside Check-Out window"
NOTE_MISSING_IN = "Missing Check-In"
NOTE_MISSING_OUT = "Missing Check-Out"


@dataclass
class ShiftContext:
    employee: object
    attendance_date: date
    day: object | None
    shift: object | None
    schedule: object | None
    shift_start_dt: datetime | None
    shift_end_dt: datetime | None
    check_in_window_start_dt: datetime | None
    check_in_window_end_dt: datetime | None
    check_out_window_start_dt: datetime | None
    check_out_window_end_dt: datetime | None
    minimum_hour: str
    grace_seconds: int = 0
    grace_out_seconds: int = 0
    grace_clock_in_type: str = "after"


@dataclass
class LeaveContext:
    request: object | None
    kind: str | None
    late_reference_dt: datetime | None
    early_reference_dt: datetime | None
    minimum_hour: str
    policy: AttendancePolicy | None = None

    @property
    def is_full_day(self) -> bool:
        return self.kind == "full_day"

    @property
    def is_half_day(self) -> bool:
        return self.kind in {"first_half", "second_half"}


@dataclass
class PunchDecision:
    log: AttendancePunchingHistory
    status: str
    accepted: bool
    reason: str


@dataclass
class ReconciliationResult:
    attendance: Attendance
    activity: AttendanceActivity


def _localize(dt_obj: Optional[datetime]) -> Optional[datetime]:
    if dt_obj is None:
        return None
    if getattr(settings, "USE_TZ", False):
        if timezone.is_naive(dt_obj):
            dt_obj = timezone.make_aware(dt_obj, timezone.get_current_timezone())
        return timezone.localtime(dt_obj, timezone.get_current_timezone())
    if timezone.is_aware(dt_obj):
        return timezone.make_naive(dt_obj, timezone.get_current_timezone())
    return dt_obj


def _combine(d: Optional[date], t: Optional[time]) -> Optional[datetime]:
    if not d or not t:
        return None
    return _localize(datetime.combine(d, t))


def _minutes_to_hhmm(minutes: int) -> str:
    if minutes <= 0:
        return "00:00"
    return format_time(minutes * 60)


def _working_duration_delta(minimum_hour: str, fallback_start_dt: Optional[datetime], fallback_end_dt: Optional[datetime]) -> timedelta:
    try:
        secs = max(0, strtime_seconds(minimum_hour or "00:00"))
    except Exception:
        secs = 0
    if secs > 0:
        return timedelta(seconds=secs)
    if fallback_start_dt and fallback_end_dt and fallback_end_dt >= fallback_start_dt:
        return fallback_end_dt - fallback_start_dt
    return timedelta(0)


def _half_day_segment_boundary(kind: str, ctx: "ShiftContext") -> Optional[datetime]:
    if not ctx.shift_start_dt or not ctx.shift_end_dt:
        return None
    working_duration = _working_duration_delta(ctx.minimum_hour, ctx.shift_start_dt, ctx.shift_end_dt)
    if working_duration <= timedelta(0):
        return ctx.shift_start_dt + ((ctx.shift_end_dt - ctx.shift_start_dt) / 2)
    half_duration = working_duration / 2
    if kind == "first_half":
        return ctx.shift_end_dt - half_duration
    if kind == "second_half":
        return ctx.shift_start_dt + half_duration
    return None


def _time_to_shift_instance_dt(
    threshold_time: Optional[time],
    *,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
) -> Optional[datetime]:
    if not (threshold_time and shift_start_dt and shift_end_dt):
        return None

    candidate = datetime.combine(shift_start_dt.date(), threshold_time)
    candidate = _localize(candidate)
    if candidate is None:
        return None

    if shift_end_dt < shift_start_dt:
        shift_end_dt = shift_end_dt + timedelta(days=1)

    if candidate < shift_start_dt and shift_end_dt.date() > shift_start_dt.date():
        candidate = candidate + timedelta(days=1)

    return candidate


def _half_minimum_hour(minimum_hour: str) -> str:
    try:
        secs = max(0, strtime_seconds(minimum_hour or "00:00"))
        return format_time(secs // 2)
    except Exception:
        return "00:00"


def _get_shift_rule_helpers():
    """Import shift rule helpers lazily to avoid attendance view circular imports."""

    from attendance.views.clock_in_out import _resolve_grace_time, get_shift_rules

    return get_shift_rules, _resolve_grace_time


def _resolve_shift_context(employee, attendance_date: date) -> ShiftContext:
    shift = getattr(getattr(employee, "employee_work_info", None), "shift_id", None)
    day = EmployeeShiftDay.objects.filter(day=attendance_date.strftime("%A").lower()).first()

    schedule = None
    shift_start_dt = None
    shift_end_dt = None
    check_in_window_start_dt = None
    check_in_window_end_dt = None
    check_out_window_start_dt = None
    check_out_window_end_dt = None
    minimum_hour = "00:00"
    grace_seconds = 0
    grace_out_seconds = 0
    grace_clock_in_type = "after"

    if shift and day:
        get_shift_rules, _resolve_grace_time = _get_shift_rule_helpers()
        try:
            minimum_hour, start_sec, end_sec = shift_schedule_today(day=day, shift=shift)
        except Exception:
            minimum_hour, start_sec, end_sec = "00:00", None, None
        rules = get_shift_rules(
            attendance_date,
            shift,
            day,
            start_time_sec=start_sec,
            end_time_sec=end_sec,
        )
        schedule = rules.get("schedule")
        shift_start_dt = _localize(rules.get("shift_start_dt"))
        shift_end_dt = _localize(rules.get("shift_end_dt"))
        check_in_window_start_dt = _localize(rules.get("check_in_window_start_dt"))
        check_in_window_end_dt = _localize(rules.get("check_in_window_end_dt"))
        check_out_window_start_dt = _localize(rules.get("check_out_window_start_dt"))
        check_out_window_end_dt = _localize(rules.get("check_out_window_end_dt"))
        grace_seconds = int(rules.get("grace_seconds") or 0)
        try:
            grace_obj = _resolve_grace_time(schedule, shift)
            if grace_obj and getattr(grace_obj, "allowed_clock_out", False):
                grace_out_seconds = int(getattr(grace_obj, "allowed_time_in_secs", 0) or 0)
            grace_clock_in_type = getattr(grace_obj, "clock_in_type", "after") or "after"
        except Exception:
            grace_out_seconds = 0
            grace_clock_in_type = "after"

    return ShiftContext(
        employee=employee,
        attendance_date=attendance_date,
        day=day,
        shift=shift,
        schedule=schedule,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
        check_in_window_start_dt=check_in_window_start_dt,
        check_in_window_end_dt=check_in_window_end_dt,
        check_out_window_start_dt=check_out_window_start_dt,
        check_out_window_end_dt=check_out_window_end_dt,
        minimum_hour=minimum_hour or "00:00",
        grace_seconds=grace_seconds,
        grace_out_seconds=grace_out_seconds,
        grace_clock_in_type=grace_clock_in_type,
    )


def _leave_kind_for_date(leave_request, attendance_date: date) -> Optional[str]:
    start_date = leave_request.start_date
    end_date = leave_request.end_date or leave_request.start_date
    if not (start_date <= attendance_date <= end_date):
        return None
    if start_date == end_date:
        return leave_request.start_date_breakdown or leave_request.end_date_breakdown or "full_day"
    if attendance_date == start_date:
        return leave_request.start_date_breakdown or "full_day"
    if attendance_date == end_date:
        return leave_request.end_date_breakdown or "full_day"
    return "full_day"


def _resolve_leave_context(employee, attendance_date: date, ctx: ShiftContext) -> LeaveContext:
    def _build_policy(kind: Optional[str]) -> AttendancePolicy:
        return build_attendance_policy(
            schedule=ctx.schedule,
            shift_start_dt=ctx.shift_start_dt,
            shift_end_dt=ctx.shift_end_dt,
            minimum_hour=ctx.minimum_hour,
            leave_kind=kind,
            check_in_cutoff_dt=ctx.check_in_window_end_dt,
        )

    if LeaveRequest is None:
        policy = _build_policy(None)
        return LeaveContext(None, None, policy.late_reference_dt, policy.nominal_policy_end_dt, policy.minimum_hour, policy=policy)

    leave_qs = LeaveRequest.objects.filter(employee_id=employee, status="approved").filter(
        start_date__lte=attendance_date + timedelta(days=1),
        end_date__gte=attendance_date - timedelta(days=1),
    ).order_by("-id")
    leave_request = leave_qs.first()
    if leave_breakdown_for_attendance_date is not None:
        try:
            kind = leave_breakdown_for_attendance_date(employee, attendance_date) or None
        except Exception:
            kind = None
    else:
        kind = None

    if not kind and leave_request:
        kind = _leave_kind_for_date(leave_request, attendance_date) or None

    if not kind:
        policy = _build_policy(None)
        return LeaveContext(None, None, policy.late_reference_dt, policy.nominal_policy_end_dt, policy.minimum_hour, policy=policy)

    policy = _build_policy(kind)
    return LeaveContext(
        leave_request,
        kind,
        policy.late_reference_dt,
        policy.nominal_policy_end_dt,
        policy.minimum_hour,
        policy=policy,
    )


def _approved_work_mode_request(employee, attendance_date: date) -> Optional[WorkModeRequest]:
    return (
        WorkModeRequest.objects.filter(
            employee_id=employee,
            start_date__lte=attendance_date,
            end_date__gte=attendance_date,
            status=WorkModeRequestStatus.APPROVED,
        )
        .order_by("-id")
        .first()
    )


def _approved_work_mode_request_for_session(employee, attendance_date: date, want: str) -> Optional[WorkModeRequest]:
    try:
        from attendance.services.work_type_request_rules import pick_relevant_request

        req = pick_relevant_request(employee, attendance_date, want)
        if req and getattr(req, "status", None) == WorkModeRequestStatus.APPROVED:
            return req
    except Exception:
        pass
    return None


def _normalize_employee_lookup(employee):
    try:
        if hasattr(employee, "pk") and getattr(employee, "pk") is not None:
            return employee
    except Exception:
        pass
    try:
        if hasattr(employee, "id") and getattr(employee, "id") is not None and not isinstance(getattr(employee, "id"), str):
            return employee
    except Exception:
        pass
    if isinstance(employee, int):
        return employee
    if isinstance(employee, str):
        text = employee.strip()
        if text.isdigit():
            return int(text)
        return None
    return employee


def _approved_attendance_correction_request_for_session(employee, attendance_date: date, want: str) -> Optional[AttendanceCorrectionRequest]:
    employee = _normalize_employee_lookup(employee)
    if employee in (None, ""):
        return None
    qs = AttendanceCorrectionRequest.objects.filter(
        employee_id=employee,
        attendance_date=attendance_date,
        status=AttendanceCorrectionRequestStatus.APPROVED,
    )
    if want == "in":
        qs = qs.filter(scope__in=[AttendanceCorrectionRequestScope.IN, AttendanceCorrectionRequestScope.FULL])
    else:
        qs = qs.filter(scope__in=[AttendanceCorrectionRequestScope.OUT, AttendanceCorrectionRequestScope.FULL])
    return qs.order_by("-approved_at", "-id").first()


def _latest_revoked_request(employee, attendance_date: date) -> Optional[WorkModeRequest]:
    return (
        WorkModeRequest.objects.filter(
            employee_id=employee,
            start_date__lte=attendance_date,
            end_date__gte=attendance_date,
            status=WorkModeRequestStatus.REVOKED,
        )
        .order_by("-id")
        .first()
    )


def _request_is_approved_request_override(attendance: Attendance, direction: str) -> bool:
    channel = (
        getattr(attendance, "attendance_clock_in_channel", None)
        if direction == AttendancePunchDirection.IN
        else getattr(attendance, "attendance_clock_out_channel", None)
    )
    if channel not in {AttendanceChannel.APPROVED_REQUEST, AttendanceChannel.CORRECTION_REQUEST}:
        return False

    # Legacy Attendance-based request overrides should only stay active while the
    # legacy request state itself indicates an approved/request-override record.
    # New AttendanceCorrectionRequest entities also reuse CORRECTION_REQUEST as the
    # final channel, but after revoke they must fall back to raw punches instead of
    # persisting the previous final value from Attendance.
    return bool(
        getattr(attendance, "is_validate_request_approved", False)
        or getattr(attendance, "requested_data", None)
    )


def _session_dt_from_attendance(attendance: Attendance, direction: str) -> Optional[datetime]:
    if direction == AttendancePunchDirection.IN:
        return _combine(getattr(attendance, "attendance_clock_in_date", None), getattr(attendance, "attendance_clock_in", None))
    return _combine(getattr(attendance, "attendance_clock_out_date", None), getattr(attendance, "attendance_clock_out", None))


def _session_mode_from_attendance(attendance: Attendance, direction: str) -> Optional[str]:
    if direction == AttendancePunchDirection.IN:
        return getattr(attendance, "attendance_clock_in_mode", None)
    return getattr(attendance, "attendance_clock_out_mode", None)


def _candidate_logs(employee, attendance_date: date, ctx: ShiftContext) -> Iterable[AttendancePunchingHistory]:
    has_shift_windows = any(
        [
            ctx.check_in_window_start_dt,
            ctx.check_out_window_end_dt,
            ctx.shift_start_dt,
            ctx.shift_end_dt,
        ]
    )
    if not has_shift_windows:
        return (
            AttendancePunchingHistory.objects.filter(employee_id=employee)
            .filter(
                Q(attendance_date=attendance_date)
                | Q(
                    punch_timestamp__gte=_localize(datetime.combine(attendance_date, time.min)),
                    punch_timestamp__lte=_localize(datetime.combine(attendance_date, time.max)),
                )
            )
            .order_by("punch_timestamp", "id")
        )

    start_dt = ctx.check_in_window_start_dt or ctx.shift_start_dt or _localize(datetime.combine(attendance_date, time.min))
    end_dt = ctx.check_out_window_end_dt or ctx.shift_end_dt or (_localize(datetime.combine(attendance_date, time.max)) + timedelta(days=1))
    start_dt = start_dt - timedelta(hours=6)
    end_dt = end_dt + timedelta(hours=6)
    return (
        AttendancePunchingHistory.objects.filter(employee_id=employee, punch_timestamp__gte=start_dt, punch_timestamp__lte=end_dt)
        .order_by("punch_timestamp", "id")
    )


def _in_window(log_dt: datetime, start_dt: Optional[datetime], end_dt: Optional[datetime]) -> bool:
    if start_dt is None or end_dt is None:
        return True
    log_dt = _localize(log_dt)
    if end_dt < start_dt:
        end_dt = end_dt + timedelta(days=1)
    if log_dt < start_dt and end_dt.date() > start_dt.date():
        log_dt = log_dt + timedelta(days=1)
    return start_dt <= log_dt <= end_dt


def _pick_raw_sessions(logs: list[AttendancePunchingHistory], ctx: ShiftContext):
    all_in = []
    valid_in = []
    invalid_in = []
    all_out = []
    valid_out = []
    invalid_out = []
    for log in logs:
        if getattr(log, "work_mode", None) == AttendanceWorkMode.WFH and getattr(log, "source", None) != "mobile":
            if log.punch_direction == AttendancePunchDirection.IN:
                invalid_in.append(log)
            elif log.punch_direction == AttendancePunchDirection.OUT:
                invalid_out.append(log)
            continue
        log_dt = _localize(log.punch_timestamp)
        if log.punch_direction == AttendancePunchDirection.IN:
            all_in.append(log)
            if _in_window(log_dt, ctx.check_in_window_start_dt, ctx.check_in_window_end_dt):
                valid_in.append(log)
            else:
                invalid_in.append(log)
        elif log.punch_direction == AttendancePunchDirection.OUT:
            all_out.append(log)
            if _in_window(log_dt, ctx.check_out_window_start_dt, ctx.check_out_window_end_dt):
                valid_out.append(log)
            else:
                invalid_out.append(log)

    all_in.sort(key=lambda x: (_localize(x.punch_timestamp), x.id))
    valid_in.sort(key=lambda x: (_localize(x.punch_timestamp), x.id))
    all_out.sort(key=lambda x: (_localize(x.punch_timestamp), x.id))
    valid_out.sort(key=lambda x: (_localize(x.punch_timestamp), x.id))
    return {
        "any_in": all_in[0] if all_in else None,
        "final_in": valid_in[0] if valid_in else None,
        "extra_in": valid_in[1:] if len(valid_in) > 1 else [],
        "invalid_in": invalid_in,
        "any_out": all_out[-1] if all_out else None,
        "final_out": valid_out[-1] if valid_out else None,
        "extra_out": valid_out[:-1] if len(valid_out) > 1 else [],
        "invalid_out": invalid_out,
    }


def _decision_status(log: AttendancePunchingHistory, *, accepted: bool, reason: str) -> str:
    if accepted:
        return "accepted"
    lower = (reason or "").lower()
    if "superseded" in lower:
        return "superseded"
    if "rejected" in lower or "outside" in lower or "invalid" in lower:
        return "invalid"
    return "not_accepted"


def _apply_punch_decisions(attendance: Attendance, logs: list[AttendancePunchingHistory], decisions: dict[int, tuple[bool, str]], source: str):
    for log in logs:
        accepted, reason = decisions.get(log.id, (False, "Ignored: not used in final attendance"))
        log.attendance_id = attendance
        log.attendance_date = attendance.attendance_date
        log.accepted_to_attendance = accepted
        log.reason = (reason or "-")[:255]
        if hasattr(log, "decision_status"):
            log.decision_status = _decision_status(log, accepted=accepted, reason=reason)
        if hasattr(log, "decision_source"):
            log.decision_source = source
        log.save(update_fields=[
            "attendance_id",
            "attendance_date",
            "accepted_to_attendance",
            "reason",
            *( ["decision_status"] if hasattr(log, "decision_status") else []),
            *( ["decision_source"] if hasattr(log, "decision_source") else []),
        ])


def _synchronize_canonical_punch_truth(
    attendance: Attendance,
    decisions: dict[int, tuple[bool, str]],
    source: str,
    *,
    logs: Optional[list[AttendancePunchingHistory]] = None,
    final_in_punch: Optional[AttendancePunchingHistory] = None,
    final_out_punch: Optional[AttendancePunchingHistory] = None,
):
    # When the attendance row is a real model instance, refresh canonical final
    # truth from DB. Some unit/integration tests use lightweight stubs that do
    # not implement refresh_from_db, so we gracefully fall back to in-memory
    # values in that case.
    refresher = getattr(attendance, "refresh_from_db", None)
    if callable(refresher):
        refresher(fields=[
            "attendance_date",
            "attendance_clock_in_punch",
            "attendance_clock_out_punch",
        ])

    canonical_pairs = []
    if getattr(attendance, "pk", None):
        final_in_punch_id = getattr(attendance, "attendance_clock_in_punch_id", None)
        final_out_punch_id = getattr(attendance, "attendance_clock_out_punch_id", None)
    else:
        final_in_punch_id = getattr(attendance, "attendance_clock_in_punch_id", None) or getattr(final_in_punch, "id", None)
        final_out_punch_id = getattr(attendance, "attendance_clock_out_punch_id", None) or getattr(final_out_punch, "id", None)
    if final_in_punch_id:
        canonical_pairs.append((final_in_punch_id, NOTE_FINAL_IN))
    if final_out_punch_id:
        canonical_pairs.append((final_out_punch_id, NOTE_FINAL_OUT))
    if not canonical_pairs:
        return

    canonical_map = {punch_id: reason for punch_id, reason in canonical_pairs}

    # Keep the in-memory decision map aligned with canonical Attendance truth.
    for punch_id, reason in canonical_pairs:
        decisions[punch_id] = (True, reason)

    # First sync any log objects already in memory (important for SimpleNamespace
    # / dataclass tests and for callers that keep references to punch objects).
    for log in logs or []:
        if getattr(log, "id", None) not in canonical_map:
            continue
        final_reason = canonical_map[log.id]
        setattr(log, "attendance_id", attendance)
        setattr(log, "attendance_date", getattr(attendance, "attendance_date", None))
        setattr(log, "accepted_to_attendance", True)
        setattr(log, "reason", (final_reason or "-")[:255])
        if hasattr(log, "decision_status"):
            setattr(log, "decision_status", "accepted")
        if hasattr(log, "decision_source"):
            setattr(log, "decision_source", source)
        saver = getattr(log, "save", None)
        if callable(saver):
            saver(update_fields=[
                "attendance_id",
                "attendance_date",
                "accepted_to_attendance",
                "reason",
                *( ["decision_status"] if hasattr(log, "decision_status") else []),
                *( ["decision_source"] if hasattr(log, "decision_source") else []),
            ])

    # Then sync canonical truth directly in the database, bypassing scoped
    # managers. We update by ID so the stored raw-punch flags always follow the
    # final Attendance truth even in multi-step recompute lifecycles.
    if getattr(attendance, "pk", None):
        for punch_id, final_reason in canonical_pairs:
            update_kwargs = {
                "attendance_id": attendance,
                "attendance_date": getattr(attendance, "attendance_date", None),
                "accepted_to_attendance": True,
                "reason": (final_reason or "-")[:255],
            }
            model = AttendancePunchingHistory
            if hasattr(model, "decision_status"):
                update_kwargs["decision_status"] = "accepted"
            if hasattr(model, "decision_source"):
                update_kwargs["decision_source"] = source
            AttendancePunchingHistory._base_manager.filter(id=punch_id).update(**update_kwargs)

def _set_late_early_rows(attendance: Attendance, late_minutes, early_minutes):
    attendance.late_come_early_out.filter(type="late_come").delete()
    attendance.late_come_early_out.filter(type="early_out").delete()
    if late_minutes > 0:
        AttendanceLateComeEarlyOut.objects.get_or_create(attendance_id=attendance, type="late_come")
    if early_minutes > 0:
        AttendanceLateComeEarlyOut.objects.get_or_create(attendance_id=attendance, type="early_out")


def _calculate_late_early(
    final_in_dt: Optional[datetime],
    final_out_dt: Optional[datetime],
    late_reference_dt: Optional[datetime],
    early_reference_dt: Optional[datetime],
    grace_seconds: int,
    grace_clock_in_type: str,
    *,
    apply_grace_to_late: bool = True,
):
    late_minutes = 0
    early_minutes = 0
    credit_seconds = 0

    final_in_dt = truncate_datetime_to_minute(final_in_dt)
    final_out_dt = truncate_datetime_to_minute(final_out_dt)

    if final_in_dt and late_reference_dt:
        if final_in_dt < late_reference_dt and grace_clock_in_type == "before_after":
            credit_seconds = int((late_reference_dt - final_in_dt).total_seconds())
        late_seconds = int((final_in_dt - late_reference_dt).total_seconds())
        if apply_grace_to_late:
            late_seconds = late_seconds - int(grace_seconds or 0)
        late_minutes = seconds_to_decimal_minutes(max(0, late_seconds))

    adjusted_end = early_reference_dt
    if adjusted_end and credit_seconds > 0:
        adjusted_end = adjusted_end - timedelta(seconds=credit_seconds)

    if final_out_dt and adjusted_end:
        early_seconds = int((adjusted_end - final_out_dt).total_seconds())
        early_minutes = seconds_to_decimal_minutes(max(0, early_seconds))

    return late_minutes, early_minutes


def _resolve_final_work_mode(
    employee,
    attendance_date: date,
    *,
    request_override_mode: Optional[str] = None,
    approved_work_request: Optional[WorkModeRequest] = None,
    accepted_in_punch: Optional[AttendancePunchingHistory] = None,
    accepted_out_punch: Optional[AttendancePunchingHistory] = None,
) -> str:
    """Resolve final attendance mode with audit-safe priority.

    Priority:
    1. approved attendance/request override mode
    2. approved work mode request
    3. accepted raw punch work_mode
    4. scheduled/default work type for the date
    5. WFO fallback only when business truth cannot be derived
    """

    if request_override_mode:
        return request_override_mode

    if approved_work_request and getattr(approved_work_request, "mode", None):
        return approved_work_request.mode

    for punch in (accepted_in_punch, accepted_out_punch):
        mode = getattr(punch, "work_mode", None)
        if mode:
            return mode

    from attendance.services.work_type_request_rules import resolve_biometric_work_mode

    resolved = resolve_biometric_work_mode(employee, attendance_date)
    return resolved.mode or AttendanceWorkMode.WFO


def _should_preserve_on_duty_raw_truth(req: Optional[WorkModeRequest]) -> bool:
    if not req or getattr(req, "mode", None) != AttendanceWorkMode.ON_DUTY:
        return False
    return getattr(req, "status", None) in {
        WorkModeRequestStatus.APPROVED,
        WorkModeRequestStatus.REVOKED,
    }


def _select_raw_truth_punch(raw: dict, direction: str, *, preserve_raw_truth: bool = False):
    final_key = "final_in" if direction == AttendancePunchDirection.IN else "final_out"
    any_key = "any_in" if direction == AttendancePunchDirection.IN else "any_out"
    selected = raw.get(final_key)
    if selected is None and preserve_raw_truth:
        selected = raw.get(any_key)
    return selected


def _minimum_for_final(ctx: ShiftContext, leave_ctx: LeaveContext, is_presence_only: bool) -> str:
    if is_presence_only:
        return "00:00"
    if leave_ctx.policy is not None:
        return leave_ctx.policy.minimum_hour or ctx.minimum_hour or "00:00"
    return leave_ctx.minimum_hour or ctx.minimum_hour or "00:00"


def _work_hours(policy: AttendancePolicy | None, final_in_dt: Optional[datetime], final_out_dt: Optional[datetime], *, is_presence_only: bool) -> str:
    if is_presence_only or not final_in_dt or not final_out_dt:
        return "00:00"
    if policy is not None:
        seconds = compute_worked_seconds(policy, final_in_dt=final_in_dt, final_out_dt=final_out_dt)
    else:
        seconds = int(max(0, (final_out_dt - final_in_dt).total_seconds()))
    return format_time(seconds)


def _sync_attendance_and_activity(attendance: Attendance, activity: AttendanceActivity, *, final_in_dt: Optional[datetime], final_out_dt: Optional[datetime], final_in_punch: Optional[AttendancePunchingHistory], final_out_punch: Optional[AttendancePunchingHistory], source: str, note: str, final_in_mode: str, final_out_mode: str, final_in_request: Optional[WorkModeRequest], final_out_request: Optional[WorkModeRequest], correction_in_override: bool = False, correction_out_override: bool = False, ctx: ShiftContext, minimum_hour: str, is_presence_only: bool, late_minutes: int, early_minutes: int, policy: AttendancePolicy | None = None):
    existing_in_channel = getattr(attendance, "attendance_clock_in_channel", None)
    existing_out_channel = getattr(attendance, "attendance_clock_out_channel", None)
    existing_in_mode = getattr(attendance, "attendance_clock_in_mode", None)
    existing_out_mode = getattr(attendance, "attendance_clock_out_mode", None)
    existing_in_image = getattr(attendance, "attendance_clock_in_image", None)
    existing_out_image = getattr(attendance, "attendance_clock_out_image", None)
    existing_in_location = getattr(attendance, "attendance_clock_in_location", None)
    existing_out_location = getattr(attendance, "attendance_clock_out_location", None)

    attendance.employee_id = ctx.employee
    attendance.attendance_date = ctx.attendance_date
    attendance.shift_id = ctx.shift
    attendance.attendance_day = ctx.day
    attendance.minimum_hour = minimum_hour
    attendance.is_presensi_only = is_presence_only
    attendance.work_mode_request_id = final_in_request if final_in_request and final_in_request == final_out_request else None
    attendance.in_related_work_type_request_id = getattr(final_in_request, "id", None) if hasattr(attendance, "in_related_work_type_request_id") else None
    attendance.out_related_work_type_request_id = getattr(final_out_request, "id", None) if hasattr(attendance, "out_related_work_type_request_id") else None
    if hasattr(attendance, "reconciliation_source"):
        attendance.reconciliation_source = source
    if hasattr(attendance, "reconciliation_note"):
        attendance.reconciliation_note = note
    if hasattr(attendance, "late_minutes"):
        attendance.late_minutes = late_minutes
    if hasattr(attendance, "early_out_minutes"):
        attendance.early_out_minutes = early_minutes

    attendance.attendance_clock_in_date = final_in_dt.date() if final_in_dt else None
    attendance.attendance_clock_in = final_in_dt.time().replace(microsecond=0) if final_in_dt else None
    attendance.attendance_clock_out_date = final_out_dt.date() if final_out_dt else None
    attendance.attendance_clock_out = final_out_dt.time().replace(microsecond=0) if final_out_dt else None

    if final_in_punch:
        attendance.attendance_clock_in_punch = final_in_punch
        attendance.attendance_clock_in_channel = AttendanceChannel.MOBILE if final_in_punch.source == "mobile" else AttendanceChannel.BIOMETRIC if final_in_punch.source == "biometric" else AttendanceChannel.API
        attendance.attendance_clock_in_image = final_in_punch.photo if getattr(final_in_punch, "photo", None) else None
        attendance.attendance_clock_in_location = getattr(final_in_punch, "location", None)
        attendance.attendance_clock_in_mode = final_in_mode
        attendance.in_attendance_status = AttendancePunchStatus.VALID
        attendance.in_attendance_reject_reason_code = None
    elif correction_in_override or _request_is_approved_request_override(attendance, AttendancePunchDirection.IN):
        attendance.attendance_clock_in_punch = None
        attendance.attendance_clock_in_channel = AttendanceChannel.CORRECTION_REQUEST
        attendance.attendance_clock_in_mode = final_in_mode
        attendance.attendance_clock_in_image = None
        attendance.attendance_clock_in_location = None
    else:
        attendance.attendance_clock_in_punch = None
        if not final_in_dt:
            attendance.attendance_clock_in_channel = None
            attendance.attendance_clock_in_mode = None
            attendance.attendance_clock_in_location = None
            attendance.attendance_clock_in_image = None

    if final_out_punch:
        attendance.attendance_clock_out_punch = final_out_punch
        attendance.attendance_clock_out_channel = AttendanceChannel.MOBILE if final_out_punch.source == "mobile" else AttendanceChannel.BIOMETRIC if final_out_punch.source == "biometric" else AttendanceChannel.API
        attendance.attendance_clock_out_image = final_out_punch.photo if getattr(final_out_punch, "photo", None) else None
        attendance.attendance_clock_out_location = getattr(final_out_punch, "location", None)
        attendance.attendance_clock_out_mode = final_out_mode
        attendance.out_attendance_status = AttendancePunchStatus.VALID
        attendance.out_attendance_reject_reason_code = None
    elif correction_out_override or _request_is_approved_request_override(attendance, AttendancePunchDirection.OUT):
        attendance.attendance_clock_out_punch = None
        attendance.attendance_clock_out_channel = AttendanceChannel.CORRECTION_REQUEST
        attendance.attendance_clock_out_mode = final_out_mode
        attendance.attendance_clock_out_image = None
        attendance.attendance_clock_out_location = None
    else:
        attendance.attendance_clock_out_punch = None
        if not final_out_dt:
            attendance.attendance_clock_out_channel = None
            attendance.attendance_clock_out_mode = None
            attendance.attendance_clock_out_location = None
            attendance.attendance_clock_out_image = None

    attendance.attendance_worked_hour = _work_hours(policy, final_in_dt, final_out_dt, is_presence_only=is_presence_only)
    attendance.attendance_validated = bool(final_in_dt or final_out_dt or note == NOTE_FULL_DAY_LEAVE)
    attendance.save()

    activity.employee_id = ctx.employee
    activity.attendance_date = ctx.attendance_date
    activity.shift_day = ctx.day
    activity.work_mode_request_id = final_in_request if final_in_request and final_in_request == final_out_request else (final_in_request or final_out_request)
    if hasattr(activity, "reconciliation_source"):
        activity.reconciliation_source = source
    if hasattr(activity, "reconciliation_note"):
        activity.reconciliation_note = note
    if hasattr(activity, "late_minutes"):
        activity.late_minutes = late_minutes
    if hasattr(activity, "early_out_minutes"):
        activity.early_out_minutes = early_minutes

    activity.clock_in_date = final_in_dt.date() if final_in_dt else None
    activity.clock_in = final_in_dt.time().replace(microsecond=0) if final_in_dt else None
    activity.in_datetime = final_in_dt
    activity.clock_out_date = final_out_dt.date() if final_out_dt else None
    activity.clock_out = final_out_dt.time().replace(microsecond=0) if final_out_dt else None
    activity.out_datetime = final_out_dt

    activity.clock_in_channel = attendance.attendance_clock_in_channel if final_in_dt else None
    activity.clock_in_image = attendance.attendance_clock_in_image if final_in_dt else None
    activity.clock_in_location = attendance.attendance_clock_in_location if final_in_dt else None
    activity.clock_in_mode = attendance.attendance_clock_in_mode if final_in_dt else None

    activity.clock_out_channel = attendance.attendance_clock_out_channel if final_out_dt else None
    activity.clock_out_image = attendance.attendance_clock_out_image if final_out_dt else None
    activity.clock_out_location = attendance.attendance_clock_out_location if final_out_dt else None
    activity.clock_out_mode = attendance.attendance_clock_out_mode if final_out_dt else None

    activity.save()


def _ensure_records(employee, attendance_date: date):
    attendance, _ = Attendance.objects.get_or_create(employee_id=employee, attendance_date=attendance_date)
    activity, _ = AttendanceActivity.objects.get_or_create(employee_id=employee, attendance_date=attendance_date)
    return attendance, activity


@transaction.atomic
def recompute_attendance(employee, attendance_date: date) -> ReconciliationResult | None:
    if not employee or not attendance_date:
        return None

    attendance, activity = _ensure_records(employee, attendance_date)
    ctx = _resolve_shift_context(employee, attendance_date)
    leave_ctx = _resolve_leave_context(employee, attendance_date, ctx)
    work_request = _approved_work_mode_request(employee, attendance_date)
    work_request_in = _approved_work_mode_request_for_session(employee, attendance_date, "in")
    work_request_out = _approved_work_mode_request_for_session(employee, attendance_date, "out")
    correction_request_in = _approved_attendance_correction_request_for_session(employee, attendance_date, "in")
    correction_request_out = _approved_attendance_correction_request_for_session(employee, attendance_date, "out")
    revoked_request = _latest_revoked_request(employee, attendance_date)
    logs = list(_candidate_logs(employee, attendance_date, ctx))
    raw = _pick_raw_sessions(logs, ctx)

    final_in_dt = None
    final_out_dt = None
    final_in_punch = None
    final_out_punch = None
    final_in_request = work_request_in
    final_out_request = work_request_out
    source = SOURCE_NORMAL
    note = "Present"
    final_in_mode = AttendanceWorkMode.WFO
    final_out_mode = AttendanceWorkMode.WFO
    is_presence_only = False
    request_override_in_mode = None
    request_override_out_mode = None
    grant_on_duty_in_final = False
    grant_on_duty_out_final = False

    if leave_ctx.is_full_day:
        source = SOURCE_LEAVE
        note = NOTE_FULL_DAY_LEAVE
    else:
        preserve_on_duty_in_raw_truth = (
            _should_preserve_on_duty_raw_truth(final_in_request)
            or _should_preserve_on_duty_raw_truth(revoked_request)
        )
        preserve_on_duty_out_raw_truth = (
            _should_preserve_on_duty_raw_truth(final_out_request)
            or _should_preserve_on_duty_raw_truth(revoked_request)
        )

        if correction_request_in is not None:
            final_in_dt = _localize(_combine(correction_request_in.requested_check_in_date, correction_request_in.requested_check_in_time))
            source = SOURCE_ATTENDANCE_REQUEST
            note = NOTE_APPROVED_ATTENDANCE_REQUEST
            final_in_request = None
        elif _request_is_approved_request_override(attendance, AttendancePunchDirection.IN):
            final_in_dt = _session_dt_from_attendance(attendance, AttendancePunchDirection.IN)
            source = SOURCE_ATTENDANCE_REQUEST
            note = NOTE_APPROVED_ATTENDANCE_REQUEST
            request_override_in_mode = _session_mode_from_attendance(attendance, AttendancePunchDirection.IN)
            final_in_request = None
        else:
            selected_in_punch = _select_raw_truth_punch(
                raw,
                AttendancePunchDirection.IN,
                preserve_raw_truth=preserve_on_duty_in_raw_truth,
            )
            if selected_in_punch is not None:
                final_in_punch = selected_in_punch
                final_in_dt = _localize(final_in_punch.punch_timestamp)

        if correction_request_out is not None:
            final_out_dt = _localize(_combine(correction_request_out.requested_check_out_date, correction_request_out.requested_check_out_time))
            source = SOURCE_ATTENDANCE_REQUEST
            note = NOTE_APPROVED_ATTENDANCE_REQUEST
            final_out_request = None
        elif _request_is_approved_request_override(attendance, AttendancePunchDirection.OUT):
            final_out_dt = _session_dt_from_attendance(attendance, AttendancePunchDirection.OUT)
            source = SOURCE_ATTENDANCE_REQUEST
            note = NOTE_APPROVED_ATTENDANCE_REQUEST
            request_override_out_mode = _session_mode_from_attendance(attendance, AttendancePunchDirection.OUT)
            final_out_request = None
        else:
            selected_out_punch = _select_raw_truth_punch(
                raw,
                AttendancePunchDirection.OUT,
                preserve_raw_truth=preserve_on_duty_out_raw_truth,
            )
            if selected_out_punch is not None:
                final_out_punch = selected_out_punch
                final_out_dt = _localize(final_out_punch.punch_timestamp)

        final_in_mode = _resolve_final_work_mode(
            employee,
            attendance_date,
            request_override_mode=request_override_in_mode,
            approved_work_request=final_in_request,
            accepted_in_punch=final_in_punch,
            accepted_out_punch=None,
        )
        final_out_mode = _resolve_final_work_mode(
            employee,
            attendance_date,
            request_override_mode=request_override_out_mode,
            approved_work_request=final_out_request,
            accepted_in_punch=None,
            accepted_out_punch=final_out_punch,
        )

        if leave_ctx.is_half_day:
            source = SOURCE_LEAVE if source == SOURCE_NORMAL else source
            note = NOTE_HALF_DAY_FIRST if leave_ctx.kind == "first_half" else NOTE_HALF_DAY_SECOND

        for session_req in [final_in_request, final_out_request]:
            if session_req and source != SOURCE_ATTENDANCE_REQUEST and session_req.mode == AttendanceWorkMode.WFA:
                source = SOURCE_WFA
                note = "WFA reconciled under normal attendance rules"
                break

        for want, session_req in (("in", final_in_request), ("out", final_out_request)):
            if not session_req or source == SOURCE_ATTENDANCE_REQUEST or session_req.mode != AttendanceWorkMode.ON_DUTY:
                continue
            resolver = getattr(session_req, "effective_document_status", None)
            document_status = resolver() if callable(resolver) else getattr(session_req, "document_status", None)
            if document_status == WorkModeRequestDocumentStatus.VERIFIED:
                if want == "in":
                    grant_on_duty_in_final = True
                else:
                    grant_on_duty_out_final = True
            elif document_status == WorkModeRequestDocumentStatus.REJECTED:
                source = SOURCE_NORMAL
                note = NOTE_ON_DUTY_NOT_GRANTED
            else:
                source = SOURCE_PROVISIONAL_ON_DUTY
                note = NOTE_ON_DUTY_PROVISIONAL

        if grant_on_duty_in_final or grant_on_duty_out_final:
            source = SOURCE_ON_DUTY
            note = NOTE_ON_DUTY_FINAL
            is_presence_only = bool(grant_on_duty_in_final and grant_on_duty_out_final)

        if revoked_request and not work_request and source == SOURCE_NORMAL:
            source = SOURCE_RECOMPUTED_AFTER_REVOKE
            note = NOTE_RECOMPUTED_AFTER_REVOKE

        if not final_in_dt and final_out_dt:
            note = NOTE_MISSING_IN if source == SOURCE_NORMAL else note
        elif final_in_dt and not final_out_dt:
            note = NOTE_MISSING_OUT if source == SOURCE_NORMAL else note

    policy = leave_ctx.policy or build_attendance_policy(
        schedule=ctx.schedule,
        shift_start_dt=ctx.shift_start_dt,
        shift_end_dt=ctx.shift_end_dt,
        minimum_hour=ctx.minimum_hour,
        leave_kind=leave_ctx.kind,
        check_in_cutoff_dt=ctx.check_in_window_end_dt,
    )
    minimum_hour = _minimum_for_final(ctx, leave_ctx, is_presence_only)
    late_minutes = 0
    early_minutes = 0

    if leave_ctx.is_full_day:
        late_minutes = 0
        early_minutes = 0
    else:
        use_nominal_policy_end_for_early_out = bool(
            preserve_on_duty_out_raw_truth and not grant_on_duty_out_final
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=final_in_dt,
            final_out_dt=final_out_dt,
            grace_seconds=ctx.grace_seconds,
            clock_in_type=ctx.grace_clock_in_type,
            is_presence_only=is_presence_only,
            early_out_grace_seconds=ctx.grace_out_seconds,
            use_nominal_policy_end_for_early_out=use_nominal_policy_end_for_early_out,
        )
        late_minutes = seconds_to_decimal_minutes(metrics.late_seconds)
        early_minutes = seconds_to_decimal_minutes(metrics.early_out_seconds)
        if grant_on_duty_in_final:
            late_minutes = 0
        if grant_on_duty_out_final:
            early_minutes = 0

    _sync_attendance_and_activity(
        attendance,
        activity,
        final_in_dt=final_in_dt,
        final_out_dt=final_out_dt,
        final_in_punch=final_in_punch,
        final_out_punch=final_out_punch,
        source=source,
        note=note,
        final_in_mode=final_in_mode,
        final_out_mode=final_out_mode,
        final_in_request=final_in_request,
        final_out_request=final_out_request,
        correction_in_override=bool(correction_request_in),
        correction_out_override=bool(correction_request_out),
        ctx=ctx,
        minimum_hour=minimum_hour,
        is_presence_only=is_presence_only,
        late_minutes=late_minutes,
        early_minutes=early_minutes,
        policy=policy,
    )
    _set_late_early_rows(attendance, late_minutes, early_minutes)

    decisions: dict[int, tuple[bool, str]] = {}
    if getattr(attendance, "pk", None):
        final_in_punch_id = getattr(attendance, "attendance_clock_in_punch_id", None)
        final_out_punch_id = getattr(attendance, "attendance_clock_out_punch_id", None)
    else:
        final_in_punch_id = getattr(attendance, "attendance_clock_in_punch_id", None) or getattr(final_in_punch, "id", None)
        final_out_punch_id = getattr(attendance, "attendance_clock_out_punch_id", None) or getattr(final_out_punch, "id", None)

    # The Attendance row is the canonical final truth. When a final punch id is
    # persisted there, force the in-memory decision map to accept that punch as
    # final even if earlier raw-selection branches classified it differently.
    if final_in_punch_id:
        decisions[final_in_punch_id] = (True, NOTE_FINAL_IN)
    if final_out_punch_id:
        decisions[final_out_punch_id] = (True, NOTE_FINAL_OUT)

    for log in logs:
        if leave_ctx.is_full_day:
            decisions[log.id] = (False, NOTE_IGNORED_FULL_DAY_LEAVE)
            continue

        if final_in_punch_id and log.id == final_in_punch_id:
            decisions[log.id] = (True, NOTE_FINAL_IN)
            continue
        if final_out_punch_id and log.id == final_out_punch_id:
            decisions[log.id] = (True, NOTE_FINAL_OUT)
            continue

        if log in raw.get("extra_in", []):
            decisions[log.id] = (False, NOTE_DUPLICATE_CHECKIN)
            continue
        if log in raw.get("extra_out", []):
            decisions[log.id] = (False, NOTE_SUPERSEDED_CHECKOUT)
            continue
        if log in raw.get("invalid_in", []):
            decisions[log.id] = (False, NOTE_INVALID_IN_WINDOW)
            continue
        if log in raw.get("invalid_out", []):
            decisions[log.id] = (False, NOTE_INVALID_OUT_WINDOW)
            continue
        if log.punch_direction in {AttendancePunchDirection.IN, AttendancePunchDirection.OUT} and source == SOURCE_ATTENDANCE_REQUEST:
            decisions[log.id] = (False, NOTE_NOT_USED_REQUEST.get(log.punch_direction, "Not used because final attendance came from approved request"))
            continue
        decisions[log.id] = (False, "Ignored: not used in final attendance")

    _apply_punch_decisions(attendance, logs, decisions, source)
    _synchronize_canonical_punch_truth(attendance, decisions, source, logs=logs, final_in_punch=final_in_punch, final_out_punch=final_out_punch)

    if leave_ctx.is_full_day and logs:
        for log in logs:
            log.attendance_id = attendance
            log.attendance_date = attendance.attendance_date
            log.accepted_to_attendance = False
            log.reason = NOTE_IGNORED_FULL_DAY_LEAVE
            if hasattr(log, "decision_status"):
                log.decision_status = _decision_status(log, accepted=False, reason=NOTE_IGNORED_FULL_DAY_LEAVE)
            if hasattr(log, "decision_source"):
                log.decision_source = source
            log.save(update_fields=[
                "attendance_id",
                "attendance_date",
                "accepted_to_attendance",
                "reason",
                *( ["decision_status"] if hasattr(log, "decision_status") else []),
                *( ["decision_source"] if hasattr(log, "decision_source") else []),
            ])

    return ReconciliationResult(attendance=attendance, activity=activity)


@transaction.atomic
def _enforce_canonical_punch_truth_for_attendance(attendance: Attendance):
    if not attendance or not getattr(attendance, 'pk', None):
        return
    source = getattr(attendance, 'reconciliation_source', SOURCE_NORMAL)
    canonical_pairs = []
    in_id = getattr(attendance, 'attendance_clock_in_punch_id', None)
    out_id = getattr(attendance, 'attendance_clock_out_punch_id', None)
    if in_id:
        canonical_pairs.append((in_id, NOTE_FINAL_IN))
    if out_id:
        canonical_pairs.append((out_id, NOTE_FINAL_OUT))
    for punch_id, reason in canonical_pairs:
        update_kwargs = {
            'attendance_id': attendance,
            'attendance_date': attendance.attendance_date,
            'accepted_to_attendance': True,
            'reason': (reason or '-')[:255],
            'decision_status': 'accepted',
            'decision_source': source,
        }
        AttendancePunchingHistory._base_manager.filter(id=punch_id).update(**update_kwargs)


@transaction.atomic
def recompute_attendance_range(employee, start_date: date, end_date: date, *, expand_for_overnight: bool = True):
    if not employee or not start_date or not end_date:
        return
    processed_start = start_date - timedelta(days=1) if expand_for_overnight else start_date
    processed_end = end_date + timedelta(days=1) if expand_for_overnight else end_date
    current = processed_start
    while current <= processed_end:
        recompute_attendance(employee, current)
        current = current + timedelta(days=1)

    # Second-pass canonical sync: after the full range recompute finishes, re-read
    # persisted Attendance rows and force final raw punch flags to match the
    # canonical attendance truth. This protects multi-step lifecycle flows
    # (reject/reopen/verify/revoke) from leaving the final OUT/IN punch flagged
    # as not accepted even though Attendance already points to it.
    employee_lookup = employee
    if not isinstance(employee_lookup, int):
        employee_lookup = getattr(employee_lookup, 'pk', None) or getattr(employee_lookup, 'id', employee_lookup)
    for attendance in Attendance.objects.filter(
        employee_id=employee_lookup,
        attendance_date__gte=processed_start,
        attendance_date__lte=processed_end,
    ):
        _enforce_canonical_punch_truth_for_attendance(attendance)
