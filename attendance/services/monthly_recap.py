"""attendance.services.monthly_recap

Compute rows for **Attendance → Attendances (Monthly Recap)**.

This service is used by the web view only (Django templates).
"""

from __future__ import annotations

import calendar
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from typing import Dict, Iterable, List, Optional, Tuple

from django.conf import settings
from django.db.models import Q
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)
from attendance.services.monthly_recap_note import NoteInputs, derive_note, seconds_to_hhmm
from attendance.services.work_type_request_rules import scheduled_attendance_mode
# NOTE: Do NOT import from attendance.views.clock_in_out at module import time.
# That module imports attendance.views.views, which imports this service.
# Import lazily inside build_employee_monthly_recap() to avoid circular imports.
from base.methods import is_holiday
from base.models import EmployeeShiftDay
from employee.models import Employee
from leave.models import LeaveRequest


def _month_range(month_yyyy_mm: str) -> Tuple[date, date]:
    """Parse YYYY-MM and return (first_day, last_day)."""
    y, m = month_yyyy_mm.split("-")
    year = int(y)
    month = int(m)
    first = date(year, month, 1)
    last = date(year, month, calendar.monthrange(year, month)[1])
    return first, last


def _iter_month_dates(first_day: date, last_day: date) -> Iterable[date]:
    cur = first_day
    while cur <= last_day:
        yield cur
        cur = cur + timedelta(days=1)


def _combine_dt(d: Optional[date], t, fallback_date: date) -> Optional[datetime]:
    if not t:
        return None
    use_date = d or fallback_date
    try:
        return datetime.combine(use_date, t)
    except Exception:
        return None


def _normalize_dt(dt_obj: Optional[datetime], tzinfo=None) -> Optional[datetime]:
    """Normalize datetimes to avoid naive/aware arithmetic errors.

    In Horilla we can get:
    - naive datetimes from datetime.combine(DateField, TimeField)
    - aware datetimes from DateTimeField / timezone utilities

    This function normalizes based on Django settings.USE_TZ.
    """

    if dt_obj is None:
        return None

    if getattr(settings, "USE_TZ", False):
        if timezone.is_aware(dt_obj):
            return timezone.localtime(dt_obj)
        tz = tzinfo or timezone.get_current_timezone()
        return timezone.make_aware(dt_obj, tz)

    # USE_TZ is False
    if timezone.is_aware(dt_obj):
        return timezone.make_naive(dt_obj, timezone.get_current_timezone())
    return dt_obj


def _format_punch(dt: Optional[datetime], attendance_date: date) -> str:
    if not dt:
        return "—"
    dt_local = _normalize_dt(dt)
    suffix = " D+1" if dt_local.date() > attendance_date else ""
    return dt_local.strftime("%H:%M") + suffix


def _work_mode_label(mode: str) -> str:
    if mode == AttendanceWorkMode.ON_DUTY:
        return "On Duty"
    if mode == AttendanceWorkMode.WFA:
        return "WFA"
    return "WFO"


def _pick_best_attendance(att_list: List[Attendance]) -> Optional[Attendance]:
    if not att_list:
        return None
    # Prefer validated/approved corrections as they represent final data.
    validated = [a for a in att_list if getattr(a, "attendance_validated", False)]
    if validated:
        return sorted(validated, key=lambda x: x.id)[-1]
    approved = [a for a in att_list if getattr(a, "is_validate_request_approved", False)]
    if approved:
        return sorted(approved, key=lambda x: x.id)[-1]
    return sorted(att_list, key=lambda x: x.id)[-1]


def _resolve_effective_mode_approved(
    *,
    requests: List[WorkModeRequest],
    attendance_date: date,
    want: str,
    baseline_mode: str,
) -> str:
    """Effective mode for IN/OUT using APPROVED only.

    Priority: IN/OUT request (APPROVED) > FULL request (APPROVED) > baseline.
    """
    if want not in ("in", "out"):
        return baseline_mode

    scope_first = WorkModeRequestScope.IN if want == "in" else WorkModeRequestScope.OUT

    def _covers(req: WorkModeRequest) -> bool:
        return req.start_date <= attendance_date <= req.end_date

    approved = [r for r in requests if r.status == WorkModeRequestStatus.APPROVED and _covers(r)]
    approved.sort(key=lambda r: r.id, reverse=True)

    for r in approved:
        if r.scope == scope_first:
            return r.mode

    for r in approved:
        if r.scope == WorkModeRequestScope.FULL:
            return r.mode

    return baseline_mode


def _pending_on_duty_suffixes(
    *,
    requests: List[WorkModeRequest],
    attendance_date: date,
) -> List[str]:
    """Only for NOTE suffix (does not affect calculations)."""
    suffixes: List[str] = []
    pending_statuses = {WorkModeRequestStatus.PENDING, WorkModeRequestStatus.WAITING_FOR_APPROVAL}

    def _covers(req: WorkModeRequest) -> bool:
        return req.start_date <= attendance_date <= req.end_date

    pending = [
        r
        for r in requests
        if r.mode == AttendanceWorkMode.ON_DUTY
        and r.status in pending_statuses
        and _covers(r)
    ]
    # Newest first
    pending.sort(key=lambda r: r.id, reverse=True)

    # IN
    if any(r.scope in (WorkModeRequestScope.IN, WorkModeRequestScope.FULL) for r in pending):
        suffixes.append("ON DUTY IN PENDING")
    # OUT
    if any(r.scope in (WorkModeRequestScope.OUT, WorkModeRequestScope.FULL) for r in pending):
        suffixes.append("ON DUTY OUT PENDING")

    return suffixes


@dataclass
class MonthlyRecapRow:
    no: int
    attendance_date: date
    shift_information: str
    check_in: str
    check_out: str
    work_type: str
    late: str
    early_out: str
    note: str
    is_off: bool = False


def build_employee_monthly_recap(*, employee: Employee, month_yyyy_mm: str) -> List[MonthlyRecapRow]:
    first_day, last_day = _month_range(month_yyyy_mm)

    # Lazy import to avoid circular imports during Django initialization.
    # attendance.views.clock_in_out imports attendance.views.views, which imports this module.
    from attendance.views.clock_in_out import get_shift_rules, _resolve_grace_time

    # Prefetch Attendance + Activity
    att_qs = Attendance.objects.filter(
        employee_id=employee,
        attendance_date__range=(first_day, last_day),
    ).order_by("attendance_date", "id")
    act_qs = AttendanceActivity.objects.filter(
        employee_id=employee,
        attendance_date__range=(first_day, last_day),
    ).order_by("attendance_date", "id")

    # Requests for the whole month (include pending for NOTE suffix)
    req_qs = (
        WorkModeRequest.objects.filter(
            employee_id=employee,
            start_date__lte=last_day,
            end_date__gte=first_day,
        )
        .exclude(status__in=[WorkModeRequestStatus.REJECTED, WorkModeRequestStatus.CANCELED])
        .order_by("-id")
    )
    requests = list(req_qs)

    # Leave dates set (approved only)
    leave_qs = LeaveRequest.objects.filter(
        employee_id=employee,
        status="approved",
        start_date__lte=last_day,
        end_date__gte=first_day,
    )
    leave_dates: set[date] = set()
    for lr in leave_qs:
        sd = lr.start_date
        ed = lr.end_date or lr.start_date
        cur = sd
        while cur <= ed:
            if first_day <= cur <= last_day:
                leave_dates.add(cur)
            cur = cur + timedelta(days=1)

    # Shift day map (monday..sunday)
    day_objs = {d.day: d for d in EmployeeShiftDay.objects.all()}

    # Group attendance/activity by date
    att_by_date: Dict[date, List[Attendance]] = {}
    for a in att_qs:
        att_by_date.setdefault(a.attendance_date, []).append(a)

    act_by_date: Dict[date, List[AttendanceActivity]] = {}
    for ac in act_qs:
        act_by_date.setdefault(ac.attendance_date, []).append(ac)

    rows: List[MonthlyRecapRow] = []
    i = 1
    for d in _iter_month_dates(first_day, last_day):
        holiday_obj = is_holiday(d)
        is_leave = d in leave_dates
        is_off = bool(holiday_obj) or is_leave

        # OFF override
        if is_off:
            shift_info = "On Leave" if is_leave else "Holiday/Off"
            note = derive_note(NoteInputs(is_off=True, off_kind="leave" if is_leave else "holiday"))
            rows.append(
                MonthlyRecapRow(
                    no=i,
                    attendance_date=d,
                    shift_information=shift_info,
                    check_in="—",
                    check_out="—",
                    work_type="—",
                    late="00:00",
                    early_out="00:00",
                    note=note,
                    is_off=True,
                )
            )
            i += 1
            continue

        att_list = att_by_date.get(d, [])
        act_list = act_by_date.get(d, [])
        best_att = _pick_best_attendance(att_list)

        # Merge punches from all sources
        in_dts: List[datetime] = []
        out_dts: List[datetime] = []

        for a in att_list:
            dt_in = _combine_dt(getattr(a, "attendance_clock_in_date", None), getattr(a, "attendance_clock_in", None), a.attendance_date)
            if dt_in:
                in_dts.append(_normalize_dt(dt_in))
            dt_out = _combine_dt(getattr(a, "attendance_clock_out_date", None), getattr(a, "attendance_clock_out", None), a.attendance_date)
            if dt_out:
                out_dts.append(_normalize_dt(dt_out))

        for ac in act_list:
            dt_in = getattr(ac, "in_datetime", None) or _combine_dt(getattr(ac, "clock_in_date", None), getattr(ac, "clock_in", None), ac.attendance_date)
            if dt_in:
                in_dts.append(_normalize_dt(dt_in))
            dt_out = getattr(ac, "out_datetime", None) or _combine_dt(getattr(ac, "clock_out_date", None), getattr(ac, "clock_out", None), ac.attendance_date)
            if dt_out:
                out_dts.append(_normalize_dt(dt_out))

        final_in_dt = min(in_dts) if in_dts else None
        final_out_dt = max(out_dts) if out_dts else None

        # Shift + rules
        shift = None
        try:
            shift = getattr(best_att, "shift_id", None) if best_att else None
        except Exception:
            shift = None
        if shift is None:
            shift = getattr(getattr(employee, "employee_work_info", None), "shift_id", None)

        weekday_key = d.strftime("%A").lower()
        day_obj = day_objs.get(weekday_key)

        rules = get_shift_rules(d, shift, day_obj)
        shift_start_dt = rules.get("shift_start_dt")
        shift_end_dt = rules.get("shift_end_dt")
        cutoff_in_dt = rules.get("cutoff_in_dt") or rules.get("check_in_window_end_dt")
        grace_in_sec = int(rules.get("grace_seconds") or 0)

        # Ensure all datetimes are comparable (avoid naive/aware subtraction errors)
        tzinfo = None
        for cand in (shift_start_dt, shift_end_dt, cutoff_in_dt, final_in_dt, final_out_dt):
            if cand and timezone.is_aware(cand):
                tzinfo = cand.tzinfo
                break
        shift_start_dt = _normalize_dt(shift_start_dt, tzinfo)
        shift_end_dt = _normalize_dt(shift_end_dt, tzinfo)
        cutoff_in_dt = _normalize_dt(cutoff_in_dt, tzinfo)
        final_in_dt = _normalize_dt(final_in_dt, tzinfo)
        final_out_dt = _normalize_dt(final_out_dt, tzinfo)

        grace_out_sec = 0
        try:
            grace_time = _resolve_grace_time(rules.get("schedule"), shift)
            if grace_time and getattr(grace_time, "allowed_clock_out", False):
                grace_out_sec = int(getattr(grace_time, "allowed_time_in_secs", 0) or 0)
        except Exception:
            grace_out_sec = 0

        # Baseline mode from WorkType name (schedule resolver already handles fallback)
        baseline_mode = scheduled_attendance_mode(employee, d)
        # If Attendance has an explicit work_type_id, try to infer from that (override schedule)
        if best_att and getattr(best_att, "work_type_id", None):
            try:
                wt_name = getattr(best_att.work_type_id, "work_type", "") or ""
                # Reuse scheduled_attendance_mode normalizer by creating a shadow employee isn't worth it.
                # We'll do a light inference.
                n = wt_name.strip().lower().replace("-", " ").replace("_", " ")
                if "on duty" in n or "onduty" in n:
                    baseline_mode = AttendanceWorkMode.ON_DUTY
                elif "wfa" in n or "work from anywhere" in n or "remote" in n:
                    baseline_mode = AttendanceWorkMode.WFA
                elif "wfo" in n or "office" in n:
                    baseline_mode = AttendanceWorkMode.WFO
            except Exception:
                pass

        eff_in_mode = _resolve_effective_mode_approved(
            requests=requests,
            attendance_date=d,
            want="in",
            baseline_mode=baseline_mode,
        )
        eff_out_mode = _resolve_effective_mode_approved(
            requests=requests,
            attendance_date=d,
            want="out",
            baseline_mode=baseline_mode,
        )

        # Work type display: single value if same, else IN/OUT.
        if eff_in_mode == eff_out_mode:
            work_type_disp = _work_mode_label(eff_in_mode)
        else:
            work_type_disp = f"IN: {_work_mode_label(eff_in_mode)}<br>OUT: {_work_mode_label(eff_out_mode)}"

        # Late/Early computation
        late_sec = 0.0
        early_sec = 0.0

        if shift_start_dt and cutoff_in_dt:
            if final_in_dt:
                if eff_in_mode == AttendanceWorkMode.ON_DUTY:
                    late_sec = 0.0
                else:
                    ref = shift_start_dt + timedelta(seconds=grace_in_sec)
                    late_sec = max(0.0, (final_in_dt - ref).total_seconds())
            else:
                late_sec = max(0.0, (cutoff_in_dt - shift_start_dt).total_seconds())

        if shift_end_dt and cutoff_in_dt:
            if final_out_dt:
                if eff_out_mode == AttendanceWorkMode.ON_DUTY:
                    early_sec = 0.0
                else:
                    ref = shift_end_dt - timedelta(seconds=grace_out_sec)
                    early_sec = max(0.0, (ref - final_out_dt).total_seconds())
            else:
                early_sec = max(0.0, (shift_end_dt - cutoff_in_dt).total_seconds())

        late_txt = seconds_to_hhmm(late_sec)
        early_txt = seconds_to_hhmm(early_sec)

        # Shift information (simple: Start - End)
        shift_info = "—"
        try:
            st = rules.get("start_time")
            et = rules.get("end_time")
            if st and et:
                shift_info = f"{st.strftime('%H:%M')} - {et.strftime('%H:%M')}"
        except Exception:
            shift_info = "—"

        # Pending suffix + correction pending note
        pending_suffixes = _pending_on_duty_suffixes(requests=requests, attendance_date=d)
        correction_pending = bool(
            best_att
            and getattr(best_att, "is_validate_request", False)
            and not getattr(best_att, "is_validate_request_approved", False)
        )

        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=final_in_dt is not None,
                has_check_out=final_out_dt is not None,
                late_seconds=late_sec,
                early_out_seconds=early_sec,
                pending_suffixes=pending_suffixes,
                correction_pending=correction_pending,
            )
        )

        rows.append(
            MonthlyRecapRow(
                no=i,
                attendance_date=d,
                shift_information=shift_info,
                check_in=_format_punch(final_in_dt, d),
                check_out=_format_punch(final_out_dt, d),
                work_type=work_type_disp,
                late=late_txt,
                early_out=early_txt,
                note=note,
                is_off=False,
            )
        )
        i += 1

    return rows
