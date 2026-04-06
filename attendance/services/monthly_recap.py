"""attendance.services.monthly_recap

Compute rows for **Attendance → Attendances (Monthly Recap)**.

This service is shared by the web view and API endpoint.
"""

from __future__ import annotations

import calendar
from dataclasses import dataclass
from datetime import date, datetime, time, timedelta
from decimal import Decimal
from typing import Dict, Iterable, List, Optional, Set, Tuple

from django.conf import settings
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestDocumentStatus,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)
from attendance.services.attendance_correction_scope_rules import (
    get_approved_scopes,
    get_current_scope,
    infer_scope_from_values,
    load_requested_data,
    scope_to_sessions,
)
from attendance.services.final_session_resolution import (
    APPROVED_REQUEST_CHANNEL,
    is_approved_request_channel,
    resolve_final_session,
)
from attendance.services.month_params import require_month_yyyy_mm
from attendance.services.monthly_recap_note import (
    NoteInputs,
    derive_note,
    localize_on_duty_work_type,
    seconds_to_hhmm,
)
from attendance.services.canonical_attendance_policy import (
    build_attendance_policy,
    coerce_non_negative_decimal,
    compute_attendance_metrics,
    format_decimal_minutes,
    seconds_to_decimal_minutes,
)
from attendance.services.work_type_request_rules import is_active_work_mode_request_status, scheduled_attendance_mode
# NOTE: Do NOT import from attendance.views.clock_in_out at module import time.
# That module imports attendance.views.views, which imports this service.
# Import lazily inside build_employee_monthly_recap() to avoid circular imports.
from base.methods import is_holiday
from base.models import EmployeeShiftDay
from employee.models import Employee
from leave.models import LeaveRequest


def _month_range(month_yyyy_mm: str) -> Tuple[date, date]:
    """Parse YYYY-MM and return (first_day, last_day)."""
    month_yyyy_mm = require_month_yyyy_mm(month_yyyy_mm)
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
    """Normalize datetimes to avoid naive/aware arithmetic errors."""

    if dt_obj is None:
        return None

    if getattr(settings, "USE_TZ", False):
        if timezone.is_aware(dt_obj):
            return timezone.localtime(dt_obj)
        tz = tzinfo or timezone.get_current_timezone()
        return timezone.make_aware(dt_obj, tz)

    if timezone.is_aware(dt_obj):
        return timezone.make_naive(dt_obj, timezone.get_current_timezone())
    return dt_obj


def _format_punch(dt: Optional[datetime], attendance_date: date) -> str:
    if not dt:
        return "-"
    dt_local = _normalize_dt(dt)
    suffix = " D+1" if dt_local.date() > attendance_date else ""
    return dt_local.strftime("%H:%M") + suffix

def _localize_leave_session_label(kind: str, language: str) -> str:
    lang = (language or "en").lower()
    labels = {
        "full": "Cuti" if lang.startswith("id") else "On Leave",
        "in": "Cuti Setengah Hari (Awal)" if lang.startswith("id") else "Half Day Leave (Check-In)",
        "out": "Cuti Setengah Hari (Akhir)" if lang.startswith("id") else "Half Day Leave (Check-Out)",
    }
    return labels[kind]


def _approved_leave_coverage(leave_qs, first_day: date, last_day: date) -> Dict[date, Dict[str, object]]:
    coverage: Dict[date, Dict[str, object]] = {}
    for lr in leave_qs:
        sd = lr.start_date
        ed = lr.end_date or lr.start_date
        cur = sd
        while cur <= ed:
            if first_day <= cur <= last_day:
                info = coverage.setdefault(
                    cur,
                    {
                        "full_day": False,
                        "first_half": False,
                        "second_half": False,
                        "breakdown": None,
                        "leave_request": None,
                    },
                )
                if sd == ed:
                    breakdown = lr.start_date_breakdown or lr.end_date_breakdown or "full_day"
                elif cur == sd:
                    breakdown = lr.start_date_breakdown or "full_day"
                elif cur == ed:
                    breakdown = lr.end_date_breakdown or "full_day"
                else:
                    breakdown = "full_day"

                if breakdown == "full_day":
                    info.update(
                        {
                            "full_day": True,
                            "first_half": False,
                            "second_half": False,
                            "breakdown": "full_day",
                            "leave_request": lr,
                        }
                    )
                elif not info.get("full_day") and breakdown == "first_half":
                    info.update(
                        {
                            "first_half": True,
                            "second_half": False,
                            "breakdown": "first_half",
                            "leave_request": lr,
                        }
                    )
                elif not info.get("full_day") and breakdown == "second_half":
                    info.update(
                        {
                            "first_half": False,
                            "second_half": True,
                            "breakdown": "second_half",
                            "leave_request": lr,
                        }
                    )
            cur = cur + timedelta(days=1)
    return coverage


def _localize_half_day_leave_note(kind: Optional[str], language: str) -> str:
    lang = (language or "en").lower()
    if kind == "first_half":
        return "Approved First Half Leave" if not lang.startswith("id") else "Cuti Setengah Hari Pagi Disetujui"
    if kind == "second_half":
        return "Approved Second Half Leave" if not lang.startswith("id") else "Cuti Setengah Hari Siang Disetujui"
    return "Approved Leave" if not lang.startswith("id") else "Cuti Disetujui"


def _time_to_shift_instance_dt(
    threshold_time: Optional[time],
    *,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
    tzinfo=None,
) -> Optional[datetime]:
    if not (threshold_time and shift_start_dt and shift_end_dt):
        return None

    candidate = datetime.combine(shift_start_dt.date(), threshold_time)
    candidate = _normalize_dt(candidate, tzinfo)
    if not candidate:
        return None

    if candidate < shift_start_dt and shift_end_dt.date() > shift_start_dt.date():
        candidate = candidate + timedelta(days=1)

    if candidate < shift_start_dt or candidate > shift_end_dt:
        return None
    return candidate


def _localize_shift_information(text: str, language: str) -> str:
    """Localize only the *phrases* inside the Shift Information string."""
    if not text:
        return text
    lang = (language or "en").lower()
    if not lang.startswith("id"):
        return text
    return (
        text.replace("Flexi In", "Waktu Fleksibel").replace("Flex In", "Waktu Fleksibel")
        .replace("Holiday/Off", "Libur")
        .replace("Holiday / Off", "Libur")
        .replace("Holiday", "Libur")
        .replace("On Leave", "Cuti")
    )


def _localize_work_type(text: str, language: str) -> str:
    """Translate Work Type values for ON DUTY only (Indonesian)."""
    return localize_on_duty_work_type(text, language=language)


def _is_pending_create_request_source(attendance) -> bool:
    """Pending create_request rows store requested times in Attendance fields.

    Those values are not actual/approved punches yet, so they must never be used
    as Check In / Check Out candidates in the monthly recap.

    Important: some legacy / inconsistent rows may have empty or unparsable
    ``requested_data`` even though the request is still a pending create_request.
    We must still exclude their raw times from the final recap.
    """

    return bool(
        attendance
        and getattr(attendance, "is_validate_request", False)
        and getattr(attendance, "request_type", "") == "create_request"
    )


def _linked_work_mode_request_status(obj, request_status_by_id: Dict[int, str], *, session: str) -> Optional[str]:
    """Return linked WorkModeRequest status for IN/OUT punch sources if available."""

    if not obj:
        return None

    req_id = None
    session_norm = (session or "").upper()

    if session_norm == "IN":
        req_id = getattr(obj, "in_related_work_type_request_id", None)
    elif session_norm == "OUT":
        req_id = getattr(obj, "out_related_work_type_request_id", None)

    if not req_id:
        linked = getattr(obj, "work_mode_request_id", None)
        req_id = getattr(linked, "id", None) or getattr(obj, "work_mode_request_id_id", None)

    if not req_id:
        return None

    return request_status_by_id.get(req_id)


def _should_use_raw_punch_source(obj, request_status_by_id: Dict[int, str], *, session: str) -> bool:
    """Only actual / approved punch sources may contribute to final IN/OUT values."""

    if _is_pending_create_request_source(obj):
        return False

    linked_status = _linked_work_mode_request_status(obj, request_status_by_id, session=session)
    if linked_status and linked_status != WorkModeRequestStatus.APPROVED:
        return False

    return True


def _session_channel(obj, session: str) -> Optional[str]:
    if not obj:
        return None

    session_norm = (session or "IN").upper()
    if session_norm == "IN":
        if hasattr(obj, "attendance_clock_in_channel"):
            return getattr(obj, "attendance_clock_in_channel", None)
        return getattr(obj, "clock_in_channel", None)

    if hasattr(obj, "attendance_clock_out_channel"):
        return getattr(obj, "attendance_clock_out_channel", None)
    return getattr(obj, "clock_out_channel", None)


def _session_dt(obj, session: str, attendance_date: date) -> Optional[datetime]:
    session_norm = (session or "IN").upper()
    if session_norm == "IN":
        if hasattr(obj, "attendance_clock_in") or hasattr(obj, "attendance_clock_in_date"):
            return _combine_dt(
                getattr(obj, "attendance_clock_in_date", None),
                getattr(obj, "attendance_clock_in", None),
                attendance_date,
            )
        return getattr(obj, "in_datetime", None) or _combine_dt(
            getattr(obj, "clock_in_date", None),
            getattr(obj, "clock_in", None),
            attendance_date,
        )

    if hasattr(obj, "attendance_clock_out") or hasattr(obj, "attendance_clock_out_date"):
        return _combine_dt(
            getattr(obj, "attendance_clock_out_date", None),
            getattr(obj, "attendance_clock_out", None),
            attendance_date,
        )
    return getattr(obj, "out_datetime", None) or _combine_dt(
        getattr(obj, "clock_out_date", None),
        getattr(obj, "clock_out", None),
        attendance_date,
    )


def _legacy_approved_request_dt(attendance: Attendance, session: str, attendance_date: date) -> Optional[datetime]:
    if not attendance or not getattr(attendance, "is_validate_request_approved", False):
        return None

    data = load_requested_data(getattr(attendance, "requested_data", None)) or {}
    scope = (get_current_scope(data) or infer_scope_from_values(data) or "").lower()
    sessions = {s.lower() for s in scope_to_sessions(scope)} if scope else set()
    want = (session or "IN").lower()
    if want not in sessions:
        return None

    if want == "in":
        return _combine_dt(
            _parse_date_like(data.get("attendance_clock_in_date"), attendance_date),
            data.get("attendance_clock_in"),
            attendance_date,
        )
    return _combine_dt(
        _parse_date_like(data.get("attendance_clock_out_date"), attendance_date),
        data.get("attendance_clock_out"),
        attendance_date,
    )


def _approved_request_dt(
    *,
    attendances: List[Attendance],
    activities: List[AttendanceActivity],
    session: str,
    attendance_date: date,
    tzinfo=None,
) -> Optional[datetime]:
    session_norm = (session or "IN").upper()

    for obj in sorted(attendances, key=lambda x: x.id, reverse=True):
        if _session_channel(obj, session_norm) and is_approved_request_channel(_session_channel(obj, session_norm)):
            dt_obj = _session_dt(obj, session_norm, attendance_date)
            if dt_obj:
                return _normalize_dt(dt_obj, tzinfo)

    for obj in sorted(activities, key=lambda x: x.id, reverse=True):
        if _session_channel(obj, session_norm) and is_approved_request_channel(_session_channel(obj, session_norm)):
            dt_obj = _session_dt(obj, session_norm, attendance_date)
            if dt_obj:
                return _normalize_dt(dt_obj, tzinfo)

    for obj in sorted(attendances, key=lambda x: x.id, reverse=True):
        dt_obj = _legacy_approved_request_dt(obj, session_norm, attendance_date)
        if dt_obj:
            return _normalize_dt(dt_obj, tzinfo)

    return None


def _effective_document_status_safe(req) -> Optional[str]:
    if not req:
        return None
    resolver = getattr(req, "effective_document_status", None)
    if callable(resolver):
        try:
            return resolver()
        except Exception:
            return getattr(req, "document_status", None)
    return getattr(req, "document_status", None)


def _resolve_effective_request_approved(
    *,
    requests: List[WorkModeRequest],
    attendance_date: date,
    want: str,
) -> Optional[WorkModeRequest]:
    """Approved WorkModeRequest covering the target session, newest first."""

    if want not in ("in", "out"):
        return None

    scope_first = WorkModeRequestScope.IN if want == "in" else WorkModeRequestScope.OUT

    def _covers(req: WorkModeRequest) -> bool:
        return req.start_date <= attendance_date <= req.end_date

    approved = [r for r in requests if r.status == WorkModeRequestStatus.APPROVED and _covers(r)]
    approved.sort(key=lambda r: r.id, reverse=True)

    for r in approved:
        if r.scope == scope_first:
            return r

    for r in approved:
        if r.scope == WorkModeRequestScope.FULL:
            return r

    return None


def _session_on_duty_benefit_active(*, mode: str, request_obj, final_dt: Optional[datetime]) -> bool:
    """Return True only when ON Duty benefit should neutralize late/early for that session."""

    if mode != AttendanceWorkMode.ON_DUTY or final_dt is None:
        return False

    if request_obj is None:
        return True

    if getattr(request_obj, "status", None) != WorkModeRequestStatus.APPROVED:
        return False

    return _effective_document_status_safe(request_obj) == WorkModeRequestDocumentStatus.VERIFIED


def _compose_work_type_display(display_in_mode: str, display_out_mode: str) -> str:
    if display_in_mode == AttendanceWorkMode.ON_DUTY and display_out_mode == AttendanceWorkMode.ON_DUTY:
        return "On Duty FULL"
    if display_in_mode == display_out_mode:
        return _work_mode_label(display_in_mode)
    return f"IN: {_work_mode_label(display_in_mode)}<br>OUT: {_work_mode_label(display_out_mode)}"


def _work_mode_label(mode: str) -> str:
    if mode == AttendanceWorkMode.ON_DUTY:
        return "On Duty"
    if mode == AttendanceWorkMode.WFA:
        return "WFA"
    if mode == AttendanceWorkMode.WFH:
        return "WFH"
    return "WFO"


def _normalize_work_mode(mode: Optional[str]) -> Optional[str]:
    raw = (mode or "").strip().lower().replace("-", " ").replace("_", " ")
    if not raw:
        return None
    if raw in {"on duty", "onduty"}:
        return AttendanceWorkMode.ON_DUTY
    if raw in {"wfh", "work from home", "home"}:
        return AttendanceWorkMode.WFH
    if raw in {"wfa", "work from anywhere", "remote"}:
        return AttendanceWorkMode.WFA
    if raw in {"wfo", "office"}:
        return AttendanceWorkMode.WFO
    return None


def _mode_from_work_type_obj(work_type_obj) -> Optional[str]:
    if not work_type_obj:
        return None
    return _normalize_work_mode(getattr(work_type_obj, "work_type", None))


def _attendance_level_mode(attendance) -> Optional[str]:
    if not attendance:
        return None
    return _mode_from_work_type_obj(getattr(attendance, "work_type_id", None))


def _session_mode(obj, session: str) -> Optional[str]:
    if not obj:
        return None
    session_norm = (session or "IN").upper()
    if session_norm == "IN":
        return _normalize_work_mode(
            getattr(obj, "attendance_clock_in_mode", None)
            or getattr(obj, "clock_in_mode", None)
        )
    return _normalize_work_mode(
        getattr(obj, "attendance_clock_out_mode", None)
        or getattr(obj, "clock_out_mode", None)
    )


def _linked_approved_request_mode(request_obj) -> Optional[str]:
    if not request_obj:
        return None
    if getattr(request_obj, "status", None) != WorkModeRequestStatus.APPROVED:
        return None
    return _normalize_work_mode(getattr(request_obj, "mode", None))


def _resolve_final_session_mode(
    *,
    attendances: List[Attendance],
    activities: List[AttendanceActivity],
    session: str,
    attendance_date: date,
    final_dt: Optional[datetime],
    final_source: Optional[str],
    request_status_by_id: Dict[int, str],
    excluded_dts: Set[datetime],
    window_start_dt: Optional[datetime],
    window_end_dt: Optional[datetime],
    tzinfo,
    fallback_mode: str,
) -> str:
    if final_dt is None:
        return fallback_mode

    want_approved = is_approved_request_channel(final_source)
    session_norm = (session or "IN").upper()
    candidates = sorted(
        [*attendances, *activities],
        key=lambda obj: getattr(obj, "id", 0) or 0,
        reverse=True,
    )

    for obj in candidates:
        if not _should_use_raw_punch_source(obj, request_status_by_id, session=session_norm):
            continue

        channel = _session_channel(obj, session_norm)
        if is_approved_request_channel(channel) != want_approved:
            continue

        candidate_dt = _normalize_dt(_session_dt(obj, session_norm, attendance_date), tzinfo)
        if candidate_dt is None or candidate_dt != final_dt:
            continue
        if candidate_dt in excluded_dts:
            continue
        if not _within_window(candidate_dt, window_start_dt, window_end_dt):
            continue

        mode = _session_mode(obj, session_norm)
        if mode:
            return mode

    return fallback_mode


def _pick_best_attendance(att_list: List[Attendance]) -> Optional[Attendance]:
    if not att_list:
        return None
    validated = [a for a in att_list if getattr(a, "attendance_validated", False)]
    if validated:
        return sorted(validated, key=lambda x: x.id)[-1]
    approved = [a for a in att_list if getattr(a, "is_validate_request_approved", False)]
    if approved:
        return sorted(approved, key=lambda x: x.id)[-1]
    return sorted(att_list, key=lambda x: x.id)[-1]


def _canonical_row_from_attendance(
    *,
    best_att: Optional[Attendance],
    attendance_date: date,
    row_no: int,
    shift_information: str,
    language: str,
    is_off: bool,
    off_kind: Optional[str] = None,
    has_activity: bool = False,
    schedule_obj=None,
    shift_start_dt: Optional[datetime] = None,
    shift_end_dt: Optional[datetime] = None,
    minimum_hour: str = "00:00",
    half_day_kind: Optional[str] = None,
    check_in_cutoff_dt: Optional[datetime] = None,
    grace_in_sec: int = 0,
    grace_out_sec: int = 0,
    grace_clock_in_type: str = "after",
    requests_by_id: Optional[Dict[int, WorkModeRequest]] = None,
) -> Optional[MonthlyRecapRow]:
    if not best_att:
        return None

    if _is_pending_create_request_source(best_att):
        return None

    note = (getattr(best_att, "reconciliation_note", None) or "").strip()
    source = (getattr(best_att, "reconciliation_source", None) or "").strip()
    explicit_canonical = bool(note or source)
    canonical_tzinfo = (
        getattr(shift_start_dt, "tzinfo", None)
        or getattr(shift_end_dt, "tzinfo", None)
        or timezone.get_current_timezone()
    )

    final_in_dt = _normalize_dt(
        _combine_dt(
            getattr(best_att, "attendance_clock_in_date", None),
            getattr(best_att, "attendance_clock_in", None),
            attendance_date,
        ),
        canonical_tzinfo,
    )
    final_out_dt = _normalize_dt(
        _combine_dt(
            getattr(best_att, "attendance_clock_out_date", None),
            getattr(best_att, "attendance_clock_out", None),
            attendance_date,
        ),
        canonical_tzinfo,
    )

    approved_request_row = (
        is_approved_request_channel(_session_channel(best_att, "IN"))
        or is_approved_request_channel(_session_channel(best_att, "OUT"))
    )
    incomplete_row = (final_in_dt is None) ^ (final_out_dt is None)

    if off_kind in {"holiday", "no_schedule"}:
        return None

    if off_kind == "leave":
        return None

    if not explicit_canonical and off_kind != "leave" and final_in_dt is None and final_out_dt is None:
        return None

    # Be conservative for normal recap rows. When activities exist, approved
    # request channels are involved, or the row is incomplete, the richer recap
    # resolver below should decide the final truth instead of short-circuiting
    # from the persisted attendance row.
    if not explicit_canonical:
        if has_activity or approved_request_row or incomplete_row:
            return None

    in_request_obj = None
    out_request_obj = None
    if requests_by_id:
        in_req_id = getattr(best_att, "in_related_work_type_request_id", None)
        out_req_id = getattr(best_att, "out_related_work_type_request_id", None)
        in_request_obj = requests_by_id.get(in_req_id)
        out_request_obj = requests_by_id.get(out_req_id)

    baseline_mode = scheduled_attendance_mode(getattr(best_att, "employee_id", None), attendance_date) or _attendance_level_mode(best_att) or AttendanceWorkMode.WFO
    display_in_mode = (
        _session_mode(best_att, "IN")
        or _linked_approved_request_mode(in_request_obj)
        or baseline_mode
    )
    display_out_mode = (
        _session_mode(best_att, "OUT")
        or _linked_approved_request_mode(out_request_obj)
        or baseline_mode
    )
    work_type_disp = _compose_work_type_display(display_in_mode, display_out_mode)

    grant_on_duty_in = _session_on_duty_benefit_active(
        mode=display_in_mode,
        request_obj=in_request_obj,
        final_dt=final_in_dt,
    )
    grant_on_duty_out = _session_on_duty_benefit_active(
        mode=display_out_mode,
        request_obj=out_request_obj,
        final_dt=final_out_dt,
    )

    late_minutes = coerce_non_negative_decimal(getattr(best_att, "late_minutes", 0) or 0)
    early_out_minutes = coerce_non_negative_decimal(getattr(best_att, "early_out_minutes", 0) or 0)
    if schedule_obj is not None or shift_start_dt is not None or shift_end_dt is not None:
        try:
            policy = build_attendance_policy(
                schedule=schedule_obj,
                shift_start_dt=shift_start_dt,
                shift_end_dt=shift_end_dt,
                minimum_hour=minimum_hour or getattr(schedule_obj, "minimum_working_hour", None) or getattr(best_att, "minimum_hour", None) or "00:00",
                leave_kind=half_day_kind,
                check_in_cutoff_dt=check_in_cutoff_dt,
            )
            metrics = compute_attendance_metrics(
                policy,
                final_in_dt=final_in_dt,
                final_out_dt=final_out_dt,
                grace_seconds=grace_in_sec,
                clock_in_type=grace_clock_in_type,
                is_presence_only=bool(grant_on_duty_in and grant_on_duty_out),
                early_out_grace_seconds=grace_out_sec,
            )
            if grant_on_duty_in:
                late_minutes = coerce_non_negative_decimal(0)
            else:
                late_minutes = seconds_to_decimal_minutes(metrics.late_seconds)
            if grant_on_duty_out:
                early_out_minutes = coerce_non_negative_decimal(0)
            else:
                early_out_minutes = seconds_to_decimal_minutes(metrics.early_out_seconds)
        except Exception:
            pass

    return MonthlyRecapRow(
        no=row_no,
        attendance_date=attendance_date,
        shift_information=_localize_shift_information(shift_information, language),
        check_in=final_in_dt is not None and _format_punch(final_in_dt, attendance_date) or "-",
        check_out=final_out_dt is not None and _format_punch(final_out_dt, attendance_date) or "-",
        work_type=_localize_work_type(work_type_disp, language),
        late=seconds_to_hhmm(float(late_minutes) * 60),
        early_out=seconds_to_hhmm(float(early_out_minutes) * 60),
        note=note or source or "-",
        is_off=is_off,
        late_minutes=late_minutes,
        early_out_minutes=early_out_minutes,
        final_in_datetime=final_in_dt,
        final_out_datetime=final_out_dt,
        display_in_mode=display_in_mode or "",
        display_out_mode=display_out_mode or "",
    )


def _resolve_effective_mode_approved(
    *,
    requests: List[WorkModeRequest],
    attendance_date: date,
    want: str,
    baseline_mode: str,
) -> str:
    """Effective mode for IN/OUT using APPROVED only."""
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
    late_minutes: Decimal | int = 0
    early_out_minutes: Decimal | int = 0
    final_in_datetime: Optional[datetime] = None
    final_out_datetime: Optional[datetime] = None
    display_in_mode: str = ""
    display_out_mode: str = ""


@dataclass(frozen=True)
class MonthlyRecapSummary:
    late_minutes: Decimal | int = 0
    early_out_minutes: Decimal | int = 0
    total_minutes: Decimal | int = 0

    def as_dict(self) -> Dict[str, Decimal]:
        return {
            "late_minutes": coerce_non_negative_decimal(self.late_minutes),
            "early_out_minutes": coerce_non_negative_decimal(self.early_out_minutes),
            "total_minutes": coerce_non_negative_decimal(self.total_minutes),
        }


def _seconds_to_minutes(total_seconds):
    return seconds_to_decimal_minutes(total_seconds)


def _safe_non_negative_decimal(value):
    return coerce_non_negative_decimal(value)

def _duration_seconds(value) -> int:
    if value is None:
        return 0
    try:
        if hasattr(value, "strftime"):
            raw = value.strftime("%H:%M:%S")
        else:
            raw = str(value).strip()
        if not raw or raw.lower() in {"none", "null"}:
            return 0
        parts = raw.split(":")
        if len(parts) == 2:
            hours, minutes = parts
            seconds = 0
        else:
            hours, minutes, seconds = (parts + ["0", "0", "0"])[:3]
        total = (int(hours) * 3600) + (int(minutes) * 60) + int(seconds)
        return total if total >= 0 else 0
    except Exception:
        return 0


def _resolve_minimum_work_seconds(schedule_obj, shift_start_dt: Optional[datetime], shift_end_dt: Optional[datetime]) -> int:
    configured = _duration_seconds(getattr(schedule_obj, "minimum_working_hour", None) if schedule_obj else None)
    if configured > 0:
        return configured
    if shift_start_dt and shift_end_dt:
        try:
            return max(0, int((shift_end_dt - shift_start_dt).total_seconds()))
        except Exception:
            return 0
    return 0


def _resolve_mobile_style_earliest_checkout_dt(
    *,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
    actual_check_in_dt: Optional[datetime],
    clock_in_type: str,
    flex_seconds: int,
) -> Optional[datetime]:
    if not (shift_start_dt and shift_end_dt):
        return None

    shift_duration = shift_end_dt - shift_start_dt
    flex_delta = timedelta(seconds=max(0, int(flex_seconds or 0)))
    mode = str(clock_in_type or "after").strip().lower()
    effective_start_dt = shift_start_dt

    if actual_check_in_dt is None:
        return shift_end_dt

    if mode == "before_after":
        window_start_dt = shift_start_dt - flex_delta
        window_end_dt = shift_start_dt + flex_delta
        if actual_check_in_dt < window_start_dt:
            effective_start_dt = window_start_dt
        elif actual_check_in_dt > window_end_dt:
            effective_start_dt = window_end_dt
        else:
            effective_start_dt = actual_check_in_dt
    elif mode == "after":
        window_start_dt = shift_start_dt
        window_end_dt = shift_start_dt + flex_delta
        if actual_check_in_dt < window_start_dt:
            effective_start_dt = window_start_dt
        elif actual_check_in_dt > window_end_dt:
            effective_start_dt = window_end_dt
        else:
            effective_start_dt = actual_check_in_dt
    else:
        effective_start_dt = shift_start_dt

    return effective_start_dt + shift_duration


def _parse_duration_to_minutes(value):
    """Safely coerce duration-like values into plain numeric minutes.

    Supported inputs:
    - raw integers / floats / timedeltas
    - HH:MM
    - HH:MM:SS
    - blank / "-" / invalid => 0
    """

    if value is None:
        return 0

    if isinstance(value, timedelta):
        return _seconds_to_minutes(value.total_seconds())

    if isinstance(value, (int, float, Decimal)):
        return _safe_non_negative_decimal(value)

    raw = str(value).strip()
    if not raw or raw in {"-", "—"} or raw.lower() in {"none", "null", "invalid"}:
        return 0

    if raw.replace(".", "", 1).isdigit():
        return _safe_non_negative_decimal(raw)

    parts = raw.split(":")
    if len(parts) in (2, 3):
        try:
            hours = int(parts[0])
            minutes = int(parts[1])
            seconds = int(parts[2]) if len(parts) == 3 else 0
        except Exception:
            return 0

        if hours < 0 or minutes < 0 or seconds < 0:
            return 0

        return seconds_to_decimal_minutes((hours * 3600) + (minutes * 60) + seconds)

    return 0


def _row_duration_minutes(row: "MonthlyRecapRow", *, minute_attr: str, text_attr: str):
    raw_minutes = getattr(row, minute_attr, None)
    if raw_minutes not in (None, ""):
        return _safe_non_negative_decimal(raw_minutes)
    return _parse_duration_to_minutes(getattr(row, text_attr, None))


def summarize_monthly_recap_rows(rows: List["MonthlyRecapRow"]) -> MonthlyRecapSummary:
    late_minutes = Decimal("0")
    early_out_minutes = Decimal("0")

    for row in rows or []:
        late_minutes += _row_duration_minutes(row, minute_attr="late_minutes", text_attr="late")
        early_out_minutes += _row_duration_minutes(row, minute_attr="early_out_minutes", text_attr="early_out")

    return MonthlyRecapSummary(
        late_minutes=late_minutes,
        early_out_minutes=early_out_minutes,
        total_minutes=late_minutes + early_out_minutes,
    )


def _within_window(dt_obj: datetime, start: Optional[datetime], end: Optional[datetime]) -> bool:
    if start and dt_obj < start:
        return False
    if end and dt_obj > end:
        return False
    return True


def _parse_date_like(value, fallback_date: date) -> date:
    if isinstance(value, date) and not isinstance(value, datetime):
        return value
    if isinstance(value, datetime):
        return value.date()
    if isinstance(value, str):
        raw = value.strip()
        if raw:
            try:
                return datetime.fromisoformat(raw).date()
            except Exception:
                pass
            try:
                return datetime.strptime(raw, "%Y-%m-%d").date()
            except Exception:
                pass
    return fallback_date


def _parse_time_like(value) -> Optional[time]:
    if isinstance(value, time):
        return value
    if isinstance(value, datetime):
        return value.time()
    if isinstance(value, str):
        raw = value.strip()
        if not raw or raw.lower() in {"none", "null"}:
            return None
        for fmt in ("%H:%M:%S", "%H:%M"):
            try:
                return datetime.strptime(raw, fmt).time()
            except Exception:
                continue
        try:
            return time.fromisoformat(raw)
        except Exception:
            return None
    return None


def _format_time_like(value) -> str:
    parsed = _parse_time_like(value)
    if parsed:
        return parsed.strftime("%H:%M")
    return ""


def _session_note_label(session: str, language: str) -> str:
    lang = (language or "en").lower()
    s = (session or "").upper()
    if lang.startswith("id"):
        return "Datang" if s == "IN" else "Pulang"
    return s or "IN"


def _work_mode_scope_label(scope: str, *, mode: str, language: str) -> str:
    lang = (language or "en").lower()
    scope_norm = (scope or "").lower()
    mode_norm = (mode or "").lower()

    if mode_norm == AttendanceWorkMode.ON_DUTY:
        if lang.startswith("id"):
            if scope_norm == WorkModeRequestScope.IN:
                return "Dinas Luar Awal"
            if scope_norm == WorkModeRequestScope.OUT:
                return "Dinas Luar Akhir"
            return "Dinas Luar Penuh"
        if scope_norm == WorkModeRequestScope.IN:
            return "On Duty IN"
        if scope_norm == WorkModeRequestScope.OUT:
            return "On Duty OUT"
        return "On Duty FULL"

    mode_label = _work_mode_label(mode_norm)
    scope_label = (scope or "full").upper()
    return f"{mode_label} {scope_label}"


def _request_has_attachments(req: WorkModeRequest) -> bool:
    files = getattr(req, "files", None)
    if files is None:
        return False
    try:
        return bool(files.exists())
    except Exception:
        try:
            return bool(len(files.all()))
        except Exception:
            return False


def _status_note_label(*, status: str, mode: str, req: Optional[WorkModeRequest], language: str) -> str:
    lang = (language or "en").lower()
    mode_norm = (mode or "").lower()

    if lang.startswith("id"):
        if mode_norm == AttendanceWorkMode.ON_DUTY and status == WorkModeRequestStatus.PENDING:
            return "menunggu upload dokumen" if not _request_has_attachments(req) else "menunggu persetujuan"
        if status == WorkModeRequestStatus.WAITING_FOR_APPROVAL:
            return "menunggu persetujuan"
        if status == WorkModeRequestStatus.PENDING:
            return "menunggu persetujuan"
        return status or ""

    if mode_norm == AttendanceWorkMode.ON_DUTY and status == WorkModeRequestStatus.PENDING:
        return "awaiting document upload" if not _request_has_attachments(req) else "pending approval"
    if status == WorkModeRequestStatus.WAITING_FOR_APPROVAL:
        return "pending approval"
    if status == WorkModeRequestStatus.PENDING:
        return "pending"
    return status or ""


def _attendance_pending_suffix(session: str, time_txt: str, *, language: str) -> str:
    label = _session_note_label(session, language)
    if (language or "en").lower().startswith("id"):
        base = f"Absensi {label} menunggu persetujuan"
    else:
        base = f"Attendance {label} pending"
    return f"{base}: {time_txt}" if time_txt else base


def _attendance_out_of_window_suffix(session: str, time_txt: str, *, language: str) -> str:
    label = _session_note_label(session, language)
    if (language or "en").lower().startswith("id"):
        base = f"Absensi {label} disetujui tetapi di luar batas waktu"
    else:
        base = f"Approved but out of time limit ({label})"
    return f"{base}: {time_txt}" if time_txt else base


def _first_time_text(*values) -> str:
    for value in values:
        txt = _format_time_like(value)
        if txt:
            return txt
    return ""


def _join_time_texts(values: List[str]) -> str:
    cleaned = []
    seen = set()
    for value in values:
        value = (value or "").strip()
        if not value or value in seen:
            continue
        seen.add(value)
        cleaned.append(value)
    return ", ".join(cleaned)


def _request_time_text_from_obj(
    req: WorkModeRequest,
    *,
    scope: str,
    fallback_in_time: Optional[time] = None,
    fallback_out_time: Optional[time] = None,
) -> str:
    scope_norm = (scope or "").lower()

    generic_txt = _first_time_text(
        getattr(req, "planned_time", None),
        getattr(req, "time", None),
        getattr(req, "request_time", None),
    )
    in_specific_txt = _first_time_text(
        getattr(req, "planned_clock_in", None),
        getattr(req, "clock_in", None),
        getattr(req, "request_clock_in", None),
        getattr(req, "request_in", None),
        getattr(req, "in_time", None),
        getattr(req, "start_time", None),
    )
    out_specific_txt = _first_time_text(
        getattr(req, "planned_clock_out", None),
        getattr(req, "clock_out", None),
        getattr(req, "request_clock_out", None),
        getattr(req, "request_out", None),
        getattr(req, "out_time", None),
        getattr(req, "end_time", None),
    )
    in_txt = in_specific_txt or generic_txt or _format_time_like(fallback_in_time)
    out_txt = out_specific_txt or generic_txt or _format_time_like(fallback_out_time)

    if scope_norm == WorkModeRequestScope.IN:
        return in_txt
    if scope_norm == WorkModeRequestScope.OUT:
        return out_txt

    return _join_time_texts([in_txt, out_txt])


def _work_mode_pending_suffix(
    *,
    mode: str,
    scope: str,
    status: str,
    req: Optional[WorkModeRequest],
    time_txt: str,
    language: str,
) -> str:
    label = _work_mode_scope_label(scope, mode=mode, language=language)
    status_label = _status_note_label(status=status, mode=mode, req=req, language=language)
    base = f"{label} {status_label}".strip()
    return f"{base}: {time_txt}" if time_txt else base


def _requested_payload_for_attendance(attendance) -> dict:
    """Return requested payload for an attendance request row.

    Fallback: legacy / inconsistent pending ``create_request`` rows may carry the
    requested IN/OUT values only in the Attendance columns while ``requested_data``
    is empty or malformed. In that case we synthesize a minimal payload so the
    request still shows the correct session/time in Note and can be ignored from
    final Check In / Check Out.
    """

    payload = load_requested_data(getattr(attendance, "requested_data", None))
    if payload:
        return payload

    if not _is_pending_create_request_source(attendance):
        return {}

    fallback = {}
    for key in (
        "attendance_clock_in_date",
        "attendance_clock_in",
        "attendance_clock_out_date",
        "attendance_clock_out",
    ):
        value = getattr(attendance, key, None)
        if value in (None, "", "None", "null"):
            continue
        fallback[key] = value

    if fallback:
        fallback["__meta"] = {
            "current_scope": infer_scope_from_values(
                fallback.get("attendance_clock_in"),
                fallback.get("attendance_clock_out"),
            )
        }
    return fallback


def _attendance_request_effects_for_one(
    *,
    attendance: Optional[Attendance],
    attendance_date: date,
    check_in_window_start_dt: Optional[datetime],
    check_in_window_end_dt: Optional[datetime],
    check_out_window_start_dt: Optional[datetime],
    check_out_window_end_dt: Optional[datetime],
    tzinfo,
    language: str,
) -> Tuple[List[str], Set[datetime], Set[datetime], bool]:
    """Return note suffixes + approved out-of-window exclusions for one row."""

    suffixes: List[str] = []
    excluded_in: Set[datetime] = set()
    excluded_out: Set[datetime] = set()
    used_detailed_pending = False

    if not attendance:
        return suffixes, excluded_in, excluded_out, used_detailed_pending

    requested_payload = _requested_payload_for_attendance(attendance)
    if not requested_payload:
        return suffixes, excluded_in, excluded_out, used_detailed_pending

    if bool(getattr(attendance, "is_validate_request", False)):
        current_scope = get_current_scope(getattr(attendance, "requested_data", None))
        if not current_scope:
            current_scope = infer_scope_from_values(
                requested_payload.get("attendance_clock_in"),
                requested_payload.get("attendance_clock_out"),
            )
        for session in ("IN", "OUT"):
            if session not in scope_to_sessions(current_scope):
                continue
            req_dt = _requested_session_dt(
                requested_payload=requested_payload,
                attendance_date=attendance_date,
                session=session,
                tzinfo=tzinfo,
            )
            time_txt = req_dt.strftime("%H:%M") if req_dt else ""
            suffixes.append(_attendance_pending_suffix(session, time_txt, language=language))
            used_detailed_pending = True

    if bool(getattr(attendance, "is_validate_request_approved", False)):
        approved_sessions: Set[str] = set()
        for scope in get_approved_scopes(getattr(attendance, "requested_data", None)):
            approved_sessions |= scope_to_sessions(scope)

        if not approved_sessions:
            approved_sessions = scope_to_sessions(
                infer_scope_from_values(
                    requested_payload.get("attendance_clock_in"),
                    requested_payload.get("attendance_clock_out"),
                )
            )

        for session in sorted(approved_sessions):
            req_dt = _requested_session_dt(
                requested_payload=requested_payload,
                attendance_date=attendance_date,
                session=session,
                tzinfo=tzinfo,
            )
            if not req_dt:
                continue

            if session == "OUT":
                in_window = _within_window(req_dt, check_out_window_start_dt, check_out_window_end_dt)
                if not in_window:
                    excluded_out.add(req_dt)
            else:
                in_window = _within_window(req_dt, check_in_window_start_dt, check_in_window_end_dt)
                if not in_window:
                    excluded_in.add(req_dt)

            if not in_window:
                suffixes.append(
                    _attendance_out_of_window_suffix(
                        session,
                        req_dt.strftime("%H:%M"),
                        language=language,
                    )
                )

    return suffixes, excluded_in, excluded_out, used_detailed_pending


def _requested_session_dt(
    *,
    requested_payload: dict,
    attendance_date: date,
    session: str,
    tzinfo=None,
) -> Optional[datetime]:
    if not requested_payload:
        return None

    session_norm = (session or "").upper()
    if session_norm == "OUT":
        date_key = "attendance_clock_out_date"
        time_key = "attendance_clock_out"
    else:
        date_key = "attendance_clock_in_date"
        time_key = "attendance_clock_in"

    dt_time = _parse_time_like(requested_payload.get(time_key))
    if not dt_time:
        return None

    dt_date = _parse_date_like(requested_payload.get(date_key), attendance_date)
    return _normalize_dt(datetime.combine(dt_date, dt_time), tzinfo)


def _attendance_request_effects(
    *,
    attendances: List[Attendance],
    attendance_date: date,
    check_in_window_start_dt: Optional[datetime],
    check_in_window_end_dt: Optional[datetime],
    check_out_window_start_dt: Optional[datetime],
    check_out_window_end_dt: Optional[datetime],
    tzinfo,
    language: str,
) -> Tuple[List[str], Set[datetime], Set[datetime], bool]:
    """Return note suffixes + approved out-of-window exclusions for requested punches.

    We must inspect *all* attendance rows for the date, not only ``best_att``.
    Otherwise a separate pending create_request row can still influence the note
    or raw punch candidates inconsistently.
    """

    suffixes: List[str] = []
    excluded_in: Set[datetime] = set()
    excluded_out: Set[datetime] = set()
    used_detailed_pending = False
    seen_suffixes: Set[str] = set()

    for attendance in attendances or []:
        row_suffixes, row_excluded_in, row_excluded_out, row_used_detailed_pending = _attendance_request_effects_for_one(
            attendance=attendance,
            attendance_date=attendance_date,
            check_in_window_start_dt=check_in_window_start_dt,
            check_in_window_end_dt=check_in_window_end_dt,
            check_out_window_start_dt=check_out_window_start_dt,
            check_out_window_end_dt=check_out_window_end_dt,
            tzinfo=tzinfo,
            language=language,
        )
        for suffix in row_suffixes:
            if suffix in seen_suffixes:
                continue
            seen_suffixes.add(suffix)
            suffixes.append(suffix)
        excluded_in |= row_excluded_in
        excluded_out |= row_excluded_out
        used_detailed_pending = used_detailed_pending or row_used_detailed_pending

    return suffixes, excluded_in, excluded_out, used_detailed_pending


def _pending_work_mode_suffixes(
    *,
    requests: List[WorkModeRequest],
    attendance_date: date,
    language: str,
    shift_start_time: Optional[time] = None,
    shift_end_time: Optional[time] = None,
) -> List[str]:
    suffixes: List[str] = []
    pending_statuses = {WorkModeRequestStatus.PENDING, WorkModeRequestStatus.WAITING_FOR_APPROVAL}
    seen: Set[Tuple[str, str, str, str]] = set()

    for req in sorted(requests, key=lambda r: r.id, reverse=True):
        if req.status not in pending_statuses:
            continue
        if getattr(req, "mode", None) != AttendanceWorkMode.ON_DUTY:
            continue
        if not (req.start_date <= attendance_date <= req.end_date):
            continue

        time_txt = _request_time_text_from_obj(
            req,
            scope=getattr(req, "scope", None),
            fallback_in_time=shift_start_time,
            fallback_out_time=shift_end_time,
        )
        key = (req.mode, req.scope, req.status, time_txt)
        if key in seen:
            continue
        seen.add(key)

        suffixes.append(
            _work_mode_pending_suffix(
                mode=req.mode,
                scope=req.scope,
                status=req.status,
                req=req,
                time_txt=time_txt,
                language=language,
            )
        )

    return suffixes


def build_employee_monthly_recap(*, employee: Employee, month_yyyy_mm: str, language: str = "en") -> List[MonthlyRecapRow]:
    first_day, last_day = _month_range(month_yyyy_mm)

    today = timezone.localdate()
    this_month_first = date(today.year, today.month, 1)
    if first_day > this_month_first:
        first_day = this_month_first
        last_day = today
    elif first_day.year == today.year and first_day.month == today.month and last_day > today:
        last_day = today

    from attendance.views.clock_in_out import get_shift_rules, _resolve_grace_time

    att_qs = Attendance.objects.filter(
        employee_id=employee,
        attendance_date__range=(first_day, last_day),
    ).order_by("attendance_date", "id")
    act_qs = AttendanceActivity.objects.filter(
        employee_id=employee,
        attendance_date__range=(first_day, last_day),
    ).order_by("attendance_date", "id")

    all_req_qs = WorkModeRequest.objects.filter(
        employee_id=employee,
        start_date__lte=last_day,
        end_date__gte=first_day,
    ).order_by("-id")
    all_requests = list(all_req_qs)
    requests = [
        r
        for r in all_requests
        if is_active_work_mode_request_status(getattr(r, "status", None))
    ]
    request_status_by_id = {
        getattr(r, "id", None): getattr(r, "status", None)
        for r in all_requests
        if getattr(r, "id", None) is not None
    }
    requests_by_id = {
        getattr(r, "id", None): r
        for r in all_requests
        if getattr(r, "id", None) is not None
    }

    leave_qs = LeaveRequest.objects.filter(
        employee_id=employee,
        status="approved",
        start_date__lte=last_day,
        end_date__gte=first_day,
    )
    leave_coverage = _approved_leave_coverage(leave_qs, first_day, last_day)

    day_objs = {d.day: d for d in EmployeeShiftDay.objects.all()}

    att_by_date: Dict[date, List[Attendance]] = {}
    for a in att_qs:
        att_by_date.setdefault(a.attendance_date, []).append(a)

    act_by_date: Dict[date, List[AttendanceActivity]] = {}
    for ac in act_qs:
        act_by_date.setdefault(ac.attendance_date, []).append(ac)

    rows: List[MonthlyRecapRow] = []
    i = 1
    tzinfo = timezone.get_current_timezone()
    for d in _iter_month_dates(first_day, last_day):
        holiday_obj = is_holiday(d)
        leave_info = leave_coverage.get(
            d,
            {
                "full_day": False,
                "first_half": False,
                "second_half": False,
                "breakdown": None,
                "leave_request": None,
            },
        )
        is_leave = bool(leave_info.get("full_day"))
        half_day_kind = leave_info.get("breakdown") if not is_leave else None
        off_kind = None

        att_list = att_by_date.get(d, [])
        act_list = act_by_date.get(d, [])
        best_att = _pick_best_attendance(att_list)

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

        schedule_obj = rules.get("schedule")
        no_schedule_off = (
            shift is None
            or schedule_obj is None
            or not rules.get("start_time")
            or not rules.get("end_time")
        )
        is_off = bool(holiday_obj) or is_leave or no_schedule_off
        if is_leave:
            off_kind = "leave"
        elif holiday_obj:
            off_kind = "holiday"
        elif no_schedule_off:
            off_kind = "holiday"

        if is_leave:
            canonical_shift_info = _localize_leave_session_label("full", language)
        elif holiday_obj or no_schedule_off:
            canonical_shift_info = "Holiday"
        else:
            canonical_shift_info = "—"
            try:
                st = rules.get("start_time")
                et = rules.get("end_time")
                if st and et:
                    canonical_shift_info = f"{st.strftime('%H:%M')} - {et.strftime('%H:%M')}"
                    flexi_min = int((int(rules.get("grace_seconds") or 0)) // 60)
                    canonical_shift_info += f" • Flexi In: {flexi_min}m"
            except Exception:
                canonical_shift_info = "—"


        shift_start_dt = _normalize_dt(rules.get("shift_start_dt"), tzinfo)
        shift_end_dt = _normalize_dt(rules.get("shift_end_dt"), tzinfo)
        cutoff_in_dt = _normalize_dt(
            rules.get("cutoff_in_dt") or rules.get("check_in_window_end_dt"),
            tzinfo,
        )
        grace_in_sec = int(rules.get("grace_seconds") or 0)
        grace_out_sec = 0
        grace_clock_in_type = str(rules.get("clock_in_type") or "after")
        try:
            grace_time = _resolve_grace_time(rules.get("schedule"), shift)
            if grace_time and getattr(grace_time, "allowed_clock_out", False):
                grace_out_sec = int(getattr(grace_time, "allowed_time_in_secs", 0) or 0)
            if grace_time and (getattr(grace_time, "allowed_clock_in", True) or grace_in_sec > 0):
                grace_clock_in_type = getattr(grace_time, "clock_in_type", "after") or "after"
        except Exception:
            grace_out_sec = 0
            grace_clock_in_type = str(rules.get("clock_in_type") or "after")

        canonical_row = _canonical_row_from_attendance(
            best_att=best_att,
            attendance_date=d,
            row_no=i,
            shift_information=canonical_shift_info,
            language=language,
            is_off=is_off,
            off_kind=off_kind,
            has_activity=bool(act_list),
            schedule_obj=rules.get("schedule"),
            shift_start_dt=shift_start_dt,
            shift_end_dt=shift_end_dt,
            minimum_hour=(getattr(rules.get("schedule"), "minimum_working_hour", None) or (getattr(best_att, "minimum_hour", None) if best_att else None) or "00:00"),
            half_day_kind=half_day_kind,
            check_in_cutoff_dt=rules.get("check_in_window_end_dt") and _normalize_dt(rules.get("check_in_window_end_dt"), tzinfo) or cutoff_in_dt,
            grace_in_sec=grace_in_sec,
            grace_out_sec=grace_out_sec,
            grace_clock_in_type=grace_clock_in_type,
            requests_by_id=requests_by_id,
        )
        if canonical_row is not None:
            rows.append(canonical_row)
            i += 1
            continue

        if is_off:
            if is_leave:
                shift_info = _localize_shift_information(_localize_leave_session_label("full", language), language)
                note = derive_note(NoteInputs(is_off=True, off_kind="leave"), language=language)
            elif holiday_obj:
                shift_info = _localize_shift_information("Holiday", language)
                note = derive_note(NoteInputs(is_off=True, off_kind="holiday"), language=language)
            else:
                shift_info = _localize_shift_information("Holiday", language)
                note = derive_note(NoteInputs(is_off=True, off_kind="holiday"), language=language)

            rows.append(
                MonthlyRecapRow(
                    no=i,
                    attendance_date=d,
                    shift_information=shift_info,
                    check_in="-",
                    check_out="-",
                    work_type="-",
                    late="00:00",
                    early_out="00:00",
                    note=note,
                    is_off=True,
                    late_minutes=0,
                    early_out_minutes=0,
                )
            )
            i += 1
            continue

        check_in_window_start_dt = rules.get("check_in_window_start_dt")
        check_in_window_end_dt = rules.get("check_in_window_end_dt")
        check_out_window_start_dt = rules.get("check_out_window_start_dt")
        check_out_window_end_dt = rules.get("check_out_window_end_dt")

        in_dts_raw: List[datetime] = []
        out_dts_raw: List[datetime] = []

        for a in att_list:
            if _should_use_raw_punch_source(a, request_status_by_id, session="IN") and not is_approved_request_channel(_session_channel(a, "IN")): 
                dt_in = _combine_dt(
                    getattr(a, "attendance_clock_in_date", None),
                    getattr(a, "attendance_clock_in", None),
                    a.attendance_date,
                )
                if dt_in:
                    in_dts_raw.append(_normalize_dt(dt_in))
            if _should_use_raw_punch_source(a, request_status_by_id, session="OUT") and not is_approved_request_channel(_session_channel(a, "OUT")): 
                dt_out = _combine_dt(
                    getattr(a, "attendance_clock_out_date", None),
                    getattr(a, "attendance_clock_out", None),
                    a.attendance_date,
                )
                if dt_out:
                    out_dts_raw.append(_normalize_dt(dt_out))

        for ac in act_list:
            if _should_use_raw_punch_source(ac, request_status_by_id, session="IN") and not is_approved_request_channel(_session_channel(ac, "IN")): 
                dt_in = getattr(ac, "in_datetime", None) or _combine_dt(
                    getattr(ac, "clock_in_date", None),
                    getattr(ac, "clock_in", None),
                    ac.attendance_date,
                )
                if dt_in:
                    in_dts_raw.append(_normalize_dt(dt_in))
            if _should_use_raw_punch_source(ac, request_status_by_id, session="OUT") and not is_approved_request_channel(_session_channel(ac, "OUT")): 
                dt_out = getattr(ac, "out_datetime", None) or _combine_dt(
                    getattr(ac, "clock_out_date", None),
                    getattr(ac, "clock_out", None),
                    ac.attendance_date,
                )
                if dt_out:
                    out_dts_raw.append(_normalize_dt(dt_out))

        tzinfo = None
        for cand in (
            rules.get("shift_start_dt"),
            rules.get("shift_end_dt"),
            rules.get("cutoff_in_dt"),
            rules.get("cutoff_out_dt"),
            check_in_window_start_dt,
            check_in_window_end_dt,
            check_out_window_start_dt,
            check_out_window_end_dt,
            *(in_dts_raw or []),
            *(out_dts_raw or []),
        ):
            if cand and timezone.is_aware(cand):
                tzinfo = cand.tzinfo
                break

        check_in_window_start_dt = _normalize_dt(check_in_window_start_dt, tzinfo)
        check_in_window_end_dt = _normalize_dt(check_in_window_end_dt, tzinfo)
        check_out_window_start_dt = _normalize_dt(check_out_window_start_dt, tzinfo)
        check_out_window_end_dt = _normalize_dt(check_out_window_end_dt, tzinfo)

        attendance_request_suffixes, excluded_in_dts, excluded_out_dts, used_detailed_pending = _attendance_request_effects(
            attendances=att_list,
            attendance_date=d,
            check_in_window_start_dt=check_in_window_start_dt,
            check_in_window_end_dt=check_in_window_end_dt,
            check_out_window_start_dt=check_out_window_start_dt,
            check_out_window_end_dt=check_out_window_end_dt,
            tzinfo=tzinfo,
            language=language,
        )

        in_dts: List[datetime] = []
        for dt_obj in in_dts_raw:
            dt_n = _normalize_dt(dt_obj, tzinfo)
            if not dt_n:
                continue
            if dt_n in excluded_in_dts:
                continue
            if _within_window(dt_n, check_in_window_start_dt, check_in_window_end_dt):
                in_dts.append(dt_n)

        out_dts: List[datetime] = []
        for dt_obj in out_dts_raw:
            dt_n = _normalize_dt(dt_obj, tzinfo)
            if not dt_n:
                continue
            if dt_n in excluded_out_dts:
                continue
            if _within_window(dt_n, check_out_window_start_dt, check_out_window_end_dt):
                out_dts.append(dt_n)

        approved_in_dt = _approved_request_dt(
            attendances=att_list,
            activities=act_list,
            session="IN",
            attendance_date=d,
            tzinfo=tzinfo,
        )
        approved_out_dt = _approved_request_dt(
            attendances=att_list,
            activities=act_list,
            session="OUT",
            attendance_date=d,
            tzinfo=tzinfo,
        )

        if approved_in_dt and (
            approved_in_dt in excluded_in_dts
            or not _within_window(approved_in_dt, check_in_window_start_dt, check_in_window_end_dt)
        ):
            approved_in_dt = None
        if approved_out_dt and (
            approved_out_dt in excluded_out_dts
            or not _within_window(approved_out_dt, check_out_window_start_dt, check_out_window_end_dt)
        ):
            approved_out_dt = None

        final_in_resolution = resolve_final_session(
            session="IN",
            approved_dt=approved_in_dt,
            raw_datetimes=in_dts,
            raw_source="raw",
        )
        final_out_resolution = resolve_final_session(
            session="OUT",
            approved_dt=approved_out_dt,
            raw_datetimes=out_dts,
            raw_source="raw",
        )
        final_in_dt = final_in_resolution.final_dt
        final_out_dt = final_out_resolution.final_dt

        final_in_dt = _normalize_dt(final_in_dt, tzinfo)
        final_out_dt = _normalize_dt(final_out_dt, tzinfo)

        baseline_mode = scheduled_attendance_mode(employee, d) or _attendance_level_mode(best_att) or AttendanceWorkMode.WFO

        eff_in_request = _resolve_effective_request_approved(
            requests=requests,
            attendance_date=d,
            want="in",
        )
        eff_out_request = _resolve_effective_request_approved(
            requests=requests,
            attendance_date=d,
            want="out",
        )
        eff_in_mode = getattr(eff_in_request, "mode", None) or _resolve_effective_mode_approved(
            requests=requests,
            attendance_date=d,
            want="in",
            baseline_mode=baseline_mode,
        )
        eff_out_mode = getattr(eff_out_request, "mode", None) or _resolve_effective_mode_approved(
            requests=requests,
            attendance_date=d,
            want="out",
            baseline_mode=baseline_mode,
        )

        display_in_mode = _resolve_final_session_mode(
            attendances=att_list,
            activities=act_list,
            session="IN",
            attendance_date=d,
            final_dt=final_in_dt,
            final_source=final_in_resolution.final_source,
            request_status_by_id=request_status_by_id,
            excluded_dts=excluded_in_dts,
            window_start_dt=check_in_window_start_dt,
            window_end_dt=check_in_window_end_dt,
            tzinfo=tzinfo,
            fallback_mode=eff_in_mode,
        )
        display_out_mode = _resolve_final_session_mode(
            attendances=att_list,
            activities=act_list,
            session="OUT",
            attendance_date=d,
            final_dt=final_out_dt,
            final_source=final_out_resolution.final_source,
            request_status_by_id=request_status_by_id,
            excluded_dts=excluded_out_dts,
            window_start_dt=check_out_window_start_dt,
            window_end_dt=check_out_window_end_dt,
            tzinfo=tzinfo,
            fallback_mode=eff_out_mode,
        )

        work_type_disp = _compose_work_type_display(display_in_mode, display_out_mode)

        leave_note_suffixes: List[str] = []
        if half_day_kind == "first_half":
            leave_note_suffixes.append(_localize_half_day_leave_note("first_half", language))
        elif half_day_kind == "second_half":
            leave_note_suffixes.append(_localize_half_day_leave_note("second_half", language))

        policy = build_attendance_policy(
            schedule=schedule_obj,
            shift_start_dt=shift_start_dt,
            shift_end_dt=shift_end_dt,
            minimum_hour=getattr(schedule_obj, "minimum_working_hour", None) or getattr(best_att, "minimum_hour", None) or "00:00",
            leave_kind=half_day_kind,
            check_in_cutoff_dt=check_in_window_end_dt or cutoff_in_dt,
        )
        metrics = compute_attendance_metrics(
            policy,
            final_in_dt=final_in_dt,
            final_out_dt=final_out_dt,
            grace_seconds=grace_in_sec,
            clock_in_type=grace_clock_in_type,
            is_presence_only=False,
            early_out_grace_seconds=grace_out_sec,
        )
        earliest_check_out_dt = metrics.earliest_checkout_dt
        grant_on_duty_in = _session_on_duty_benefit_active(
            mode=eff_in_mode,
            request_obj=eff_in_request,
            final_dt=final_in_dt,
        )
        grant_on_duty_out = _session_on_duty_benefit_active(
            mode=eff_out_mode,
            request_obj=eff_out_request,
            final_dt=final_out_dt,
        )

        late_sec = 0.0 if grant_on_duty_in else float(metrics.late_seconds)
        early_sec = 0.0 if grant_on_duty_out else float(metrics.early_out_seconds)

        late_minutes = _seconds_to_minutes(late_sec)
        early_minutes = _seconds_to_minutes(early_sec)
        late_txt = seconds_to_hhmm(float(late_sec))
        early_txt = seconds_to_hhmm(float(early_sec))

        shift_info = "—"
        try:
            st = rules.get("start_time")
            et = rules.get("end_time")
            if st and et:
                shift_info = f"{st.strftime('%H:%M')} - {et.strftime('%H:%M')}"
                flexi_min = int((grace_in_sec or 0) // 60)
                if flexi_min > 0:
                    flex_symbol = "±" if grace_clock_in_type == "before_after" else "+"
                    shift_info += f" • Flex In {flex_symbol}{flexi_min}m"
        except Exception:
            shift_info = "—"

        work_mode_pending_suffixes = _pending_work_mode_suffixes(
            requests=requests,
            attendance_date=d,
            language=language,
            shift_start_time=rules.get("start_time"),
            shift_end_time=rules.get("end_time"),
        )
        note_suffixes = attendance_request_suffixes + work_mode_pending_suffixes + leave_note_suffixes
        correction_pending = bool(
            any(getattr(att, "is_validate_request", False) for att in att_list)
            and not used_detailed_pending
        )

        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=final_in_dt is not None,
                has_check_out=final_out_dt is not None,
                late_seconds=late_sec,
                early_out_seconds=early_sec,
                pending_suffixes=note_suffixes,
                correction_pending=correction_pending,
            ),
            language=language,
        )

        shift_info = _localize_shift_information(shift_info, language)
        work_type_disp = _localize_work_type(work_type_disp, language)

        rows.append(
            MonthlyRecapRow(
                no=i,
                attendance_date=d,
                shift_information=shift_info,
                check_in=final_in_dt is not None and _format_punch(final_in_dt, d) or "-",
                check_out=final_out_dt is not None and _format_punch(final_out_dt, d) or "-",
                work_type=work_type_disp,
                late=late_txt,
                early_out=early_txt,
                note=note,
                is_off=False,
                late_minutes=late_minutes,
                early_out_minutes=early_minutes,
                final_in_datetime=final_in_dt,
                final_out_datetime=final_out_dt,
                display_in_mode=display_in_mode,
                display_out_mode=display_out_mode,
            )
        )
        i += 1

    return rows


def get_monthly_attendance_rows(employee: Employee, month: str, **kwargs) -> List[MonthlyRecapRow]:
    """Shared helper for Attendance → Attendances monthly recap rows."""
    language = (kwargs.get("language") or kwargs.get("lang") or "en")
    return build_employee_monthly_recap(employee=employee, month_yyyy_mm=month, language=language)


def get_monthly_attendance_summary(employee: Employee, month: str, **kwargs) -> Dict[str, int]:
    """Shared helper returning plain integer minute totals for the recap summary."""
    rows = get_monthly_attendance_rows(employee, month, **kwargs)
    return summarize_monthly_recap_rows(rows).as_dict()


def get_monthly_attendance_recap(employee: Employee, month: str, **kwargs) -> Dict[str, object]:
    """Return shared monthly recap payload consumed by web, API, and PDF."""
    rows = get_monthly_attendance_rows(employee, month, **kwargs)
    return {
        "rows": rows,
        "summary": summarize_monthly_recap_rows(rows).as_dict(),
    }
