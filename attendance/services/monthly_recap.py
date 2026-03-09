"""attendance.services.monthly_recap

Compute rows for **Attendance → Attendances (Monthly Recap)**.

This service is shared by the web view and API endpoint.
"""

from __future__ import annotations

import calendar
from dataclasses import dataclass
from datetime import date, datetime, time, timedelta
from typing import Dict, Iterable, List, Optional, Set, Tuple

from django.conf import settings
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceWorkMode,
    WorkModeRequest,
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
    resolve_final_session,
)
from attendance.services.monthly_recap_note import (
    NoteInputs,
    derive_note,
    localize_on_duty_work_type,
    seconds_to_hhmm,
)
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


def _localize_shift_information(text: str, language: str) -> str:
    """Localize only the *phrases* inside the Shift Information string."""
    if not text:
        return text
    lang = (language or "en").lower()
    if not lang.startswith("id"):
        return text
    return (
        text.replace("Flexi In", "Waktu Fleksibel")
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
    if isinstance(obj, Attendance):
        if session_norm == "IN":
            return getattr(obj, "attendance_clock_in_channel", None)
        return getattr(obj, "attendance_clock_out_channel", None)
    if session_norm == "IN":
        return getattr(obj, "clock_in_channel", None)
    return getattr(obj, "clock_out_channel", None)


def _session_dt(obj, session: str, attendance_date: date) -> Optional[datetime]:
    session_norm = (session or "IN").upper()
    if isinstance(obj, Attendance):
        if session_norm == "IN":
            return _combine_dt(
                getattr(obj, "attendance_clock_in_date", None),
                getattr(obj, "attendance_clock_in", None),
                attendance_date,
            )
        return _combine_dt(
            getattr(obj, "attendance_clock_out_date", None),
            getattr(obj, "attendance_clock_out", None),
            attendance_date,
        )

    if session_norm == "IN":
        return getattr(obj, "in_datetime", None) or _combine_dt(
            getattr(obj, "clock_in_date", None),
            getattr(obj, "clock_in", None),
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
        if _session_channel(obj, session_norm) == APPROVED_REQUEST_CHANNEL:
            dt_obj = _session_dt(obj, session_norm, attendance_date)
            if dt_obj:
                return _normalize_dt(dt_obj, tzinfo)

    for obj in sorted(activities, key=lambda x: x.id, reverse=True):
        if _session_channel(obj, session_norm) == APPROVED_REQUEST_CHANNEL:
            dt_obj = _session_dt(obj, session_norm, attendance_date)
            if dt_obj:
                return _normalize_dt(dt_obj, tzinfo)

    for obj in sorted(attendances, key=lambda x: x.id, reverse=True):
        dt_obj = _legacy_approved_request_dt(obj, session_norm, attendance_date)
        if dt_obj:
            return _normalize_dt(dt_obj, tzinfo)

    return None


def _work_mode_label(mode: str) -> str:
    if mode == AttendanceWorkMode.ON_DUTY:
        return "On Duty"
    if mode == AttendanceWorkMode.WFA:
        return "WFA"
    return "WFO"


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
        if r.status not in [WorkModeRequestStatus.REJECTED, WorkModeRequestStatus.CANCELED]
    ]
    request_status_by_id = {
        getattr(r, "id", None): getattr(r, "status", None)
        for r in all_requests
        if getattr(r, "id", None) is not None
    }

    leave_qs = LeaveRequest.objects.filter(
        employee_id=employee,
        status="approved",
        start_date__lte=last_day,
        end_date__gte=first_day,
    )
    leave_dates: Set[date] = set()
    for lr in leave_qs:
        sd = lr.start_date
        ed = lr.end_date or lr.start_date
        cur = sd
        while cur <= ed:
            if first_day <= cur <= last_day:
                leave_dates.add(cur)
            cur = cur + timedelta(days=1)

    day_objs = {d.day: d for d in EmployeeShiftDay.objects.all()}

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

        if is_off:
            if is_leave:
                shift_info = _localize_shift_information("On Leave", language)
                note = derive_note(NoteInputs(is_off=True, off_kind="leave"), language=language)
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
            if _should_use_raw_punch_source(a, request_status_by_id, session="IN") and _session_channel(a, "IN") != APPROVED_REQUEST_CHANNEL:
                dt_in = _combine_dt(
                    getattr(a, "attendance_clock_in_date", None),
                    getattr(a, "attendance_clock_in", None),
                    a.attendance_date,
                )
                if dt_in:
                    in_dts_raw.append(_normalize_dt(dt_in))
            if _should_use_raw_punch_source(a, request_status_by_id, session="OUT") and _session_channel(a, "OUT") != APPROVED_REQUEST_CHANNEL:
                dt_out = _combine_dt(
                    getattr(a, "attendance_clock_out_date", None),
                    getattr(a, "attendance_clock_out", None),
                    a.attendance_date,
                )
                if dt_out:
                    out_dts_raw.append(_normalize_dt(dt_out))

        for ac in act_list:
            if _should_use_raw_punch_source(ac, request_status_by_id, session="IN") and _session_channel(ac, "IN") != APPROVED_REQUEST_CHANNEL:
                dt_in = getattr(ac, "in_datetime", None) or _combine_dt(
                    getattr(ac, "clock_in_date", None),
                    getattr(ac, "clock_in", None),
                    ac.attendance_date,
                )
                if dt_in:
                    in_dts_raw.append(_normalize_dt(dt_in))
            if _should_use_raw_punch_source(ac, request_status_by_id, session="OUT") and _session_channel(ac, "OUT") != APPROVED_REQUEST_CHANNEL:
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

        final_in_dt = resolve_final_session(
            session="IN",
            approved_dt=approved_in_dt,
            raw_datetimes=in_dts,
            raw_source="raw",
        ).final_dt
        final_out_dt = resolve_final_session(
            session="OUT",
            approved_dt=approved_out_dt,
            raw_datetimes=out_dts,
            raw_source="raw",
        ).final_dt

        shift_start_dt = _normalize_dt(rules.get("shift_start_dt"), tzinfo)
        shift_end_dt = _normalize_dt(rules.get("shift_end_dt"), tzinfo)
        cutoff_in_dt = _normalize_dt(
            rules.get("cutoff_in_dt") or rules.get("check_in_window_end_dt"),
            tzinfo,
        )
        final_in_dt = _normalize_dt(final_in_dt, tzinfo)
        final_out_dt = _normalize_dt(final_out_dt, tzinfo)

        grace_in_sec = int(rules.get("grace_seconds") or 0)
        grace_out_sec = 0
        try:
            grace_time = _resolve_grace_time(rules.get("schedule"), shift)
            if grace_time and getattr(grace_time, "allowed_clock_out", False):
                grace_out_sec = int(getattr(grace_time, "allowed_time_in_secs", 0) or 0)
        except Exception:
            grace_out_sec = 0

        baseline_mode = scheduled_attendance_mode(employee, d)
        if best_att and getattr(best_att, "work_type_id", None):
            try:
                wt_name = getattr(best_att.work_type_id, "work_type", "") or ""
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

        if eff_in_mode == AttendanceWorkMode.ON_DUTY and eff_out_mode == AttendanceWorkMode.ON_DUTY:
            work_type_disp = "On Duty FULL"
        elif eff_in_mode == AttendanceWorkMode.ON_DUTY and eff_out_mode != AttendanceWorkMode.ON_DUTY:
            work_type_disp = "On Duty IN"
        elif eff_out_mode == AttendanceWorkMode.ON_DUTY and eff_in_mode != AttendanceWorkMode.ON_DUTY:
            work_type_disp = "On Duty OUT"
        elif eff_in_mode == eff_out_mode:
            work_type_disp = _work_mode_label(eff_in_mode)
        else:
            work_type_disp = f"IN: {_work_mode_label(eff_in_mode)}<br>OUT: {_work_mode_label(eff_out_mode)}"

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

        shift_info = "—"
        try:
            st = rules.get("start_time")
            et = rules.get("end_time")
            if st and et:
                shift_info = f"{st.strftime('%H:%M')} - {et.strftime('%H:%M')}"
                flexi_min = int((grace_in_sec or 0) // 60)
                shift_info += f" • Flexi In: {flexi_min}m"
        except Exception:
            shift_info = "—"

        work_mode_pending_suffixes = _pending_work_mode_suffixes(
            requests=requests,
            attendance_date=d,
            language=language,
            shift_start_time=rules.get("start_time"),
            shift_end_time=rules.get("end_time"),
        )
        note_suffixes = attendance_request_suffixes + work_mode_pending_suffixes
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


def get_monthly_attendance_rows(employee: Employee, month: str, **kwargs) -> List[MonthlyRecapRow]:
    """Shared helper for Attendance → Attendances monthly recap rows."""
    language = (kwargs.get("language") or kwargs.get("lang") or "en")
    return build_employee_monthly_recap(employee=employee, month_yyyy_mm=month, language=language)
