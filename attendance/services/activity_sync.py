"""Helpers to keep single-session AttendanceActivity aligned with final Attendance.

Pre-launch integrity rules:
- never fabricate a check-in
- preserve explicit channel/source fields
- approved requests only mark the sessions they actually replace
- activity sync must be null-safe for OUT-only or IN-only records
"""

from __future__ import annotations

from datetime import date, datetime, timedelta
from typing import Optional, Tuple

from django.core.exceptions import ValidationError
from django.db import IntegrityError
from django.utils import timezone

from attendance.methods.utils import shift_schedule_today
from attendance.models import Attendance, AttendanceActivity
from attendance.services.attendance_correction_scope_rules import load_requested_data
from base.models import EmployeeShift, EmployeeShiftDay


APPROVED_REQUEST_CHANNEL = "approved_request"
CORRECTION_REQUEST_CHANNEL = "correction_request"


def _normalize_none(value):
    if value is None:
        return None
    if isinstance(value, str) and value.strip() in ("", "None", "null", "NULL"):
        return None
    return value



def _combine_dt(d, t):
    if not d or not t:
        return None
    try:
        value = datetime.combine(d, t)
        if timezone.is_aware(timezone.now()):
            if timezone.is_naive(value):
                value = timezone.make_aware(value, timezone.get_current_timezone())
            else:
                value = timezone.localtime(value, timezone.get_current_timezone())
        elif timezone.is_aware(value):
            value = timezone.make_naive(value, timezone.get_current_timezone())
        return value
    except Exception:
        return None


def _approved_channel_for(attendance: Attendance) -> str:
    request_type = getattr(attendance, "request_type", None)
    if request_type == "create_request":
        return APPROVED_REQUEST_CHANNEL
    return CORRECTION_REQUEST_CHANNEL


def _requested_sessions(attendance: Attendance) -> Tuple[bool, bool]:
    data = load_requested_data(getattr(attendance, "requested_data", None))

    in_present = _normalize_none(data.get("attendance_clock_in")) not in (None, "None")
    out_present = _normalize_none(data.get("attendance_clock_out")) not in (None, "None")

    meta = data.get("__meta") or {}
    scopes = meta.get("approved_scopes") or []
    current_scope = str(meta.get("current_scope") or "").upper()

    scope_set = {str(item).upper() for item in scopes if item}
    if current_scope:
        if current_scope in ("FULL", "BOTH"):
            scope_set.update({"IN", "OUT"})
        else:
            scope_set.add(current_scope)

    if scope_set:
        if "FULL" in scope_set or "BOTH" in scope_set:
            scope_set.update({"IN", "OUT"})
        in_present = in_present or ("IN" in scope_set)
        out_present = out_present or ("OUT" in scope_set)

    return in_present, out_present


def get_requested_sessions(attendance: Attendance) -> Tuple[bool, bool]:
    """Public wrapper returning whether the request overrides IN and/or OUT."""

    return _requested_sessions(attendance)


def mark_approved_request_channels(attendance: Attendance) -> Attendance:
    """Persist explicit request source for only the approved sessions."""

    wants_in, wants_out = _requested_sessions(attendance)
    channel = _approved_channel_for(attendance)
    updates = []

    if wants_in and getattr(attendance, "attendance_clock_in", None) and getattr(attendance, "attendance_clock_in_date", None):
        attendance.attendance_clock_in_channel = channel
        updates.append("attendance_clock_in_channel")

    if wants_out and getattr(attendance, "attendance_clock_out", None) and getattr(attendance, "attendance_clock_out_date", None):
        attendance.attendance_clock_out_channel = channel
        updates.append("attendance_clock_out_channel")

    if updates:
        attendance.save(update_fields=updates)
    return attendance


def _locked_activity(employee, attendance_date: date):
    qs = (
        AttendanceActivity.objects.select_for_update()
        .filter(employee_id=employee, attendance_date=attendance_date)
        .order_by("-id")
    )
    activity = qs.first()
    if activity:
        qs.exclude(id=activity.id).delete()
        return activity
    try:
        return AttendanceActivity.objects.create(employee_id=employee, attendance_date=attendance_date)
    except IntegrityError:
        activity = (
            AttendanceActivity.objects.select_for_update()
            .filter(employee_id=employee, attendance_date=attendance_date)
            .order_by("-id")
            .first()
        )
        if activity:
            AttendanceActivity.objects.select_for_update().filter(
                employee_id=employee, attendance_date=attendance_date
            ).exclude(id=activity.id).delete()
        return activity


def sync_single_session_activity(attendance: Attendance, prev_attendance_date: Optional[date] = None) -> AttendanceActivity:
    """Sync exactly one AttendanceActivity row to the final Attendance row.

    Honest sync rules:
    - if only OUT exists, keep IN null
    - if only IN exists, keep OUT null
    - never invent placeholder values
    """

    employee = attendance.employee_id
    target_date = attendance.attendance_date

    if prev_attendance_date and prev_attendance_date != target_date:
        old_qs = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=prev_attendance_date)
        if old_qs.exists():
            if not AttendanceActivity.objects.filter(employee_id=employee, attendance_date=target_date).exists():
                old_qs.update(attendance_date=target_date)
            else:
                old_qs.delete()

    activity = _locked_activity(employee, target_date)
    if activity is None:
        activity = AttendanceActivity(employee_id=employee, attendance_date=target_date)

    day = getattr(attendance, "attendance_day", None)
    if day is None and target_date is not None:
        day = EmployeeShiftDay.objects.filter(day=target_date.strftime("%A").lower()).first()

    activity.employee_id = employee
    activity.attendance_date = target_date
    activity.shift_day = day

    in_date = getattr(attendance, "attendance_clock_in_date", None)
    in_time = getattr(attendance, "attendance_clock_in", None)
    activity.clock_in_date = in_date if in_time else None
    activity.clock_in = in_time if in_date else None
    activity.in_datetime = _combine_dt(activity.clock_in_date, activity.clock_in)

    out_date = getattr(attendance, "attendance_clock_out_date", None)
    out_time = getattr(attendance, "attendance_clock_out", None)
    activity.clock_out_date = out_date if out_time else None
    activity.clock_out = out_time if out_date else None
    activity.out_datetime = _combine_dt(activity.clock_out_date, activity.clock_out)

    activity.clock_in_channel = getattr(attendance, "attendance_clock_in_channel", None)
    activity.clock_out_channel = getattr(attendance, "attendance_clock_out_channel", None)
    activity.clock_in_image = getattr(attendance, "attendance_clock_in_image", None)
    activity.clock_out_image = getattr(attendance, "attendance_clock_out_image", None)
    activity.clock_in_mode = getattr(attendance, "attendance_clock_in_mode", None)
    activity.clock_out_mode = getattr(attendance, "attendance_clock_out_mode", None)
    activity.clock_in_location = getattr(attendance, "attendance_clock_in_location", None)
    activity.clock_out_location = getattr(attendance, "attendance_clock_out_location", None)
    activity.work_mode_request_id = getattr(attendance, "work_mode_request_id", None)

    activity.save()
    return activity


def _time_in_window(target_time, start_dt, end_dt) -> bool:
    if target_time is None or start_dt is None or end_dt is None:
        return False

    current_tz = timezone.get_current_timezone()
    windows_are_aware = timezone.is_aware(start_dt) or timezone.is_aware(end_dt)

    def normalize_dt(value):
        if value is None:
            return None
        if windows_are_aware:
            if timezone.is_naive(value):
                return timezone.make_aware(value, current_tz)
            return timezone.localtime(value, current_tz)
        if timezone.is_aware(value):
            return timezone.make_naive(value, current_tz)
        return value

    candidate = normalize_dt(datetime.combine(start_dt.date(), target_time))
    start = normalize_dt(start_dt)
    end = normalize_dt(end_dt)

    if candidate is None or start is None or end is None:
        return False

    if end < start:
        end = end + timedelta(days=1)
    if candidate < start and end.date() > start.date():
        candidate = candidate + timedelta(days=1)
    return start <= candidate <= end


def validate_requested_data_with_windows(attendance: Attendance) -> Tuple[bool, Optional[str]]:
    """Validate request approval context.

    Returns ``(False, error)`` only for genuinely invalid approval context, such as
    missing shift/day information. Window mismatches return ``(True, warning)`` so
    the request can still proceed with manual approver judgement.
    """

    data = load_requested_data(getattr(attendance, "requested_data", None))
    if not data:
        return True, None

    attendance_date = _normalize_none(data.get("attendance_date")) or getattr(attendance, "attendance_date", None)
    if isinstance(attendance_date, str):
        try:
            attendance_date = date.fromisoformat(attendance_date)
        except Exception:
            attendance_date = getattr(attendance, "attendance_date", None)

    shift = getattr(attendance, "shift_id", None)
    shift_id = _normalize_none(data.get("shift_id"))
    if shift is None and shift_id:
        try:
            shift = EmployeeShift.objects.filter(id=shift_id).first()
        except Exception:
            shift = None
    if shift is None:
        shift = getattr(getattr(getattr(attendance, "employee_id", None), "employee_work_info", None), "shift_id", None)

    if not attendance_date or not shift:
        return False, "Attendance request cannot be approved because shift/date context is incomplete."

    day_obj = EmployeeShiftDay.objects.filter(day=attendance_date.strftime("%A").lower()).first()
    if not day_obj:
        return False, "Attendance request cannot be approved because shift day is missing."

    _min_h, start_sec, end_sec = shift_schedule_today(day=day_obj, shift=shift)

    try:
        from attendance.views.clock_in_out import get_shift_rules

        rules = get_shift_rules(
            attendance_date,
            shift,
            day_obj,
            start_time_sec=start_sec,
            end_time_sec=end_sec,
        ) or {}
    except Exception:
        rules = {}

    in_time = _normalize_none(data.get("attendance_clock_in"))
    out_time = _normalize_none(data.get("attendance_clock_out"))

    if isinstance(in_time, str):
        for fmt in ("%H:%M:%S", "%H:%M"):
            try:
                in_time = datetime.strptime(in_time, fmt).time()
                break
            except Exception:
                continue
    if isinstance(out_time, str):
        for fmt in ("%H:%M:%S", "%H:%M"):
            try:
                out_time = datetime.strptime(out_time, fmt).time()
                break
            except Exception:
                continue

    warnings = []

    in_start = rules.get("check_in_window_start_dt")
    in_end = rules.get("check_in_window_end_dt")
    out_start = rules.get("check_out_window_start_dt")
    out_end = rules.get("check_out_window_end_dt")

    if in_time:
        if in_start is None or in_end is None:
            warnings.append("Requested check-in is outside the configured attendance window and requires manual approval review.")
        elif not _time_in_window(in_time, in_start, in_end):
            warnings.append("Requested check-in is outside the allowed attendance window and requires manual approval review.")

    if out_time:
        if out_start is None or out_end is None:
            warnings.append("Requested check-out is outside the configured attendance window and requires manual approval review.")
        elif not _time_in_window(out_time, out_start, out_end):
            warnings.append("Requested check-out is outside the allowed attendance window and requires manual approval review.")

    if warnings:
        return True, " ".join(dict.fromkeys(warnings))

    return True, None
