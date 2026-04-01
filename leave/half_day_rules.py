from __future__ import annotations

from datetime import date, datetime, timedelta
from typing import Dict, List, Optional, Set, Tuple

from django.apps import apps
from django.core.exceptions import ValidationError
from django.utils.translation import gettext_lazy as _

from base.models import EmployeeShiftDay, EmployeeShiftSchedule


HALF_DAY_FIRST = "first_half"
HALF_DAY_SECOND = "second_half"


def _day_key(target_date: date) -> str:
    return target_date.strftime("%A").lower()


def _employee_shift(employee):
    try:
        return employee.employee_work_info.shift_id
    except Exception:
        return None


def _schedule_for_shift_date(shift, shift_date: date) -> Optional[EmployeeShiftSchedule]:
    if not shift or not shift_date:
        return None
    day = EmployeeShiftDay.objects.filter(day=_day_key(shift_date)).first()
    if not day:
        return None
    return (
        EmployeeShiftSchedule.objects.filter(shift_id=shift, day=day)
        .select_related("day", "shift_id")
        .first()
    )


def _schedule_bounds(shift_date: date, schedule: Optional[EmployeeShiftSchedule]):
    if not schedule or not shift_date or not schedule.start_time or not schedule.end_time:
        return None, None
    start_dt = datetime.combine(shift_date, schedule.start_time)
    end_dt = datetime.combine(shift_date, schedule.end_time)
    if bool(getattr(schedule, "is_night_shift", False)) or schedule.end_time <= schedule.start_time:
        end_dt += timedelta(days=1)
    return start_dt, end_dt


def _attendance_or_activity_exists(employee, attendance_date: date) -> bool:
    if not apps.is_installed("attendance") or not employee or not attendance_date:
        return False

    from attendance.models import Attendance, AttendanceActivity

    attendance = (
        Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date)
        .only(
            "id",
            "attendance_clock_in",
            "attendance_clock_out",
            "attendance_clock_in_date",
            "attendance_clock_out_date",
        )
        .order_by("-id")
        .first()
    )
    if attendance and (
        getattr(attendance, "attendance_clock_in", None)
        or getattr(attendance, "attendance_clock_out", None)
    ):
        return True

    activity = (
        AttendanceActivity.objects.filter(employee_id=employee, attendance_date=attendance_date)
        .only("id", "clock_in", "clock_out", "clock_in_date", "clock_out_date")
        .order_by("-id")
        .first()
    )
    return bool(activity and (getattr(activity, "clock_in", None) or getattr(activity, "clock_out", None)))


def _raw_punch_exists(employee, start_dt: Optional[datetime], end_dt: Optional[datetime]) -> bool:
    if not apps.is_installed("attendance") or not employee or not start_dt or not end_dt:
        return False
    try:
        from attendance.models import AttendancePunchingHistory
    except Exception:
        return False

    buffer_start = start_dt - timedelta(hours=6)
    buffer_end = end_dt + timedelta(hours=6)
    return AttendancePunchingHistory.objects.filter(
        employee_id=employee,
        punch_timestamp__gte=buffer_start,
        punch_timestamp__lte=buffer_end,
    ).exists()


def _shift_instance_has_evidence(employee, attendance_date: date, start_dt: Optional[datetime], end_dt: Optional[datetime]) -> bool:
    return _attendance_or_activity_exists(employee, attendance_date) or _raw_punch_exists(employee, start_dt, end_dt)


def resolve_shift_schedule_context(employee, target_date: date) -> Dict[str, object]:
    """Resolve the most likely shift instance for a calendar date.

    Normal shifts map to the same day. For overnight shifts, the target calendar
    date may belong to the previous day's shift instance. Prefer the previous
    day when its schedule spans the target date and there is attendance/activity/raw
    punch evidence for that shift instance. If the current day has no schedule but
    the previous overnight schedule spans the target date, use the previous shift
    instance as a safe fallback.
    """

    if not employee or not target_date:
        return {
            "shift": None,
            "schedule": None,
            "attendance_date": target_date,
            "shift_start": None,
            "shift_end": None,
        }

    shift = _employee_shift(employee)
    if not shift:
        return {
            "shift": None,
            "schedule": None,
            "attendance_date": target_date,
            "shift_start": None,
            "shift_end": None,
        }

    direct_schedule = _schedule_for_shift_date(shift, target_date)
    direct_start, direct_end = _schedule_bounds(target_date, direct_schedule)

    prev_date = target_date - timedelta(days=1)
    prev_schedule = _schedule_for_shift_date(shift, prev_date)
    prev_start, prev_end = _schedule_bounds(prev_date, prev_schedule)
    prev_spans_target = bool(prev_start and prev_end and prev_start.date() <= target_date <= prev_end.date())

    if prev_spans_target:
        prev_has_evidence = _shift_instance_has_evidence(employee, prev_date, prev_start, prev_end)
        if prev_has_evidence or not direct_schedule:
            return {
                "shift": shift,
                "schedule": prev_schedule,
                "attendance_date": prev_date,
                "shift_start": prev_start,
                "shift_end": prev_end,
            }

    return {
        "shift": shift,
        "schedule": direct_schedule,
        "attendance_date": target_date,
        "shift_start": direct_start,
        "shift_end": direct_end,
    }


def schedule_for_employee_date(employee, target_date: date) -> Optional[EmployeeShiftSchedule]:
    return resolve_shift_schedule_context(employee, target_date).get("schedule")


def get_half_day_schedule_config(employee, target_date: date, breakdown: str) -> Dict[str, object]:
    context = resolve_shift_schedule_context(employee, target_date)
    schedule = context.get("schedule")
    if not schedule:
        return {
            "schedule": None,
            "attendance_date": context.get("attendance_date") or target_date,
            "enabled": False,
            "threshold_time": None,
            "require_check_out_before_submit": False,
            "shift_start": context.get("shift_start"),
            "shift_end": context.get("shift_end"),
        }

    if breakdown == HALF_DAY_FIRST:
        return {
            "schedule": schedule,
            "attendance_date": context.get("attendance_date") or target_date,
            "enabled": bool(bool(schedule)),
            "threshold_time": getattr(schedule, "first_half_leave_latest_check_in_time", None),
            "require_check_out_before_submit": False,
            "shift_start": context.get("shift_start"),
            "shift_end": context.get("shift_end"),
        }

    if breakdown == HALF_DAY_SECOND:
        return {
            "schedule": schedule,
            "attendance_date": context.get("attendance_date") or target_date,
            "enabled": bool(bool(schedule)),
            "threshold_time": None,
            "require_check_out_before_submit": bool(
                getattr(schedule, "require_check_out_before_second_half_leave", False)
            ),
            "shift_start": context.get("shift_start"),
            "shift_end": context.get("shift_end"),
        }

    return {
        "schedule": schedule,
        "attendance_date": context.get("attendance_date") or target_date,
        "enabled": False,
        "threshold_time": None,
        "require_check_out_before_submit": False,
        "shift_start": context.get("shift_start"),
        "shift_end": context.get("shift_end"),
    }


def leave_breakdown_for_date(
    *,
    start_date: date,
    end_date: date,
    start_date_breakdown: str,
    end_date_breakdown: str,
    target_date: date,
) -> str:
    if target_date < start_date or target_date > end_date:
        return ""
    if start_date == end_date:
        return start_date_breakdown or end_date_breakdown or "full_day"
    if target_date == start_date:
        return start_date_breakdown or "full_day"
    if target_date == end_date:
        return end_date_breakdown or "full_day"
    return "full_day"


def second_half_dates_for_request(
    *,
    start_date: date,
    end_date: date,
    start_date_breakdown: str,
    end_date_breakdown: str,
) -> List[date]:
    dates: List[date] = []
    current = start_date
    while current <= end_date:
        breakdown = leave_breakdown_for_date(
            start_date=start_date,
            end_date=end_date,
            start_date_breakdown=start_date_breakdown,
            end_date_breakdown=end_date_breakdown,
            target_date=current,
        )
        if breakdown == HALF_DAY_SECOND:
            dates.append(current)
        current = current.fromordinal(current.toordinal() + 1)
    return dates


def impacted_attendance_dates_for_calendar_date(employee, target_date: date) -> List[date]:
    impacted: Set[date] = set()
    if not target_date:
        return []

    impacted.add(target_date)
    context = resolve_shift_schedule_context(employee, target_date)
    attendance_date = context.get("attendance_date")
    if attendance_date:
        impacted.add(attendance_date)

    shift = _employee_shift(employee)
    prev_date = target_date - timedelta(days=1)
    prev_schedule = _schedule_for_shift_date(shift, prev_date)
    prev_start, prev_end = _schedule_bounds(prev_date, prev_schedule)
    if prev_start and prev_end and prev_start.date() <= target_date <= prev_end.date():
        impacted.add(prev_date)

    return sorted(impacted)


def impacted_attendance_dates_for_leave_request(
    *,
    employee,
    start_date: date,
    end_date: date,
) -> List[date]:
    impacted: Set[date] = set()
    current = start_date
    while current <= end_date:
        impacted.update(impacted_attendance_dates_for_calendar_date(employee, current))
        current = current.fromordinal(current.toordinal() + 1)
    return sorted(impacted)


def leave_breakdown_for_attendance_date(employee, attendance_date: date) -> str:
    """Resolve approved leave breakdown affecting a final attendance date.

    This checks nearby calendar dates and maps them back to the attendance date
    through impacted_attendance_dates_for_calendar_date(), which keeps overnight
    shifts aligned without depending on existing Attendance/Activity rows.
    """

    try:
        from leave.models import LeaveRequest
    except Exception:
        return ""

    priority = {"full_day": 3, HALF_DAY_FIRST: 2, HALF_DAY_SECOND: 2, "": 0}
    best = ""
    qs = LeaveRequest.objects.filter(
        employee_id=employee,
        status="approved",
        start_date__lte=attendance_date + timedelta(days=1),
        end_date__gte=attendance_date - timedelta(days=1),
    ).order_by("-id")

    for leave_request in qs:
        current = leave_request.start_date
        while current <= leave_request.end_date:
            if attendance_date in impacted_attendance_dates_for_calendar_date(employee, current):
                breakdown = leave_breakdown_for_date(
                    start_date=leave_request.start_date,
                    end_date=leave_request.end_date,
                    start_date_breakdown=leave_request.start_date_breakdown,
                    end_date_breakdown=leave_request.end_date_breakdown,
                    target_date=current,
                )
                if priority.get(breakdown, 0) > priority.get(best, 0):
                    best = breakdown
                    if best == "full_day":
                        return best
            current = current.fromordinal(current.toordinal() + 1)
    return best


def _raw_punch_state(employee, candidate_dates: List[date]) -> Tuple[bool, bool]:
    if not apps.is_installed("attendance") or not employee or not candidate_dates:
        return False, False

    try:
        from attendance.models import AttendancePunchDirection, AttendancePunchingHistory
    except Exception:
        return False, False

    shift = _employee_shift(employee)
    has_in = False
    has_out = False
    for att_date in candidate_dates:
        schedule = _schedule_for_shift_date(shift, att_date)
        start_dt, end_dt = _schedule_bounds(att_date, schedule)
        qs = AttendancePunchingHistory.objects.filter(employee_id=employee)
        if start_dt and end_dt:
            qs = qs.filter(
                punch_timestamp__gte=start_dt - timedelta(hours=6),
                punch_timestamp__lte=end_dt + timedelta(hours=6),
            )
        else:
            qs = qs.filter(attendance_date=att_date)

        if qs.filter(punch_direction=AttendancePunchDirection.IN).exists():
            has_in = True
        if qs.filter(punch_direction=AttendancePunchDirection.OUT).exists():
            has_out = True
        if has_in or has_out:
            break

    return has_in, has_out


def _current_day_check_state(employee, target_date: date) -> Tuple[bool, bool]:
    if not apps.is_installed("attendance"):
        return False, False

    from attendance.models import Attendance, AttendanceActivity

    candidate_dates = impacted_attendance_dates_for_calendar_date(employee, target_date)
    attendance_by_date = {
        obj.attendance_date: obj
        for obj in Attendance.objects.filter(
            employee_id=employee,
            attendance_date__in=candidate_dates,
        ).order_by("-attendance_date", "-id")
    }
    for att_date in candidate_dates:
        attendance = attendance_by_date.get(att_date)
        if attendance:
            has_in = bool(getattr(attendance, "attendance_clock_in", None))
            has_out = bool(getattr(attendance, "attendance_clock_out", None))
            if has_in or has_out:
                return has_in, has_out

    activity_by_date = {
        obj.attendance_date: obj
        for obj in AttendanceActivity.objects.filter(
            employee_id=employee,
            attendance_date__in=candidate_dates,
        ).order_by("-attendance_date", "-id")
    }
    for att_date in candidate_dates:
        activity = activity_by_date.get(att_date)
        if activity:
            has_in = bool(getattr(activity, "clock_in", None))
            has_out = bool(getattr(activity, "clock_out", None))
            if has_in or has_out:
                return has_in, has_out

    return _raw_punch_state(employee, candidate_dates)


def validate_second_half_leave_submission(
    *,
    employee,
    start_date: date,
    end_date: date,
    start_date_breakdown: str,
    end_date_breakdown: str,
):
    for target_date in second_half_dates_for_request(
        start_date=start_date,
        end_date=end_date,
        start_date_breakdown=start_date_breakdown,
        end_date_breakdown=end_date_breakdown,
    ):
        cfg = get_half_day_schedule_config(employee, target_date, HALF_DAY_SECOND)
        if not cfg.get("require_check_out_before_submit"):
            continue
        has_in, has_out = _current_day_check_state(employee, target_date)
        if has_in and not has_out:
            raise ValidationError(
                _("You must check out first before submitting second half leave.")
            )
