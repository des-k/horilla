"""
clock_in_out.py

Endpoints for check-in / check-out in single-session mode:
- One Attendance + one AttendanceActivity per (employee, attendance_date)
- Grace time resolution: schedule -> shift -> default
- Cutoff check-in: block after cutoff
- Cutoff check-out: block after cutoff (must submit request)
- Check-out is allowed even if check-in is missing (creates an incomplete skeleton);
  check-in can be fixed later via Attendance Request.
"""

import ipaddress
import logging
from datetime import date, datetime, time, timedelta

from django.contrib import messages
from django.http import HttpResponse
from django.utils.translation import gettext_lazy as _
from django.db import transaction
from django.conf import settings
from django.utils import timezone as dj_timezone


from attendance.methods.utils import (
    employee_exists,
    format_time,
    overtime_calculation,
    shift_schedule_today,
    strtime_seconds,
)
from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceGeneralSetting,
    AttendanceLateComeEarlyOut,
    GraceTime,
)
from attendance.views.views import attendance_validate
from base.context_processors import (
    enable_late_come_early_out_tracking,
    timerunner_enabled,
)
from base.models import AttendanceAllowedIP, Company, EmployeeShiftDay, EmployeeShiftSchedule
from horilla.decorators import hx_request_required, login_required
from typing import Optional

logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------
# Helpers: request time, schedule, cutoff, grace time
# ---------------------------------------------------------------------
def _now_local() -> datetime:
    """Return current time for business-rule comparisons (local time when USE_TZ=True)."""
    if getattr(settings, "USE_TZ", False):
        return dj_timezone.localtime(dj_timezone.now())
    return datetime.now()


def _get_request_datetime(request=None) -> datetime:
    """Return a datetime to use for attendance rules.

    Important: keep timezone-consistent with shift schedule datetimes.
    - When USE_TZ=True: always return tz-aware local time.
    - When USE_TZ=False: always return tz-naive local time.
    """
    dt = None
    if request is not None:
        dt = getattr(request, "datetime", None)

    if dt:
        if getattr(settings, "USE_TZ", False):
            if dj_timezone.is_naive(dt):
                dt = dj_timezone.make_aware(dt, dj_timezone.get_current_timezone())
            return dj_timezone.localtime(dt)

        # USE_TZ=False
        if dj_timezone.is_aware(dt):
            dt = dj_timezone.make_naive(dt, dj_timezone.get_current_timezone())
        return dt

    return _now_local()

def _get_schedule(shift, day):
    """
    Return EmployeeShiftSchedule for the given shift and day (EmployeeShiftDay).
    Use a direct query to avoid dependency on related_name.
    """
    return EmployeeShiftSchedule.objects.filter(shift_id=shift, day=day).first()


def _combine_shift_datetime(attendance_date: date, t: time) -> datetime:
    """Combine date + time into a datetime consistent with Django timezone settings."""
    dt = datetime.combine(attendance_date, t)
    if getattr(settings, "USE_TZ", False):
        return dj_timezone.make_aware(dt, dj_timezone.get_current_timezone())
    return dt

def _calc_cutoff_in_dt(
    attendance_date: date,
    start_time: time | None,
    grace_time_min: int | None,
    cutoff_in_time: time | None,
) -> datetime | None:
    """Return the last allowed datetime for clock-in.

    Returns tz-aware local datetime when USE_TZ=True, otherwise tz-naive datetime.
    """
    if cutoff_in_time:
        return _combine_shift_datetime(attendance_date, cutoff_in_time)

    if not start_time:
        return None

    base = _combine_shift_datetime(attendance_date, start_time)
    return base + timedelta(minutes=int(grace_time_min or 0))

def _calc_cutoff_out_dt(
    attendance_date: date,
    end_time: time | None,
    cutoff_out_time: time | None,
    is_night_shift: bool = False,
) -> datetime | None:
    """Return the last allowed datetime for clock-out.

    Returns tz-aware local datetime when USE_TZ=True, otherwise tz-naive datetime.
    """
    if cutoff_out_time:
        out_dt = _combine_shift_datetime(attendance_date, cutoff_out_time)
    elif end_time:
        out_dt = _combine_shift_datetime(attendance_date, end_time)
    else:
        return None

    if is_night_shift:
        out_dt = out_dt + timedelta(days=1)

    return out_dt

def _resolve_grace_time(schedule, shift):
    """
    Resolve grace time in priority order:
    1) schedule.grace_time_id (day-level override)
    2) shift.grace_time_id
    3) default GraceTime (is_default=True)
    """
    if schedule and schedule.grace_time_id and schedule.grace_time_id.is_active:
        return schedule.grace_time_id
    if shift and shift.grace_time_id and shift.grace_time_id.is_active:
        return shift.grace_time_id
    return GraceTime.objects.filter(is_default=True, is_active=True).first()

def _time_like_to_hhmm(time_like) -> Optional[str]:
    """
    Accept TimeField, datetime, or string ("HH:MM" / "HH:MM:SS") and return "HH:MM".
    Return None if cannot parse.
    """
    if not time_like:
        return None

    if hasattr(time_like, "strftime"):
        # datetime.time or datetime.datetime
        return time_like.strftime("%H:%M")

    if isinstance(time_like, str):
        # Accept both "HH:MM:SS" and "HH:MM"
        try:
            return datetime.strptime(time_like, "%H:%M:%S").strftime("%H:%M")
        except ValueError:
            try:
                return datetime.strptime(time_like, "%H:%M").strftime("%H:%M")
            except ValueError:
                return None

    return None


# ---------------------------------------------------------------------
# Late come / Early out tracking (grace time schedule-level)
# ---------------------------------------------------------------------
def late_come_create(attendance):
    """
    Create/replace late come record for an Attendance.
    """
    obj = AttendanceLateComeEarlyOut.objects.filter(type="late_come", attendance_id=attendance).first()
    if not obj:
        obj = AttendanceLateComeEarlyOut()

    obj.type = "late_come"
    obj.attendance_id = attendance
    obj.employee_id = attendance.employee_id
    obj.save()
    return obj


def late_come(attendance, start_time, end_time, shift, schedule=None):
    """
    Mark late check-in using grace time resolution:
    schedule -> shift -> default
    """
    if not enable_late_come_early_out_tracking(None).get("tracking"):
        return

    hhmm = _time_like_to_hhmm(attendance.attendance_clock_in)
    if not hhmm:
        return

    now_sec = strtime_seconds(hhmm)
    mid_day_sec = strtime_seconds("12:00")

    grace_time = _resolve_grace_time(schedule, shift)
    if grace_time and grace_time.allowed_clock_in:
        now_sec -= grace_time.allowed_time_in_secs

    # Night shift logic
    if start_time > end_time and start_time != end_time:
        if now_sec < mid_day_sec:
            late_come_create(attendance)
        elif now_sec > start_time:
            late_come_create(attendance)
    elif start_time < now_sec:
        late_come_create(attendance)

    return True


def early_out_create(attendance):
    """
    Create/replace early out record for an Attendance.
    """
    obj = AttendanceLateComeEarlyOut.objects.filter(type="early_out", attendance_id=attendance).first()
    if not obj:
        obj = AttendanceLateComeEarlyOut()

    obj.type = "early_out"
    obj.attendance_id = attendance
    obj.employee_id = attendance.employee_id
    obj.save()
    return obj


def early_out(attendance, start_time, end_time, shift, schedule=None):
    """
    Mark early check-out using grace time resolution:
    schedule -> shift -> default
    """
    if not enable_late_come_early_out_tracking(None).get("tracking"):
        return

    hhmm = _time_like_to_hhmm(attendance.attendance_clock_out)
    if not hhmm:
        return

    now_sec = strtime_seconds(hhmm)
    mid_day_sec = strtime_seconds("12:00")

    grace_time = _resolve_grace_time(schedule, shift)
    if grace_time and grace_time.allowed_clock_out:
        now_sec += grace_time.allowed_time_in_secs

    # Existing Horilla logic
    if start_time > end_time:
        # Night shift
        if now_sec < mid_day_sec:
            if now_sec < end_time:
                early_out_create(attendance)
        else:
            early_out_create(attendance)
        return

    if end_time > now_sec:
        early_out_create(attendance)

    return

@transaction.atomic
def clock_in_attendance_and_activity(
    employee,
    date_today,
    attendance_date,
    day,
    now_hhmm,
    shift,
    minimum_hour,
    start_time_sec,
    end_time_sec,
    in_datetime,
    clock_in_image=None,
):
    """
    Single-session mode:
    - Create ONE AttendanceActivity per (employee, attendance_date).
    - If already exists, do NOT create a new one (no-op).
    - Attendance summary remains one per (employee, attendance_date).
    """

    # 1) AttendanceActivity: create once
    activity, created = AttendanceActivity.objects.get_or_create(
        employee_id=employee,
        attendance_date=attendance_date,
        defaults={
            "clock_in_date": date_today,
            "shift_day": day,
            "clock_in": in_datetime.time(),   # TimeField expected
            "in_datetime": in_datetime,       # DateTimeField expected
            "clock_in_image": clock_in_image,
        },
    )

    if not created:
        # Keep original check-in; allow patching shift_day and saving first image only
        updates = []
        if getattr(activity, "shift_day_id", None) != day.id:
            activity.shift_day = day
            updates.append("shift_day")
        if clock_in_image and not getattr(activity, "clock_in_image", None):
            activity.clock_in_image = clock_in_image
            updates.append("clock_in_image")
        if updates:
            activity.save(update_fields=updates)

    # 2) Attendance summary: create once
    attendance, attendance_created = Attendance.objects.get_or_create(
        employee_id=employee,
        attendance_date=attendance_date,
        defaults={
            "shift_id": shift,
            "work_type_id": employee.employee_work_info.work_type_id,
            "attendance_day": day,
            "attendance_clock_in": now_hhmm,
            "attendance_clock_in_date": date_today,
            "minimum_hour": minimum_hour,
            "attendance_clock_in_image": clock_in_image if clock_in_image else None,
        },
    )

    if not attendance_created:
        # Self-healing (DO NOT overwrite check-in time/date)
        updates = []

        # Keep metadata consistent
        if not attendance.attendance_day_id or attendance.attendance_day_id != day.id:
            attendance.attendance_day = day
            updates.append("attendance_day")

        if attendance.shift_id_id != (shift.id if shift else None):
            attendance.shift_id = shift
            updates.append("shift_id")

        if attendance.minimum_hour != minimum_hour:
            attendance.minimum_hour = minimum_hour
            updates.append("minimum_hour")

        if not attendance.work_type_id:
            attendance.work_type_id = employee.employee_work_info.work_type_id
            updates.append("work_type_id")

        # Keep the first image only (optional behavior)
        if clock_in_image and not getattr(attendance, "attendance_clock_in_image", None):
            attendance.attendance_clock_in_image = clock_in_image
            updates.append("attendance_clock_in_image")

        if updates:
            attendance.save(update_fields=updates)

    # Late come only once on first Attendance creation
    if attendance_created:
        attendance = Attendance.find(attendance.id)
        schedule = _get_schedule(shift, day)
        late_come(
            attendance=attendance,
            start_time=start_time_sec,
            end_time=end_time_sec,
            shift=shift,
            schedule=schedule,
        )

    return attendance

@transaction.atomic
def clock_out_attendance_and_activity(
    employee,
    attendance_date,
    shift,
    minimum_hour,
    out_datetime,
    day=None,
    clock_out_image=None,
):
    """
    Single-session mode (NOT nullable clock_in):
    - Allow check-out even if check-in is missing.
    - Ensure Attendance + AttendanceActivity exist for (employee, attendance_date).
    - If check-in is missing, create placeholder: clock_in = clock_out (duration becomes 0).
    - Keep the latest check-out (last punch wins).
    - Return (attendance, missing_check_in_flag).
    """

    # Ensure day exists (avoid FK null issues)
    if day is None:
        day_name = attendance_date.strftime("%A").lower()
        day = EmployeeShiftDay.objects.get(day=day_name)

    out_date = out_datetime.date()
    out_time = out_datetime.time()

    # 1) Ensure Attendance exists (skeleton allowed)
    attendance, _ = Attendance.objects.get_or_create(
        employee_id=employee,
        attendance_date=attendance_date,
        defaults={
            "shift_id": shift,
            "work_type_id": employee.employee_work_info.work_type_id,
            "minimum_hour": minimum_hour,
            "attendance_day": day,
            # Missing check-in by default; corrected later via Attendance Request
            "attendance_clock_in": None,
            "attendance_clock_in_date": None,
            "attendance_validated": False,
        },
    )

    # Sync critical fields
    updates = []
    if attendance.shift_id_id != (shift.id if shift else None):
        attendance.shift_id = shift
        updates.append("shift_id")
    if not attendance.work_type_id:
        attendance.work_type_id = employee.employee_work_info.work_type_id
        updates.append("work_type_id")
    if attendance.minimum_hour != minimum_hour:
        attendance.minimum_hour = minimum_hour
        updates.append("minimum_hour")
    if not attendance.attendance_day_id or attendance.attendance_day_id != day.id:
        attendance.attendance_day = day
        updates.append("attendance_day")
    if updates:
        attendance.save(update_fields=updates)

    missing_check_in = not attendance.attendance_clock_in or not attendance.attendance_clock_in_date

    # 2) Ensure AttendanceActivity exists (clock_in NOT NULL -> placeholder if missing)
    placeholder_in_date = attendance.attendance_clock_in_date or attendance_date
    placeholder_in_time = attendance.attendance_clock_in or out_time

    activity, _ = AttendanceActivity.objects.get_or_create(
        employee_id=employee,
        attendance_date=attendance_date,
        defaults={
            "shift_day": day,
            "clock_in_date": placeholder_in_date,
            "clock_in": placeholder_in_time,
            "in_datetime": datetime.combine(placeholder_in_date, placeholder_in_time),
        },
    )

    # Patch activity if needed
    act_updates = []
    if activity.shift_day_id != day.id:
        activity.shift_day = day
        act_updates.append("shift_day")
    if not activity.clock_in_date:
        activity.clock_in_date = placeholder_in_date
        act_updates.append("clock_in_date")
    if not activity.clock_in:
        activity.clock_in = placeholder_in_time
        act_updates.append("clock_in")
    if not activity.in_datetime and activity.clock_in_date and activity.clock_in:
        activity.in_datetime = datetime.combine(activity.clock_in_date, activity.clock_in)
        act_updates.append("in_datetime")
    if act_updates:
        activity.save(update_fields=act_updates)

    # 3) Last punch wins: ignore older punches
    existing_out_dt = activity.out_datetime
    if not existing_out_dt and activity.clock_out_date and activity.clock_out:
        existing_out_dt = datetime.combine(activity.clock_out_date, activity.clock_out)

    if existing_out_dt and out_datetime <= existing_out_dt:
        return attendance, missing_check_in

    # 4) Update activity OUT
    activity.clock_out_date = out_date
    activity.clock_out = out_time
    activity.out_datetime = out_datetime
    if clock_out_image:
        activity.clock_out_image = clock_out_image
    activity.save()

    # 5) Update Attendance OUT
    attendance.attendance_clock_out_date = out_date
    attendance.attendance_clock_out = out_time
    if clock_out_image:
        attendance.attendance_clock_out_image = clock_out_image

    # Compute worked hours only when check-in exists
    if not missing_check_in:
        in_dt = datetime.combine(attendance.attendance_clock_in_date, attendance.attendance_clock_in)
        out_dt = datetime.combine(attendance.attendance_clock_out_date, attendance.attendance_clock_out)
        duration_seconds = int((out_dt - in_dt).total_seconds())
        if duration_seconds < 0:
            duration_seconds = 0

        attendance.attendance_worked_hour = format_time(duration_seconds)
        attendance.attendance_overtime = overtime_calculation(attendance)
        attendance.attendance_validated = attendance_validate(attendance)
    else:
        attendance.attendance_worked_hour = "00:00"
        attendance.attendance_overtime = "00:00"
        attendance.attendance_validated = False

    attendance.save()
    return attendance, missing_check_in


# ---------------------------------------------------------------------
# Views: clock_in / clock_out
# ---------------------------------------------------------------------
@login_required
@hx_request_required
def clock_in(request):
    """
    Single-session clock-in:
    - One check-in per attendance_date
    - Blocks check-in after cutoff-in
    """
    selected_company = request.session.get("selected_company")
    if selected_company == "all":
        attendance_general_settings = AttendanceGeneralSetting.objects.filter(company_id=None).first()
    else:
        company = Company.objects.filter(id=selected_company).first()
        attendance_general_settings = AttendanceGeneralSetting.objects.filter(company_id=company).first()

    # Check feature enabled OR biometric request
    if not (
        (attendance_general_settings and attendance_general_settings.enable_check_in)
        or request.__dict__.get("datetime")
        or (request.__dict__.get("date") and request.__dict__.get("time"))
    ):
        messages.error(request, _("Check in/Check out feature is not enabled."))
        return HttpResponse("<script>location.reload();</script>")

    # IP restriction (only for normal web requests)
    allowed_attendance_ips = AttendanceAllowedIP.objects.first()
    if (
        not request.__dict__.get("datetime")
        and not (request.__dict__.get("date") and request.__dict__.get("time"))
        and allowed_attendance_ips
        and allowed_attendance_ips.is_enabled
    ):
        x_forwarded_for = request.META.get("HTTP_X_FORWARDED_FOR")
        ip = request.META.get("REMOTE_ADDR")
        if x_forwarded_for:
            ip = x_forwarded_for.split(",")[0]

        allowed_ips = (allowed_attendance_ips.additional_data or {}).get("allowed_ips", [])
        ip_allowed = False
        for allowed_ip in allowed_ips:
            try:
                if ipaddress.ip_address(ip) in ipaddress.ip_network(allowed_ip, strict=False):
                    ip_allowed = True
                    break
            except ValueError:
                continue

        if not ip_allowed:
            return HttpResponse(_("You cannot mark attendance from this network"))

    employee, work_info = employee_exists(request)
    if not employee or work_info is None:
        return HttpResponse(_("You Don't have work information filled or your employee detail neither entered "))

    shift = work_info.shift_id

    datetime_now = _get_request_datetime(request)
    date_today = datetime_now.date()
    now_hhmm = datetime_now.strftime("%H:%M")

    # Determine attendance_date + day (night shift rule)
    attendance_date = date_today
    day = EmployeeShiftDay.objects.get(day=date_today.strftime("%A").lower())

    now_sec = strtime_seconds(now_hhmm)
    mid_day_sec = strtime_seconds("12:00")

    minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)

    # Night shift: if punch before noon, attendance belongs to yesterday
    if start_time_sec > end_time_sec and mid_day_sec > now_sec:
        date_yesterday = date_today - timedelta(days=1)
        day = EmployeeShiftDay.objects.get(day=date_yesterday.strftime("%A").lower())
        minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)
        attendance_date = date_yesterday

    # Cutoff IN enforcement
    schedule = _get_schedule(shift, day)
    cutoff_in_dt = _calc_cutoff_in_dt(attendance_date, schedule)
    if cutoff_in_dt and datetime_now > cutoff_in_dt:
        messages.error(
            request,
            _("Check-in cut-off has passed. Last allowed: %(t)s")
            % {"t": cutoff_in_dt.strftime("%Y-%m-%d %H:%M")},
        )
        return HttpResponse(
            _("Check-in is not allowed after cut-off time (%(t)s).")
            % {"t": cutoff_in_dt.strftime("%H:%M")}
        )

    clock_in_image = getattr(request, "image", None)

    clock_in_attendance_and_activity(
        employee=employee,
        date_today=date_today,
        attendance_date=attendance_date,
        day=day,
        now_hhmm=now_hhmm,
        shift=shift,
        minimum_hour=minimum_hour,
        start_time_sec=start_time_sec,
        end_time_sec=end_time_sec,
        in_datetime=datetime_now,
        clock_in_image=clock_in_image,
    )

    # UI response
    script = ""
    hidden_label = ""
    mouse_in = ""
    mouse_out = ""
    if timerunner_enabled(request)["enabled_timerunner"]:
        script = """
        <script>
            $(".time-runner").removeClass("stop-runner");
            run = 1;
            at_work_seconds = {at_work_seconds_forecasted};
        </script>
        """.format(
            at_work_seconds_forecasted=employee.get_forecasted_at_work()["forecasted_at_work_seconds"]
        )
        hidden_label = 'style="display:none"'
        mouse_in = """ onmouseenter="$(this).find('span').show();$(this).find('.time-runner').hide();" """
        mouse_out = """ onmouseleave="$(this).find('span').hide();$(this).find('.time-runner').show();" """

    return HttpResponse(
        """
        <button class="oh-btn oh-btn--warning-outline check-in mr-2"
            {mouse_in}
            {mouse_out}
            hx-get="/attendance/clock-out"
            hx-target='#attendance-activity-container'
            hx-swap='innerHTML'>
            <ion-icon class="oh-navbar__clock-icon mr-2 text-warning" name="exit-outline"></ion-icon>
            <span {hidden_label} class="hr-check-in-out-text">{check_out}</span>
            <div class="time-runner"></div>
        </button>
        {script}
        """.format(
            check_out=_("Check-Out"),
            script=script,
            hidden_label=hidden_label,
            mouse_in=mouse_in,
            mouse_out=mouse_out,
        )
    )


@login_required
@hx_request_required
def clock_out(request):
    """
    Single-session clock-out:
    - Allows check-out even if check-in is missing (fix later via Attendance Request)
    - Blocks check-out after cutoff-out (force Attendance Request)
    """
    selected_company = request.session.get("selected_company")
    if selected_company == "all":
        attendance_general_settings = AttendanceGeneralSetting.objects.filter(company_id=None).first()
    else:
        company = Company.objects.filter(id=selected_company).first()
        attendance_general_settings = AttendanceGeneralSetting.objects.filter(company_id=company).first()

    if not (
        (attendance_general_settings and attendance_general_settings.enable_check_in)
        or request.__dict__.get("datetime")
        or (request.__dict__.get("date") and request.__dict__.get("time"))
    ):
        messages.error(request, _("Check in/Check out feature is not enabled."))
        return HttpResponse("<script>location.reload();</script>")

    employee, work_info = employee_exists(request)
    if not employee or work_info is None:
        return HttpResponse(_("You Don't have work information filled or your employee detail neither entered "))

    shift = work_info.shift_id

    datetime_now = _get_request_datetime(request)
    date_today = datetime_now.date()
    now_hhmm = datetime_now.strftime("%H:%M")

    # Determine attendance_date + day (night shift rule)
    attendance_date = date_today
    day = EmployeeShiftDay.objects.get(day=date_today.strftime("%A").lower())

    now_sec = strtime_seconds(now_hhmm)
    mid_day_sec = strtime_seconds("12:00")

    minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)

    # Night shift: if punch before noon, attendance belongs to yesterday
    if start_time_sec > end_time_sec and mid_day_sec > now_sec:
        date_yesterday = date_today - timedelta(days=1)
        day = EmployeeShiftDay.objects.get(day=date_yesterday.strftime("%A").lower())
        minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)
        attendance_date = date_yesterday

    # Cutoff OUT enforcement (strict block)
    schedule = _get_schedule(shift, day)
    cutoff_out_dt = _calc_cutoff_out_dt(attendance_date, schedule) if schedule else None
    if cutoff_out_dt and datetime_now > cutoff_out_dt:
        messages.error(request, _("Check-out cut-off has passed. Please submit an attendance request."))
        return HttpResponse("<script>location.reload();</script>")

    clock_out_image = getattr(request, "image", None)

    attendance, missing_check_in = clock_out_attendance_and_activity(
        employee=employee,
        attendance_date=attendance_date,
        day=day,
        shift=shift,
        minimum_hour=minimum_hour,
        out_datetime=datetime_now,
        clock_out_image=clock_out_image,
    )

    if not attendance:
        messages.error(request, _("Unable to record check-out. Please contact admin."))
        return HttpResponse("<script>location.reload();</script>")

    if missing_check_in:
        messages.warning(
            request,
            _("Check-out recorded, but check-in is missing. Please submit an attendance request later.")
        )
        # Skip early_out for incomplete attendance
    else:
        # Because check-out can be updated multiple times, always re-evaluate early_out
        attendance.late_come_early_out.filter(type="early_out").delete()

        is_night_shift = attendance.is_night_shift()
        next_date = attendance.attendance_date + timedelta(days=1)

        if is_night_shift:
            # Horilla night-shift condition (noon-to-noon)
            if (attendance.attendance_date == date_today) or (
                strtime_seconds("12:00") >= now_sec and date_today == next_date
            ):
                schedule = _get_schedule(shift, day)
                early_out(
                    attendance=attendance,
                    start_time=start_time_sec,
                    end_time=end_time_sec,
                    shift=shift,
                    schedule=schedule,
                )
        else:
            if attendance.attendance_date == date_today:
                schedule = _get_schedule(shift, day)
                early_out(
                    attendance=attendance,
                    start_time=start_time_sec,
                    end_time=end_time_sec,
                    shift=shift,
                    schedule=schedule,
                )

    # UI response
    script = ""
    hidden_label = ""
    mouse_in = ""
    mouse_out = ""

    if timerunner_enabled(request)["enabled_timerunner"]:
        script = """
        <script>
            $(document).ready(function () {{
                $('.at-work-seconds').html(secondsToDuration({at_work_seconds_forecasted}))
            }});
            run = 0;
            at_work_seconds = {at_work_seconds_forecasted};
        </script>
        """.format(
            at_work_seconds_forecasted=employee.get_forecasted_at_work()["forecasted_at_work_seconds"]
        )
        hidden_label = 'style="display:none"'
        mouse_in = """ onmouseenter="$(this).find('div.at-work-seconds').hide();$(this).find('span').show();" """
        mouse_out = """ onmouseleave="$(this).find('div.at-work-seconds').show();$(this).find('span').hide();" """

    return HttpResponse(
        """
        <button class="oh-btn oh-btn--success-outline mr-2"
            {mouse_in}
            {mouse_out}
            hx-get="/attendance/clock-in"
            hx-target='#attendance-activity-container'
            hx-swap='innerHTML'>
            <ion-icon class="oh-navbar__clock-icon mr-2 text-success" name="enter-outline"></ion-icon>
            <span class="hr-check-in-out-text" {hidden_label}>{check_in}</span>
            <div class="at-work-seconds"></div>
        </button>
        {script}
        """.format(
            check_in=_("Check-In"),
            script=script,
            hidden_label=hidden_label,
            mouse_in=mouse_in,
            mouse_out=mouse_out,
        )
    )
