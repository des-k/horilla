"""
Middleware to automatically trigger employee clock-out based on shift schedules.
"""

import logging
from datetime import datetime, timedelta

from django.utils import timezone
from django.utils.deprecation import MiddlewareMixin

from attendance.methods.utils import Request, strtime_seconds

logger = logging.getLogger(__name__)


class AttendanceMiddleware(MiddlewareMixin):
    """
    Auto punch-out middleware.

    On each request, it checks for open attendances (no clock-out yet) where the employee's
    shift schedule has auto punch-out enabled. If the configured auto punch-out time has
    already passed, it triggers `clock_out(...)` using the same Request wrapper used by
    API/mobile and biometric sync.
    """

    def process_request(self, request):
        self.trigger_function()

    def trigger_function(self):
        from attendance.models import Attendance, AttendanceActivity
        from attendance.views.clock_in_out import clock_out, shift_schedule_today
        from base.models import EmployeeShiftSchedule

        schedules = (
            EmployeeShiftSchedule.objects.filter(
                is_auto_punch_out_enabled=True,
                auto_punch_out_time__isnull=False,
            )
            .select_related("shift_id", "day")
        )
        if not schedules.exists():
            return

        schedule_map = {(s.shift_id_id, s.day_id): s for s in schedules}

        shift_ids = {s.shift_id_id for s in schedules}
        day_ids = {s.day_id for s in schedules}

        open_attendances = (
            Attendance.objects.filter(
                attendance_clock_out__isnull=True,
                attendance_clock_out_date__isnull=True,
                shift_id_id__in=shift_ids,
                attendance_day_id__in=day_ids,
            )
            .select_related("employee_id", "employee_id__employee_user_id", "shift_id", "attendance_day")
            .order_by("-attendance_date", "-id")
        )

        now_dt = timezone.now()
        current_tz = timezone.get_current_timezone()

        for attendance in open_attendances:
            schedule = schedule_map.get((attendance.shift_id_id, attendance.attendance_day_id))
            if not schedule:
                continue

            # IMPORTANT: match activity to the same attendance day/date to avoid clocking out the wrong record
            activity = (
                AttendanceActivity.objects.filter(
                    employee_id=attendance.employee_id,
                    attendance_date=attendance.attendance_date,
                    shift_day=attendance.attendance_day,
                    clock_out__isnull=True,
                    clock_out_date__isnull=True,
                )
                .order_by("-in_datetime", "-id")
                .first()
            )
            if not activity:
                continue

            target_date = attendance.attendance_date
            try:
                _, start_sec, end_sec = shift_schedule_today(day=schedule.day, shift=schedule.shift_id)
                auto_sec = strtime_seconds(schedule.auto_punch_out_time.strftime("%H:%M"))

                # Night shift detection: if shift crosses midnight and auto time is after midnight,
                # then auto punch-out should happen on the next calendar day.
                if start_sec > end_sec and auto_sec < start_sec:
                    target_date = target_date + timedelta(days=1)
            except Exception:
                # Fallback to attendance_date if schedule resolution fails.
                pass

            target_dt = timezone.make_aware(
                datetime.combine(target_date, schedule.auto_punch_out_time),
                current_tz,
            )

            if target_dt > now_dt:
                continue

            # Guard: don't clock-out before clock-in
            if activity.in_datetime and activity.in_datetime > target_dt:
                logger.warning(
                    "Skipping auto punch-out (auto time before clock-in). "
                    "employee_id=%s attendance_id=%s in_datetime=%s auto_datetime=%s",
                    attendance.employee_id_id,
                    attendance.id,
                    activity.in_datetime,
                    target_dt,
                )
                continue

            try:
                clock_out(
                    Request(
                        user=attendance.employee_id.employee_user_id,
                        date=target_date,
                        time=schedule.auto_punch_out_time,
                        datetime=target_dt,
                    )
                )
            except Exception:
                logger.exception(
                    "Auto punch-out failed. employee_id=%s attendance_id=%s schedule_id=%s",
                    attendance.employee_id_id,
                    attendance.id,
                    schedule.id,
                )
