# leave/signals.py

from datetime import datetime, timedelta

from django.apps import apps
from django.db.models import Q
from django.db.models.signals import post_migrate, post_save, post_delete
from django.dispatch import receiver
from django.utils.translation import gettext_lazy as _

from attendance.methods.utils import format_time, overtime_calculation, strtime_seconds
from attendance.models import AttendanceValidationCondition
from horilla.methods import get_horilla_model_class
from leave.half_day_rules import (
    HALF_DAY_FIRST,
    HALF_DAY_SECOND,
    impacted_attendance_dates_for_leave_request,
    leave_breakdown_for_attendance_date,
)
from leave.models import LeaveRequest

if apps.is_installed("attendance"):

    def _get_breakdown_for_date(instance, date):
        if instance.start_date == instance.end_date:
            return instance.start_date_breakdown
        if date == instance.start_date:
            return instance.start_date_breakdown
        if date == instance.end_date:
            return instance.end_date_breakdown
        return "full_day"

    def _cleanup_leave_work_records(WorkRecords, instance):
        linked_records = WorkRecords.objects.filter(leave_request_id=instance)
        for work_entry in linked_records:
            if work_entry.is_attendance_record:
                work_entry.is_leave_record = False
                work_entry.leave_request_id = None
                work_entry.day_percentage = 1.0 if work_entry.work_record_type == "FDP" else 0.5
                work_entry.save(update_fields=["is_leave_record", "leave_request_id", "day_percentage"])
            else:
                work_entry.delete()

    def _affected_attendance_dates(instance):
        try:
            return impacted_attendance_dates_for_leave_request(
                employee=instance.employee_id,
                start_date=instance.start_date,
                end_date=instance.end_date,
            )
        except Exception:
            return list(instance.requested_dates())

    def _reconcile_leave_related_punches(instance):
        try:
            from attendance.services.reconciliation import recompute_attendance_range
        except Exception:
            return

        attendance_dates = _affected_attendance_dates(instance)
        if not attendance_dates:
            return
        try:
            recompute_attendance_range(
                instance.employee_id,
                min(attendance_dates),
                max(attendance_dates),
            )
        except Exception:
            return

    def _day_object_for_date(target_date):
        try:
            from base.models import EmployeeShiftDay
        except Exception:
            return None
        if not target_date:
            return None
        return EmployeeShiftDay.objects.filter(day=target_date.strftime("%A").lower()).first()

    def _schedule_for_employee_attendance_date(employee, attendance_date):
        if not employee or not attendance_date:
            return None
        try:
            shift = employee.employee_work_info.shift_id
        except Exception:
            shift = None
        if not shift:
            return None
        day = _day_object_for_date(attendance_date)
        if not day:
            return None
        try:
            return day.day_schedule.filter(shift_id=shift).first()
        except Exception:
            return None

    def _raw_logs_for_attendance_date(employee, attendance_date, schedule=None):
        try:
            from attendance.models import AttendancePunchingHistory
        except Exception:
            return []
        if not employee or not attendance_date:
            return []

        if schedule and getattr(schedule, "start_time", None) and getattr(schedule, "end_time", None):
            start_dt = datetime.combine(attendance_date, schedule.start_time)
            end_dt = datetime.combine(attendance_date, schedule.end_time)
            if bool(getattr(schedule, "is_night_shift", False)) or schedule.end_time <= schedule.start_time:
                end_dt += timedelta(days=1)
            qs = AttendancePunchingHistory.objects.filter(employee_id=employee).filter(
                Q(attendance_date=attendance_date)
                | Q(
                    punch_timestamp__gte=start_dt - timedelta(hours=6),
                    punch_timestamp__lte=end_dt + timedelta(hours=6),
                )
            )
        else:
            qs = AttendancePunchingHistory.objects.filter(employee_id=employee).filter(
                Q(attendance_date=attendance_date)
                | Q(punch_timestamp__date=attendance_date)
                | Q(punch_timestamp__date=attendance_date + timedelta(days=1))
            )
        return list(qs.order_by("punch_timestamp", "id"))

    def _pick_raw_sessions(logs):
        try:
            from attendance.models import AttendancePunchDirection
        except Exception:
            return None, None

        in_logs = [log for log in logs if getattr(log, "punch_direction", None) == AttendancePunchDirection.IN]
        out_logs = [log for log in logs if getattr(log, "punch_direction", None) == AttendancePunchDirection.OUT]

        in_punch = sorted(in_logs, key=lambda log: (log.punch_timestamp, log.id))[0] if in_logs else None
        out_punch = sorted(out_logs, key=lambda log: (log.punch_timestamp, log.id))[-1] if out_logs else None
        return in_punch, out_punch

    def _ensure_attendance_shell(employee, attendance_date):
        try:
            from attendance.models import Attendance
        except Exception:
            return None
        if not employee or not attendance_date:
            return None

        schedule = _schedule_for_employee_attendance_date(employee, attendance_date)
        day = _day_object_for_date(attendance_date)
        try:
            shift = employee.employee_work_info.shift_id
        except Exception:
            shift = None
        try:
            work_type = employee.employee_work_info.work_type_id
        except Exception:
            work_type = None

        defaults = {
            "shift_id": shift,
            "work_type_id": work_type,
            "attendance_day": day,
            "minimum_hour": getattr(schedule, "minimum_working_hour", None) or "00:00",
            "attendance_validated": False,
        }
        attendance, _created = Attendance.objects.get_or_create(
            employee_id=employee,
            attendance_date=attendance_date,
            defaults=defaults,
        )

        updates = []
        if day and getattr(attendance, "attendance_day_id", None) != getattr(day, "id", None):
            attendance.attendance_day = day
            updates.append("attendance_day")
        if shift and getattr(attendance, "shift_id_id", None) != getattr(shift, "id", None):
            attendance.shift_id = shift
            updates.append("shift_id")
        if work_type and getattr(attendance, "work_type_id_id", None) != getattr(work_type, "id", None):
            attendance.work_type_id = work_type
            updates.append("work_type_id")
        minimum_hour = getattr(schedule, "minimum_working_hour", None) or getattr(attendance, "minimum_hour", None) or "00:00"
        if getattr(attendance, "minimum_hour", None) != minimum_hour:
            attendance.minimum_hour = minimum_hour
            updates.append("minimum_hour")
        if updates:
            attendance.save(update_fields=list(dict.fromkeys(updates)))
        return attendance

    def _clear_final_sessions_for_leave(attendance):
        if not attendance:
            return attendance
        updates = []
        for field_name, value in [
            ("attendance_clock_in_date", None),
            ("attendance_clock_in", None),
            ("attendance_clock_in_channel", None),
            ("attendance_clock_in_punch_id", None),
            ("attendance_clock_in_image", None),
            ("attendance_clock_in_mode", None),
            ("attendance_clock_in_location", None),
            ("in_attendance_status", None),
            ("in_attendance_reject_reason_code", None),
            ("attendance_clock_out_date", None),
            ("attendance_clock_out", None),
            ("attendance_clock_out_channel", None),
            ("attendance_clock_out_punch_id", None),
            ("attendance_clock_out_image", None),
            ("attendance_clock_out_mode", None),
            ("attendance_clock_out_location", None),
            ("out_attendance_status", None),
            ("out_attendance_reject_reason_code", None),
        ]:
            if hasattr(attendance, field_name) and getattr(attendance, field_name) != value:
                setattr(attendance, field_name, value)
                updates.append(field_name)
        if updates:
            attendance.save(update_fields=updates)
        return attendance

    def _materialize_attendance_for_leave_date(employee, attendance_date):
        try:
            from attendance.models import Attendance, AttendanceChannel
            from attendance.services.punching_history import assign_raw_punch_to_attendance
        except Exception:
            return None

        breakdown = leave_breakdown_for_attendance_date(employee, attendance_date)
        schedule = _schedule_for_employee_attendance_date(employee, attendance_date)
        logs = _raw_logs_for_attendance_date(employee, attendance_date, schedule=schedule)

        if not logs and not breakdown:
            return Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()

        attendance = _ensure_attendance_shell(employee, attendance_date)
        if not attendance:
            return None

        # Full-day leave should override final punch sessions but still keep a stored daily attendance row.
        if breakdown == "full_day":
            return _clear_final_sessions_for_leave(attendance)

        in_punch, out_punch = _pick_raw_sessions(logs)

        in_channel = getattr(attendance, "attendance_clock_in_channel", None)
        out_channel = getattr(attendance, "attendance_clock_out_channel", None)
        raw_like_channels = {None, "", AttendanceChannel.MOBILE, AttendanceChannel.BIOMETRIC, AttendanceChannel.API}

        should_save = False
        if in_punch and (not getattr(attendance, "attendance_clock_in", None) or in_channel in raw_like_channels):
            assign_raw_punch_to_attendance(attendance, punch=in_punch, direction="in")
            should_save = True
        if out_punch and (not getattr(attendance, "attendance_clock_out", None) or out_channel in raw_like_channels):
            assign_raw_punch_to_attendance(attendance, punch=out_punch, direction="out")
            should_save = True

        if should_save:
            attendance.save()
        return attendance

    def _schedule_for_attendance(attendance):
        if not attendance.shift_id or not attendance.attendance_date:
            return None
        try:
            from base.models import EmployeeShiftDay
        except Exception:
            return None
        day = EmployeeShiftDay.objects.filter(day=attendance.attendance_date.strftime("%A").lower()).first()
        if not day:
            return None
        return day.day_schedule.filter(shift_id=attendance.shift_id).first()

    def _combine(date_value, time_value):
        if not date_value or not time_value:
            return None
        return datetime.combine(date_value, time_value)

    def _shift_bounds(attendance, schedule):
        if not schedule or not schedule.start_time or not schedule.end_time or not attendance.attendance_date:
            return None, None
        shift_start = datetime.combine(attendance.attendance_date, schedule.start_time)
        shift_end = datetime.combine(attendance.attendance_date, schedule.end_time)
        if bool(getattr(schedule, "is_night_shift", False)) or schedule.end_time <= schedule.start_time:
            shift_end += timedelta(days=1)
        return shift_start, shift_end

    def _threshold_dt(threshold_time, shift_start, shift_end):
        if not threshold_time or not shift_start or not shift_end:
            return None
        candidate = datetime.combine(shift_start.date(), threshold_time)
        if shift_end <= shift_start and candidate < shift_start:
            candidate += timedelta(days=1)
        return candidate

    def _grace_seconds(schedule, attr_flag):
        grace = getattr(schedule, "grace_time_id", None)
        if not grace:
            return 0
        if attr_flag == "in" and getattr(grace, "allowed_clock_in", False):
            return int(getattr(grace, "allowed_time_in_secs", 0) or 0)
        if attr_flag == "out" and getattr(grace, "allowed_clock_out", False):
            return int(getattr(grace, "allowed_time_in_secs", 0) or 0)
        return 0

    def _rebuild_attendance_summary(attendance):
        schedule = _schedule_for_attendance(attendance)
        if schedule and getattr(schedule, "minimum_working_hour", None):
            attendance.minimum_hour = schedule.minimum_working_hour

        if getattr(attendance, "is_presensi_only", False):
            attendance.attendance_worked_hour = "00:00"
            attendance.attendance_overtime = "00:00"
            attendance.attendance_validated = False
            attendance.save(update_fields=["minimum_hour", "attendance_worked_hour", "attendance_overtime", "attendance_validated"])
            return

        shift_start, _shift_end = _shift_bounds(attendance, schedule)
        in_dt = _combine(getattr(attendance, "attendance_clock_in_date", None), getattr(attendance, "attendance_clock_in", None))
        out_dt = _combine(getattr(attendance, "attendance_clock_out_date", None), getattr(attendance, "attendance_clock_out", None))

        if in_dt and out_dt:
            worked_start = max(in_dt, shift_start) if shift_start else in_dt
            duration_seconds = int((out_dt - worked_start).total_seconds())
            if duration_seconds < 0:
                duration_seconds = 0
            attendance.attendance_worked_hour = format_time(duration_seconds)
            attendance.attendance_overtime = overtime_calculation(attendance)
            threshold = strtime_seconds("09:00")
            conditions = AttendanceValidationCondition.objects.all()
            if conditions.exists():
                threshold = strtime_seconds(conditions[0].validation_at_work)
            attendance.attendance_validated = threshold >= strtime_seconds(attendance.attendance_worked_hour)
        else:
            attendance.attendance_worked_hour = "00:00"
            attendance.attendance_overtime = "00:00"
            attendance.attendance_validated = False

        attendance.save(update_fields=["minimum_hour", "attendance_worked_hour", "attendance_overtime", "attendance_validated"])

    def _rebuild_late_early_records(attendance):
        try:
            from attendance.models import AttendanceLateComeEarlyOut
        except Exception:
            return

        AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance, type__in=["late_come", "early_out"]).delete()

        if getattr(attendance, "is_presensi_only", False):
            return

        schedule = _schedule_for_attendance(attendance)
        if not schedule:
            return

        breakdown = leave_breakdown_for_attendance_date(attendance.employee_id, attendance.attendance_date)
        if breakdown == "full_day":
            return

        shift_start, shift_end = _shift_bounds(attendance, schedule)
        if not shift_start or not shift_end:
            return

        grace_in_sec = _grace_seconds(schedule, "in")
        grace_out_sec = _grace_seconds(schedule, "out")

        in_dt = _combine(getattr(attendance, "attendance_clock_in_date", None), getattr(attendance, "attendance_clock_in", None))
        out_dt = _combine(getattr(attendance, "attendance_clock_out_date", None), getattr(attendance, "attendance_clock_out", None))

        if in_dt:
            if breakdown == HALF_DAY_FIRST and getattr(schedule, "enable_first_half_leave_rule", False):
                ref_in = _threshold_dt(getattr(schedule, "first_half_leave_latest_check_in_time", None), shift_start, shift_end)
            else:
                ref_in = shift_start + timedelta(seconds=grace_in_sec)
            if ref_in and in_dt > ref_in:
                AttendanceLateComeEarlyOut.objects.get_or_create(attendance_id=attendance, type="late_come", defaults={"employee_id": attendance.employee_id})

        if out_dt:
            if breakdown == HALF_DAY_SECOND and getattr(schedule, "enable_second_half_leave_rule", False):
                ref_out = _threshold_dt(getattr(schedule, "second_half_leave_earliest_check_out_time", None), shift_start, shift_end)
            else:
                ref_out = shift_end - timedelta(seconds=grace_out_sec)
            if ref_out and out_dt < ref_out:
                AttendanceLateComeEarlyOut.objects.get_or_create(attendance_id=attendance, type="early_out", defaults={"employee_id": attendance.employee_id})

    def _sync_leave_related_attendance_layers(instance):
        """Canonical reconciliation already synchronizes attendance, activity, and punch decisions."""
        return

    @receiver(post_save, sender=LeaveRequest)
    def leaverequest_pre_save(sender, instance, **_kwargs):
        """Keep attendance work records aligned with approved leave breakdowns."""
        WorkRecords = get_horilla_model_class(
            app_label="attendance", model="workrecords"
        )
        if (
            instance.start_date == instance.end_date
            and instance.end_date_breakdown != instance.start_date_breakdown
        ):
            instance.end_date_breakdown = instance.start_date_breakdown
            super(LeaveRequest, instance).save(update_fields=["end_date_breakdown"])

        period_dates = instance.requested_dates()
        if instance.status == "approved":
            for date in period_dates:
                try:
                    work_entry = WorkRecords.objects.filter(
                        date=date,
                        employee_id=instance.employee_id,
                    ).first() or WorkRecords()
                    breakdown = _get_breakdown_for_date(instance, date)
                    is_half_day = breakdown in ["first_half", "second_half"]

                    work_entry.employee_id = instance.employee_id
                    work_entry.date = date
                    work_entry.is_leave_record = True
                    work_entry.leave_request_id = instance
                    work_entry.day_percentage = 0.50 if is_half_day else 0.00

                    if not work_entry.is_attendance_record:
                        work_entry.work_record_type = "HDP" if is_half_day else "FDP"
                        work_entry.message = (
                            _("Half day leave") if is_half_day else _("Leave")
                        )
                    work_entry.save()

                except Exception as e:
                    print(e)

        else:
            _cleanup_leave_work_records(WorkRecords, instance)

        _reconcile_leave_related_punches(instance)

    @receiver(post_delete, sender=LeaveRequest)
    def leaverequest_post_delete(sender, instance, **kwargs):
        from attendance.models import WorkRecords

        linked_records = WorkRecords.objects.filter(
            employee_id=instance.employee_id,
            date__in=instance.requested_dates(),
            is_leave_record=True,
        )
        for work_entry in linked_records:
            if work_entry.is_attendance_record:
                work_entry.is_leave_record = False
                work_entry.leave_request_id = None
                work_entry.day_percentage = 1.0 if work_entry.work_record_type == "FDP" else 0.5
                work_entry.save(update_fields=["is_leave_record", "leave_request_id", "day_percentage"])
            else:
                work_entry.delete()
        _reconcile_leave_related_punches(instance)


# @receiver(post_migrate)
def add_missing_leave_to_workrecords(sender, **kwargs):
    if sender.label not in ["attendance", "leave"]:
        return

    if not apps.is_installed("attendance"):
        return
    try:
        from attendance.models import WorkRecords

        work_records = WorkRecords.objects.filter(
            is_leave_record=True, leave_request_id__isnull=True
        )
        if not work_records.exists():
            return

        leave_requests = LeaveRequest.objects.all()
        date_leave_map = {}

        for leave in leave_requests:
            for date in leave.requested_dates():
                key = (leave.employee_id, date)
                date_leave_map[key] = leave

        records_to_update = []
        for record in work_records:
            leave_request = date_leave_map.get((record.employee_id, record.date))
            if leave_request:
                record.leave_request_id = leave_request
                records_to_update.append(record)

        if records_to_update:
            WorkRecords.objects.bulk_update(
                records_to_update, ["leave_request_id"], batch_size=500
            )
            print(
                f"Successfully updated {len(records_to_update)} work records with leave information"
            )

    except Exception as e:
        print(f"Error in leave/work records sync: {e}")
