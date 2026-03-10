# leave/signals.py

import threading

from django.apps import apps
from django.db.models.signals import post_migrate, post_save, pre_delete, pre_save
from django.dispatch import receiver
from django.utils.translation import gettext_lazy as _

from horilla.methods import get_horilla_model_class
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

    @receiver(pre_delete, sender=LeaveRequest)
    def leaverequest_pre_delete(sender, instance, **kwargs):
        from attendance.models import WorkRecords

        _cleanup_leave_work_records(WorkRecords, instance)


# @receiver(post_migrate)
def add_missing_leave_to_workrecords(sender, **kwargs):
    if sender.label not in ["attendance", "leave"]:
        return

    if not apps.is_installed("attendance"):
        return
    try:
        from attendance.models import WorkRecords
        from leave.models import LeaveRequest

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
