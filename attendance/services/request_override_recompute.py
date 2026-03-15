from __future__ import annotations

from attendance.models import Attendance
from attendance.services.reconciliation import recompute_attendance


REQUEST_OVERRIDE_IN_FIELDS = [
    "attendance_clock_in_date",
    "attendance_clock_in",
    "attendance_clock_in_channel",
    "attendance_clock_in_mode",
    "attendance_clock_in_punch",
    "attendance_clock_in_image",
    "attendance_clock_in_location",
    "in_attendance_status",
    "in_attendance_reject_reason_code",
    "in_related_work_type_request_id",
]

REQUEST_OVERRIDE_OUT_FIELDS = [
    "attendance_clock_out_date",
    "attendance_clock_out",
    "attendance_clock_out_channel",
    "attendance_clock_out_mode",
    "attendance_clock_out_punch",
    "attendance_clock_out_image",
    "attendance_clock_out_location",
    "out_attendance_status",
    "out_attendance_reject_reason_code",
    "out_related_work_type_request_id",
]


def _set_none(attendance: Attendance, field_name: str):
    if hasattr(attendance, field_name):
        setattr(attendance, field_name, None)


def clear_request_override_and_recompute(
    attendance: Attendance,
    *,
    include_in: bool = False,
    include_out: bool = False,
):
    """Drop request-derived final session values and rebuild from raw state.

    Revokes/cancels must restore the final attendance from raw punches plus the
    currently active rules, not from a stale request snapshot. This helper only
    clears the request-derived final fields, then delegates to the canonical
    reconciliation engine.
    """

    if attendance is None:
        return None

    update_fields: list[str] = []

    if include_in:
        for field_name in REQUEST_OVERRIDE_IN_FIELDS:
            _set_none(attendance, field_name)
            update_fields.append(field_name)

    if include_out:
        for field_name in REQUEST_OVERRIDE_OUT_FIELDS:
            _set_none(attendance, field_name)
            update_fields.append(field_name)

    if hasattr(attendance, "work_mode_request_id"):
        attendance.work_mode_request_id = None
        update_fields.append("work_mode_request_id")

    if hasattr(attendance, "request_restore_snapshot"):
        attendance.request_restore_snapshot = None
        update_fields.append("request_restore_snapshot")

    if update_fields:
        attendance.save(update_fields=list(dict.fromkeys(update_fields)))

    result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
    return result.attendance if result is not None else attendance
