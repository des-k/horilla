from __future__ import annotations

from datetime import date, datetime, timedelta
from typing import Any, Optional

from django.core.files.base import ContentFile
from django.db.models import Q
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceChannel,
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchingHistory,
)


def _clone_uploaded_file(uploaded):
    if not uploaded:
        return None
    pos = None
    if hasattr(uploaded, "tell"):
        try:
            pos = uploaded.tell()
        except Exception:
            pos = None
    data = uploaded.read()
    try:
        uploaded.seek(0)
    except Exception:
        pass
    if pos not in (None, 0):
        try:
            uploaded.seek(pos)
        except Exception:
            pass
    copied = ContentFile(data)
    copied.name = getattr(uploaded, "name", "punch.jpg")
    return copied


def _save_cloned_photo(instance: AttendancePunchingHistory, uploaded):
    cloned = _clone_uploaded_file(uploaded)
    if cloned:
        instance.photo.save(cloned.name, cloned, save=False)


def normalize_mobile_device_info(request) -> str:
    device_model = (
        request.data.get("device_model")
        or request.POST.get("device_model")
    )
    if device_model:
        return str(device_model).strip()[:255]

    explicit_info = (
        request.data.get("device_info")
        or request.POST.get("device_info")
    )
    if explicit_info:
        return f"Model unavailable - {str(explicit_info).strip()}"[:255]

    return "-"


def humanize_mobile_error(message: Optional[str], *, direction: str) -> str:
    msg = (message or "").strip()
    lower = msg.lower()
    if not msg:
        return "Punch rejected"
    if "already clocked-in" in lower or "already clocked in" in lower:
        return "Already Has Valid Check-In"
    if "already clocked-out" in lower or "already clocked out" in lower:
        return "Already Has Valid Check-Out"
    if "cut-off has passed" in lower or "window has ended" in lower:
        return "Outside Cutoff"
    if "window" in lower and "check-in" in lower:
        return "Outside Check-In Window"
    if "window" in lower and "check-out" in lower:
        return "Outside Check-Out Window"
    if "disabled for reporting managers" in lower:
        return "Attendance Disabled"
    if "request is required" in lower or "not approved" in lower:
        return "Rejected by Work Type Rule"
    if "must be recorded via biometric" in lower:
        return "Rejected: WFO must use biometric"
    if "photo is required" in lower:
        return "Missing Photo"
    if "location is required" in lower or "location unavailable" in lower:
        return "Missing Location"
    if "missing work information" in lower or "employee details" in lower:
        return "Employee Not Matched"
    return msg[:255]


def humanize_biometric_error(message: Optional[str], *, direction: str) -> str:
    msg = (message or "").strip()
    if not msg:
        return "Punch rejected"
    normalized = humanize_mobile_error(msg, direction=direction)
    if normalized and normalized != msg[:255]:
        return normalized

    lower = msg.lower()
    if "check-in is not allowed after cut-off time" in lower:
        return "Outside Cutoff"
    if "window has not started" in lower and direction == AttendancePunchDirection.IN:
        return "Outside Check-In Window"
    if "window has ended" in lower and direction == AttendancePunchDirection.OUT:
        return "Outside Check-Out Window"
    return msg[:255]


GENERIC_REASONS = {
    "",
    "raw mobile punch received",
    "raw biometric punch received",
    "punch ignored",
    "later in not selected",
    "clocked-in",
    "clocked-out",
}


def is_generic_reason(reason: Optional[str]) -> bool:
    return (reason or "").strip().lower() in GENERIC_REASONS


def should_preserve_reason(reason: Optional[str]) -> bool:
    value = (reason or "").strip()
    if not value:
        return False
    lower = value.lower()
    if lower in GENERIC_REASONS:
        return False
    if lower.startswith("accepted as "):
        return False
    return True


def _expected_final_channel(source: str) -> Optional[str]:
    if source == AttendancePunchSource.MOBILE:
        return AttendanceChannel.MOBILE
    if source == AttendancePunchSource.BIOMETRIC:
        return AttendanceChannel.BIOMETRIC
    return None


def _match_allowed_for_log(log: AttendancePunchingHistory, channel: Optional[str]) -> bool:
    expected = _expected_final_channel(log.source)
    return bool(expected and channel == expected)


def _final_source_reason(channel: Optional[str], *, direction: str) -> Optional[str]:
    if channel == AttendanceChannel.APPROVED_REQUEST:
        return (
            "Final Check-In came from approved request"
            if direction == AttendancePunchDirection.IN
            else "Final Check-Out came from approved request"
        )
    if channel == AttendanceChannel.CORRECTION_REQUEST:
        return (
            "Final Check-In came from correction request"
            if direction == AttendancePunchDirection.IN
            else "Final Check-Out came from correction request"
        )
    if channel and channel not in {AttendanceChannel.MOBILE, AttendanceChannel.BIOMETRIC}:
        return (
            "Final Check-In came from another source"
            if direction == AttendancePunchDirection.IN
            else "Final Check-Out came from another source"
        )
    return None



def create_mobile_punch_history(
    *,
    request,
    employee=None,
    attendance_date: Optional[date],
    punch_timestamp: Optional[datetime],
    direction: str,
    image=None,
    location=None,
    reason: Optional[str] = None,
    accepted_to_attendance: bool = False,
    attendance=None,
) -> AttendancePunchingHistory:
    punch_timestamp = punch_timestamp or timezone.localtime(timezone.now())
    payload = {
        "latitude": request.data.get("latitude") or request.POST.get("latitude"),
        "longitude": request.data.get("longitude") or request.POST.get("longitude"),
        "accuracy": request.data.get("accuracy") or request.POST.get("accuracy"),
        "captured_at": request.data.get("captured_at") or request.POST.get("captured_at"),
        "device_model": request.data.get("device_model") or request.POST.get("device_model"),
        "device_info": request.data.get("device_info") or request.POST.get("device_info"),
    }
    instance = AttendancePunchingHistory(
        employee_id=employee,
        attendance_id=attendance,
        attendance_date=attendance_date,
        punch_timestamp=punch_timestamp,
        source=AttendancePunchSource.MOBILE,
        punch_direction=direction or AttendancePunchDirection.UNKNOWN,
        device_info=normalize_mobile_device_info(request),
        location=location,
        accepted_to_attendance=accepted_to_attendance,
        reason=reason,
        raw_payload=payload,
        raw_employee_identifier=getattr(getattr(request, "user", None), "username", None),
    )
    _save_cloned_photo(instance, image)
    instance.save()
    return instance


def create_biometric_punch_history(
    *,
    device,
    punch_timestamp: Optional[datetime],
    direction: str,
    employee=None,
    attendance_date: Optional[date] = None,
    raw_employee_identifier: Optional[str] = None,
    punch_code: Optional[str] = None,
    reason: Optional[str] = None,
    raw_payload: Optional[dict] = None,
) -> AttendancePunchingHistory:
    punch_timestamp = punch_timestamp or timezone.localtime(timezone.now())
    payload = {"punch_code": punch_code, "device_id": str(getattr(device, "id", ""))}
    if raw_payload:
        payload["raw"] = raw_payload
    instance = AttendancePunchingHistory.objects.create(
        employee_id=employee,
        attendance_date=attendance_date,
        punch_timestamp=punch_timestamp,
        source=AttendancePunchSource.BIOMETRIC,
        punch_direction=direction or AttendancePunchDirection.UNKNOWN,
        device_info=(getattr(device, "name", None) or "-")[:255],
        accepted_to_attendance=False,
        reason=reason,
        raw_payload=payload,
        raw_employee_identifier=raw_employee_identifier,
    )
    return instance


def update_punch_history(
    punch: Optional[AttendancePunchingHistory],
    *,
    accepted: Optional[bool] = None,
    reason: Optional[str] = None,
    attendance=None,
    attendance_date: Optional[date] = None,
    device_info: Optional[str] = None,
):
    if not punch:
        return
    fields = []
    if accepted is not None:
        punch.accepted_to_attendance = accepted
        fields.append("accepted_to_attendance")
    if reason is not None:
        punch.reason = reason[:255]
        fields.append("reason")
    if attendance is not None:
        punch.attendance_id = attendance
        fields.append("attendance_id")
    if attendance_date is not None:
        punch.attendance_date = attendance_date
        fields.append("attendance_date")
    if device_info:
        punch.device_info = device_info[:255]
        fields.append("device_info")
    if fields:
        punch.save(update_fields=fields)


def _same_timestamp(att_date, att_time, punch_dt: datetime) -> bool:
    if not att_date or not att_time:
        return False
    return att_date == punch_dt.date() and att_time == punch_dt.time().replace(microsecond=0)


def _logs_for_attendance(employee, attendance_date: date):
    return AttendancePunchingHistory.objects.filter(
        employee_id=employee,
    ).filter(
        Q(attendance_date=attendance_date)
        | Q(punch_timestamp__date=attendance_date)
        | Q(punch_timestamp__date=attendance_date + timedelta(days=1))
    ).order_by("punch_timestamp", "id")


def reconcile_attendance_punches(*, employee, attendance_date: date):
    if not employee or not attendance_date:
        return
    attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
    logs = list(_logs_for_attendance(employee, attendance_date))
    if not logs:
        return

    in_match = None
    out_match = None
    in_final_source_reason = None
    out_final_source_reason = None

    if attendance:
        in_final_source_reason = _final_source_reason(
            attendance.attendance_clock_in_channel,
            direction=AttendancePunchDirection.IN,
        )
        out_final_source_reason = _final_source_reason(
            attendance.attendance_clock_out_channel,
            direction=AttendancePunchDirection.OUT,
        )

        for log in logs:
            localized_ts = timezone.localtime(log.punch_timestamp) if timezone.is_aware(log.punch_timestamp) else log.punch_timestamp
            if (
                log.punch_direction == AttendancePunchDirection.IN
                and _match_allowed_for_log(log, attendance.attendance_clock_in_channel)
                and _same_timestamp(
                    attendance.attendance_clock_in_date,
                    attendance.attendance_clock_in,
                    localized_ts,
                )
            ):
                in_match = log.id
                break
        for log in reversed(logs):
            localized_ts = timezone.localtime(log.punch_timestamp) if timezone.is_aware(log.punch_timestamp) else log.punch_timestamp
            if (
                log.punch_direction == AttendancePunchDirection.OUT
                and _match_allowed_for_log(log, attendance.attendance_clock_out_channel)
                and _same_timestamp(
                    attendance.attendance_clock_out_date,
                    attendance.attendance_clock_out,
                    localized_ts,
                )
            ):
                out_match = log.id
                break

    for log in logs:
        accepted = False
        reason = (log.reason or "").strip()

        if log.punch_direction == AttendancePunchDirection.IN:
            if in_match and log.id == in_match:
                accepted = True
                reason = "Accepted as earliest valid Check-In"
            elif should_preserve_reason(reason):
                pass
            elif in_match:
                reason = "Duplicate IN / Later valid IN not selected"
            elif attendance and attendance.attendance_clock_in and in_final_source_reason:
                reason = in_final_source_reason
            else:
                reason = reason or "Later IN not selected"

        elif log.punch_direction == AttendancePunchDirection.OUT:
            if out_match and log.id == out_match:
                accepted = True
                reason = "Accepted as latest valid Check-Out"
            elif should_preserve_reason(reason):
                pass
            elif out_match:
                reason = "Earlier OUT superseded by later valid OUT"
            elif attendance and attendance.attendance_clock_out and out_final_source_reason:
                reason = out_final_source_reason
            else:
                reason = reason or "Earlier OUT superseded by later valid OUT"

        else:
            if not should_preserve_reason(reason):
                reason = reason or "Punch ignored"

        update_punch_history(
            log,
            accepted=accepted,
            reason=reason,
            attendance=attendance,
            attendance_date=attendance_date,
        )


def reconcile_single_punch_against_attendance(punch: AttendancePunchingHistory):
    if not punch or not punch.employee_id:
        return
    dt = timezone.localtime(punch.punch_timestamp) if timezone.is_aware(punch.punch_timestamp) else punch.punch_timestamp
    attendance = Attendance.objects.filter(employee_id=punch.employee_id).filter(
        Q(attendance_date=dt.date()) | Q(attendance_date=dt.date() - timedelta(days=1))
    ).order_by('-attendance_date').first()
    if attendance:
        update_punch_history(punch, attendance=attendance, attendance_date=attendance.attendance_date)
        reconcile_attendance_punches(employee=punch.employee_id, attendance_date=attendance.attendance_date)
