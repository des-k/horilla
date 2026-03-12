from __future__ import annotations

from copy import deepcopy
from datetime import date, datetime, time, timedelta
from typing import Optional

from django.core.files.base import ContentFile
from django.db.models import Q
from django.utils import timezone

from attendance.models import (
    Attendance,
    AttendanceChannel,
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchStatus,
    AttendancePunchingHistory,
)


RAW_CHANNELS = {AttendanceChannel.MOBILE, AttendanceChannel.BIOMETRIC}


REASON_REWRITE_MAP = {
    "Punch rejected": "Rejected: punch was not accepted",
    "Already Has Valid Check-In": "Rejected: valid Check-In already exists",
    "Already Has Valid Check-Out": "Rejected: valid Check-Out already exists",
    "Outside Cutoff": "Rejected: outside cutoff",
    "Outside Check-In Window": "Rejected: outside Check-In window",
    "Outside Check-Out Window": "Rejected: outside Check-Out window",
    "Attendance Disabled": "Rejected: attendance disabled",
    "Rejected by Work Type Rule": "Rejected: work type request approval required",
    "Rejected: WFO must use biometric": "Rejected: WFO must use biometric",
    "Missing Photo": "Rejected: photo required",
    "Missing Location": "Rejected: location required",
    "Employee Not Matched": "Rejected: employee not matched",
    "Accepted as earliest valid Check-In": "Used as final Check-In",
    "Accepted as latest valid Check-Out": "Used as final Check-Out",
    "Duplicate IN / Later valid IN not selected": "Ignored because an earlier valid Check-In was selected",
    "Later IN not selected": "Ignored because this Check-In was not selected",
    "Earlier OUT superseded by later valid OUT": "Ignored because a later valid Check-Out was selected",
    "Final Check-In came from approved request": "Not used because final Check-In came from approved request",
    "Final Check-Out came from approved request": "Not used because final Check-Out came from approved request",
    "Final Check-In came from correction request": "Not used because final Check-In came from attendance correction",
    "Final Check-Out came from correction request": "Not used because final Check-Out came from attendance correction",
    "Final Check-In came from another source": "Not used because final Check-In came from another source",
    "Final Check-Out came from another source": "Not used because final Check-Out came from another source",
    "Punch ignored": "Ignored: not used in final attendance",
}


REJECT_REASON_CODE_MAP = {
    "AUTO_REJECT_CUTOFF_IN_PASSED": "Rejected: outside Check-In cutoff",
    "AUTO_REJECT_CUTOFF_OUT_PASSED": "Rejected: outside Check-Out cutoff",
    "AUTO_REJECT_CUTOFF_FULL_PASSED": "Rejected: outside cutoff",
    "EARLY_CHECKOUT_BEFORE_SHIFT_END": "Rejected: outside Check-Out window",
    "EARLY_CHECKOUT_BEFORE_CUTOFF_IN": "Rejected: outside Check-Out window",
    "MANUAL_REJECT": "Rejected by approver",
}


def _clean_reason_text(reason: Optional[str], *, fallback: str = "") -> str:
    value = (reason or fallback or "").strip()
    if not value:
        return "-"
    return REASON_REWRITE_MAP.get(value, value[:255])


def _direction_label(direction: str) -> str:
    return "Check-In" if direction == AttendancePunchDirection.IN else "Check-Out"


def _accepted_reason(direction: str) -> str:
    return f"Used as final {_direction_label(direction)}"


def _superseded_reason(direction: str) -> str:
    if direction == AttendancePunchDirection.IN:
        return "Ignored because an earlier valid Check-In was selected"
    return "Ignored because a later valid Check-Out was selected"


def _final_source_reason(channel: Optional[str], *, direction: str) -> Optional[str]:
    label = _direction_label(direction)
    if channel == AttendanceChannel.APPROVED_REQUEST:
        return f"Not used because final {label} came from approved request"
    if channel == AttendanceChannel.CORRECTION_REQUEST:
        return f"Not used because final {label} came from attendance correction"
    if channel and channel not in RAW_CHANNELS:
        return f"Not used because final {label} came from another source"
    return None


def _attendance_reject_reason(attendance: Optional[Attendance], *, direction: str) -> Optional[str]:
    if not attendance:
        return None
    status = getattr(attendance, _session_status_attr(direction), None)
    if status != AttendancePunchStatus.REJECTED:
        return None
    code = getattr(attendance, _session_reject_attr(direction), None)
    if code:
        return REJECT_REASON_CODE_MAP.get(code, "Rejected by attendance rule")
    return "Rejected by attendance rule"


def _clone_uploaded_file(uploaded):
    if not uploaded:
        return None
    pos = None
    if hasattr(uploaded, "tell"):
        try:
            pos = uploaded.tell()
        except Exception:
            pos = None
    try:
        uploaded.seek(0)
    except Exception:
        pass
    data = uploaded.read()
    if pos is not None:
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
        instance.photo = cloned


def canonical_punch_image_reference(*, punch: Optional[AttendancePunchingHistory] = None, uploaded=None):
    """Return a canonical image artifact for reuse across attendance consumers.

    Prefer the already-saved raw punch photo so Attendance and AttendanceActivity
    can point at the same stored file instead of re-compressing and re-saving the
    same upload independently in the same request flow.
    """
    if punch is not None:
        photo = getattr(punch, "photo", None)
        if photo:
            return photo
    return uploaded


def normalize_mobile_device_info(request) -> str:
    device_model = request.data.get("device_model") or request.POST.get("device_model")
    if device_model:
        return str(device_model).strip()[:255]

    explicit_info = request.data.get("device_info") or request.POST.get("device_info")
    if explicit_info:
        return f"Model unavailable - {str(explicit_info).strip()}"[:255]

    return "-"


def humanize_mobile_error(message: Optional[str], *, direction: str) -> str:
    msg = (message or "").strip()
    lower = msg.lower()
    if not msg:
        return _clean_reason_text(None, fallback="Punch rejected")
    if "already clocked-in" in lower or "already clocked in" in lower:
        return _clean_reason_text("Already Has Valid Check-In")
    if "already clocked-out" in lower or "already clocked out" in lower:
        return _clean_reason_text("Already Has Valid Check-Out")
    if "cut-off has passed" in lower or "window has ended" in lower:
        return _clean_reason_text("Outside Cutoff")
    if "window" in lower and "check-in" in lower:
        return _clean_reason_text("Outside Check-In Window")
    if "window" in lower and "check-out" in lower:
        return _clean_reason_text("Outside Check-Out Window")
    if "disabled for reporting managers" in lower:
        return _clean_reason_text("Attendance Disabled")
    if "request is required" in lower or "not approved" in lower:
        return _clean_reason_text("Rejected by Work Type Rule")
    if "must be recorded via biometric" in lower:
        return _clean_reason_text("Rejected: WFO must use biometric")
    if "photo is required" in lower:
        return _clean_reason_text("Missing Photo")
    if "location is required" in lower or "location unavailable" in lower:
        return _clean_reason_text("Missing Location")
    if "missing work information" in lower or "employee details" in lower:
        return _clean_reason_text("Employee Not Matched")
    return _clean_reason_text(msg)


def humanize_biometric_error(message: Optional[str], *, direction: str) -> str:
    msg = (message or "").strip()
    if not msg:
        return _clean_reason_text(None, fallback="Punch rejected")
    normalized = humanize_mobile_error(msg, direction=direction)
    if normalized and normalized != _clean_reason_text(msg):
        return normalized

    lower = msg.lower()
    if "check-in is not allowed after cut-off time" in lower:
        return _clean_reason_text("Outside Cutoff")
    if "window has not started" in lower and direction == AttendancePunchDirection.IN:
        return _clean_reason_text("Outside Check-In Window")
    if "window has ended" in lower and direction == AttendancePunchDirection.OUT:
        return _clean_reason_text("Outside Check-Out Window")
    return _clean_reason_text(msg)


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
    if lower.startswith("accepted as ") or lower.startswith("used as final "):
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
    return bool(expected and channel in {expected, None, ""})




def _session_prefix(direction: str) -> str:
    return "attendance_clock_in" if direction == AttendancePunchDirection.IN else "attendance_clock_out"


def _session_channel_attr(direction: str) -> str:
    return f"{_session_prefix(direction)}_channel"


def _session_punch_attr(direction: str) -> str:
    return f"{_session_prefix(direction)}_punch"


def _session_date_attr(direction: str) -> str:
    return f"{_session_prefix(direction)}_date"


def _session_time_attr(direction: str) -> str:
    return _session_prefix(direction)


def _session_image_attr(direction: str) -> str:
    return f"{_session_prefix(direction)}_image"


def _session_location_attr(direction: str) -> str:
    return f"{_session_prefix(direction)}_location"


def _session_mode_attr(direction: str) -> str:
    return f"{_session_prefix(direction)}_mode"


def _session_status_attr(direction: str) -> str:
    return "in_attendance_status" if direction == AttendancePunchDirection.IN else "out_attendance_status"


def _session_reject_attr(direction: str) -> str:
    return (
        "in_attendance_reject_reason_code"
        if direction == AttendancePunchDirection.IN
        else "out_attendance_reject_reason_code"
    )


def _session_related_request_attr(direction: str) -> str:
    return (
        "in_related_work_type_request_id"
        if direction == AttendancePunchDirection.IN
        else "out_related_work_type_request_id"
    )


def _aware_local(dt: datetime) -> datetime:
    return timezone.localtime(dt) if timezone.is_aware(dt) else dt


def _session_dt_from_attendance(attendance: Attendance, direction: str) -> Optional[datetime]:
    d = getattr(attendance, _session_date_attr(direction), None)
    t = getattr(attendance, _session_time_attr(direction), None)
    if not d or not t:
        return None
    return datetime.combine(d, t)


def _same_timestamp(att_date, att_time, punch_dt: datetime) -> bool:
    if not att_date or not att_time:
        return False
    return att_date == punch_dt.date() and att_time == punch_dt.time().replace(microsecond=0)


def _same_minute(att_date, att_time, punch_dt: datetime) -> bool:
    if not att_date or not att_time:
        return False
    return (
        att_date == punch_dt.date()
        and att_time.hour == punch_dt.hour
        and att_time.minute == punch_dt.minute
    )


def _serialize_date(value):
    return value.isoformat() if value else None


def _serialize_time(value):
    if not value:
        return None
    return value.replace(microsecond=0).isoformat()


def _parse_date(value):
    if not value:
        return None
    if isinstance(value, date):
        return value
    try:
        return date.fromisoformat(str(value))
    except Exception:
        return None


def _parse_time(value):
    if not value:
        return None
    if isinstance(value, time):
        return value.replace(microsecond=0)
    try:
        return time.fromisoformat(str(value)).replace(microsecond=0)
    except Exception:
        return None


def _serialize_image(value):
    try:
        return value.name or None
    except Exception:
        return None


def _serialize_session_state(attendance: Attendance, direction: str) -> dict:
    return {
        "date": _serialize_date(getattr(attendance, _session_date_attr(direction), None)),
        "time": _serialize_time(getattr(attendance, _session_time_attr(direction), None)),
        "channel": getattr(attendance, _session_channel_attr(direction), None),
        "mode": getattr(attendance, _session_mode_attr(direction), None),
        "location": deepcopy(getattr(attendance, _session_location_attr(direction), None)),
        "image": _serialize_image(getattr(attendance, _session_image_attr(direction), None)),
        "punch_id": getattr(attendance, f"{_session_punch_attr(direction)}_id", None),
        "status": getattr(attendance, _session_status_attr(direction), None),
        "reject_reason_code": getattr(attendance, _session_reject_attr(direction), None),
        "related_work_type_request_id": getattr(attendance, _session_related_request_attr(direction), None),
        "work_mode_request_id": getattr(attendance, "work_mode_request_id_id", None),
    }


def capture_request_restore_snapshot(attendance: Attendance, *, include_in: bool = False, include_out: bool = False):
    snapshot = deepcopy(getattr(attendance, "request_restore_snapshot", None) or {})
    if include_in:
        snapshot["in"] = _serialize_session_state(attendance, AttendancePunchDirection.IN)
    if include_out:
        snapshot["out"] = _serialize_session_state(attendance, AttendancePunchDirection.OUT)
    attendance.request_restore_snapshot = snapshot
    attendance.save(update_fields=["request_restore_snapshot"])
    return snapshot


def clear_request_restore_snapshot(attendance: Attendance, *, include_in: bool = False, include_out: bool = False):
    snapshot = deepcopy(getattr(attendance, "request_restore_snapshot", None) or {})
    if include_in:
        snapshot.pop("in", None)
    if include_out:
        snapshot.pop("out", None)
    attendance.request_restore_snapshot = snapshot or None
    attendance.save(update_fields=["request_restore_snapshot"])
    return attendance.request_restore_snapshot


def _restore_session_from_snapshot(attendance: Attendance, direction: str, state: Optional[dict]):
    date_attr = _session_date_attr(direction)
    time_attr = _session_time_attr(direction)
    channel_attr = _session_channel_attr(direction)
    punch_attr = f"{_session_punch_attr(direction)}_id"
    image_attr = _session_image_attr(direction)
    location_attr = _session_location_attr(direction)
    mode_attr = _session_mode_attr(direction)
    status_attr = _session_status_attr(direction)
    reject_attr = _session_reject_attr(direction)
    related_attr = _session_related_request_attr(direction)

    if not state:
        setattr(attendance, date_attr, None)
        setattr(attendance, time_attr, None)
        setattr(attendance, channel_attr, None)
        setattr(attendance, punch_attr, None)
        setattr(attendance, image_attr, None)
        setattr(attendance, location_attr, None)
        setattr(attendance, mode_attr, None)
        setattr(attendance, status_attr, None)
        setattr(attendance, reject_attr, None)
        setattr(attendance, related_attr, None)
        return

    setattr(attendance, date_attr, _parse_date(state.get("date")))
    setattr(attendance, time_attr, _parse_time(state.get("time")))
    setattr(attendance, channel_attr, state.get("channel") or None)
    setattr(attendance, punch_attr, state.get("punch_id"))
    setattr(attendance, image_attr, state.get("image") or None)
    setattr(attendance, location_attr, deepcopy(state.get("location")))
    setattr(attendance, mode_attr, state.get("mode") or None)
    setattr(attendance, status_attr, state.get("status") or None)
    setattr(attendance, reject_attr, state.get("reject_reason_code") or None)
    setattr(attendance, related_attr, state.get("related_work_type_request_id") or None)
    if state.get("work_mode_request_id") is not None:
        attendance.work_mode_request_id_id = state.get("work_mode_request_id")


def _candidate_logs(employee, attendance_date: date, direction: str):
    return list(
        _logs_for_attendance(employee, attendance_date).filter(
            punch_direction=direction,
            source__in=[AttendancePunchSource.MOBILE, AttendancePunchSource.BIOMETRIC],
        )
    )


def _pick_best_raw_candidate(attendance: Attendance, direction: str):
    employee = getattr(attendance, "employee_id", None)
    attendance_date = getattr(attendance, "attendance_date", None)
    if not employee or not attendance_date:
        return None
    logs = _candidate_logs(employee, attendance_date, direction)
    if not logs:
        return None

    target_dt = _session_dt_from_attendance(attendance, direction)
    if target_dt is not None:
        for log in logs:
            localized_ts = _aware_local(log.punch_timestamp)
            if _same_timestamp(target_dt.date(), target_dt.time(), localized_ts):
                return log
        same_minute = [
            log for log in logs
            if _same_minute(target_dt.date(), target_dt.time(), _aware_local(log.punch_timestamp))
        ]
        if same_minute:
            if direction == AttendancePunchDirection.IN:
                return sorted(same_minute, key=lambda l: (_aware_local(l.punch_timestamp), l.id))[0]
            return sorted(same_minute, key=lambda l: (_aware_local(l.punch_timestamp), l.id))[-1]

    if direction == AttendancePunchDirection.IN:
        return sorted(logs, key=lambda l: (_aware_local(l.punch_timestamp), l.id))[0]
    return sorted(logs, key=lambda l: (_aware_local(l.punch_timestamp), l.id))[-1]


def assign_raw_punch_to_attendance(
    attendance: Attendance,
    *,
    punch: AttendancePunchingHistory,
    direction: str,
    persist: bool = False,
):
    if not attendance or not punch:
        return attendance
    localized_ts = _aware_local(punch.punch_timestamp)
    setattr(attendance, _session_date_attr(direction), localized_ts.date())
    setattr(attendance, _session_time_attr(direction), localized_ts.time().replace(microsecond=0))
    setattr(attendance, _session_channel_attr(direction), _expected_final_channel(punch.source))
    setattr(attendance, f"{_session_punch_attr(direction)}_id", punch.id)
    if hasattr(attendance, _session_image_attr(direction)):
        setattr(attendance, _session_image_attr(direction), punch.photo if getattr(punch, "photo", None) else None)
    if hasattr(attendance, _session_location_attr(direction)):
        setattr(attendance, _session_location_attr(direction), deepcopy(getattr(punch, "location", None)))
    if direction == AttendancePunchDirection.IN and hasattr(attendance, "in_attendance_status"):
        attendance.in_attendance_status = "VALID"
        if hasattr(attendance, "in_attendance_reject_reason_code"):
            attendance.in_attendance_reject_reason_code = None
    if direction == AttendancePunchDirection.OUT and hasattr(attendance, "out_attendance_status"):
        attendance.out_attendance_status = "VALID"
        if hasattr(attendance, "out_attendance_reject_reason_code"):
            attendance.out_attendance_reject_reason_code = None
    if persist:
        attendance.save()
    return attendance


def relink_attendance_to_raw_punches(attendance: Attendance, *, include_in: bool = False, include_out: bool = False):
    if not attendance:
        return attendance
    if include_in and getattr(attendance, _session_channel_attr(AttendancePunchDirection.IN), None) in RAW_CHANNELS.union({None, ""}):
        if getattr(attendance, f"{_session_punch_attr(AttendancePunchDirection.IN)}_id", None) is None:
            punch = _pick_best_raw_candidate(attendance, AttendancePunchDirection.IN)
            if punch:
                assign_raw_punch_to_attendance(attendance, punch=punch, direction=AttendancePunchDirection.IN)
    if include_out and getattr(attendance, _session_channel_attr(AttendancePunchDirection.OUT), None) in RAW_CHANNELS.union({None, ""}):
        if getattr(attendance, f"{_session_punch_attr(AttendancePunchDirection.OUT)}_id", None) is None:
            punch = _pick_best_raw_candidate(attendance, AttendancePunchDirection.OUT)
            if punch:
                assign_raw_punch_to_attendance(attendance, punch=punch, direction=AttendancePunchDirection.OUT)
    return attendance


def clear_raw_links_for_request_override(attendance: Attendance, *, include_in: bool = False, include_out: bool = False):
    if include_in:
        attendance.attendance_clock_in_punch_id = None
        if hasattr(attendance, "attendance_clock_in_image"):
            attendance.attendance_clock_in_image = None
        if hasattr(attendance, "attendance_clock_in_location"):
            attendance.attendance_clock_in_location = None
    if include_out:
        attendance.attendance_clock_out_punch_id = None
        if hasattr(attendance, "attendance_clock_out_image"):
            attendance.attendance_clock_out_image = None
        if hasattr(attendance, "attendance_clock_out_location"):
            attendance.attendance_clock_out_location = None
    return attendance


def restore_raw_state_after_request(attendance: Attendance, *, include_in: bool = False, include_out: bool = False):
    snapshot = deepcopy(getattr(attendance, "request_restore_snapshot", None) or {})
    if include_in:
        _restore_session_from_snapshot(attendance, AttendancePunchDirection.IN, snapshot.get("in"))
    if include_out:
        _restore_session_from_snapshot(attendance, AttendancePunchDirection.OUT, snapshot.get("out"))

    relink_attendance_to_raw_punches(attendance, include_in=include_in, include_out=include_out)
    attendance.save()
    clear_request_restore_snapshot(attendance, include_in=include_in, include_out=include_out)
    return attendance


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

        in_match = getattr(attendance, "attendance_clock_in_punch_id", None)
        out_match = getattr(attendance, "attendance_clock_out_punch_id", None)

        if not in_match and attendance.attendance_clock_in and attendance.attendance_clock_in_channel in RAW_CHANNELS.union({None, ""}):
            for log in logs:
                localized_ts = _aware_local(log.punch_timestamp)
                if (
                    log.punch_direction == AttendancePunchDirection.IN
                    and _match_allowed_for_log(log, attendance.attendance_clock_in_channel)
                    and _same_timestamp(attendance.attendance_clock_in_date, attendance.attendance_clock_in, localized_ts)
                ):
                    in_match = log.id
                    break
        if not out_match and attendance.attendance_clock_out and attendance.attendance_clock_out_channel in RAW_CHANNELS.union({None, ""}):
            for log in reversed(logs):
                localized_ts = _aware_local(log.punch_timestamp)
                if (
                    log.punch_direction == AttendancePunchDirection.OUT
                    and _match_allowed_for_log(log, attendance.attendance_clock_out_channel)
                    and _same_timestamp(attendance.attendance_clock_out_date, attendance.attendance_clock_out, localized_ts)
                ):
                    out_match = log.id
                    break

    in_reject_reason = _attendance_reject_reason(attendance, direction=AttendancePunchDirection.IN)
    out_reject_reason = _attendance_reject_reason(attendance, direction=AttendancePunchDirection.OUT)

    for log in logs:
        accepted = False
        reason = (log.reason or "").strip()

        if log.punch_direction == AttendancePunchDirection.IN:
            if in_match and log.id == in_match:
                accepted = True
                reason = _accepted_reason(AttendancePunchDirection.IN)
            elif should_preserve_reason(reason):
                reason = _clean_reason_text(reason)
            elif in_reject_reason:
                reason = in_reject_reason
            elif in_match:
                reason = _superseded_reason(AttendancePunchDirection.IN)
            elif attendance and attendance.attendance_clock_in and in_final_source_reason:
                reason = in_final_source_reason
            else:
                reason = "Ignored because this Check-In was not selected"

        elif log.punch_direction == AttendancePunchDirection.OUT:
            if out_match and log.id == out_match:
                accepted = True
                reason = _accepted_reason(AttendancePunchDirection.OUT)
            elif should_preserve_reason(reason):
                reason = _clean_reason_text(reason)
            elif out_reject_reason:
                reason = out_reject_reason
            elif out_match:
                reason = _superseded_reason(AttendancePunchDirection.OUT)
            elif attendance and attendance.attendance_clock_out and out_final_source_reason:
                reason = out_final_source_reason
            else:
                reason = _superseded_reason(AttendancePunchDirection.OUT)

        else:
            if not should_preserve_reason(reason):
                reason = "Ignored: unsupported punch direction"
            else:
                reason = _clean_reason_text(reason)

        update_punch_history(
            log,
            accepted=accepted,
            reason=_clean_reason_text(reason),
            attendance=attendance,
            attendance_date=attendance_date,
        )


def reconcile_single_punch_against_attendance(punch: AttendancePunchingHistory):
    if not punch or not punch.employee_id:
        return
    dt = _aware_local(punch.punch_timestamp)
    attendance = Attendance.objects.filter(employee_id=punch.employee_id).filter(
        Q(attendance_date=dt.date()) | Q(attendance_date=dt.date() - timedelta(days=1))
    ).order_by('-attendance_date').first()
    if attendance:
        update_punch_history(punch, attendance=attendance, attendance_date=attendance.attendance_date)
        reconcile_attendance_punches(employee=punch.employee_id, attendance_date=attendance.attendance_date)
