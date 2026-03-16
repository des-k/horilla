from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping


@dataclass(frozen=True)
class MobileAttendanceHeaderState:
    code: str
    message: str
    detail_message: str | None = None

    def as_payload(self) -> dict[str, str | None]:
        return {
            "header_state_code": self.code,
            "header_state_message": self.message,
            "header_detail_message": self.detail_message,
        }


READY_TO_CHECK_IN = "READY_TO_CHECK_IN"
CHECKED_IN = "CHECKED_IN"
MISSING_CHECK_IN = "MISSING_CHECK_IN"
CHECK_OUT_REQUEST_REQUIRED = "CHECK_OUT_REQUEST_REQUIRED"
CHECKED_OUT_EARLY = "CHECKED_OUT_EARLY"
BELOW_MINIMUM_HOURS = "BELOW_MINIMUM_HOURS"
ATTENDANCE_RECORDED = "ATTENDANCE_RECORDED"
ATTENDANCE_UNAVAILABLE = "ATTENDANCE_UNAVAILABLE"


def _clean_text(value: Any) -> str | None:
    if value is None:
        return None
    text = str(value).strip()
    if not text or text.lower() == "null":
        return None
    return text


def _as_bool(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    if isinstance(value, str):
        return value.strip().lower() in {"1", "true", "yes", "y"}
    return bool(value)


def build_mobile_header_state(payload: Mapping[str, Any]) -> dict[str, str | None]:
    """Return the canonical, backend-driven mobile header state.

    The state is derived from final backend truth already computed by the
    attendance status endpoint (attendance row, activity meaning, cutoff state,
    minimum-hours result, etc.), not from Flutter heuristics.
    """

    first_check_in = _clean_text(
        payload.get("first_check_in")
        or payload.get("clock_in")
        or payload.get("clock_in_time")
    )
    last_check_out = _clean_text(
        payload.get("last_check_out")
        or payload.get("clock_out")
        or payload.get("clock_out_time")
    )
    shortfall = _clean_text(payload.get("header_note_work_hours_shortfall")) or _clean_text(payload.get("work_hours_shortfall"))
    minimum_hour = _clean_text(payload.get("header_note_effective_minimum_hour")) or _clean_text(payload.get("minimum_working_hour"))
    unavailable_detail = _clean_text(payload.get("attendance_disabled_message"))

    has_attendance = _as_bool(payload.get("has_attendance"))
    has_check_in = bool(first_check_in)
    has_check_out = bool(last_check_out)
    missing_check_in = _as_bool(payload.get("missing_check_in"))
    can_clock_in = _as_bool(payload.get("can_clock_in") or payload.get("can_check_in"))
    can_clock_out = _as_bool(payload.get("can_clock_out") or payload.get("can_check_out"))
    attendance_enabled = _as_bool(payload.get("attendance_enabled", True))
    check_in_cutoff_passed = _as_bool(payload.get("check_in_cutoff_has_passed"))
    if "header_note_work_hours_below_minimum" in payload:
        work_hours_below_minimum = _as_bool(payload.get("header_note_work_hours_below_minimum"))
    else:
        work_hours_below_minimum = _as_bool(payload.get("work_hours_below_minimum"))
    checked_out_early = _as_bool(payload.get("checked_out_early"))

    check_in_block_reason = (_clean_text(payload.get("check_in_block_reason")) or "").upper()
    check_out_block_reason = (_clean_text(payload.get("check_out_block_reason")) or "").upper()

    blocked_unavailable_reasons = {
        "ATTENDANCE_DISABLED",
        "SHIFT_NOT_ASSIGNED",
        "MODE_NOT_ALLOWED",
    }

    if (not attendance_enabled) or (
        not has_attendance
        and not has_check_in
        and not has_check_out
        and not can_clock_in
        and not can_clock_out
        and (
            check_in_block_reason in blocked_unavailable_reasons
            or check_out_block_reason in blocked_unavailable_reasons
        )
    ):
        return MobileAttendanceHeaderState(
            code=ATTENDANCE_UNAVAILABLE,
            message="Attendance unavailable",
            detail_message=unavailable_detail,
        ).as_payload()

    if missing_check_in:
        return MobileAttendanceHeaderState(
            code=MISSING_CHECK_IN,
            message=(
                "Missing Check In • Check Out saved"
                if has_check_out
                else "Missing Check In • Check Out available"
            ),
        ).as_payload()

    if has_check_in and not has_check_out:
        if check_out_block_reason == "AFTER_WINDOW_END" and not can_clock_out:
            return MobileAttendanceHeaderState(
                code=CHECK_OUT_REQUEST_REQUIRED,
                message="Check Out cutoff passed • Please submit an attendance request",
            ).as_payload()

        return MobileAttendanceHeaderState(
            code=CHECKED_IN,
            message="Checked In • Don’t forget to Check Out",
        ).as_payload()

    if has_check_in and has_check_out:
        if work_hours_below_minimum:
            detail_parts: list[str] = []
            if shortfall:
                detail_parts.append(f"Short by {shortfall}")
            elif minimum_hour:
                detail_parts.append(f"Expected work session {minimum_hour}")
            if checked_out_early:
                detail_parts.append("Checked out early")
            detail_message = " • ".join(detail_parts) if detail_parts else None
            return MobileAttendanceHeaderState(
                code=BELOW_MINIMUM_HOURS,
                message="Below minimum hours",
                detail_message=detail_message,
            ).as_payload()

        if checked_out_early:
            return MobileAttendanceHeaderState(
                code=CHECKED_OUT_EARLY,
                message="Checked Out early",
            ).as_payload()

        return MobileAttendanceHeaderState(
            code=ATTENDANCE_RECORDED,
            message="Attendance recorded",
        ).as_payload()

    if has_check_out and not has_check_in:
        return MobileAttendanceHeaderState(
            code=MISSING_CHECK_IN,
            message="Missing Check In • Check Out saved",
        ).as_payload()

    if not has_attendance and check_in_cutoff_passed and can_clock_out:
        return MobileAttendanceHeaderState(
            code=MISSING_CHECK_IN,
            message="Missing Check In • Check Out available",
        ).as_payload()

    if not has_attendance and check_out_block_reason == "AFTER_WINDOW_END" and not can_clock_out:
        return MobileAttendanceHeaderState(
            code=CHECK_OUT_REQUEST_REQUIRED,
            message="Check Out cutoff passed • Please submit an attendance request",
        ).as_payload()

    return MobileAttendanceHeaderState(
        code=READY_TO_CHECK_IN,
        message="No record yet • Please Check In",
    ).as_payload()
