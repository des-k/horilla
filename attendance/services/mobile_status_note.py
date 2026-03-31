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


def _late_detail_text(late_by: str | None) -> str | None:
    return f"Late by {late_by}" if late_by else None


def _short_by_text(checked_out_early: bool, checked_out_early_by: str | None) -> str | None:
    if checked_out_early and checked_out_early_by:
        return f"Short by {checked_out_early_by}"
    return None


def _missing_check_in_early_header(has_check_out: bool, checked_out_early: bool) -> str:
    if has_check_out and checked_out_early:
        return "Missing Check In, Check Out Early"
    return "Missing Check In"


def _missing_check_in_detail(
    *,
    has_check_out: bool,
    can_clock_out: bool,
    checked_out_early: bool,
    checked_out_early_by: str | None,
) -> str | None:
    if has_check_out and checked_out_early:
        return _join_details(
            _short_by_text(checked_out_early, checked_out_early_by),
            "Check Out saved",
        )
    if has_check_out:
        return "Check Out saved"
    if can_clock_out:
        return "Check Out available"
    return None


def _join_details(*parts: str | None) -> str | None:
    cleaned = [part for part in parts if part]
    return " - ".join(cleaned) if cleaned else None


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
    unavailable_detail = _clean_text(payload.get("attendance_disabled_message"))
    late_by = _clean_text(payload.get("late_by"))
    checked_out_early_by = _clean_text(payload.get("checked_out_early_by"))

    has_attendance = _as_bool(payload.get("has_attendance"))
    has_check_in = bool(first_check_in)
    has_check_out = bool(last_check_out)
    missing_check_in = _as_bool(payload.get("missing_check_in"))
    can_clock_in = _as_bool(payload.get("can_clock_in") or payload.get("can_check_in"))
    can_clock_out = _as_bool(payload.get("can_clock_out") or payload.get("can_check_out"))
    attendance_enabled = _as_bool(payload.get("attendance_enabled", True))
    check_in_cutoff_passed = _as_bool(payload.get("check_in_cutoff_has_passed"))
    checked_out_early = _as_bool(payload.get("checked_out_early"))
    invalid_check_in = _as_bool(payload.get("invalid_check_in"))
    earliest_check_out = _clean_text(payload.get("earliest_check_out")) or _clean_text(payload.get("check_out_window_start"))

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
            message=_missing_check_in_early_header(has_check_out, checked_out_early),
            detail_message=_missing_check_in_detail(
                has_check_out=has_check_out,
                can_clock_out=can_clock_out,
                checked_out_early=checked_out_early,
                checked_out_early_by=checked_out_early_by,
            ),
        ).as_payload()

    if has_check_in and not has_check_out:
        if check_out_block_reason == "AFTER_WINDOW_END" and not can_clock_out:
            return MobileAttendanceHeaderState(
                code=CHECK_OUT_REQUEST_REQUIRED,
                message="Check Out cutoff passed",
                detail_message="Please submit an attendance request",
            ).as_payload()

        return MobileAttendanceHeaderState(
            code=CHECKED_IN,
            message="Checked In",
            detail_message=_join_details(
                _late_detail_text(late_by),
                f"Earliest Check Out: {earliest_check_out}" if earliest_check_out else None,
            ),
        ).as_payload()

    if has_check_in and has_check_out:
        if checked_out_early:
            return MobileAttendanceHeaderState(
                code=CHECKED_OUT_EARLY,
                message="Checked Out early",
                detail_message=_join_details(
                    _short_by_text(checked_out_early, checked_out_early_by),
                    _late_detail_text(late_by),
                ),
            ).as_payload()

        return MobileAttendanceHeaderState(
            code=ATTENDANCE_RECORDED,
            message="Attendance recorded",
            detail_message=_late_detail_text(late_by),
        ).as_payload()

    if has_check_out and not has_check_in:
        return MobileAttendanceHeaderState(
            code=MISSING_CHECK_IN,
            message=_missing_check_in_early_header(has_check_out, checked_out_early),
            detail_message=_missing_check_in_detail(
                has_check_out=has_check_out,
                can_clock_out=can_clock_out,
                checked_out_early=checked_out_early,
                checked_out_early_by=checked_out_early_by,
            ),
        ).as_payload()

    if not has_attendance and check_in_cutoff_passed and can_clock_out:
        return MobileAttendanceHeaderState(
            code=MISSING_CHECK_IN,
            message="Missing Check In",
            detail_message="Check Out available",
        ).as_payload()

    if not has_attendance and check_out_block_reason == "AFTER_WINDOW_END" and not can_clock_out:
        return MobileAttendanceHeaderState(
            code=CHECK_OUT_REQUEST_REQUIRED,
            message="Check Out cutoff passed",
            detail_message="Please submit an attendance request",
        ).as_payload()

    return MobileAttendanceHeaderState(
        code=READY_TO_CHECK_IN,
        message="No record yet",
        detail_message="Please Check In",
    ).as_payload()
