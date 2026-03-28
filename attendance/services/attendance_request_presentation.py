from __future__ import annotations

from datetime import date, datetime, time
from typing import Any, Dict

from attendance.services.attendance_correction_scope_rules import load_requested_data

EMPTY_VALUES = {None, "", "None", "null", "NULL"}


REQUEST_TIME_FIELDS = (
    "attendance_clock_in",
    "attendance_clock_out",
    "attendance_clock_in_date",
    "attendance_clock_out_date",
)


def _clean_value(value: Any) -> Any:
    if isinstance(value, str):
        value = value.strip()
    return None if value in EMPTY_VALUES else value



def _format_time_value(value: Any) -> str | None:
    value = _clean_value(value)
    if value is None:
        return None
    if isinstance(value, datetime):
        return value.strftime("%H:%M")
    if isinstance(value, time):
        return value.strftime("%H:%M")
    text = str(value).strip()
    if not text:
        return None
    if "T" in text:
        try:
            parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
            return parsed.strftime("%H:%M")
        except Exception:
            pass
    if len(text) >= 5 and text[2:3] == ":":
        return text[:5]
    return text



def _format_date_value(value: Any) -> str | None:
    value = _clean_value(value)
    if value is None:
        return None
    if isinstance(value, datetime):
        return value.strftime("%Y-%m-%d")
    if isinstance(value, date):
        return value.strftime("%Y-%m-%d")
    text = str(value).strip()
    if not text:
        return None
    if "T" in text:
        try:
            parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
            return parsed.strftime("%Y-%m-%d")
        except Exception:
            pass
    return text[:10] if len(text) >= 10 else text



def _format_for_field(field_name: str, value: Any) -> str | None:
    if field_name.endswith("_date"):
        return _format_date_value(value)
    return _format_time_value(value)



def build_attendance_request_time_surface(attendance) -> Dict[str, Any]:
    requested = load_requested_data(getattr(attendance, "requested_data", None))
    surface: Dict[str, Any] = {"has_proposed_values": False}

    for field_name in REQUEST_TIME_FIELDS:
        proposed = _format_for_field(field_name, requested.get(field_name))
        final = _format_for_field(field_name, getattr(attendance, field_name, None))
        effective = proposed or final
        show_final = bool(proposed and final and proposed != final)

        if proposed:
            surface["has_proposed_values"] = True

        surface[f"proposed_{field_name}"] = proposed
        surface[f"final_{field_name}"] = final
        surface[f"effective_{field_name}"] = effective
        surface[f"show_final_{field_name}"] = show_final

    return surface
