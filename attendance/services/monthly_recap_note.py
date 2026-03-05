"""attendance.services.monthly_recap_note

Pure helpers for the **Attendance → Attendances (Monthly Recap)** view.

Kept Django-free so it can be unit-tested without requiring Django settings.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Optional


def seconds_to_hhmm(total_seconds: float) -> str:
    """Format a duration (seconds) as HH:MM.

    - Negative values are clamped to 0.
    - Seconds are floored to the nearest minute.
    """
    try:
        sec = int(total_seconds)
    except Exception:
        sec = 0
    if sec < 0:
        sec = 0
    minutes = sec // 60
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"


@dataclass(frozen=True)
class NoteInputs:
    is_off: bool
    off_kind: Optional[str] = None  # "holiday" | "leave" | None
    has_check_in: bool = False
    has_check_out: bool = False
    late_seconds: float = 0
    early_out_seconds: float = 0
    pending_suffixes: Optional[List[str]] = None
    correction_pending: bool = False


def derive_note(inp: NoteInputs, *, language: str = "en") -> str:
    """Derive the UI Note (keterangan) for the monthly recap table.

    Rules (FINAL spec):
    1) OFF (holiday/leave) overrides everything: never Alpha.
    2) If no check-in AND no check-out => Alpha.
    3) Otherwise:
       - Late if (late > 0) OR missing check-in
       - Leave Early if (early > 0) OR missing check-out
       - Combine deterministically.
    4) Pending ON DUTY suffixes do not change effective calculations.
    """

    lang = (language or "en").lower()
    labels = {
        "en": {
            "holiday": "Holiday",
            "leave": "On Leave",
            "alpha": "Alpha",
            "late": "Late",
            "leave_early": "Leave Early",
            "late_and_early": "Late, Leave Early",
            "correction_pending": "Attendance correction pending",
        },
        "id": {
            "holiday": "Libur",
            "leave": "Cuti",
            "alpha": "Alpha",
            "late": "Terlambat",
            "leave_early": "Pulang Cepat",
            "late_and_early": "Terlambat, Pulang Cepat",
            "correction_pending": "Koreksi presensi menunggu persetujuan",
        },
    }
    t = labels["id"] if lang.startswith("id") else labels["en"]

    # 1) OFF overrides
    if inp.is_off:
        if inp.off_kind == "leave":
            return t["leave"]
        return t["holiday"]

    # 2) Alpha
    if not inp.has_check_in and not inp.has_check_out:
        return t["alpha"]

    # 3) Late / Leave early flags
    is_late = bool(inp.late_seconds and inp.late_seconds > 0) or (not inp.has_check_in)
    is_leave_early = bool(inp.early_out_seconds and inp.early_out_seconds > 0) or (
        not inp.has_check_out
    )

    if is_late and is_leave_early:
        base = t["late_and_early"]
    elif is_late:
        base = t["late"]
    elif is_leave_early:
        base = t["leave_early"]
    else:
        base = ""

    suffixes: List[str] = []
    for s in (inp.pending_suffixes or []):
        if s and s.strip():
            suffixes.append(s.strip())
    if inp.correction_pending:
        suffixes.append(t["correction_pending"])

    if not suffixes:
        return base

    suffix_txt = "; ".join(suffixes)
    if base:
        return f"{base} ({suffix_txt})"
    return f"({suffix_txt})"

