"""attendance.services.monthly_recap_note

Pure helpers for the **Attendance → Attendances (Monthly Recap)** view.

Kept Django-free so it can be unit-tested without requiring Django settings.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import List, Optional


# NOTE suffix / Work Type translation table (longest phrases first)
_ID_SUFFIX_REPLACEMENTS = [
    # Pending / awaiting upload variants
    ("On Duty FULL Pending Approval", "Dinas Luar Penuh menunggu persetujuan"),
    ("On Duty OUT Pending Approval", "Dinas Luar Akhir menunggu persetujuan"),
    ("On Duty IN Pending Approval", "Dinas Luar Awal menunggu persetujuan"),
    ("On Duty OUT Awaiting Document Upload", "Dinas Luar Akhir menunggu upload dokumen"),
    ("On Duty IN Awaiting Document Upload", "Dinas Luar Awal menunggu upload dokumen"),
    ("On Duty FULL Awaiting Document Upload", "Dinas Luar Penuh menunggu upload dokumen"),
    # Base labels
    ("On Duty FULL", "Dinas Luar Penuh"),
    ("On Duty OUT", "Dinas Luar Akhir"),
    ("On Duty IN", "Dinas Luar Awal"),
]


def _translate_on_duty_phrases(text: str, *, language: str) -> str:
    """Translate known ON DUTY phrases for Indonesian output."""

    if not text:
        return text
    lang = (language or "en").lower()
    if not lang.startswith("id"):
        return text

    out = text
    for src, dst in _ID_SUFFIX_REPLACEMENTS:
        out = re.sub(re.escape(src), dst, out, flags=re.IGNORECASE)
    return out


def localize_on_duty_work_type(text: str, *, language: str) -> str:
    """Translate Work Type values for ON DUTY only (Indonesian).

    Requirement (latest): translate Work Type only when the Work Type value is
    ON DUTY (IN/OUT/FULL). Keep other Work Type values (WFO/WFA, etc.) unchanged.
    """

    if not text:
        return text
    lang = (language or "en").lower()
    if not lang.startswith("id"):
        return text
    if "on duty" not in text.lower():
        return text
    return _translate_on_duty_phrases(text, language=lang)


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
    3) If only one session exists, surface the missing session explicitly.
    4) Otherwise derive Late / Leave Early deterministically.
    5) Pending request suffixes do not change effective calculations.
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
            "missing_check_in": "Missing Check-In",
            "missing_check_out": "Missing Check-Out",
            "correction_pending": "Attendance correction pending",
        },
        "id": {
            "holiday": "Libur",
            "leave": "Cuti",
            "alpha": "Alpa",
            "late": "Terlambat",
            "leave_early": "Pulang Cepat",
            "late_and_early": "Terlambat, Pulang Cepat",
            "missing_check_in": "Check-in Tidak Ada",
            "missing_check_out": "Check-out Tidak Ada",
            "correction_pending": "Koreksi presensi menunggu persetujuan",
        },
    }
    t = labels["id"] if lang.startswith("id") else labels["en"]

    # Base note
    if inp.is_off:
        base = t["leave"] if inp.off_kind == "leave" else t["holiday"]
    elif not inp.has_check_in and not inp.has_check_out:
        base = t["alpha"]
    elif not inp.has_check_in:
        base = t["missing_check_in"]
        if inp.early_out_seconds and inp.early_out_seconds > 0:
            base = f"{base}, {t['leave_early']}"
    elif not inp.has_check_out:
        base = t["missing_check_out"]
        if inp.late_seconds and inp.late_seconds > 0:
            base = f"{t['late']}, {base}"
    else:
        is_late = bool(inp.late_seconds and inp.late_seconds > 0)
        is_leave_early = bool(inp.early_out_seconds and inp.early_out_seconds > 0)

        if is_late and is_leave_early:
            base = t["late_and_early"]
        elif is_late:
            base = t["late"]
        elif is_leave_early:
            base = t["leave_early"]
        else:
            base = ""

    # Suffixes (pending requests, correction pending)
    suffixes: List[str] = []
    for s in (inp.pending_suffixes or []):
        if s and s.strip():
            suffixes.append(_translate_on_duty_phrases(s.strip(), language=lang))
    if inp.correction_pending:
        suffixes.append(t["correction_pending"])

    if not suffixes:
        return base

    suffix_txt = "; ".join(suffixes)
    if base:
        return f"{base} ({suffix_txt})"
    return f"({suffix_txt})"
