"""base.worktype_display

Helpers to keep Work Type wording consistent across Web UI.

- Store short codes in DB: WFO / WFA
- Display friendly labels in UI: "Work From Office (WFO)", "Work From Anywhere (WFA)"

Attendance "Work Type Request" (attendance.WorkModeRequest) stores mode as string
and may also use ON_DUTY independently from base.WorkType.
"""

from __future__ import annotations

from typing import Any


def _norm(val: str) -> str:
    return (val or "").strip().lower().replace("_", " ").replace("-", " ")


def worktype_label(val: Any) -> str:
    """Return UI label for a WorkType (instance) or string code."""

    if val is None:
        return ""

    # WorkType instance
    if hasattr(val, "work_type"):
        s = getattr(val, "work_type", "") or ""
    else:
        s = str(val)

    n = _norm(s)
    if n == "wfo" or "work from office" in n or n == "office":
        return "Work From Office (WFO)"
    if n == "wfa" or "work from anywhere" in n or "anywhere" in n:
        return "Work From Anywhere (WFA)"

    # legacy names treated as WFA in display
    if "work from home" in n or "remote" in n or "hybrid" in n:
        return "Work From Anywhere (WFA)"

    return s


def worktype_queryset_wfo_wfa(qs):
    """Filter a WorkType queryset to only WFO/WFA for employee defaults/requests."""
    try:
        return qs.filter(work_type__in=["WFO", "WFA"])
    except Exception:
        return qs
