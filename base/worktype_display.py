"""base.worktype_display

Helpers to keep Work Type wording consistent across Web UI.
"""

from __future__ import annotations

from typing import Any

from django.db.models import Q


CANONICAL_WORK_TYPES = {"WFO": "WFO", "WFA": "WFA", "WFH": "WFH"}
LEGACY_ALIASES = {
    "work from office": "WFO",
    "work from anywhere": "WFA",
    "work from home": "WFH",
    "office": "WFO",
    "remote": "WFA",
}


def _norm(val: str) -> str:
    return (val or "").strip().lower().replace("_", " ").replace("-", " ")


def normalize_work_type_label(val: Any) -> str:
    if val is None:
        return ""
    if hasattr(val, "work_type"):
        s = getattr(val, "work_type", "") or ""
    else:
        s = str(val)
    n = _norm(s)
    if n in {"wfo", "wfa", "wfh"}:
        return n.upper()
    for alias, canonical in LEGACY_ALIASES.items():
        if alias in n:
            return canonical
    return s.strip().upper() or ""


def worktype_label(val: Any) -> str:
    normalized = normalize_work_type_label(val)
    if normalized == "WFO":
        return "Work From Office (WFO)"
    if normalized == "WFA":
        return "Work From Anywhere (WFA)"
    if normalized == "WFH":
        return "Work From Home (WFH)"
    return str(val or "")


def worktype_queryset_wfo_wfa(qs):
    """Filter a WorkType queryset to canonical attendance work types."""
    try:
        return qs.filter(
            Q(work_type__iexact="WFO")
            | Q(work_type__iexact="WFA")
            | Q(work_type__iexact="WFH")
            | Q(work_type__iexact="work from office")
            | Q(work_type__iexact="work from anywhere")
            | Q(work_type__iexact="work from home")
        )
    except Exception:
        return qs
