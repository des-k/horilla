"""Shared helpers for validating attendance monthly recap query params."""

from __future__ import annotations

import re
from typing import Optional

_MONTH_YYYY_MM_RE = re.compile(r"^\d{4}-(0[1-9]|1[0-2])$")


def is_valid_month_yyyy_mm(value: Optional[str]) -> bool:
    raw = (value or "").strip()
    return bool(_MONTH_YYYY_MM_RE.fullmatch(raw))


def require_month_yyyy_mm(value: Optional[str]) -> str:
    month = (value or "").strip()
    if not is_valid_month_yyyy_mm(month):
        raise ValueError("Invalid month format. Expected YYYY-MM")
    return month


def normalize_month_yyyy_mm(
    value: Optional[str],
    *,
    fallback_month: str,
    max_month: Optional[str] = None,
) -> str:
    """Return a safe YYYY-MM value.

    - invalid / malformed input falls back to ``fallback_month``
    - future month is clamped to ``max_month`` when provided
    """

    resolved_fallback = require_month_yyyy_mm(fallback_month)
    month = (value or "").strip()
    if not is_valid_month_yyyy_mm(month):
        month = resolved_fallback

    if max_month:
        resolved_max = require_month_yyyy_mm(max_month)
        if month > resolved_max:
            return resolved_max

    return month
