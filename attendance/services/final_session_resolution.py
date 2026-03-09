"""Helpers for resolving the effective attendance session winner.

Business rule:
- Approved attendance request wins per session.
- Otherwise use earliest raw IN / latest raw OUT.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from typing import Iterable, Optional

APPROVED_REQUEST_CHANNEL = "approved_request"


@dataclass(frozen=True)
class SessionResolution:
    session: str
    final_dt: Optional[datetime]
    final_source: Optional[str]
    approved_dt: Optional[datetime]
    raw_dt: Optional[datetime]


def is_approved_request_channel(value: Optional[str]) -> bool:
    return (value or "").strip().lower() == APPROVED_REQUEST_CHANNEL


def resolve_final_session(
    *,
    session: str,
    approved_dt: Optional[datetime],
    raw_datetimes: Iterable[Optional[datetime]],
    raw_source: Optional[str] = None,
) -> SessionResolution:
    session_norm = (session or "IN").upper()
    raw_candidates = [dt for dt in raw_datetimes if dt is not None]
    raw_dt = None
    if raw_candidates:
        raw_dt = min(raw_candidates) if session_norm == "IN" else max(raw_candidates)

    if approved_dt is not None:
        return SessionResolution(
            session=session_norm,
            final_dt=approved_dt,
            final_source=APPROVED_REQUEST_CHANNEL,
            approved_dt=approved_dt,
            raw_dt=raw_dt,
        )

    return SessionResolution(
        session=session_norm,
        final_dt=raw_dt,
        final_source=raw_source,
        approved_dt=None,
        raw_dt=raw_dt,
    )


def should_accept_raw_session(
    *,
    session: str,
    existing_dt: Optional[datetime],
    incoming_dt: Optional[datetime],
    existing_channel: Optional[str] = None,
) -> bool:
    if incoming_dt is None:
        return False
    if is_approved_request_channel(existing_channel):
        return False
    if existing_dt is None:
        return True
    session_norm = (session or "IN").upper()
    if session_norm == "IN":
        return incoming_dt < existing_dt
    return incoming_dt > existing_dt
