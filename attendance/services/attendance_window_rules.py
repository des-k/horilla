"""attendance_window_rules.py

Pure helpers for attendance IN/OUT windows.

This module intentionally avoids importing Django models so it can be unit tested
without DB setup.

Business rules (FINAL spec):
- Check-in window:
    earliest = shift_start - early_checkin_minutes
    latest   = cutoff_in_dt (if provided) else shift_start_dt
- Check-out window (all work modes):
    earliest = shift_end - early_checkout_minutes
    latest   = cutoff_out_dt (if provided) else shift_end_dt

Attendance policy decision:
- ON_DUTY uses the same check-in/check-out window boundaries as normal attendance.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Optional, Tuple


@dataclass(frozen=True)
class WindowConfig:
    early_checkin_minutes: int = 120
    early_checkout_minutes: int = 0


def _clamp_nonneg(v: int, default: int) -> int:
    try:
        v_int = int(v)
        return v_int if v_int >= 0 else int(default)
    except Exception:
        return int(default)


def normalize_config(cfg: Optional[WindowConfig]) -> WindowConfig:
    cfg = cfg or WindowConfig()
    return WindowConfig(
        early_checkin_minutes=_clamp_nonneg(cfg.early_checkin_minutes, 120),
        early_checkout_minutes=_clamp_nonneg(cfg.early_checkout_minutes, 0),
    )


def compute_checkin_window(
    *,
    shift_start_dt: Optional[datetime],
    cutoff_in_dt: Optional[datetime],
    cfg: Optional[WindowConfig] = None,
) -> Tuple[Optional[datetime], Optional[datetime]]:
    cfg_n = normalize_config(cfg)
    if not shift_start_dt:
        return None, cutoff_in_dt

    start = shift_start_dt - timedelta(minutes=cfg_n.early_checkin_minutes)
    end = cutoff_in_dt if cutoff_in_dt else shift_start_dt
    return start, end


def compute_checkout_window_wfo_wfa(
    *,
    shift_end_dt: Optional[datetime],
    cutoff_out_dt: Optional[datetime],
    cfg: Optional[WindowConfig] = None,
) -> Tuple[Optional[datetime], Optional[datetime]]:
    cfg_n = normalize_config(cfg)
    if not shift_end_dt:
        return None, cutoff_out_dt

    start = shift_end_dt - timedelta(minutes=cfg_n.early_checkout_minutes)
    end = cutoff_out_dt if cutoff_out_dt else shift_end_dt
    return start, end


def compute_checkout_window_on_duty(
    *,
    cutoff_in_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
    cutoff_out_dt: Optional[datetime],
    cfg: Optional[WindowConfig] = None,
) -> Tuple[Optional[datetime], Optional[datetime]]:
    del cutoff_in_dt
    return compute_checkout_window_wfo_wfa(
        shift_end_dt=shift_end_dt,
        cutoff_out_dt=cutoff_out_dt,
        cfg=cfg,
    )


def early_checkout_reject_reason(*, is_on_duty: bool) -> str:
    del is_on_duty
    return "EARLY_CHECKOUT_BEFORE_SHIFT_END"


def is_early_checkout(
    *,
    out_dt: datetime,
    earliest_checkout_dt: Optional[datetime],
) -> bool:
    if not earliest_checkout_dt:
        return False
    return out_dt < earliest_checkout_dt
