"""attendance_window_rules.py

Pure helpers for attendance IN/OUT windows.

This module intentionally avoids importing Django models so it can be unit tested
without DB setup.

Business rules (FINAL spec):
- Check-in window:
    earliest = shift_start - early_checkin_minutes
    latest   = cutoff_in_dt (if provided) else shift_start + late_checkin_minutes
- Check-out window (WFO/WFA):
    earliest = shift_end - early_checkout_grace_minutes
    latest   = cutoff_out_dt (if provided) else shift_end + max_late_checkout_hours
- Check-out window (ON_DUTY presence-only):
    earliest = cutoff_in_dt
    latest   = cutoff_out_dt (if provided) else shift_end + max_late_checkout_hours

Reject reasons (Option B):
- WFO/WFA: EARLY_CHECKOUT_BEFORE_SHIFT_END
- ON_DUTY: EARLY_CHECKOUT_BEFORE_CUTOFF_IN
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta
from typing import Optional, Tuple


@dataclass(frozen=True)
class WindowConfig:
    early_checkin_minutes: int = 120
    late_checkin_minutes: int = 120
    early_checkout_grace_minutes: int = 0
    max_late_checkout_hours: int = 12


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
        late_checkin_minutes=_clamp_nonneg(cfg.late_checkin_minutes, 120),
        early_checkout_grace_minutes=_clamp_nonneg(cfg.early_checkout_grace_minutes, 0),
        max_late_checkout_hours=_clamp_nonneg(cfg.max_late_checkout_hours, 12),
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
    end = cutoff_in_dt if cutoff_in_dt else (shift_start_dt + timedelta(minutes=cfg_n.late_checkin_minutes))
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

    start = shift_end_dt - timedelta(minutes=cfg_n.early_checkout_grace_minutes)
    end = cutoff_out_dt if cutoff_out_dt else (shift_end_dt + timedelta(hours=cfg_n.max_late_checkout_hours))
    return start, end


def compute_checkout_window_on_duty(
    *,
    cutoff_in_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
    cutoff_out_dt: Optional[datetime],
    cfg: Optional[WindowConfig] = None,
) -> Tuple[Optional[datetime], Optional[datetime]]:
    cfg_n = normalize_config(cfg)
    start = cutoff_in_dt
    if cutoff_out_dt:
        end = cutoff_out_dt
    elif shift_end_dt:
        end = shift_end_dt + timedelta(hours=cfg_n.max_late_checkout_hours)
    else:
        end = None
    return start, end


def early_checkout_reject_reason(*, is_on_duty: bool) -> str:
    return "EARLY_CHECKOUT_BEFORE_CUTOFF_IN" if is_on_duty else "EARLY_CHECKOUT_BEFORE_SHIFT_END"


def is_early_checkout(
    *,
    out_dt: datetime,
    earliest_checkout_dt: Optional[datetime],
) -> bool:
    if not earliest_checkout_dt:
        return False
    return out_dt < earliest_checkout_dt
