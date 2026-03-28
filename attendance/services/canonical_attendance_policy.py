from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta, time
from typing import Optional

from attendance.methods.utils import format_time, strtime_seconds


@dataclass
class AttendancePolicy:
    kind: Optional[str]
    shift_start_dt: Optional[datetime]
    shift_end_dt: Optional[datetime]
    break_start_dt: Optional[datetime]
    break_end_dt: Optional[datetime]
    late_reference_dt: Optional[datetime]
    nominal_policy_end_dt: Optional[datetime]
    required_work_seconds: int
    minimum_hour: str
    maximum_late_seconds: int
    apply_grace_to_late: bool
    cap_actual_late_to_max: bool


@dataclass
class AttendanceMetrics:
    worked_seconds: int
    late_seconds: int
    early_out_seconds: int
    effective_start_dt: Optional[datetime]
    earliest_checkout_dt: Optional[datetime]
    valid_check_in: bool


def _seconds_to_hhmm(seconds: int) -> str:
    if seconds <= 0:
        return "00:00"
    return format_time(int(seconds))


def _duration_seconds(value) -> int:
    if value is None:
        return 0
    try:
        if hasattr(value, "strftime"):
            raw = value.strftime("%H:%M:%S")
        else:
            raw = str(value or "").strip()
        if not raw:
            return 0
        if raw.count(":") == 1:
            raw = f"{raw}:00"
        return max(0, int(strtime_seconds(raw)))
    except Exception:
        return 0


def time_to_shift_instance_dt(
    threshold_time: Optional[time],
    *,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
) -> Optional[datetime]:
    if not (threshold_time and shift_start_dt and shift_end_dt):
        return None

    candidate = datetime.combine(shift_start_dt.date(), threshold_time)
    if shift_start_dt.tzinfo is not None and candidate.tzinfo is None:
        candidate = candidate.replace(tzinfo=shift_start_dt.tzinfo)
    if candidate < shift_start_dt and shift_end_dt.date() > shift_start_dt.date():
        candidate = candidate + timedelta(days=1)
    return candidate


def resolve_break_datetimes(
    schedule,
    *,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
) -> tuple[Optional[datetime], Optional[datetime]]:
    if not schedule:
        return None, None
    break_start_dt = time_to_shift_instance_dt(
        getattr(schedule, "break_start_time", None),
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
    )
    break_end_dt = time_to_shift_instance_dt(
        getattr(schedule, "break_end_time", None),
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
    )
    if break_start_dt and break_end_dt and break_end_dt <= break_start_dt:
        return None, None
    return break_start_dt, break_end_dt


def net_duration_excluding_break(
    start_dt: Optional[datetime],
    end_dt: Optional[datetime],
    *,
    break_start_dt: Optional[datetime] = None,
    break_end_dt: Optional[datetime] = None,
) -> int:
    if not (start_dt and end_dt) or end_dt <= start_dt:
        return 0
    total = int((end_dt - start_dt).total_seconds())
    if total <= 0:
        return 0
    if not (break_start_dt and break_end_dt) or break_end_dt <= break_start_dt:
        return total
    overlap_start = max(start_dt, break_start_dt)
    overlap_end = min(end_dt, break_end_dt)
    overlap = int((overlap_end - overlap_start).total_seconds()) if overlap_end > overlap_start else 0
    return max(0, total - max(0, overlap))


def add_net_work_duration(
    start_dt: Optional[datetime],
    work_seconds: int,
    *,
    break_start_dt: Optional[datetime] = None,
    break_end_dt: Optional[datetime] = None,
) -> Optional[datetime]:
    if start_dt is None:
        return None
    remaining = max(0, int(work_seconds or 0))
    if remaining == 0:
        return start_dt
    if not (break_start_dt and break_end_dt) or break_end_dt <= break_start_dt:
        return start_dt + timedelta(seconds=remaining)

    if start_dt < break_start_dt:
        seconds_before_break = int((break_start_dt - start_dt).total_seconds())
        if remaining <= seconds_before_break:
            return start_dt + timedelta(seconds=remaining)
        remaining -= max(0, seconds_before_break)
        return break_end_dt + timedelta(seconds=remaining)

    if break_start_dt <= start_dt < break_end_dt:
        return break_end_dt + timedelta(seconds=remaining)

    return start_dt + timedelta(seconds=remaining)


def _resolve_normal_required_work_seconds(
    minimum_hour: str,
    *,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
    break_start_dt: Optional[datetime],
    break_end_dt: Optional[datetime],
) -> int:
    configured = _duration_seconds(minimum_hour)
    if configured > 0:
        return configured
    return net_duration_excluding_break(
        shift_start_dt,
        shift_end_dt,
        break_start_dt=break_start_dt,
        break_end_dt=break_end_dt,
    )


def build_attendance_policy(
    *,
    schedule,
    shift_start_dt: Optional[datetime],
    shift_end_dt: Optional[datetime],
    minimum_hour: str,
    leave_kind: Optional[str],
    check_in_cutoff_dt: Optional[datetime] = None,
) -> AttendancePolicy:
    break_start_dt, break_end_dt = resolve_break_datetimes(
        schedule,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
    )

    normal_required_seconds = _resolve_normal_required_work_seconds(
        minimum_hour,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
        break_start_dt=break_start_dt,
        break_end_dt=break_end_dt,
    )

    late_reference_dt = shift_start_dt
    nominal_policy_end_dt = shift_end_dt
    required_work_seconds = normal_required_seconds
    maximum_late_seconds = net_duration_excluding_break(
        shift_start_dt,
        check_in_cutoff_dt,
        break_start_dt=break_start_dt,
        break_end_dt=break_end_dt,
    ) if (shift_start_dt and check_in_cutoff_dt) else 0
    apply_grace_to_late = leave_kind not in {"first_half", "second_half"}
    cap_actual_late_to_max = leave_kind in {"first_half", "second_half"}

    if leave_kind == "first_half":
        late_reference_dt = time_to_shift_instance_dt(
            getattr(schedule, "first_half_leave_latest_check_in_time", None) if schedule else None,
            shift_start_dt=shift_start_dt,
            shift_end_dt=shift_end_dt,
        ) or shift_start_dt
        nominal_policy_end_dt = time_to_shift_instance_dt(
            getattr(schedule, "first_half_leave_new_shift_end_time", None) if schedule else None,
            shift_start_dt=shift_start_dt,
            shift_end_dt=shift_end_dt,
        ) or shift_end_dt
        required_work_seconds = net_duration_excluding_break(
            late_reference_dt,
            nominal_policy_end_dt,
            break_start_dt=break_start_dt,
            break_end_dt=break_end_dt,
        )
        maximum_late_seconds = required_work_seconds
    elif leave_kind == "second_half":
        nominal_policy_end_dt = time_to_shift_instance_dt(
            getattr(schedule, "second_half_leave_earliest_check_out_time", None) if schedule else None,
            shift_start_dt=shift_start_dt,
            shift_end_dt=shift_end_dt,
        ) or shift_end_dt
        required_work_seconds = net_duration_excluding_break(
            shift_start_dt,
            nominal_policy_end_dt,
            break_start_dt=break_start_dt,
            break_end_dt=break_end_dt,
        )
        maximum_late_seconds = required_work_seconds
    elif leave_kind == "full_day":
        required_work_seconds = 0
        maximum_late_seconds = 0

    minimum_hour_value = minimum_hour or "00:00"
    if leave_kind in {"first_half", "second_half"}:
        minimum_hour_value = _seconds_to_hhmm(required_work_seconds)

    return AttendancePolicy(
        kind=leave_kind,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
        break_start_dt=break_start_dt,
        break_end_dt=break_end_dt,
        late_reference_dt=late_reference_dt,
        nominal_policy_end_dt=nominal_policy_end_dt,
        required_work_seconds=max(0, int(required_work_seconds or 0)),
        minimum_hour=minimum_hour_value or "00:00",
        maximum_late_seconds=max(0, int(maximum_late_seconds or 0)),
        apply_grace_to_late=apply_grace_to_late,
        cap_actual_late_to_max=cap_actual_late_to_max,
    )


def resolve_effective_check_in_and_earliest_checkout(
    policy: AttendancePolicy,
    *,
    actual_check_in_dt: Optional[datetime],
    clock_in_type: Optional[str],
    flex_seconds: Optional[int],
) -> tuple[Optional[datetime], Optional[datetime], bool]:
    base_dt = policy.late_reference_dt or policy.shift_start_dt
    if base_dt is None:
        return None, None, True

    if actual_check_in_dt is None:
        earliest_checkout_dt = add_net_work_duration(
            base_dt,
            policy.required_work_seconds,
            break_start_dt=policy.break_start_dt,
            break_end_dt=policy.break_end_dt,
        )
        return base_dt, earliest_checkout_dt, True

    if policy.kind == "first_half":
        effective_start_dt = actual_check_in_dt if actual_check_in_dt >= base_dt else base_dt
        earliest_checkout_dt = add_net_work_duration(
            effective_start_dt,
            policy.required_work_seconds,
            break_start_dt=policy.break_start_dt,
            break_end_dt=policy.break_end_dt,
        )
        return effective_start_dt, earliest_checkout_dt, True

    flex_delta = timedelta(seconds=max(0, int(flex_seconds or 0)))
    mode = str(clock_in_type or "after").strip().lower()
    effective_start_dt = base_dt
    valid_check_in = True

    if mode == "before_after":
        window_start_dt = base_dt - flex_delta
        window_end_dt = base_dt + flex_delta
        valid_check_in = window_start_dt <= actual_check_in_dt <= window_end_dt
        if actual_check_in_dt < window_start_dt:
            effective_start_dt = window_start_dt
        elif actual_check_in_dt > window_end_dt:
            effective_start_dt = actual_check_in_dt
        else:
            effective_start_dt = actual_check_in_dt
    elif mode == "after":
        window_start_dt = base_dt
        window_end_dt = base_dt + flex_delta
        valid_check_in = window_start_dt <= actual_check_in_dt <= window_end_dt
        if actual_check_in_dt < window_start_dt:
            effective_start_dt = window_start_dt
        elif actual_check_in_dt > window_end_dt:
            effective_start_dt = actual_check_in_dt
        else:
            effective_start_dt = actual_check_in_dt
    else:
        effective_start_dt = base_dt
        valid_check_in = True

    earliest_checkout_dt = add_net_work_duration(
        effective_start_dt,
        policy.required_work_seconds,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )
    return effective_start_dt, earliest_checkout_dt, valid_check_in


def compute_worked_seconds(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    final_out_dt: Optional[datetime],
) -> int:
    return net_duration_excluding_break(
        final_in_dt,
        final_out_dt,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )


def _calculate_late_seconds(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    grace_seconds: int,
) -> int:
    if final_in_dt is None:
        return max(0, int(policy.maximum_late_seconds or 0))
    late_seconds = net_duration_excluding_break(
        policy.late_reference_dt,
        final_in_dt,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )
    if policy.apply_grace_to_late:
        late_seconds = max(0, late_seconds - max(0, int(grace_seconds or 0)))
    if policy.cap_actual_late_to_max and policy.maximum_late_seconds > 0:
        late_seconds = min(late_seconds, policy.maximum_late_seconds)
    return max(0, int(late_seconds))


def _calculate_early_out_seconds(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    final_out_dt: Optional[datetime],
    earliest_checkout_dt: Optional[datetime],
) -> int:
    if final_in_dt is None and final_out_dt is None:
        return 0
    if final_out_dt is None:
        return max(0, int(policy.required_work_seconds or 0))

    reference_end_dt = policy.nominal_policy_end_dt
    if policy.kind == "second_half":
        reference_end_dt = earliest_checkout_dt or policy.nominal_policy_end_dt
    elif policy.kind not in {"first_half", "full_day"} and policy.break_start_dt and policy.break_end_dt:
        reference_end_dt = earliest_checkout_dt or policy.nominal_policy_end_dt

    return net_duration_excluding_break(
        final_out_dt,
        reference_end_dt,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )


def compute_attendance_metrics(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    final_out_dt: Optional[datetime],
    grace_seconds: int,
    clock_in_type: Optional[str],
    is_presence_only: bool = False,
) -> AttendanceMetrics:
    if is_presence_only or policy.kind == "full_day":
        return AttendanceMetrics(
            worked_seconds=0,
            late_seconds=0,
            early_out_seconds=0,
            effective_start_dt=None,
            earliest_checkout_dt=None,
            valid_check_in=True,
        )

    effective_start_dt, earliest_checkout_dt, valid_check_in = resolve_effective_check_in_and_earliest_checkout(
        policy,
        actual_check_in_dt=final_in_dt,
        clock_in_type=clock_in_type,
        flex_seconds=grace_seconds,
    )

    worked_seconds = compute_worked_seconds(policy, final_in_dt=final_in_dt, final_out_dt=final_out_dt)

    if final_in_dt is None and final_out_dt is None:
        late_seconds = max(0, int(policy.maximum_late_seconds or 0))
        early_out_seconds = 0
    else:
        late_seconds = _calculate_late_seconds(policy, final_in_dt=final_in_dt, grace_seconds=grace_seconds)
        early_out_seconds = _calculate_early_out_seconds(
            policy,
            final_in_dt=final_in_dt,
            final_out_dt=final_out_dt,
            earliest_checkout_dt=earliest_checkout_dt,
        )

    return AttendanceMetrics(
        worked_seconds=max(0, int(worked_seconds or 0)),
        late_seconds=max(0, int(late_seconds or 0)),
        early_out_seconds=max(0, int(early_out_seconds or 0)),
        effective_start_dt=effective_start_dt,
        earliest_checkout_dt=earliest_checkout_dt,
        valid_check_in=valid_check_in,
    )
