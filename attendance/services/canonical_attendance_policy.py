from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timedelta, time
from decimal import Decimal, InvalidOperation
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
    checkin_window_end_dt: Optional[datetime]
    checkout_start_dt: Optional[datetime]
    early_checkout_minutes: int
    required_work_seconds: int
    minimum_hour: str
    maximum_late_seconds: int
    maximum_early_out_seconds: int
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


def coerce_non_negative_decimal(value) -> Decimal:
    try:
        parsed = Decimal(str(value or 0))
    except (InvalidOperation, TypeError, ValueError):
        return Decimal("0")
    return parsed if parsed >= 0 else Decimal("0")


def truncate_datetime_to_minute(value: Optional[datetime]) -> Optional[datetime]:
    if value is None:
        return None
    return value.replace(second=0, microsecond=0)


def seconds_to_decimal_minutes(total_seconds) -> Decimal:
    seconds = coerce_non_negative_decimal(total_seconds)
    if seconds == 0:
        return Decimal("0")

    minutes = seconds / Decimal("60")
    if seconds % Decimal("30") == 0:
        minutes = minutes.quantize(Decimal("0.1"))
    elif seconds % Decimal("1") == 0:
        minutes = minutes.quantize(Decimal("0.01"))

    normalized = minutes.normalize()
    if normalized == normalized.to_integral():
        return normalized.quantize(Decimal("1"))
    return normalized


def format_decimal_minutes(value) -> str:
    decimal_value = coerce_non_negative_decimal(value)
    normalized = decimal_value.normalize()
    if normalized == normalized.to_integral():
        normalized = normalized.quantize(Decimal("1"))
    text = format(normalized, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text or "0"


def _half_minimum_seconds(policy: AttendancePolicy) -> int:
    return max(0, int(Decimal(int(policy.required_work_seconds or 0)) / Decimal("2")))


def _cap_early_out_seconds(policy: AttendancePolicy, early_out_seconds: int) -> int:
    capped = max(0, int(early_out_seconds or 0))
    maximum_early_out_seconds = max(0, int(getattr(policy, "maximum_early_out_seconds", 0) or 0))
    if maximum_early_out_seconds > 0 and policy.kind not in {"first_half", "second_half"}:
        capped = min(capped, maximum_early_out_seconds)
    return capped


def _uses_dynamic_policy_end(policy: AttendancePolicy, *, clock_in_type: Optional[str], flex_seconds: Optional[int]) -> bool:
    if policy.kind == "second_half":
        return True
    if policy.kind == "first_half":
        return False
    mode = str(clock_in_type or "after").strip().lower()
    return max(0, int(flex_seconds or 0)) > 0 and mode in {"after", "before_after"}


def _reference_end_dt(
    policy: AttendancePolicy,
    *,
    earliest_checkout_dt: Optional[datetime],
    clock_in_type: Optional[str],
    flex_seconds: Optional[int],
    force_nominal: bool = False,
) -> Optional[datetime]:
    if force_nominal:
        return policy.nominal_policy_end_dt
    if _uses_dynamic_policy_end(policy, clock_in_type=clock_in_type, flex_seconds=flex_seconds):
        return earliest_checkout_dt or policy.nominal_policy_end_dt
    return policy.nominal_policy_end_dt


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


def _resolve_half_day_early_checkout_minutes(schedule, leave_kind: Optional[str]) -> int:
    field_name = None
    if leave_kind == "first_half":
        field_name = "first_half_leave_early_checkout_minutes"
    elif leave_kind == "second_half":
        field_name = "second_half_leave_early_checkout_minutes"
    if not field_name:
        return 0
    try:
        value = getattr(schedule, field_name, 30) if schedule is not None else 30
        return max(0, int(30 if value is None else value))
    except Exception:
        return 30


def _resolve_half_day_window_bounds(
    *,
    leave_kind: Optional[str],
    policy_end_dt: Optional[datetime],
    early_checkout_minutes: int,
) -> tuple[Optional[datetime], Optional[datetime]]:
    if leave_kind not in {"first_half", "second_half"} or policy_end_dt is None:
        return None, None
    checkout_start_dt = policy_end_dt - timedelta(minutes=max(0, int(early_checkout_minutes or 0)))
    checkin_window_end_dt = checkout_start_dt - timedelta(minutes=1)
    return checkin_window_end_dt, checkout_start_dt


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
    checkin_window_end_dt = check_in_cutoff_dt
    checkout_start_dt = None
    early_checkout_minutes = 0
    required_work_seconds = normal_required_seconds
    maximum_late_seconds = max(0, int(Decimal(int(normal_required_seconds or 0)) / Decimal("2")))
    maximum_early_out_seconds = maximum_late_seconds
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
        maximum_early_out_seconds = required_work_seconds
        early_checkout_minutes = _resolve_half_day_early_checkout_minutes(schedule, leave_kind)
        checkin_window_end_dt, checkout_start_dt = _resolve_half_day_window_bounds(
            leave_kind=leave_kind,
            policy_end_dt=nominal_policy_end_dt,
            early_checkout_minutes=early_checkout_minutes,
        )
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
        maximum_early_out_seconds = required_work_seconds
        early_checkout_minutes = _resolve_half_day_early_checkout_minutes(schedule, leave_kind)
        checkin_window_end_dt, checkout_start_dt = _resolve_half_day_window_bounds(
            leave_kind=leave_kind,
            policy_end_dt=nominal_policy_end_dt,
            early_checkout_minutes=early_checkout_minutes,
        )
    elif leave_kind == "full_day":
        required_work_seconds = 0
        maximum_late_seconds = 0
        maximum_early_out_seconds = 0

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
        checkin_window_end_dt=checkin_window_end_dt,
        checkout_start_dt=checkout_start_dt,
        early_checkout_minutes=max(0, int(early_checkout_minutes or 0)),
        required_work_seconds=max(0, int(required_work_seconds or 0)),
        minimum_hour=minimum_hour_value or "00:00",
        maximum_late_seconds=max(0, int(maximum_late_seconds or 0)),
        maximum_early_out_seconds=max(0, int(maximum_early_out_seconds or 0)),
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

    actual_check_in_dt = truncate_datetime_to_minute(actual_check_in_dt)

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

    if policy.kind == "second_half":
        flex_delta = timedelta(seconds=max(0, int(flex_seconds or 0)))
        mode = str(clock_in_type or "after").strip().lower()
        valid_check_in = actual_check_in_dt <= base_dt
        effective_start_dt = actual_check_in_dt if actual_check_in_dt >= base_dt else base_dt
        if mode == "before_after":
            window_start_dt = base_dt - flex_delta
            if actual_check_in_dt < window_start_dt:
                effective_start_dt = window_start_dt
                valid_check_in = False
            elif actual_check_in_dt < base_dt:
                effective_start_dt = actual_check_in_dt
                valid_check_in = True
            else:
                effective_start_dt = actual_check_in_dt
                valid_check_in = True
        earliest_checkout_dt = add_net_work_duration(
            effective_start_dt,
            policy.required_work_seconds,
            break_start_dt=policy.break_start_dt,
            break_end_dt=policy.break_end_dt,
        )
        return effective_start_dt, earliest_checkout_dt, valid_check_in

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
            effective_start_dt = window_end_dt
        else:
            effective_start_dt = actual_check_in_dt
    elif mode == "after":
        window_start_dt = base_dt
        window_end_dt = base_dt + flex_delta
        valid_check_in = window_start_dt <= actual_check_in_dt <= window_end_dt
        if actual_check_in_dt < window_start_dt:
            effective_start_dt = window_start_dt
        elif actual_check_in_dt > window_end_dt:
            effective_start_dt = window_end_dt
        else:
            effective_start_dt = actual_check_in_dt
    else:
        effective_start_dt = base_dt
        valid_check_in = True

    dynamic_earliest_checkout_dt = add_net_work_duration(
        effective_start_dt,
        policy.required_work_seconds,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )
    if _uses_dynamic_policy_end(policy, clock_in_type=clock_in_type, flex_seconds=flex_seconds):
        earliest_checkout_dt = dynamic_earliest_checkout_dt
    else:
        earliest_checkout_dt = policy.nominal_policy_end_dt or dynamic_earliest_checkout_dt
    return effective_start_dt, earliest_checkout_dt, valid_check_in


def compute_worked_seconds(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    final_out_dt: Optional[datetime],
) -> int:
    minute_final_in_dt = truncate_datetime_to_minute(final_in_dt)
    minute_final_out_dt = truncate_datetime_to_minute(final_out_dt)
    return net_duration_excluding_break(
        minute_final_in_dt,
        minute_final_out_dt,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )


def resolve_policy_windows(
    policy: AttendancePolicy,
    *,
    actual_check_in_dt: Optional[datetime],
    clock_in_type: Optional[str],
    flex_seconds: Optional[int],
) -> tuple[Optional[datetime], Optional[datetime], Optional[datetime]]:
    if policy.kind == "second_half":
        _, effective_policy_end_dt, _ = resolve_effective_check_in_and_earliest_checkout(
            policy,
            actual_check_in_dt=actual_check_in_dt,
            clock_in_type=clock_in_type,
            flex_seconds=flex_seconds,
        )
        effective_policy_end_dt = effective_policy_end_dt or policy.nominal_policy_end_dt
        checkin_window_end_dt, checkout_start_dt = _resolve_half_day_window_bounds(
            leave_kind=policy.kind,
            policy_end_dt=effective_policy_end_dt,
            early_checkout_minutes=policy.early_checkout_minutes,
        )
        return effective_policy_end_dt, checkin_window_end_dt, checkout_start_dt
    return policy.nominal_policy_end_dt, policy.checkin_window_end_dt, policy.checkout_start_dt


def compute_mobile_status_metrics(
    policy: AttendancePolicy,
    *,
    actual_check_in_dt: Optional[datetime],
    clock_in_type: Optional[str],
    flex_seconds: Optional[int],
) -> tuple[Optional[datetime], Optional[datetime], bool, Optional[datetime], Optional[datetime]]:
    actual_check_in_dt = truncate_datetime_to_minute(actual_check_in_dt)
    effective_start_dt, dynamic_earliest_checkout_dt, valid_check_in = resolve_effective_check_in_and_earliest_checkout(
        policy,
        actual_check_in_dt=actual_check_in_dt,
        clock_in_type=clock_in_type,
        flex_seconds=flex_seconds,
    )
    effective_policy_end_dt, checkin_window_end_dt, checkout_start_dt = resolve_policy_windows(
        policy,
        actual_check_in_dt=actual_check_in_dt,
        clock_in_type=clock_in_type,
        flex_seconds=flex_seconds,
    )
    if _uses_dynamic_policy_end(policy, clock_in_type=clock_in_type, flex_seconds=flex_seconds):
        display_earliest_checkout_dt = dynamic_earliest_checkout_dt or effective_policy_end_dt
    else:
        display_earliest_checkout_dt = effective_policy_end_dt or policy.nominal_policy_end_dt
    return effective_start_dt, display_earliest_checkout_dt, valid_check_in, checkin_window_end_dt, checkout_start_dt


def _calculate_late_seconds(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    grace_seconds: int,
) -> int:
    final_in_dt = truncate_datetime_to_minute(final_in_dt)
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
    reference_end_dt: Optional[datetime],
    early_out_grace_seconds: int = 0,
) -> int:
    final_in_dt = truncate_datetime_to_minute(final_in_dt)
    final_out_dt = truncate_datetime_to_minute(final_out_dt)
    if final_in_dt is None and final_out_dt is None:
        return 0
    if final_out_dt is None:
        if final_in_dt is not None and reference_end_dt is not None:
            return max(
                0,
                net_duration_excluding_break(
                    final_in_dt,
                    reference_end_dt,
                    break_start_dt=policy.break_start_dt,
                    break_end_dt=policy.break_end_dt,
                ),
            )
        return max(0, int(policy.maximum_early_out_seconds or policy.required_work_seconds or 0))

    if final_in_dt is None:
        reference_end_dt = policy.nominal_policy_end_dt

    early_out_seconds = net_duration_excluding_break(
        final_out_dt,
        reference_end_dt,
        break_start_dt=policy.break_start_dt,
        break_end_dt=policy.break_end_dt,
    )
    early_out_seconds = max(0, int(early_out_seconds or 0) - max(0, int(early_out_grace_seconds or 0)))
    return max(0, int(early_out_seconds))


def compute_attendance_metrics(
    policy: AttendancePolicy,
    *,
    final_in_dt: Optional[datetime],
    final_out_dt: Optional[datetime],
    grace_seconds: int,
    clock_in_type: Optional[str],
    is_presence_only: bool = False,
    early_out_grace_seconds: int = 0,
    use_nominal_policy_end_for_early_out: bool = False,
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

    minute_final_in_dt = truncate_datetime_to_minute(final_in_dt)
    minute_final_out_dt = truncate_datetime_to_minute(final_out_dt)

    effective_start_dt, earliest_checkout_dt, valid_check_in = resolve_effective_check_in_and_earliest_checkout(
        policy,
        actual_check_in_dt=minute_final_in_dt,
        clock_in_type=clock_in_type,
        flex_seconds=grace_seconds,
    )
    reference_end_dt = _reference_end_dt(
        policy,
        earliest_checkout_dt=earliest_checkout_dt,
        clock_in_type=clock_in_type,
        flex_seconds=grace_seconds,
        force_nominal=use_nominal_policy_end_for_early_out,
    )
    # First-half leave has a special split behavior in the existing contract:
    # - when both punches are present, the user may need to fulfill the reduced
    #   minimum working hours from the actual check-in time, so early-out should
    #   compare against the dynamic earliest checkout;
    # - when check-out is missing, tests still expect the nominal half-day end,
    #   not an extended dynamic target.
    if (
        policy.kind == "first_half"
        and minute_final_in_dt is not None
        and minute_final_out_dt is not None
        and earliest_checkout_dt is not None
        and not use_nominal_policy_end_for_early_out
    ):
        reference_end_dt = earliest_checkout_dt

    worked_seconds = compute_worked_seconds(policy, final_in_dt=final_in_dt, final_out_dt=final_out_dt)
    half_minimum_seconds = _half_minimum_seconds(policy)

    if final_in_dt is None and final_out_dt is None:
        if policy.kind in {"first_half", "second_half"}:
            late_seconds = max(0, int(policy.maximum_late_seconds or 0))
            early_out_seconds = 0
        else:
            late_seconds = half_minimum_seconds
            early_out_seconds = half_minimum_seconds
    elif final_in_dt is None and final_out_dt is not None:
        late_seconds = max(0, int(policy.maximum_late_seconds or half_minimum_seconds))
        early_out_seconds = _calculate_early_out_seconds(
            policy,
            final_in_dt=None,
            final_out_dt=minute_final_out_dt,
            reference_end_dt=reference_end_dt,
            early_out_grace_seconds=early_out_grace_seconds,
        )
        if policy.kind not in {"first_half", "second_half"}:
            early_out_seconds = _cap_early_out_seconds(policy, early_out_seconds)
    elif final_in_dt is not None and final_out_dt is None:
        if policy.kind in {"first_half", "second_half"}:
            late_seconds = _calculate_late_seconds(policy, final_in_dt=minute_final_in_dt, grace_seconds=grace_seconds)
            early_out_seconds = _calculate_early_out_seconds(
                policy,
                final_in_dt=minute_final_in_dt,
                final_out_dt=minute_final_out_dt,
                reference_end_dt=reference_end_dt,
                early_out_grace_seconds=early_out_grace_seconds,
            )
        else:
            late_seconds = _calculate_late_seconds(policy, final_in_dt=minute_final_in_dt, grace_seconds=grace_seconds)
            early_out_seconds = _cap_early_out_seconds(policy, max(0, int(policy.maximum_early_out_seconds or half_minimum_seconds)))
    else:
        late_seconds = _calculate_late_seconds(policy, final_in_dt=minute_final_in_dt, grace_seconds=grace_seconds)
        early_out_seconds = _calculate_early_out_seconds(
            policy,
            final_in_dt=final_in_dt,
            final_out_dt=final_out_dt,
            reference_end_dt=reference_end_dt,
            early_out_grace_seconds=early_out_grace_seconds,
        )
        if policy.kind not in {"first_half", "second_half"}:
            early_out_seconds = _cap_early_out_seconds(policy, early_out_seconds)

    return AttendanceMetrics(
        worked_seconds=max(0, int(worked_seconds or 0)),
        late_seconds=max(0, int(late_seconds or 0)),
        early_out_seconds=max(0, int(early_out_seconds or 0)),
        effective_start_dt=effective_start_dt,
        earliest_checkout_dt=earliest_checkout_dt,
        valid_check_in=valid_check_in,
    )
