from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from attendance.models import (
    AttendanceWorkMode,
    GraceClockInType,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)


@dataclass(frozen=True)
class RequestBlueprint:
    code: str
    label: str
    mode: str | None
    scope: str | None
    status: str | None
    request_source: str
    mobile_expected: bool | None
    notes: str = ""


@dataclass(frozen=True)
class LeaveBlueprint:
    code: str
    breakdown: str | None
    status: str | None
    effective_session: str
    notes: str = ""


@dataclass(frozen=True)
class SourceBlueprint:
    code: str
    label: str
    in_sources: tuple[str, ...]
    out_sources: tuple[str, ...]
    duplicate_in_attempt: bool = False
    duplicate_out_attempt: bool = False
    multi_tap: bool = False
    notes: str = ""


@dataclass(frozen=True)
class GraceBlueprint:
    code: str
    clock_in_type: str
    label: str


@dataclass(frozen=True)
class ScenarioFamily:
    scenario_id: str
    scheduled_mode: str
    request_case: RequestBlueprint
    leave_case: LeaveBlueprint
    source_case: SourceBlueprint
    grace_case: GraceBlueprint
    expected_assertion_bundle: str


@dataclass(frozen=True)
class PriorityScenario:
    scenario_id: str
    family: ScenarioFamily
    expectation_summary: str
    must_verify_modules: tuple[str, ...]


REQUEST_BLUEPRINTS: tuple[RequestBlueprint, ...] = (
    RequestBlueprint("REQ_NONE", "No request", None, None, None, "schedule", None),
    RequestBlueprint(
        "WFA_PENDING",
        "WFA pending",
        AttendanceWorkMode.WFA,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.PENDING,
        "request",
        False,
        "Pending request must not unlock mobile punch when approval is mandatory.",
    ),
    RequestBlueprint(
        "WFA_WAITING",
        "WFA waiting for approval",
        AttendanceWorkMode.WFA,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        "request",
        False,
    ),
    RequestBlueprint(
        "WFA_APPROVED",
        "WFA approved",
        AttendanceWorkMode.WFA,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.APPROVED,
        "request",
        True,
    ),
    RequestBlueprint(
        "WFA_REJECTED",
        "WFA rejected",
        AttendanceWorkMode.WFA,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.REJECTED,
        "request",
        False,
    ),
    RequestBlueprint(
        "OD_FULL_PENDING",
        "On Duty full pending",
        AttendanceWorkMode.ON_DUTY,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.PENDING,
        "request",
        False,
    ),
    RequestBlueprint(
        "OD_FULL_APPROVED",
        "On Duty full approved",
        AttendanceWorkMode.ON_DUTY,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.APPROVED,
        "request",
        True,
    ),
    RequestBlueprint(
        "OD_FULL_REVOKED",
        "On Duty full revoked",
        AttendanceWorkMode.ON_DUTY,
        WorkModeRequestScope.FULL,
        WorkModeRequestStatus.REVOKED,
        "request",
        False,
    ),
    RequestBlueprint(
        "OD_IN_APPROVED",
        "On Duty IN approved",
        AttendanceWorkMode.ON_DUTY,
        WorkModeRequestScope.IN,
        WorkModeRequestStatus.APPROVED,
        "request",
        True,
        "Use for first-half / morning allowance scenarios.",
    ),
    RequestBlueprint(
        "OD_OUT_APPROVED",
        "On Duty OUT approved",
        AttendanceWorkMode.ON_DUTY,
        WorkModeRequestScope.OUT,
        WorkModeRequestStatus.APPROVED,
        "request",
        True,
        "Use for second-half / afternoon allowance scenarios.",
    ),
)


LEAVE_BLUEPRINTS: tuple[LeaveBlueprint, ...] = (
    LeaveBlueprint("LEAVE_NONE", None, None, "full_day_working"),
    LeaveBlueprint("LEAVE_FULL_APPROVED", "full_day", "approved", "off_day"),
    LeaveBlueprint("LEAVE_FIRST_HALF_APPROVED", "first_half", "approved", "second_session_only"),
    LeaveBlueprint("LEAVE_SECOND_HALF_APPROVED", "second_half", "approved", "first_session_only"),
    LeaveBlueprint("LEAVE_PENDING_FULL", "full_day", "pending", "full_day_working"),
)


SOURCE_BLUEPRINTS: tuple[SourceBlueprint, ...] = (
    SourceBlueprint("NO_PUNCH", "No punch", (), (), notes="Missing check-in/check-out / correction scenarios."),
    SourceBlueprint("BIO_BIO", "Biometric IN / Biometric OUT", ("biometric",), ("biometric",)),
    SourceBlueprint("MOB_MOB", "Mobile IN / Mobile OUT", ("mobile",), ("mobile",)),
    SourceBlueprint("BIO_MOB", "Biometric IN / Mobile OUT", ("biometric",), ("mobile",)),
    SourceBlueprint("MOB_BIO", "Mobile IN / Biometric OUT", ("mobile",), ("biometric",)),
    SourceBlueprint(
        "BIO_MULTI_IN",
        "Biometric multi-tap IN",
        ("biometric", "biometric"),
        ("biometric",),
        duplicate_in_attempt=True,
        multi_tap=True,
        notes="Earliest valid biometric IN should win.",
    ),
    SourceBlueprint(
        "BIO_MULTI_OUT",
        "Biometric multi-tap OUT",
        ("biometric",),
        ("biometric", "biometric"),
        duplicate_out_attempt=True,
        multi_tap=True,
        notes="Latest valid biometric OUT should win.",
    ),
    SourceBlueprint(
        "BIO_MULTI_BOTH",
        "Biometric multi-tap IN and OUT",
        ("biometric", "biometric"),
        ("biometric", "biometric"),
        duplicate_in_attempt=True,
        duplicate_out_attempt=True,
        multi_tap=True,
    ),
    SourceBlueprint(
        "MOB_MULTI_IN_ATTEMPT",
        "Mobile duplicate IN attempt",
        ("mobile", "mobile"),
        ("mobile",),
        duplicate_in_attempt=True,
        notes="Mobile UI may block, but backend must still reject duplicate IN safely.",
    ),
    SourceBlueprint(
        "MOB_MULTI_OUT_ATTEMPT",
        "Mobile duplicate OUT attempt",
        ("mobile",),
        ("mobile", "mobile"),
        duplicate_out_attempt=True,
        notes="Use with can_update_clock_out cases and audit trail checks.",
    ),
    SourceBlueprint(
        "MULTI_MIXED",
        "Mixed biometric and mobile raw punches",
        ("biometric", "mobile", "biometric"),
        ("mobile", "biometric", "mobile"),
        duplicate_in_attempt=True,
        duplicate_out_attempt=True,
        multi_tap=True,
        notes="Selection engine should still pick earliest IN / latest OUT unless request override wins.",
    ),
)


GRACE_BLUEPRINTS: tuple[GraceBlueprint, ...] = (
    GraceBlueprint("GRACE_AFTER", GraceClockInType.AFTER, "Flex In +Xm"),
    GraceBlueprint("GRACE_BEFORE_AFTER", GraceClockInType.BEFORE_AND_AFTER, "Flex In ±Xm"),
)


PRIORITY_ASSERTION_BUNDLES = {
    "approval_gate",
    "source_selection",
    "leave_half_day_window",
    "grace_late_early",
    "sync_all_modules",
    "attendance_request_override",
    "duplicate_punch_protection",
}


def iter_scenario_families() -> Iterable[ScenarioFamily]:
    for scheduled_mode in (
        AttendanceWorkMode.WFO,
        AttendanceWorkMode.WFA,
        AttendanceWorkMode.ON_DUTY,
    ):
        for request_case in REQUEST_BLUEPRINTS:
            for leave_case in LEAVE_BLUEPRINTS:
                for source_case in SOURCE_BLUEPRINTS:
                    for grace_case in GRACE_BLUEPRINTS:
                        assertion_bundle = _pick_assertion_bundle(
                            scheduled_mode=scheduled_mode,
                            request_case=request_case,
                            leave_case=leave_case,
                            source_case=source_case,
                            grace_case=grace_case,
                        )
                        scenario_id = "/".join(
                            [
                                scheduled_mode.upper(),
                                request_case.code,
                                leave_case.code,
                                source_case.code,
                                grace_case.code,
                            ]
                        )
                        yield ScenarioFamily(
                            scenario_id=scenario_id,
                            scheduled_mode=scheduled_mode,
                            request_case=request_case,
                            leave_case=leave_case,
                            source_case=source_case,
                            grace_case=grace_case,
                            expected_assertion_bundle=assertion_bundle,
                        )


def build_priority_scenarios() -> tuple[PriorityScenario, ...]:
    by_id = {family.scenario_id: family for family in iter_scenario_families()}
    wanted = (
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_NONE/BIO_BIO/GRACE_AFTER",
            "Baseline WFO via biometric only; no late/early anomalies.",
            ("Attendances", "Attendance Activities", "Punching History"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_NONE/MOB_MOB/GRACE_AFTER",
            "Mobile WFO should be rejected or ignored by backend policy.",
            ("API status", "Punching History", "Attendances"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/WFA_APPROVED/LEAVE_NONE/MOB_MOB/GRACE_AFTER",
            "Approved WFA request must unlock mobile IN/OUT.",
            ("Work Type Request", "Attendances", "Punching History"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/OD_FULL_APPROVED/LEAVE_NONE/MOB_MOB/GRACE_AFTER",
            "Approved On Duty full request must unlock mobile IN/OUT.",
            ("Work Type Request", "Attendances", "Punching History"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_FIRST_HALF_APPROVED/BIO_BIO/GRACE_AFTER",
            "First-half leave should move the effective check-in reference to the second session.",
            ("Leave", "Attendances", "Monthly recap"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_SECOND_HALF_APPROVED/BIO_BIO/GRACE_AFTER",
            "Second-half leave should move the effective check-out reference to the first session.",
            ("Leave", "Attendances", "Monthly recap"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_NONE/BIO_MULTI_BOTH/GRACE_AFTER",
            "Biometric multi-tap should keep only earliest IN and latest OUT as final winners.",
            ("Punching History", "Attendances"),
        ),
        (
            f"{AttendanceWorkMode.WFA.upper()}/REQ_NONE/LEAVE_NONE/MOB_MULTI_IN_ATTEMPT/GRACE_AFTER",
            "Duplicate mobile IN attempts should be blocked by UI and still safe on backend.",
            ("Mobile status", "Punching History", "Attendances"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_NONE/MULTI_MIXED/GRACE_BEFORE_AFTER",
            "Mixed raw punches under Flex In ± must still pick correct winners and grace interpretation.",
            ("Attendances", "Monthly recap", "Punching History"),
        ),
        (
            f"{AttendanceWorkMode.WFO.upper()}/REQ_NONE/LEAVE_NONE/BIO_BIO/GRACE_BEFORE_AFTER",
            "Flex In ± should credit early IN against early OUT in recap and list views.",
            ("Monthly recap", "Attendances", "API status"),
        ),
    )
    return tuple(
        PriorityScenario(
            scenario_id=scenario_id,
            family=by_id[scenario_id],
            expectation_summary=summary,
            must_verify_modules=modules,
        )
        for scenario_id, summary, modules in wanted
    )


def _pick_assertion_bundle(*, scheduled_mode, request_case, leave_case, source_case, grace_case) -> str:
    if leave_case.breakdown in {"first_half", "second_half"}:
        return "leave_half_day_window"
    if request_case.request_source == "request" and request_case.status in {
        WorkModeRequestStatus.PENDING,
        WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        WorkModeRequestStatus.APPROVED,
        WorkModeRequestStatus.REJECTED,
        WorkModeRequestStatus.REVOKED,
    }:
        return "approval_gate"
    if source_case.duplicate_in_attempt or source_case.duplicate_out_attempt:
        return "duplicate_punch_protection"
    if grace_case.clock_in_type == GraceClockInType.BEFORE_AND_AFTER:
        return "grace_late_early"
    if source_case.multi_tap:
        return "source_selection"
    return "sync_all_modules"
