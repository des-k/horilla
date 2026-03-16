from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from attendance.models import AttendanceGeneralSetting
from employee.models import EmployeeWorkInformation


ADMIN_ATTENDANCE_PERMISSION_CODES: tuple[str, ...] = (
    "attendance.change_attendance",
    "attendance.add_attendance",
)


@dataclass(frozen=True)
class AttendanceAccessDecision:
    allowed: bool
    reason_code: str | None
    message: str | None
    blocked_roles: tuple[str, ...]
    is_reporting_manager: bool
    is_admin: bool
    allow_reporting_manager_attendance: bool
    allow_admin_attendance: bool


@dataclass(frozen=True)
class AttendanceRoleSettings:
    allow_reporting_manager_attendance: bool = False
    allow_admin_attendance: bool = False


def _base_manager():
    manager = AttendanceGeneralSetting.objects
    return manager.entire() if hasattr(manager, "entire") else manager.all()


def get_attendance_general_setting_for_employee(employee):
    company = None
    try:
        company = employee.get_company()
    except Exception:
        try:
            company = employee.employee_work_info.company_id
        except Exception:
            company = None

    queryset = _base_manager()

    if company is not None:
        setting = queryset.filter(company_id=company).first()
        if setting is not None:
            return setting

    setting = queryset.filter(company_id__isnull=True).first()
    if setting is not None:
        return setting

    return queryset.first()


def get_attendance_role_settings(employee) -> AttendanceRoleSettings:
    setting = get_attendance_general_setting_for_employee(employee)
    if setting is None:
        return AttendanceRoleSettings()
    return AttendanceRoleSettings(
        allow_reporting_manager_attendance=bool(
            getattr(setting, "allow_reporting_manager_attendance", False)
        ),
        allow_admin_attendance=bool(
            getattr(setting, "allow_admin_attendance", False)
        ),
    )


def is_reporting_manager_employee(employee) -> bool:
    if employee is None:
        return False
    try:
        return (
            EmployeeWorkInformation.objects.filter(reporting_manager_id=employee)
            .only("id")
            .exists()
        )
    except Exception:
        return False


def _user_has_any_perm(user, permission_codes: Iterable[str]) -> bool:
    if not user:
        return False
    try:
        if getattr(user, "is_superuser", False):
            return True
        for perm in permission_codes:
            if user.has_perm(perm):
                return True
    except Exception:
        return False
    return False


def is_admin_employee(*, employee=None, user=None) -> bool:
    user_obj = user
    if user_obj is None and employee is not None:
        user_obj = getattr(employee, "employee_user_id", None)
    return _user_has_any_perm(user_obj, ADMIN_ATTENDANCE_PERMISSION_CODES)


def build_attendance_access_decision(
    *,
    is_reporting_manager: bool,
    is_admin: bool,
    allow_reporting_manager_attendance: bool,
    allow_admin_attendance: bool,
) -> AttendanceAccessDecision:
    blocked_roles: list[str] = []

    if is_reporting_manager and not allow_reporting_manager_attendance:
        blocked_roles.append("REPORTING_MANAGER")

    if is_admin and not allow_admin_attendance:
        blocked_roles.append("ADMIN")

    if not blocked_roles:
        return AttendanceAccessDecision(
            allowed=True,
            reason_code=None,
            message=None,
            blocked_roles=(),
            is_reporting_manager=is_reporting_manager,
            is_admin=is_admin,
            allow_reporting_manager_attendance=allow_reporting_manager_attendance,
            allow_admin_attendance=allow_admin_attendance,
        )

    if blocked_roles == ["REPORTING_MANAGER"]:
        reason_code = "REPORTING_MANAGER"
        message = "Attendance is disabled for reporting manager employees."
    elif blocked_roles == ["ADMIN"]:
        reason_code = "ADMIN"
        message = "Attendance is disabled for admin users."
    else:
        reason_code = "MULTIPLE_PRIVILEGED_ROLES"
        message = (
            "Attendance is disabled because one or more privileged-role attendance settings "
            "for this employee are disabled."
        )

    return AttendanceAccessDecision(
        allowed=False,
        reason_code=reason_code,
        message=message,
        blocked_roles=tuple(blocked_roles),
        is_reporting_manager=is_reporting_manager,
        is_admin=is_admin,
        allow_reporting_manager_attendance=allow_reporting_manager_attendance,
        allow_admin_attendance=allow_admin_attendance,
    )


def evaluate_attendance_access(*, employee=None, user=None) -> AttendanceAccessDecision:
    settings = get_attendance_role_settings(employee)
    return build_attendance_access_decision(
        is_reporting_manager=is_reporting_manager_employee(employee),
        is_admin=is_admin_employee(employee=employee, user=user),
        allow_reporting_manager_attendance=settings.allow_reporting_manager_attendance,
        allow_admin_attendance=settings.allow_admin_attendance,
    )
