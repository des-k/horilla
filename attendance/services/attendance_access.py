from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from attendance.models import AttendanceGeneralSetting
from base.methods import filtersubordinatesemployeemodel
from employee.models import Employee, EmployeeWorkInformation


ADMIN_ATTENDANCE_PERMISSION_CODES: tuple[str, ...] = (
    "attendance.view_attendance",
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



def self_attendance_subject_enabled(*, employee=None, user=None) -> bool:
    """Return True when the employee may appear as their own attendance subject."""
    if employee is None and user is not None:
        employee = getattr(user, "employee_get", None)
    if employee is None:
        return False
    return evaluate_attendance_access(employee=employee, user=user).allowed


def can_access_attendance_scope_views(*, user=None) -> bool:
    if not user or not getattr(user, "is_authenticated", False):
        return False
    if getattr(user, "is_superuser", False):
        return True
    return bool(getattr(user, "employee_get", None))


def get_attendance_subject_employees(request, *, perm_codename: str, base_queryset=None):
    """Return permission-scoped employee queryset for attendance subject selection.

    This separates "can open page" from "who may appear as attendance subject".
    Admin / manager self-inclusion follows attendance general settings, while
    subordinate/global visibility stays intact.
    """
    if base_queryset is None:
        base_queryset = Employee.objects.filter(is_active=True)

    user = getattr(request, "user", None)
    employee = getattr(user, "employee_get", None) if user else None
    can_view_all = bool(
        getattr(user, "is_superuser", False)
        or (user and perm_codename and user.has_perm(perm_codename))
        or is_admin_employee(employee=employee, user=user)
    )

    if can_view_all:
        queryset = base_queryset
        if employee and not self_attendance_subject_enabled(employee=employee, user=user):
            queryset = queryset.exclude(id=employee.id)
        queryset = queryset.order_by("employee_first_name", "employee_last_name", "id")
        default_employee_id = None
        if employee and queryset.filter(id=employee.id).exists():
            default_employee_id = employee.id
        else:
            first = queryset.values_list("id", flat=True).first()
            default_employee_id = first if first is not None else None
        show_employee_filter = queryset.count() > 1
        return queryset, show_employee_filter, True, default_employee_id

    if not employee:
        return base_queryset.none(), False, False, None

    subordinate_ids = list(
        filtersubordinatesemployeemodel(request, base_queryset, perm=perm_codename).values_list("id", flat=True)
    )
    subordinate_ids = [emp_id for emp_id in subordinate_ids if emp_id != employee.id]

    scoped_ids = list(subordinate_ids)
    if self_attendance_subject_enabled(employee=employee, user=user):
        scoped_ids.insert(0, employee.id)

    if not scoped_ids:
        return base_queryset.none(), False, False, None

    queryset = (
        base_queryset.filter(id__in=scoped_ids)
        .order_by("employee_first_name", "employee_last_name", "id")
    )
    # preserve self-first ordering when self is included
    if employee and employee.id in scoped_ids:
        ordered_ids = [employee.id] + [emp_id for emp_id in scoped_ids if emp_id != employee.id]
    else:
        ordered_ids = scoped_ids
    ordering_map = {emp_id: index for index, emp_id in enumerate(ordered_ids)}
    employees = list(queryset)
    employees.sort(key=lambda emp: (ordering_map.get(emp.id, 10**9), (emp.employee_first_name or '').lower(), (emp.employee_last_name or '').lower(), emp.id))
    ordered_ids = [emp.id for emp in employees]
    queryset = base_queryset.filter(id__in=ordered_ids).extra(select={'_scope_order': '0'}) if False else Employee.objects.filter(id__in=ordered_ids)
    # return a query-set-like ordered queryset using Case/When to preserve order
    from django.db.models import Case, IntegerField, Value, When
    preserved = Case(*[When(id=pk, then=Value(pos)) for pos, pk in enumerate(ordered_ids)], output_field=IntegerField())
    queryset = base_queryset.filter(id__in=ordered_ids).annotate(_scope_order=preserved).order_by('_scope_order', 'employee_first_name', 'employee_last_name', 'id')

    default_employee_id = employee.id if employee and employee.id in ordered_ids else (ordered_ids[0] if ordered_ids else None)
    show_employee_filter = len(ordered_ids) > 1
    return queryset, show_employee_filter, False, default_employee_id
