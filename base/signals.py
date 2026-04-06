import logging
import os
import time
from datetime import datetime

from django.apps import apps
from django.conf import settings
from django.contrib import messages
from django.contrib.auth.signals import user_login_failed
from django.db.models import Max, Q
from django.db.models.signals import m2m_changed, post_migrate, post_save
from django.dispatch import receiver
from django.http import Http404
from django.shortcuts import redirect, render
from datetime import time as dt_time
from django.db import DatabaseError, connections, transaction

from base.models import Announcement, PenaltyAccounts
from horilla.methods import get_horilla_model_class


def _table_exists(table_name, using=None):
    alias = using or "default"
    try:
        connection = connections[alias]
        return table_name in connection.introspection.table_names()
    except Exception:
        return False


def _safe_m2m_add(manager, *objs, using=None):
    """Safely add M2M rows during bootstrap/post_migrate.

    During migrate/test bootstrap, through tables may not exist yet or may raise
    a DatabaseError while the outer post_migrate transaction is still open.
    Use an inner atomic block so failures roll back to a savepoint instead of
    poisoning the outer transaction.
    """
    try:
        through_table = manager.through._meta.db_table
    except Exception:
        return

    if not _table_exists(through_table, using=using):
        return

    try:
        with transaction.atomic(using=using):
            manager.add(*objs)
    except DatabaseError:
        return


def _ensure_wfo_wfa_worktypes(company=None, using=None):
    """Ensure WorkType codes WFO/WFA/WFH exist and are attached to companies.

    Fresh installs often create the first user via `createhorillauser` without
    loading fixtures. Our employee forms intentionally filter WorkTypes to
    only WFO/WFA, so if those rows don't exist the dropdown becomes empty.

    We store short codes in DB (WFO/WFA) and render friendly labels in UI.
    Attendance ON_DUTY is handled separately (string mode) and does not need
    to exist as a base.WorkType.
    """

    try:
        from base.models import Company, WorkType

        required_tables = {WorkType._meta.db_table}
        try:
            required_tables.add(WorkType.company_id.through._meta.db_table)
        except Exception:
            pass
        if company is None:
            try:
                required_tables.add(Company._meta.db_table)
            except Exception:
                pass
        if not all(_table_exists(t, using=using) for t in required_tables):
            return

        # Use entire() to avoid any request/company middleware filtering.
        qs = (
            WorkType.objects.entire()
            if hasattr(WorkType.objects, "entire")
            else WorkType.objects
        )
        if using:
            qs = qs.using(using)

        wfo = qs.filter(work_type__iexact="WFO").first()
        if not wfo:
            wfo = WorkType(work_type="WFO")
            wfo.save(using=using)

        wfa = qs.filter(work_type__iexact="WFA").first()
        if not wfa:
            wfa = WorkType(work_type="WFA")
            wfa.save(using=using)

        wfh = qs.filter(work_type__iexact="WFH").first()
        if not wfh:
            wfh = WorkType(work_type="WFH")
            wfh.save(using=using)

        # Attach to companies so it appears under company-filtered UI.
        if company is not None:
            companies = [company]
        else:
            companies = list(Company.objects.using(using).all()) if Company else []

        for c in companies:
            _safe_m2m_add(wfo.company_id, c, using=using)
            _safe_m2m_add(wfa.company_id, c, using=using)
            _safe_m2m_add(wfh.company_id, c, using=using)
    except Exception:
        # DB may not be ready during early migrate phases.
        return


@receiver(post_migrate)
def seed_default_worktypes(sender, **kwargs):
    """Seed WFO/WFA after base migrations."""

    try:
        if getattr(sender, "label", "") != "base":
            return
    except Exception:
        return

    _ensure_wfo_wfa_worktypes(using=kwargs.get("using"))


@receiver(post_save)
def seed_worktypes_on_company_create(sender, instance, created=False, **kwargs):
    """When a new Company is created (e.g. createhorillauser), ensure WFO/WFA exist."""

    try:
        from base.models import Company

        if sender is not Company:
            return
    except Exception:
        return

    if not created:
        return

    _ensure_wfo_wfa_worktypes(company=instance, using=kwargs.get("using"))


@receiver(post_save, sender=PenaltyAccounts)
def create_deduction_cutleave_from_penalty(sender, instance, created, **kwargs):
    """
    This is post save method, used to create deduction and cut available leave days
    """
    # only work when creating
    if created:
        penalty_amount = instance.penalty_amount
        if apps.is_installed("payroll") and penalty_amount:
            Deduction = get_horilla_model_class(app_label="payroll", model="deduction")
            penalty = Deduction()
            if instance.late_early_id:
                penalty.title = f"{instance.late_early_id.get_type_display()} penalty"
                penalty.one_time_date = (
                    instance.late_early_id.attendance_id.attendance_date
                )
            elif instance.leave_request_id:
                penalty.title = f"Leave penalty {instance.leave_request_id.end_date}"
                penalty.one_time_date = instance.leave_request_id.end_date
            else:
                penalty.title = f"Penalty on {datetime.today()}"
                penalty.one_time_date = datetime.today()
            penalty.include_active_employees = False
            penalty.is_fixed = True
            penalty.amount = instance.penalty_amount
            penalty.only_show_under_employee = True
            penalty.save()
            penalty.include_active_employees = False
            penalty.specific_employees.add(instance.employee_id)
            penalty.save()

        if (
            apps.is_installed("leave")
            and instance.leave_type_id
            and instance.minus_leaves
        ):
            available = instance.employee_id.available_leave.filter(
                leave_type_id=instance.leave_type_id
            ).first()
            unit = round(instance.minus_leaves * 2) / 2
            if not instance.deduct_from_carry_forward:
                available.available_days = max(0, (available.available_days - unit))
            else:
                available.carryforward_days = max(
                    0, (available.carryforward_days - unit)
                )

            available.save()


# @receiver(post_migrate)
def clean_work_records(sender, **kwargs):
    if sender.label not in ["attendance"]:
        return
    from attendance.models import WorkRecords

    latest_records = (
        WorkRecords.objects.exclude(work_record_type="DFT")
        .values("employee_id", "date")
        .annotate(latest_id=Max("id"))
    )

    # Delete all but the latest WorkRecord
    deleted_count = 0
    for record in latest_records:
        deleted_count += (
            WorkRecords.objects.filter(
                employee_id=record["employee_id"], date=record["date"]
            )
            .exclude(id=record["latest_id"])
            .delete()[0]
        )


@receiver(m2m_changed, sender=Announcement.employees.through)
def filtered_employees(sender, instance, action, **kwargs):
    """
    filtered employees
    """
    if action not in ["post_add", "post_remove", "post_clear"]:
        return  # Only run after M2M changes
    employee_ids = list(instance.employees.values_list("id", flat=True))
    department_ids = list(instance.department.values_list("id", flat=True))
    job_position_ids = list(instance.job_position.values_list("id", flat=True))

    employees = instance.model_employee.objects.filter(
        Q(id__in=employee_ids)
        | Q(employee_work_info__department_id__in=department_ids)
        | Q(employee_work_info__job_position_id__in=job_position_ids)
    )

    instance.filtered_employees.set(employees)


# Logger setup
logger = logging.getLogger("django.security")

# Create a global dictionary to track login attempts and ban time per session
failed_attempts = {}
ban_time = {}

FAIL2BAN_LOG_ENABLED = os.path.exists(
    "security.log"
)  # Checking that any file is created for the details of the wrong logins.
# The file will be created only if you set the LOGGING in your settings.py


@receiver(user_login_failed)
def log_login_failed(sender, credentials, request, **kwargs):
    """
    To ban the IP of user that enter wrong credentials for multiple times
    you should add this section in your settings.py file. And also it creates the security file for deatils of wrong logins.


    LOGGING = {
        'version': 1,
        'disable_existing_loggers': False,
        'handlers': {
            'security_file': {
                'level': 'WARNING',
                'class': 'logging.FileHandler',
                'filename': '/var/log/django/security.log', # File Path for view the log details.
                                                            # Give the same path to the section FAIL2BAN_LOG_ENABLED = os.path.exists('security.log') in signals.py in Base.
            },
        },
        'loggers': {
            'django.security': {
                'handlers': ['security_file'],
                'level': 'WARNING',
                'propagate': False,
            },
        },
    }

    # This section is for giving the maxtry and bantime

    FAIL2BAN_MAX_RETRY = 3        # Same as maxretry in jail.local
    FAIL2BAN_BAN_TIME = 300       # Same as bantime in jail.local (in seconds)

    """

    # Checking that the file is created or not to initiate the ban functions.
    if not FAIL2BAN_LOG_ENABLED:
        return

    max_attempts = getattr(settings, "FAIL2BAN_MAX_RETRY", 3)
    ban_duration = getattr(settings, "FAIL2BAN_BAN_TIME", 300)

    username = credentials.get("username", "unknown")
    ip = request.META.get("REMOTE_ADDR", "unknown")
    session_key = (
        request.session.session_key or request.session._get_or_create_session_key()
    )

    # Check if currently banned
    if session_key in ban_time and ban_time[session_key] > time.time():
        banned_until = time.strftime("%H:%M", time.localtime(ban_time[session_key]))
        messages.info(
            request, f"You are banned until {banned_until}. Please try again later."
        )
        return redirect("/")

    # If ban expired, reset counters
    if session_key in ban_time and ban_time[session_key] <= time.time():
        del ban_time[session_key]
        if session_key in failed_attempts:
            del failed_attempts[session_key]

    # Initialize tracking if needed
    if session_key not in failed_attempts:
        failed_attempts[session_key] = 0

    failed_attempts[session_key] += 1
    attempts_left = max_attempts - failed_attempts[session_key]

    logger.warning(f"Invalid login attempt for user '{username}' from {ip}")

    if failed_attempts[session_key] >= max_attempts:
        ban_time[session_key] = time.time() + ban_duration
        messages.info(
            request,
            f"You have been banned for {ban_duration // 60} minutes due to multiple failed login attempts.",
        )
        return redirect("/")

    messages.info(
        request,
        f"You have {attempts_left} login attempt(s) left before a temporary ban.",
    )
    return redirect("login")


class Fail2BanMiddleware:
    """
    Middleware to force password change for new employees.
    """

    def __init__(self, get_response):
        self.get_response = get_response

    def __call__(self, request):
        session_key = request.session.session_key
        if not session_key:
            request.session.create()

        # Check ban and enforce it
        if session_key in ban_time and ban_time[session_key] > time.time():
            banned_until = time.strftime("%H:%M", time.localtime(ban_time[session_key]))
            messages.info(
                request, f"You are banned until {banned_until}. Please try again later."
            )
            return render(request, "403.html")

        # If ban expired, clear counters
        if session_key in ban_time and ban_time[session_key] <= time.time():
            del ban_time[session_key]
            if session_key in failed_attempts:
                del failed_attempts[session_key]

        return self.get_response(request)


settings.MIDDLEWARE.append("base.signals.Fail2BanMiddleware")

@receiver(post_migrate, dispatch_uid="base_ensure_default_company_shift_schedule")
def ensure_default_company_and_shift(sender, **kwargs):
    """
    After migrations:
    1) Ensure there is exactly ONE default company.
    2) Ensure the default company has a default shift.
    3) Ensure that shift has 7-day schedules.
    4) (Optional but usually required) Assign default shift to employees who don't have a shift yet.
    """
    # post_migrate runs for every app; only execute for the "base" app
    if getattr(sender, "label", None) != "base":
        return

    using = kwargs.get("using")

    from base.models import Company, EmployeeShift, EmployeeShiftDay, EmployeeShiftSchedule

    # Fetch Employee model safely (in case of import order issues)
    from django.apps import apps
    Employee = apps.get_model("employee", "Employee")

    required_tables = {
        Company._meta.db_table,
        EmployeeShift._meta.db_table,
        EmployeeShiftDay._meta.db_table,
        EmployeeShiftSchedule._meta.db_table,
    }
    employee_table = getattr(getattr(Employee, "_meta", None), "db_table", None)
    if employee_table:
        required_tables.add(employee_table)
    if not all(_table_exists(table_name, using=using) for table_name in required_tables):
        return

    with transaction.atomic(using=using):
        # =========================
        # A) Ensure Default Company
        # =========================
        default_company = Company.objects.using(using).filter(is_default=True).order_by("id").first()

        if not default_company:
            first_company = Company.objects.using(using).order_by("id").first()

            if not first_company:
                # No company exists -> create one (from settings seed if provided)
                seed = getattr(settings, "HORILLA_BOOTSTRAP_COMPANY", None) or {}
                default_company = Company.objects.using(using).create(
                    company=seed.get("company", "Default Company"),
                    hq=seed.get("hq", True),
                    address=seed.get("address", "-"),
                    country=seed.get("country", "-"),
                    state=seed.get("state", "-"),
                    city=seed.get("city", "-"),
                    zip=seed.get("zip", "-"),
                    date_format=seed.get("date_format"),
                    time_format=seed.get("time_format"),
                    is_default=True,
                )
            else:
                # Companies exist but none is default -> pick the first company as default
                first_company.is_default = True
                first_company.save(using=using, update_fields=["is_default"])
                default_company = first_company

        # If multiple defaults exist, keep the oldest (smallest ID) and unset the rest
        Company.objects.using(using).exclude(id=default_company.id).filter(is_default=True).update(is_default=False)

        # =========================
        # B) Ensure Default Shift
        # =========================
        default_shift = None

        # If company already has a default shift, reuse it
        if getattr(default_company, "default_employee_shift_id_id", None):
            default_shift = default_company.default_employee_shift_id
        else:
            # Try to reuse an existing shift already linked to this company
            default_shift = EmployeeShift.objects.using(using).filter(company_id=default_company).order_by("id").first()

            # If no shift exists, create a Default Shift
            if not default_shift:
                default_shift = EmployeeShift.objects.using(using).create(
                    employee_shift="Default Shift",
                    weekly_full_time="40:00",
                    full_time="200:00",
                )
                _safe_m2m_add(default_shift.company_id, default_company, using=using)

            # Set as company's default shift
            default_company.default_employee_shift_id = default_shift
            default_company.save(using=using, update_fields=["default_employee_shift_id"])

        # Ensure shift is linked to the company (safe add)
        try:
            _safe_m2m_add(default_shift.company_id, default_company, using=using)
        except Exception:
            pass

        # =========================
        # C) Ensure 7-Day Schedules
        # =========================
        day_codes = ["monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"]

        for d in day_codes:
            shift_day, _ = EmployeeShiftDay.objects.using(using).get_or_create(day=d)

            # Ensure day is linked to the company (if day has M2M company_id)
            try:
                _safe_m2m_add(shift_day.company_id, default_company, using=using)
            except Exception:
                pass

            # Create schedule if it doesn't exist
            schedule, created = EmployeeShiftSchedule.objects.using(using).get_or_create(
                shift_id=default_shift,
                day=shift_day,
                defaults={
                    "minimum_working_hour": "09:00",
                    "start_time": dt_time(7, 30),
                    "end_time": dt_time(16, 0),
                    "is_auto_punch_out_enabled": False,
                    "auto_punch_out_time": None,
                    # Use STRING values so model.save() can normalize and compute *_secs
                    "cutoff_check_in_offset": "04:30:00",
                    "cutoff_check_out_offset": "07:00:00",
                    # grace_time_id intentionally left NULL -> means no grace
                },
            )

            # Link schedule to company (schedule also has M2M company_id)
            try:
                _safe_m2m_add(schedule.company_id, default_company, using=using)
            except Exception:
                pass

            # If schedule exists but cutoff fields are empty, fill them and resave
            if not created:
                changed = False
                if not getattr(schedule, "cutoff_check_in_offset", None):
                    schedule.cutoff_check_in_offset = "04:30:00"
                    changed = True
                if not getattr(schedule, "cutoff_check_out_offset", None):
                    schedule.cutoff_check_out_offset = "07:00:00"
                    changed = True
                if changed:
                    schedule.save(using=using)

        # =========================
        # D) Assign Default Shift to Employees (if missing)
        # =========================
        # Employees "have schedules" only when they are assigned to a shift.
        # This step ensures employees who don't have a shift get the default shift.
        try:
            qs = Employee.objects.using(using).filter(employee_work_info__shift_id__isnull=True)

            # If you want to limit by company (only if your work_info has company_id):
            # qs = qs.filter(employee_work_info__company_id=default_company)

            qs.update(employee_work_info__shift_id=default_shift)
        except Exception:
            # If your EmployeeWorkInfo relation/field names differ, adjust this block accordingly.
            pass
        
