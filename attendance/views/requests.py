"""
requests.py

This module is used to register the endpoints to the attendance requests
"""

import copy
import logging
import json
from datetime import date, datetime, time, timedelta
from urllib.parse import parse_qs

from django.contrib import messages
from django import forms
from django.core.exceptions import ValidationError
from django.db import transaction
from django.db.models import ProtectedError, Q, Count
from django.http import HttpResponse, HttpResponseRedirect, JsonResponse, HttpResponseForbidden
from django.shortcuts import redirect, render
from django.template.loader import render_to_string
from django.urls import reverse
from django.utils import timezone
from django.utils.translation import gettext_lazy as _

from attendance.filters import AttendanceFilters, AttendanceRequestReGroup
from attendance.forms import (
    AttendanceRequestForm,
    BatchAttendanceForm,
    BulkAttendanceRequestForm,
    NewRequestForm,
)
from attendance.methods.utils import (
    get_diff_dict,
    get_employee_last_name,
    paginator_qry,
)
from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceRequestActionType,
    AttendanceRequestFile,
    BatchAttendance,
)
import attendance.views.clock_in_out as cio
from attendance.services.activity_sync import (
    get_requested_sessions,
    mark_approved_request_channels,
    sync_single_session_activity,
    validate_requested_data_with_windows,
)
from attendance.services.punching_history import (
    capture_request_restore_snapshot,
    clear_raw_links_for_request_override,
    reconcile_attendance_punches,
    restore_raw_state_after_request,
)
from attendance.services.reconciliation import recompute_attendance
from attendance.services.request_override_recompute import clear_request_override_and_recompute
from attendance.services.request_audit import log_request_action
from attendance.services.attachment_validation import validate_uploaded_files
from attendance.services.attendance_request_access import (
    iter_request_attachments,
    hard_delete_request_attachment,
    user_can_approve_request,
    user_can_delete_attachment,
    user_can_manage_request,
    user_can_view_request,
)
from attendance.services.attendance_correction_scope_rules import load_requested_data
from attendance.services.attendance_request_presentation import build_attendance_request_time_surface
from base.methods import (
    choosesubordinates,
    closest_numbers,
    eval_validate,
    filtersubordinates,
    filtersubordinatesemployeemodel,
    get_key_instances,
    is_reportingmanager,
)
from base.models import EmployeeShift, EmployeeShiftDay, EmployeeShiftSchedule
from employee.models import Employee
from notifications.domain_notifications import (
    send_attendance_request_notification,
)
from horilla.decorators import (
    hx_request_required,
    login_required,
    manager_can_enter,
    permission_required,
)
from notifications.signals import notify

logger = logging.getLogger(__name__)



def _parse_history_month_range(raw_value):
    raw = (raw_value or "").strip()
    parsed_date = None
    if raw:
        for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%Y/%m/%d"):
            try:
                parsed_date = datetime.strptime(raw, fmt).date()
                break
            except Exception:
                parsed_date = None
    if parsed_date is not None:
        month_start = parsed_date.replace(day=1)
    elif raw:
        month_start = None
        for fmt in ("%Y-%m", "%m-%Y", "%m/%Y", "%Y/%m"):
            try:
                parsed = datetime.strptime(raw, fmt)
                month_start = date(parsed.year, parsed.month, 1)
                break
            except Exception:
                month_start = None
        if month_start is None:
            month_start = timezone.localdate().replace(day=1)
    else:
        month_start = timezone.localdate().replace(day=1)

    if month_start.month == 12:
        next_month = date(month_start.year + 1, 1, 1)
    else:
        next_month = date(month_start.year, month_start.month + 1, 1)
    month_end = next_month - timedelta(days=1)
    return month_start, month_end, month_start.strftime("%Y-%m")


# -----------------------------------------------------------------------------
# Single-session helpers
# -----------------------------------------------------------------------------
def _normalize_none(value):
    """Normalize common "empty" representations to Python None."""
    if value is None:
        return None
    if isinstance(value, str) and value.strip() in ("", "None", "null", "NULL"):
        return None
    return value


def _normalize_requested_data(requested_data: dict) -> dict:
    """Ensure requested_data from JSON can be safely used in queryset.update().

    Note: requested_data may contain non-model keys (e.g., "__meta").
    We *must* filter to model fields only before using queryset.update().
    """
    if not requested_data:
        return requested_data

    allowed = (
        "attendance_date",
        "attendance_clock_in_date",
        "attendance_clock_out_date",
        "attendance_clock_in",
        "attendance_clock_out",
        "attendance_worked_hour",
        "minimum_hour",
        "batch_attendance_id",
        "shift_id",
        "work_type_id",
    )
    cleaned = {k: requested_data.get(k) for k in allowed if k in requested_data}

    for key in allowed:
        if key in cleaned:
            cleaned[key] = _normalize_none(cleaned[key])

    return cleaned


def _get_shift_schedule(shift, day):
    """Schedule-level lookup for grace time & cutoffs."""
    return EmployeeShiftSchedule.objects.filter(shift_id=shift, day=day).first()


def _build_shift_info_map(attendances):
    """Build shift display info for a list of Attendance objects.

    Output: {attendance_id: {name, start, end, flexi_minutes}}
    """
    info = {}
    for att in attendances or []:
        try:
            shift = getattr(att, "shift_id", None)
            if not shift:
                info[getattr(att, "id", None)] = None
                continue

            day = getattr(att, "attendance_day", None)
            schedule = None
            try:
                schedule = _get_shift_schedule(shift, day) if day else None
            except Exception:
                schedule = None

            # Flexi In (minutes) resolves like clock_in_out: schedule.grace_time_id > shift.grace_time_id > default
            flexi_minutes = 0
            try:
                grace = cio._resolve_grace_time(schedule, shift)
                secs = int(getattr(grace, "allowed_time_in_secs", 0) or 0) if grace else 0
                flexi_minutes = int(secs // 60)
            except Exception:
                flexi_minutes = 0

            start_time = getattr(schedule, "start_time", None) if schedule else None
            end_time = getattr(schedule, "end_time", None) if schedule else None
            start_s = start_time.strftime("%H:%M") if start_time else "-"
            end_s = end_time.strftime("%H:%M") if end_time else "-"

            info[getattr(att, "id", None)] = {
                "name": str(shift),
                "start": start_s,
                "end": end_s,
                "flexi_minutes": flexi_minutes,
            }
        except Exception:
            # Be defensive: never break the page because of shift metadata.
            info[getattr(att, "id", None)] = None
    return info

def _ensure_single_session_activity(attendance: Attendance, prev_attendance_date=None) -> AttendanceActivity:
    """Delegate single-session activity sync to the centralized null-safe helper."""

    return sync_single_session_activity(
        attendance,
        prev_attendance_date=prev_attendance_date,
    )


def _mark_approved_request_channels(attendance: Attendance) -> Attendance:
    """Persist approved/correction request channels on final attendance."""

    return mark_approved_request_channels(attendance)


def _apply_request_override_snapshot(attendance: Attendance, *, include_in: bool, include_out: bool):
    capture_request_restore_snapshot(attendance, include_in=include_in, include_out=include_out)


def _detach_request_overridden_raw_links(attendance: Attendance, *, include_in: bool, include_out: bool):
    clear_raw_links_for_request_override(attendance, include_in=include_in, include_out=include_out)
    fields = []
    if include_in:
        fields.extend([
            "attendance_clock_in_punch",
            "attendance_clock_in_image",
            "attendance_clock_in_location",
        ])
    if include_out:
        fields.extend([
            "attendance_clock_out_punch",
            "attendance_clock_out_image",
            "attendance_clock_out_location",
        ])
    if fields:
        attendance.save(update_fields=fields)


def _restore_request_back_to_raw(attendance: Attendance, *, include_in: bool, include_out: bool, prev_attendance_date=None):
    return restore_raw_state_after_request(
        attendance,
        include_in=include_in,
        include_out=include_out,
    )


def _log_attendance_request_action(attendance: Attendance, request, *, action_type: str, old_status: str = None, new_status: str = None, remark: str = None):
    try:
        log_request_action(
            attendance=attendance,
            actor=getattr(request.user, 'employee_get', None),
            action_type=action_type,
            old_status=old_status,
            new_status=new_status,
            remark=remark,
        )
    except Exception as exc:
        logger.exception(
            "Failed to log attendance request action for attendance=%s action=%s",
            getattr(attendance, "id", None),
            action_type,
        )
        raise


@login_required
def request_attendance(request):
    """
    This method is used to render template to register new attendance for a normal user
    """
    if request.GET.get("previous_url"):
        form = AttendanceRequestForm(initial=request.GET.dict())
    else:
        form = AttendanceRequestForm()
    if request.method == "POST":
        form = AttendanceRequestForm(request.POST)
        if form.is_valid():
            instance = form.save(commit=False)
            instance.save()
    return render(request, "requests/attendance/form.html", {"form": form})


@login_required
def _legacy_request_attendance_view_deprecated(request):
    """Deprecated duplicate implementation kept only for reference during cleanup.

    The active request-attendance page is the later ``request_attendance_view``
    definition in this module. This older block is intentionally renamed so the
    runtime uses exactly one canonical implementation while preserving git-blame
    friendly history during staged cleanup.
    """
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = bool(getattr(request.user, "has_perm", lambda _p: False)("attendance.change_attendance"))

    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    search = (request.GET.get("search") or "").strip()
    status_my = (request.GET.get("status_my") or "all").strip().lower()
    allowed_status_my = {"all", "waiting", "approved", "rejected", "revoked", "canceled", "cancel"}
    if status_my not in allowed_status_my:
        status_my = "all"

    approval_subtab = (request.GET.get("approval_subtab") or "active").strip().lower()
    if approval_subtab not in {"active", "history"}:
        approval_subtab = "active"
    show_approval_tab = any(
        key in request.GET
        for key in ("tab", "approval_subtab", "page_app", "page_app_hist", "history_month", "history_status", "history_employee_id")
    ) or (request.GET.get("tab") or "").strip().lower() == "approvals"

    history_status = (request.GET.get("history_status") or "all").strip().lower()
    allowed_history_status = {"all", "waiting", "approved", "rejected", "revoked", "canceled", "cancel"}
    if history_status not in allowed_history_status:
        history_status = "all"
    history_employee_id = (request.GET.get("history_employee_id") or "").strip()
    history_month_start, history_month_end, history_month = _parse_history_month_range(
        request.GET.get("history_month") or request.GET.get("history_date")
    )
    my_month_start, my_month_end, my_month = _parse_history_month_range(
        request.GET.get("my_month")
    )

    request_history_filter = (
        Q(is_validate_request=True)
        | Q(is_validate_request_approved=True)
        | Q(action_type__in=[
            AttendanceRequestActionType.APPROVED,
            AttendanceRequestActionType.REJECTED,
            AttendanceRequestActionType.CANCELED,
            AttendanceRequestActionType.REVOKED,
        ])
        | Q(request_type__in=["create_request", "cancel_request", "reject_request", "revoke_request"])
    )

    approvals_qs = Attendance.objects.filter(is_validate_request=True)
    if is_reportingmanager(request) and not (has_global_perm or is_super):
        approvals_qs = filtersubordinates(
            request=request,
            perm="attendance.change_attendance",
            queryset=approvals_qs,
        )
    elif not (has_global_perm or is_super):
        approvals_qs = Attendance.objects.none()
    approvals_qs = approvals_qs.exclude(employee_id__employee_user_id=request.user).distinct()

    my_qs = Attendance.objects.filter(employee_id__employee_user_id=request.user).filter(request_history_filter).distinct()
    my_qs = my_qs.filter(attendance_date__range=(my_month_start, my_month_end))
    if status_my == "waiting":
        my_qs = my_qs.filter(is_validate_request=True)
    elif status_my == "approved":
        my_qs = (
            my_qs.filter(Q(is_validate_request_approved=True) | Q(attendance_validated=True))
            .exclude(is_validate_request=True)
            .exclude(request_type__in=["cancel_request", "reject_request", "revoke_request"])
        )
    elif status_my == "rejected":
        my_qs = my_qs.filter(request_type="reject_request")
    elif status_my == "revoked":
        my_qs = my_qs.filter(request_type="revoke_request")
    elif status_my in ("canceled", "cancel"):
        my_qs = my_qs.filter(request_type="cancel_request")

    history_base_qs = Attendance.objects.filter(request_history_filter).exclude(employee_id__employee_user_id=request.user).distinct()
    if is_reportingmanager(request) and not (has_global_perm or is_super):
        history_base_qs = filtersubordinates(
            request=request,
            perm="attendance.change_attendance",
            queryset=history_base_qs,
        )
    elif not (has_global_perm or is_super):
        history_base_qs = Attendance.objects.none()

    history_qs = history_base_qs.filter(attendance_date__range=(history_month_start, history_month_end))
    if history_employee_id:
        history_qs = history_qs.filter(employee_id_id=history_employee_id)
    if history_status == "waiting":
        history_qs = history_qs.filter(is_validate_request=True)
    elif history_status == "approved":
        history_qs = history_qs.filter(Q(is_validate_request_approved=True) | Q(attendance_validated=True)).exclude(is_validate_request=True)
    elif history_status == "rejected":
        history_qs = history_qs.filter(Q(request_type="reject_request") | Q(action_type=AttendanceRequestActionType.REJECTED))
    elif history_status == "revoked":
        history_qs = history_qs.filter(Q(request_type="revoke_request") | Q(action_type=AttendanceRequestActionType.REVOKED))
    elif history_status in ("canceled", "cancel"):
        history_qs = history_qs.filter(Q(request_type="cancel_request") | Q(action_type=AttendanceRequestActionType.CANCELED))
    else:
        history_qs = history_qs.exclude(is_validate_request=True)

    if search:
        parsed_date = None
        for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%Y/%m/%d"):
            try:
                parsed_date = datetime.strptime(search, fmt).date()
                break
            except Exception:
                parsed_date = None
        if parsed_date:
            approvals_qs = approvals_qs.filter(attendance_date=parsed_date)
            my_qs = my_qs.filter(attendance_date=parsed_date)
            history_qs = history_qs.filter(attendance_date=parsed_date)
        else:
            approvals_qs = approvals_qs.filter(
                Q(employee_id__employee_first_name__icontains=search)
                | Q(employee_id__employee_last_name__icontains=search)
                | Q(employee_id__badge_id__icontains=search)
                | Q(request_description__icontains=search)
            )
            my_qs = my_qs.filter(
                Q(request_description__icontains=search)
                | Q(request_type__icontains=search)
            )
            history_qs = history_qs.filter(
                Q(employee_id__employee_first_name__icontains=search)
                | Q(employee_id__employee_last_name__icontains=search)
                | Q(employee_id__badge_id__icontains=search)
                | Q(request_description__icontains=search)
            )

    page_my = request.GET.get("page_my")
    page_app = request.GET.get("page_app")
    page_app_hist = request.GET.get("page_app_hist")

    my_requests = paginator_qry(
        my_qs.select_related("employee_id", "action_by", "shift_id", "work_type_id").order_by("-id"),
        page_my,
    )
    approvals = paginator_qry(
        approvals_qs.select_related("employee_id", "action_by", "shift_id", "work_type_id").order_by("-id"),
        page_app,
    )
    approval_history = paginator_qry(
        history_qs.select_related("employee_id", "action_by", "shift_id", "work_type_id").order_by("-id"),
        page_app_hist,
    )

    try:
        my_attach_counts = {obj.id: len(list(iter_request_attachments(obj))) for obj in getattr(my_requests, "object_list", [])}
        app_attach_counts = {obj.id: len(list(iter_request_attachments(obj))) for obj in getattr(approvals, "object_list", [])}
        history_attach_counts = {obj.id: len(list(iter_request_attachments(obj))) for obj in getattr(approval_history, "object_list", [])}
    except Exception:
        my_attach_counts = {}
        app_attach_counts = {}
        history_attach_counts = {}

    try:
        my_shift_info = _build_shift_info_map(list(getattr(my_requests, 'object_list', []) or []))
        app_shift_info = _build_shift_info_map(list(getattr(approvals, 'object_list', []) or []))
        history_shift_info = _build_shift_info_map(list(getattr(approval_history, 'object_list', []) or []))
    except Exception:
        my_shift_info = {}
        app_shift_info = {}
        history_shift_info = {}

    try:
        history_time_surface = {
            obj.id: build_attendance_request_time_surface(obj)
            for obj in list(getattr(approval_history, "object_list", []) or [])
        }
    except Exception:
        history_time_surface = {}

    can_approve = bool(request.user.has_perm("attendance.change_attendance") or is_reportingmanager(request))
    status_my_options = [
        ("all", _("All")),
        ("waiting", _("Waiting")),
        ("approved", _("Approved")),
        ("rejected", _("Rejected")),
        ("revoked", _("Revoked")),
        ("canceled", _("Canceled")),
    ]
    history_status_options = [
        ("all", _("All")),
        ("approved", _("Approved")),
        ("rejected", _("Rejected")),
        ("revoked", _("Revoked")),
        ("canceled", _("Canceled")),
    ]

    try:
        history_employees = Employee.objects.all()
        if not request.user.has_perm("attendance.change_attendance"):
            history_employees = filtersubordinatesemployeemodel(
                request,
                history_employees,
                perm="attendance.change_attendance",
            )
        if employee is not None:
            history_employees = history_employees.exclude(id=employee.id)
        history_employees = history_employees.order_by("employee_first_name", "employee_last_name").distinct()
    except Exception:
        history_employees = Employee.objects.none()

    try:
        q_my = request.GET.copy(); q_my.pop("page_my", None); pd_my = q_my.urlencode()
        q_app = request.GET.copy(); q_app.pop("page_app", None); pd_app = q_app.urlencode()
        q_app_hist = request.GET.copy(); q_app_hist.pop("page_app_hist", None); pd_app_hist = q_app_hist.urlencode()
    except Exception:
        pd_my = pd_app = pd_app_hist = ""

    return render(
        request,
        "attendance/attendance_requests/view.html",
        {
            "my_requests": my_requests,
            "approvals": approvals,
            "approval_history": approval_history,
            "can_approve": can_approve,
            "search": search,
            "status_my": status_my,
            "status_my_options": status_my_options,
            "history_status": history_status,
            "history_status_options": history_status_options,
            "history_employee_id": history_employee_id,
            "history_employees": history_employees,
            "history_month": history_month,
            "my_month": my_month,
            "approval_subtab": approval_subtab,
            "show_approval_tab": show_approval_tab,
            "my_attach_counts": my_attach_counts,
            "app_attach_counts": app_attach_counts,
            "history_attach_counts": history_attach_counts,
            "my_shift_info": my_shift_info,
            "app_shift_info": app_shift_info,
            "history_shift_info": history_shift_info,
            "history_time_surface": history_time_surface,
            "pd_my": pd_my,
            "pd_app": pd_app,
            "pd_app_hist": pd_app_hist,
        },
    )




@login_required
@hx_request_required
@transaction.atomic
def request_new(request):
    """
    This method is used to create new attendance requests
    """

    if request.GET.get("bulk") and eval_validate(request.GET.get("bulk")):
        # Attendance Correction Request (mobile parity): no bulk/batch create flow in this UI.
        return HttpResponseForbidden(_("Bulk attendance request is not available here."))
    # Self-only: employee selector is disabled.
    # Keep other GET params (e.g., attendance_date) but force employee_id to the logged-in employee.
    form = NewRequestForm(initial=request.GET.dict() if request.GET else None)
    try:
        self_emp_id = request.user.employee_get.id
    except Exception:
        self_emp_id = None

    if self_emp_id:
        form.fields['employee_id'].queryset = Employee.objects.filter(id=self_emp_id)
        form.fields['employee_id'].initial = self_emp_id
        form.fields['employee_id'].widget = forms.HiddenInput()
    if request.method == "POST":
        post_data = request.POST.copy()
        try:
            post_data['employee_id'] = request.user.employee_get.id
        except Exception:
            pass
        form = NewRequestForm(post_data, files=getattr(request, 'FILES', None))
        # Hide employee selector (self-only)
        try:
            self_emp_id = request.user.employee_get.id
            form.fields['employee_id'].queryset = Employee.objects.filter(id=self_emp_id)
            form.fields['employee_id'].initial = self_emp_id
            form.fields['employee_id'].widget = forms.HiddenInput()
        except Exception:
            pass
        if form.is_valid():
            # Save (create_request) or update existing attendance (update_request)
            attendance_obj = None
            is_created = False

            if form.new_instance is not None:
                form.new_instance.save()
                attendance_obj = form.new_instance
                is_created = True
            else:
                # update_request style: attendance is already saved in form.clean()
                try:
                    emp = form.cleaned_data.get("employee_id")
                    att_date = form.cleaned_data.get("attendance_date")
                    attendance_obj = Attendance.objects.filter(employee_id=emp, attendance_date=att_date).first()
                except Exception:
                    attendance_obj = None

            # Attach optional proof files directly to the attendance request
            from attendance.models import AttendanceRequestFile

            uploaded = []
            if hasattr(request, "FILES"):
                uploaded = request.FILES.getlist("files") or request.FILES.getlist("files[]") or []
                if not uploaded:
                    f_single = request.FILES.get("file")
                    if f_single:
                        uploaded = [f_single]

            try:
                validate_uploaded_files(uploaded)
            except ValidationError as exc:
                form.add_error(None, exc)
                transaction.set_rollback(True)
                return render(
                    request,
                    "requests/attendance/request_new_form.html",
                    {"form": form, "bulk": False},
                )

            if attendance_obj and uploaded:
                for up in uploaded:
                    arf = AttendanceRequestFile.objects.create(file=up)
                    attendance_obj.request_attachments.add(arf)

            warning_text = " ".join(dict.fromkeys(getattr(form, "window_warnings", []) or []))
            if warning_text:
                messages.warning(request, warning_text)

            if is_created:
                messages.success(request, _("New attendance request created"))
            else:
                messages.success(request, _("Update request updated"))

            return HttpResponse(
                render(
                    request,
                    "requests/attendance/request_new_form.html",
                    {"form": form},
                ).content.decode("utf-8")
                + "<script>location.reload();</script>"
            )
    return render(
            request,
            "requests/attendance/request_new_form.html",
            {"form": form, "bulk": False},
        )




@login_required
def attendance_request_shift_info(request):
    """
    AJAX helper for Web create Attendance Correction Request.
    Returns shift name, start-end time, and flexi-in minutes (grace time) similar to mobile.
    """
    emp_id = (request.GET.get("employee_id") or request.POST.get("employee_id") or "").strip()
    date_str = (request.GET.get("attendance_date") or request.GET.get("date") or request.POST.get("attendance_date") or "").strip()

    if not emp_id or not date_str:
        return JsonResponse({"shift_name": "", "shift_start": "", "shift_end": "", "flexi_in_minutes": ""}, status=200)

    try:
        from datetime import datetime as _dt
        att_date = _dt.strptime(date_str, "%Y-%m-%d").date()
    except Exception:
        return JsonResponse({"shift_name": "", "shift_start": "", "shift_end": "", "flexi_in_minutes": ""}, status=200)

    # Validate employee is selectable by current user (same as request_new)
    try:
        from attendance.forms import NewRequestForm
        form = NewRequestForm()
        form = choosesubordinates(request, form, "attendance.change_attendance")
        employees_qs = Employee.objects.filter(
            Q(id__in=form.fields["employee_id"].queryset.values_list("id", flat=True))
            | Q(employee_user_id=request.user)
        ).distinct()
        if not employees_qs.filter(id=emp_id).exists():
            return JsonResponse({"error": "Forbidden"}, status=403)
        employee = employees_qs.filter(id=emp_id).first()
    except Exception:
        return JsonResponse({"error": "Forbidden"}, status=403)

    shift_name = ""
    shift_start = ""
    shift_end = ""
    flexi_min = ""

    try:
        shift = getattr(getattr(employee, "employee_work_info", None), "shift_id", None)
        if shift:
            shift_name = str(getattr(shift, "employee_shift", "")) or str(shift)

            # Schedule start/end per day
            from base.models import EmployeeShiftSchedule
            day = att_date.strftime("%A").lower()
            sched = EmployeeShiftSchedule.objects.filter(shift_id=shift, day__day=day).first()
            if sched:
                if getattr(sched, "start_time", None):
                    shift_start = sched.start_time.strftime("%H:%M")
                if getattr(sched, "end_time", None):
                    shift_end = sched.end_time.strftime("%H:%M")

            # Flexi-in minutes from grace time (clock-in)
            grace = cio._resolve_grace_time(sched, shift)
            if grace and getattr(grace, "allowed_clock_in", False):
                secs = int(getattr(grace, "allowed_time_in_secs", 0) or 0)
                flexi_min = str(secs // 60)
    except Exception:
        pass

    return JsonResponse(
        {
            "shift_name": shift_name,
            "shift_start": shift_start,
            "shift_end": shift_end,
            "flexi_in_minutes": flexi_min,
        },
        status=200,
    )

@login_required
def create_batch_attendance(request):
    form = BatchAttendanceForm()
    previous_form_data = request.GET.urlencode()
    previous_url = request.GET.get("previous_url")
    # Split the string at "?" and extract the first part, then reattach the "?"
    previous_url = previous_url.split("?")[0] + "?"
    if "attendance-update" in previous_url:
        hx_target = "#updateAttendanceModalBody"
    elif "edit-validate-attendance" in previous_url:
        hx_target = "#editValidateAttendanceRequestModalBody"
    elif "request-attendance" in previous_url:
        hx_target = "#objectUpdateModalTarget"
    elif "attendance-create" in previous_url:
        hx_target = "#addAttendanceModalBody"
    else:
        hx_target = "#objectCreateModalTarget"
    if request.method == "POST":
        form = BatchAttendanceForm(request.POST)
        if form.is_valid():
            batch = form.save()
            messages.success(request, _("Attendance batch created successfully."))
            previous_form_data += f"&batch_attendance_id={batch.id}"
    return render(
        request,
        "attendance/attendance/batch_attendance_form.html",
        {
            "form": form,
            "previous_form_data": previous_form_data,
            "previous_url": previous_url,
            "hx_target": hx_target,
        },
    )


@login_required
def get_batches(request):
    batches = BatchAttendance.objects.all()
    return render(
        request, "attendance/attendance/batches_list.html", {"batches": batches}
    )


@login_required
def update_title(request):
    batch_id = request.POST.get("batch_id")
    try:
        batch = BatchAttendance.objects.filter(id=batch_id).first()
        if (
            request.user.has_perm("attendance.change_attendancegeneralsettings")
            or request.user == batch.created_by
        ):
            title = request.POST.get("title")
            batch.title = title
            batch.save()
            messages.success(request, _("Batch attendance title updated sucessfully."))
        else:
            messages.info(request, _("You don't have permission."))
    except:
        messages.error(request, _("Something went wrong."))
    return redirect(reverse("get-batches"))


@login_required
@permission_required("attendance.delete_batchattendance")
def delete_batch(request, batch_id):
    try:
        batch_name = BatchAttendance.objects.filter(id=batch_id).first().__str__()
        BatchAttendance.objects.filter(id=batch_id).first().delete()
        messages.success(
            request, _(f"{batch_name} - batch has been deleted sucessfully")
        )
    except ProtectedError as e:
        model_verbose_names_set = set()
        for obj in e.protected_objects:
            # Convert the lazy translation proxy to a string.
            model_verbose_names_set.add(str(_(obj._meta.verbose_name.capitalize())))
        model_names_str = ", ".join(model_verbose_names_set)
        messages.error(
            request,
            _("This {} is already in use for {}.").format(batch_name, model_names_str),
        ),
    except:
        messages.error(request, _("Something went wrong."))

    return redirect(reverse("get-batches"))


@login_required
def attendance_request_changes(request, attendance_id):
    """
    This method is used to store the requested changes to the instance
    """
    attendance = Attendance.objects.get(id=attendance_id)
    if request.GET.get("previous_url"):
        form = AttendanceRequestForm(initial=request.GET.dict())
    else:
        form = AttendanceRequestForm(instance=attendance)
        # form.fields["work_type_id"].widget.attrs.update(
        #     {
        #         "class": "w-100",
        #         "style": "height:50px;border-radius:0;border:1px solid hsl(213deg,22%,84%)",
        #     }
        # )
        # form.fields["shift_id"].widget.attrs.update(
        #     {
        #         "class": "w-100",
        #         "style": "height:50px;border-radius:0;border:1px solid hsl(213deg,22%,84%)",
        #     }
        # )
    if request.method == "POST":
        form = AttendanceRequestForm(request.POST, instance=copy.copy(attendance))
        form.fields["work_type_id"].widget.attrs.update(
            {
                "class": "w-100",
                "style": "height:50px;border-radius:0;border:1px solid hsl(213deg,22%,84%)",
            }
        )
        form.fields["shift_id"].widget.attrs.update(
            {
                "class": "w-100",
                "style": "height:50px;border-radius:0;border:1px solid hsl(213deg,22%,84%)",
            }
        )
        work_type_id = form.data["work_type_id"]
        shift_id = form.data["shift_id"]
        if work_type_id is None or not len(work_type_id):
            form.add_error("work_type_id", "This field is required")
        if shift_id is None or not len(shift_id):
            form.add_error("shift_id", "This field is required")
        if form.is_valid():
            # commit already set to False
            # so the changes not affected to the db
            instance = form.save()
            instance.employee_id = attendance.employee_id
            instance.id = attendance.id
            if attendance.request_type != "create_request":
                # Preserve approved-scope meta and validate against already-approved scopes.
                try:
                    from attendance.services.attendance_correction_scope_rules import (
                        infer_scope_from_values,
                        get_approved_scopes,
                        build_requested_data_for_save,
                        validate_new_request_scope,
                    )
                    serialized = instance.serialize()
                    incoming_scope = infer_scope_from_values(
                        serialized.get("attendance_clock_in"),
                        serialized.get("attendance_clock_out"),
                    )
                    approved_scopes = get_approved_scopes(getattr(attendance, "requested_data", None))
                    # Editing existing request is allowed; only block overlaps with approved scopes.
                    validate_new_request_scope(
                        existing_waiting_scope="",
                        approved_scopes=approved_scopes,
                        incoming_scope=incoming_scope,
                    )

                    wrapped = build_requested_data_for_save(
                        new_payload=serialized,
                        existing_requested_data=getattr(attendance, "requested_data", None),
                        incoming_scope=incoming_scope,
                        keep_existing_fields=True,
                    )
                    attendance.requested_data = wrapped
                except ValidationError as ve:
                    # Attach error and re-render form.
                    for k, v in ve.message_dict.items():
                        try:
                            form.add_error(k if k in form.fields else None, v)
                        except Exception:
                            form.add_error(None, v)
                    return render(
                        request,
                        "requests/attendance/form.html",
                        {"form": form, "attendance_id": attendance_id},
                    )
                except Exception:
                    attendance.requested_data = instance.serialize()
                attendance.request_description = instance.request_description
                # set the user level validation here
                attendance.is_validate_request = True
                attendance.save()
            else:
                instance.is_validate_request_approved = False
                instance.is_validate_request = True
                instance.save()
            messages.success(request, _("Attendance update request created."))
            employee = attendance.employee_id
            if attendance.employee_id.employee_work_info.reporting_manager_id:
                reporting_manager = (
                    attendance.employee_id.employee_work_info.reporting_manager_id.employee_user_id
                )
                user_last_name = get_employee_last_name(attendance)
                notify.send(
                    request.user,
                    recipient=reporting_manager,
                    verb=f"{employee.employee_first_name} {user_last_name}'s\
                          attendance update request for {attendance.attendance_date} is created",
                    verb_ar=f"تم إنشاء طلب تحديث الحضور لـ {employee.employee_first_name} \
                        {user_last_name }في {attendance.attendance_date}",
                    verb_de=f"Die Anfrage zur Aktualisierung der Anwesenheit von \
                        {employee.employee_first_name} {user_last_name} \
                            für den {attendance.attendance_date} wurde erstellt",
                    verb_es=f"Se ha creado la solicitud de actualización de asistencia para {employee.employee_first_name}\
                          {user_last_name} el {attendance.attendance_date}",
                    verb_fr=f"La demande de mise à jour de présence de {employee.employee_first_name}\
                          {user_last_name} pour le {attendance.attendance_date} a été créée",
                    redirect=reverse("request-attendance-view")
                    + f"?id={attendance.id}",
                    icon="checkmark-circle-outline",
                )
            return HttpResponse(
                render(
                    request,
                    "requests/attendance/form.html",
                    {"form": form, "attendance_id": attendance_id},
                ).content.decode("utf-8")
                + "<script>location.reload();</script>"
            )
    return render(
        request,
        "requests/attendance/form.html",
        {"form": form, "attendance_id": attendance_id},
    )



def _locked_correction_request(pk):
    try:
        return AttendanceCorrectionRequest._base_manager.select_related(None).select_for_update().get(id=pk)
    except Exception:
        return None


def _locked_legacy_attendance(pk):
    try:
        return Attendance.objects.select_for_update().get(id=pk)
    except Exception:
        return None


def _legacy_web_approve_attendance_request(request, attendance_id):
    attendance = Attendance.objects.select_for_update().get(id=attendance_id)
    try:
        if attendance.employee_id.employee_user_id == request.user:
            messages.error(request, _("You cannot approve your own request."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    except Exception:
        pass
    if not getattr(attendance, "is_validate_request", False):
        messages.error(request, _("Request is not waiting for approval."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    old_status = attendance.request_type or "waiting_request"
    is_valid_request, validation_error = validate_requested_data_with_windows(attendance)
    if not is_valid_request:
        messages.error(request, validation_error or _("Requested attendance cannot be approved because required shift context is missing."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    if validation_error:
        messages.warning(request, validation_error)
    wants_in, wants_out = get_requested_sessions(attendance)
    _apply_request_override_snapshot(attendance, include_in=wants_in, include_out=wants_out)
    attendance.attendance_validated = True
    attendance.is_validate_request_approved = True
    attendance.is_validate_request = False
    try:
        attendance.action_by = request.user.employee_get
    except Exception:
        attendance.action_by = None
    attendance.action_type = AttendanceRequestActionType.APPROVED
    attendance.action_at = timezone.now()
    attendance.save()
    _log_attendance_request_action(attendance, request, action_type=AttendanceRequestActionType.APPROVED, old_status=old_status, new_status="approved")
    requested_data = _normalize_requested_data(load_requested_data(getattr(attendance, "requested_data", None)))
    if requested_data:
        Attendance.objects.filter(id=attendance_id).update(**requested_data)
        try: attendance.refresh_from_db()
        except Exception: pass
    _mark_approved_request_channels(attendance)
    _detach_request_overridden_raw_links(attendance, include_in=wants_in, include_out=wants_out)
    result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
    if result is not None: attendance = result.attendance
    messages.success(request, _("Attendance request has been approved"))
    try:
        notify.send(request.user, recipient=attendance.employee_id.employee_user_id, verb=f"Your attendance request for {attendance.attendance_date} is validated", redirect=reverse("request-attendance-view") + f"?id={attendance.id}", icon="checkmark-circle-outline")
    except Exception:
        pass
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


def _legacy_web_revoke_attendance_request(request, attendance_id):
    qs = Attendance.objects.filter(id=attendance_id, is_validate_request_approved=True)
    try:
        qs = filtersubordinates(request=request, perm="attendance.change_attendance", queryset=qs)
    except Exception:
        pass
    attendance = qs.select_for_update().get() if hasattr(qs, "select_for_update") else qs.get()
    try:
        if attendance.employee_id.employee_user_id == request.user:
            messages.error(request, _("You cannot revoke your own approved request."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    except Exception:
        pass
    wants_in, wants_out = get_requested_sessions(attendance)
    _restore_request_back_to_raw(attendance, include_in=wants_in, include_out=wants_out, prev_attendance_date=attendance.attendance_date)
    try: attendance.refresh_from_db()
    except Exception: pass
    attendance.is_validate_request_approved = False
    attendance.is_validate_request = False
    attendance.request_type = "revoke_request"
    attendance.action_type = AttendanceRequestActionType.REVOKED
    attendance.action_at = timezone.now()
    try: attendance.action_by = request.user.employee_get
    except Exception: attendance.action_by = None
    attendance.save()
    _log_attendance_request_action(attendance, request, action_type=AttendanceRequestActionType.REVOKED, old_status="approved", new_status="revoke_request")
    recompute_attendance(attendance.employee_id, attendance.attendance_date)
    messages.success(request, _("Attendance request approval revoked."))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


def _legacy_web_cancel_attendance_request(request, attendance_id):
    attendance = Attendance.objects.select_for_update().get(id=attendance_id)
    try:
        if attendance.employee_id.employee_user_id != request.user:
            messages.error(request, _("Only the requester can cancel this request."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    except Exception:
        messages.error(request, _("You do not have permission to perform this action."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    if not getattr(attendance, "is_validate_request", False) or getattr(attendance, "is_validate_request_approved", False):
        messages.error(request, _("Only waiting requests can be canceled."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    req_type = attendance.request_type
    old_status = attendance.request_type or "waiting_request"
    wants_in, wants_out = get_requested_sessions(attendance)
    attendance.is_validate_request_approved = False
    attendance.is_validate_request = False
    attendance.request_type = "cancel_request"
    try: attendance.action_by = request.user.employee_get
    except Exception: attendance.action_by = None
    attendance.action_type = AttendanceRequestActionType.CANCELED
    attendance.action_at = timezone.now()
    attendance.save()
    _log_attendance_request_action(attendance, request, action_type=AttendanceRequestActionType.CANCELED, old_status=old_status, new_status="cancel_request")
    if req_type == "create_request":
        clear_request_override_and_recompute(attendance, include_in=wants_in, include_out=wants_out)
    messages.success(request, _("Attendance request canceled."))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


def _legacy_web_reject_attendance_request(request, attendance_id):
    if request.method != "POST":
        attendance = Attendance.objects.filter(id=attendance_id, is_validate_request=True).first()
        if not attendance or not user_can_approve_request(request.user, attendance):
            return HttpResponseForbidden("Permission denied")
        return render(request, "attendance/attendance_requests/reject_form.html", {"attendance": attendance})
    attendance = Attendance.objects.select_for_update().get(id=attendance_id, is_validate_request=True)
    if not user_can_approve_request(request.user, attendance):
        messages.error(request, _("You do not have permission to perform this action."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    try:
        if attendance.employee_id.employee_user_id == request.user:
            messages.error(request, _("Use cancel for your own request."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    except Exception:
        pass
    req_type = attendance.request_type
    wants_in, wants_out = get_requested_sessions(attendance)
    comment_text = (request.POST.get("comment") or request.POST.get("reason") or "").strip()
    if not comment_text:
        messages.error(request, _("Reject reason is required."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    attendance.is_validate_request_approved = False
    attendance.is_validate_request = False
    attendance.request_type = "reject_request"
    attendance.action_type = AttendanceRequestActionType.REJECTED
    attendance.action_at = timezone.now()
    try: attendance.action_by = request.user.employee_get
    except Exception: attendance.action_by = None
    attendance.save()
    _log_attendance_request_action(attendance, request, action_type=AttendanceRequestActionType.REJECTED, old_status=req_type or "waiting_request", new_status="reject_request", remark=comment_text)
    if req_type == "create_request":
        clear_request_override_and_recompute(attendance, include_in=wants_in, include_out=wants_out)
    messages.success(request, _("Attendance request rejected."))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))



@login_required
def validate_attendance_request(request, attendance_id):
    """
    This method to validate the requested attendance
    args:
        attendance_id : attendance id
    """
    attendance = Attendance.objects.get(id=attendance_id)
    first_dict = attendance.serialize()
    empty_data = {
        "employee_id": None,
        "attendance_date": None,
        "attendance_clock_in_date": None,
        "attendance_clock_in": None,
        "attendance_clock_out": None,
        "attendance_clock_out_date": None,
        "shift_id": None,
        "work_type_id": None,
        "attendance_worked_hour": None,
        "batch_attendance_id": None,
    }
    if attendance.request_type == "create_request":
        other_dict = first_dict
        # For create_request there is no "previous" attendance record, but the request still has a date.
        # Keep attendance_date in "Current Value" for UI parity with mobile (so it doesn't look empty).
        first_dict = copy.deepcopy(empty_data)
        _req_date = other_dict.get("attendance_date")
        if not _req_date:
            # Fallback to requested_data payload (older / web-created records may store date there)
            try:
                if isinstance(attendance.requested_data, dict):
                    _req_date = (
                        attendance.requested_data.get("attendance_date")
                        or attendance.requested_data.get("date")
                        or _req_date
                    )
            except Exception:
                pass
        if not _req_date:
            try:
                _req_date = (
                    attendance.attendance_date.strftime("%Y-%m-%d")
                    if attendance.attendance_date
                    else None
                )
            except Exception:
                _req_date = attendance.attendance_date
        first_dict["attendance_date"] = _req_date
    else:
        other_dict = load_requested_data(attendance.requested_data)

    requests_ids_json = request.GET.get("requests_ids")
    previous_instance_id = next_instance_id = attendance.pk
    if requests_ids_json:
        previous_instance_id, next_instance_id = closest_numbers(
            json.loads(requests_ids_json), attendance_id
        )

    # Attachments count (direct attachment flow)
    try:
        attachment_count = len(list(iter_request_attachments(attendance)))
    except Exception:
        attachment_count = 0

    diff_data = get_diff_dict(first_dict, other_dict, Attendance)
    # Ensure Attendance Date always shows in detail (even if unchanged), for mobile parity.
    try:
        _date_key = Attendance._meta.get_field("attendance_date").verbose_name
        _cur_date = first_dict.get("attendance_date")
        _req_date2 = other_dict.get("attendance_date")

        def _fmt_date(_d):
            try:
                if _d and _d != "None" and isinstance(_d, str):
                    return datetime.strptime(_d, "%Y-%m-%d").strftime("%d %b %Y")
            except Exception:
                return _d
            return _d

        if _cur_date or _req_date2:
            diff_data.setdefault(_date_key, (_fmt_date(_cur_date), _fmt_date(_req_date2)))
    except Exception:
        pass

    # Attendance Correction Request (mobile parity): do not show worked hours / batch
    for _k in ("Employee", "Employee ID", "Employee Id", "Employee Name", "Employee name", "Worked Hours", "Worked Hour", "Minimum hour", "Minimum Hour", "Batch Attendance", "Work Type", "Work type", "Work Mode", "Work mode"):
        try:
            diff_data.pop(_k, None)
        except Exception:
            pass

    # Shift info (display only)
    try:
        shift_info = _build_shift_info_map([attendance]).get(attendance.id)
    except Exception:
        shift_info = None

    # Ensure Shift always shows in detail (even if unchanged), for mobile parity.
    try:
        _shift_key = Attendance._meta.get_field("shift_id").verbose_name
        if shift_info and _shift_key not in diff_data:
            diff_data[_shift_key] = (shift_info.name, shift_info.name)
    except Exception:
        pass
    # Reorder diff_data: Attendance Date first, then Shift, then punch fields
    # (UI request: after Shift -> Check-In Date, Check-In, Check-Out Date, Check-Out)
    try:
        from collections import OrderedDict
        _ordered = OrderedDict()
        _keys = [
            Attendance._meta.get_field("attendance_date").verbose_name,
            Attendance._meta.get_field("shift_id").verbose_name,
            Attendance._meta.get_field("attendance_clock_in_date").verbose_name,
            Attendance._meta.get_field("attendance_clock_in").verbose_name,
            Attendance._meta.get_field("attendance_clock_out_date").verbose_name,
            Attendance._meta.get_field("attendance_clock_out").verbose_name,
        ]

        for _kk in _keys:
            if _kk in diff_data:
                _ordered[_kk] = diff_data.pop(_kk)
        for _k, _v in diff_data.items():
            _ordered[_k] = _v
        diff_data = _ordered
    except Exception:
        pass




    return render(
        request,
        "requests/attendance/individual_view.html",
        {
            "data": diff_data,
            "attendance": attendance,
            "previous": previous_instance_id,
            "next": next_instance_id,
            "requests_ids": requests_ids_json,
            "attachment_count": attachment_count,
            "shift_info": shift_info,
        },
    )


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def approve_validate_attendance_request(request, attendance_id):
    """
    This method is used to validate the attendance requests
    """
    attendance = Attendance.objects.select_for_update().get(id=attendance_id)

    # Disallow approving your own request (even if admin)
    try:
        if attendance.employee_id.employee_user_id == request.user:
            messages.error(request, _("You cannot approve your own request."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    except Exception:
        pass

    # Only pending requests can be approved
    if not getattr(attendance, "is_validate_request", False):
        messages.error(request, _("Request is not waiting for approval."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))

    prev_attendance_date = attendance.attendance_date
    old_status = attendance.request_type or "waiting_request"

    is_valid_request, validation_error = validate_requested_data_with_windows(attendance)
    if not is_valid_request:
        messages.error(request, validation_error or _("Requested attendance cannot be approved because required shift context is missing."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    if validation_error:
        messages.warning(request, validation_error)

    wants_in, wants_out = get_requested_sessions(attendance)
    _apply_request_override_snapshot(attendance, include_in=wants_in, include_out=wants_out)

    # Approve request flags (these fields are NOT included in serialize/requested_data)
    attendance.attendance_validated = True
    attendance.is_validate_request_approved = True
    attendance.is_validate_request = False
    try:
        attendance.action_by = request.user.employee_get
    except Exception:
        attendance.action_by = None
    attendance.action_type = AttendanceRequestActionType.APPROVED
    # Keep request_description for history
    attendance.action_at = timezone.now()
    attendance.save()
    _log_attendance_request_action(
        attendance,
        request,
        action_type=AttendanceRequestActionType.APPROVED,
        old_status=old_status,
        new_status="approved",
    )

    # Apply requested field changes (if any)
    if attendance.requested_data:
        # Record approved scope in requested_data.__meta so future requests can enforce
        # one-approval-per-scope per day.
        try:
            from attendance.services.attendance_correction_scope_rules import (
                record_approved_scope_on_requested_data,
            )
            new_req_data = record_approved_scope_on_requested_data(attendance.requested_data)
            if new_req_data and new_req_data != attendance.requested_data:
                attendance.requested_data = new_req_data
                attendance.save(update_fields=["requested_data"])
        except Exception:
            pass

        requested_data = _normalize_requested_data(load_requested_data(attendance.requested_data))
        Attendance.objects.filter(id=attendance_id).update(**requested_data)

        # Re-fetch to ensure types are correct (TimeField -> datetime.time, etc.)
        attendance.refresh_from_db()

        # Save once more to trigger Attendance.save() side effects (e.g., overtime calc)
        attendance.attendance_validated = True
        attendance.is_validate_request_approved = True
        attendance.is_validate_request = False
        attendance.action_by = attendance.action_by or getattr(request.user, "employee_get", None)
        attendance.action_type = attendance.action_type or AttendanceRequestActionType.APPROVED
        attendance.action_at = attendance.action_at or timezone.now()
        attendance.save()

    _mark_approved_request_channels(attendance)
    _detach_request_overridden_raw_links(attendance, include_in=wants_in, include_out=wants_out)
    attendance.refresh_from_db()
    result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
    if result is not None:
        attendance = result.attendance

    messages.success(request, _("Attendance request has been approved"))
    employee = attendance.employee_id
    notify.send(
        request.user,
        recipient=employee.employee_user_id,
        verb=f"Your attendance request for \
            {attendance.attendance_date} is validated",
        verb_ar=f"تم التحقق من طلب حضورك في تاريخ \
            {attendance.attendance_date}",
        verb_de=f"Ihr Anwesenheitsantrag für das Datum \
            {attendance.attendance_date} wurde bestätigt",
        verb_es=f"Se ha validado su solicitud de asistencia \
            para la fecha {attendance.attendance_date}",
        verb_fr=f"Votre demande de présence pour la date \
            {attendance.attendance_date} est validée",
        redirect=reverse("request-attendance-view") + f"?id={attendance.id}",
        icon="checkmark-circle-outline",
    )
    if attendance.employee_id.employee_work_info.reporting_manager_id:
        reporting_manager = (
            attendance.employee_id.employee_work_info.reporting_manager_id.employee_user_id
        )
        user_last_name = get_employee_last_name(attendance)
        notify.send(
            request.user,
            recipient=reporting_manager,
            verb=f"{employee.employee_first_name} {user_last_name}'s\
                  attendance request for {attendance.attendance_date} is validated",
            verb_ar=f"تم التحقق من طلب الحضور لـ {employee.employee_first_name} \
                {user_last_name} في {attendance.attendance_date}",
            verb_de=f"Die Anwesenheitsanfrage von {employee.employee_first_name} \
                {user_last_name} für den {attendance.attendance_date} wurde validiert",
            verb_es=f"Se ha validado la solicitud de asistencia de \
                {employee.employee_first_name} {user_last_name} para el {attendance.attendance_date}",
            verb_fr=f"La demande de présence de {employee.employee_first_name} \
                {user_last_name} pour le {attendance.attendance_date} a été validée",
            redirect=reverse("request-attendance-view") + f"?id={attendance.id}",
            icon="checkmark-circle-outline",
        )
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def revoke_validate_attendance_request(request, attendance_id):
    """Revoke an already approved attendance request and restore the pre-request raw state."""

    try:
        qs = Attendance.objects.filter(id=attendance_id, is_validate_request_approved=True)
        qs = filtersubordinates(
            request=request,
            perm="attendance.change_attendance",
            queryset=qs,
        )
        attendance = qs.select_for_update().get()

        try:
            if attendance.employee_id.employee_user_id == request.user:
                messages.error(request, _("You cannot revoke your own approved request."))
                return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
        except Exception:
            pass

        prev_attendance_date = attendance.attendance_date
        old_status = attendance.request_type or "approved"
        wants_in, wants_out = get_requested_sessions(attendance)
        _restore_request_back_to_raw(attendance, include_in=wants_in, include_out=wants_out, prev_attendance_date=prev_attendance_date)
        attendance.refresh_from_db()
        attendance.is_validate_request_approved = False
        attendance.is_validate_request = False
        attendance.request_type = "revoke_request"
        attendance.action_type = AttendanceRequestActionType.REVOKED
        attendance.action_at = timezone.now()
        try:
            attendance.action_by = request.user.employee_get
        except Exception:
            attendance.action_by = None
        attendance.save()
        _log_attendance_request_action(
            attendance,
            request,
            action_type=AttendanceRequestActionType.REVOKED,
            old_status=old_status,
            new_status="revoke_request",
        )

        result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
        if result is not None:
            attendance = result.attendance

        messages.success(request, _("Attendance request approval revoked."))
    except Attendance.DoesNotExist:
        messages.error(request, _("Attendance request not found"))
    except Exception:
        messages.error(request, _("Something went wrong."))

    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@transaction.atomic
def cancel_attendance_request(request, attendance_id):
    """Cancel an attendance request (owner action).

    Aligned with mobile Attendance Correction Request:
    - Only the requester can cancel
    - Only WAITING requests can be canceled
    - Keep the Attendance row for history (status=CANCELED)
    """
    try:
        attendance = Attendance.objects.select_for_update().get(id=attendance_id)

        # Owner-only
        try:
            if attendance.employee_id.employee_user_id != request.user:
                messages.error(request, _("Only the requester can cancel this request."))
                return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
        except Exception:
            messages.error(request, _("You do not have permission to perform this action."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))

        is_pending_request = bool(getattr(attendance, "is_validate_request", False))
        is_approved_request = bool(getattr(attendance, "is_validate_request_approved", False))
        if not is_pending_request or is_approved_request:
            messages.error(request, _("Only waiting requests can be canceled."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))

        req_type = attendance.request_type
        old_status = attendance.request_type or ("approved" if is_approved_request else "waiting_request")
        req_date = attendance.attendance_date
        req_employee = attendance.employee_id
        wants_in, wants_out = get_requested_sessions(attendance)
        needs_canonical_reset = bool(req_type == "create_request")

        attendance.is_validate_request_approved = False
        attendance.is_validate_request = False
        attendance.request_type = "cancel_request"
        try:
            attendance.action_by = request.user.employee_get
        except Exception:
            attendance.action_by = None
        attendance.action_type = AttendanceRequestActionType.CANCELED
        attendance.action_at = timezone.now()
        attendance.save()
        _log_attendance_request_action(
            attendance,
            request,
            action_type=AttendanceRequestActionType.CANCELED,
            old_status=old_status,
            new_status="cancel_request",
        )

        if needs_canonical_reset:
            attendance = clear_request_override_and_recompute(
                attendance,
                include_in=wants_in,
                include_out=wants_out,
            )
        messages.success(request, _("Attendance request canceled."))
        send_attendance_request_notification(
            actor=request.user,
            recipient=attendance.employee_id.employee_user_id,
            attendance=attendance,
            event="attendance_request_canceled",
            recipient_role="requester",
        )

    except Attendance.DoesNotExist:
        messages.error(request, _("Attendance request not found"))
    except Exception:
        messages.error(request, _("Something went wrong."))

    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def reject_validate_attendance_request(request, attendance_id):
    """Reject an attendance request (approver action) with mandatory reason."""
    if request.method != "POST":
        attendance = Attendance.objects.filter(id=attendance_id, is_validate_request=True).first()
        if not attendance or not user_can_approve_request(request.user, attendance):
            return HttpResponseForbidden("Permission denied")
        return render(request, "attendance/attendance_requests/reject_form.html", {"attendance": attendance})
    try:
        # Fetch via permission-filtered queryset to ensure manager/admin scope
        attendance = Attendance.objects.select_for_update().get(id=attendance_id, is_validate_request=True)
        if not user_can_approve_request(request.user, attendance):
            messages.error(request, _("You do not have permission to perform this action."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))

        # Disallow rejecting your own request
        try:
            if attendance.employee_id.employee_user_id == request.user:
                messages.error(request, _("Use cancel for your own request."))
                return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
        except Exception:
            pass

        req_type = attendance.request_type
        old_status = attendance.request_type or "waiting_request"
        req_date = attendance.attendance_date
        req_employee = attendance.employee_id
        wants_in, wants_out = get_requested_sessions(attendance)
        needs_canonical_reset = req_type == "create_request"

        comment_text = (request.POST.get("comment") or request.POST.get("reason") or "").strip()
        if not comment_text:
            messages.error(request, _("Reject reason is required."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))

        attendance.is_validate_request_approved = False
        attendance.is_validate_request = False
        attendance.request_type = "reject_request"
        try:
            attendance.action_by = request.user.employee_get
        except Exception:
            attendance.action_by = None
        attendance.action_type = AttendanceRequestActionType.REJECTED
        attendance.action_at = timezone.now()
        attendance.save()
        _log_attendance_request_action(
            attendance,
            request,
            action_type=AttendanceRequestActionType.REJECTED,
            old_status=old_status,
            new_status="reject_request",
            remark=comment_text,
        )

        if needs_canonical_reset:
            attendance = clear_request_override_and_recompute(
                attendance,
                include_in=wants_in,
                include_out=wants_out,
            )

        messages.success(request, _("Attendance request rejected."))
        send_attendance_request_notification(
            actor=request.user,
            recipient=attendance.employee_id.employee_user_id,
            attendance=attendance,
            event="attendance_request_rejected",
            recipient_role="requester",
            reason=comment_text,
        )

    except Attendance.DoesNotExist:
        messages.error(request, _("Attendance request not found"))
    except Exception:
        messages.error(request, _("Something went wrong."))

    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@hx_request_required
def attendance_request_attachments(request, attendance_id):
    """HTMX modal: show Attendance Request direct attachments."""
    attendance = Attendance.objects.filter(id=attendance_id).first()
    if not attendance:
        return render(request, "attendance/attendance_requests/attachments_modal.html", {"req": None, "files": []})
    if not user_can_view_request(request.user, attendance):
        return HttpResponseForbidden("Permission denied")
    files = list(iter_request_attachments(attendance))
    return render(request, "attendance/attendance_requests/attachments_modal.html", {"req": attendance, "files": files, "can_delete": user_can_delete_attachment(request.user, attendance)})

@login_required
@transaction.atomic
def delete_attendance_request_attachment(request, attendance_id, file_id):
    if request.method != "POST":
        return HttpResponseForbidden("Method not allowed")
    attendance = Attendance.objects.filter(id=attendance_id).first()
    if not attendance:
        messages.error(request, _("Attendance request not found."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    if not user_can_delete_attachment(request.user, attendance):
        messages.error(request, _("You do not have permission to delete this attachment."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    file_obj = AttendanceRequestFile.objects.filter(id=file_id).first()
    if not file_obj or file_obj not in list(iter_request_attachments(attendance)):
        messages.error(request, _("Attachment not found."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    hard_delete_request_attachment(attendance, file_obj)
    messages.success(request, _("Attachment deleted."))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))





@login_required
def select_all_filter_attendance_request(request):
    page_number = request.GET.get("page")
    filtered = request.GET.get("filter")
    filters = json.loads(filtered) if filtered else {}

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendance"):
            employee_filter = AttendanceFilters(
                request.GET,
                queryset=Attendance.objects.filter(is_validate_request=True),
            )
        else:
            employee_filter = AttendanceFilters(
                request.GET,
                queryset=Attendance.objects.filter(
                    employee_id__employee_user_id=request.user, is_validate_request=True
                )
                | Attendance.objects.filter(
                    employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user,
                    is_validate_request=True,
                ),
            )

        # Get the filtered queryset

        filtered_employees = employee_filter.qs

        employee_ids = [str(emp.id) for emp in filtered_employees]
        total_count = filtered_employees.count()

        context = {"employee_ids": employee_ids, "total_count": total_count}

        return JsonResponse(context)


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def bulk_approve_attendance_request(request):
    """Approve multiple attendance requests (single-session aware)."""

    ids = json.loads(request.POST["ids"])
    warning_count = 0
    for attendance_id in ids:
        # Lock row per id to prevent partial updates in concurrent approvals
        attendance = Attendance.objects.select_for_update().get(id=attendance_id)

        # Disallow approving your own request (bulk)
        try:
            if attendance.employee_id.employee_user_id == request.user:
                continue
        except Exception:
            pass

        # Only pending requests can be approved
        if not getattr(attendance, 'is_validate_request', False):
            continue

        prev_attendance_date = attendance.attendance_date
        old_status = attendance.request_type or "waiting_request"

        is_valid_request, _validation_error = validate_requested_data_with_windows(attendance)
        if not is_valid_request:
            continue
        if _validation_error:
            warning_count += 1

        wants_in, wants_out = get_requested_sessions(attendance)
        _apply_request_override_snapshot(attendance, include_in=wants_in, include_out=wants_out)

        # Mark approved
        attendance.attendance_validated = True
        attendance.is_validate_request_approved = True
        attendance.is_validate_request = False
        try:
            attendance.action_by = request.user.employee_get
        except Exception:
            attendance.action_by = None
        attendance.action_type = AttendanceRequestActionType.APPROVED
        attendance.action_at = timezone.now()
        attendance.save()
        _log_attendance_request_action(
            attendance,
            request,
            action_type=AttendanceRequestActionType.APPROVED,
            old_status=old_status,
            new_status="approved",
        )

        # Apply requested changes
        if attendance.requested_data is not None:
            # Record approved scope in requested_data.__meta for future scope enforcement.
            try:
                from attendance.services.attendance_correction_scope_rules import (
                    record_approved_scope_on_requested_data,
                )
                new_req_data = record_approved_scope_on_requested_data(attendance.requested_data)
                if new_req_data and new_req_data != attendance.requested_data:
                    attendance.requested_data = new_req_data
                    attendance.save(update_fields=["requested_data"])
            except Exception:
                pass

            requested_data = _normalize_requested_data(load_requested_data(attendance.requested_data))
            Attendance.objects.filter(id=attendance_id).update(**requested_data)
            attendance.refresh_from_db()
            attendance.attendance_validated = True
            attendance.is_validate_request_approved = True
            attendance.is_validate_request = False
            attendance.action_by = attendance.action_by or getattr(request.user, "employee_get", None)
            attendance.action_type = attendance.action_type or AttendanceRequestActionType.APPROVED
            attendance.action_at = attendance.action_at or timezone.now()
            attendance.save()

        _mark_approved_request_channels(attendance)
        _detach_request_overridden_raw_links(attendance, include_in=wants_in, include_out=wants_out)
        attendance.refresh_from_db()
        result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
        if result is not None:
            attendance = result.attendance

        messages.success(request, _("Attendance request has been approved"))

        employee = attendance.employee_id
        send_attendance_request_notification(
            actor=request.user,
            recipient=employee.employee_user_id,
            attendance=attendance,
            event="attendance_request_approved",
            recipient_role="requester",
        )

        if attendance.employee_id.employee_work_info.reporting_manager_id:
            reporting_manager = (
                attendance.employee_id.employee_work_info.reporting_manager_id.employee_user_id
            )
            user_last_name = get_employee_last_name(attendance)
            send_attendance_request_notification(
                actor=request.user,
                recipient=reporting_manager,
                attendance=attendance,
                event="attendance_request_approved",
                recipient_role="approver",
            )

    if warning_count:
        messages.warning(request, _("%(count)s request(s) were approved outside the configured attendance window and require manual review context.") % {"count": warning_count})
    return HttpResponse("success")


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def bulk_reject_attendance_request(request):
    """Bulk reject pending attendance requests (approver action).

    This keeps the Attendance row for history (status=REJECTED), aligned with the
    mobile Attendance Correction Request flow.
    """
    ids = request.POST.get("ids") or "[]"
    ids = json.loads(ids)

    for attendance_id in ids:
        try:
            qs = Attendance.objects.filter(id=attendance_id, is_validate_request=True)
            qs = filtersubordinates(
                request=request,
                perm="attendance.change_attendance",
                queryset=qs,
            )
            attendance = qs.select_for_update().get()

            # Skip own request
            try:
                if attendance.employee_id.employee_user_id == request.user:
                    continue
            except Exception:
                pass

            req_type = attendance.request_type
            old_status = attendance.request_type or "waiting_request"
            req_date = attendance.attendance_date
            req_employee = attendance.employee_id
            wants_in, wants_out = get_requested_sessions(attendance)
            needs_canonical_reset = req_type == "create_request"

            attendance.is_validate_request_approved = False
            attendance.is_validate_request = False
            attendance.request_type = "reject_request"
            try:
                attendance.action_by = request.user.employee_get
            except Exception:
                attendance.action_by = None
            attendance.action_type = AttendanceRequestActionType.REJECTED
            attendance.action_at = timezone.now()
            attendance.save()
            _log_attendance_request_action(
                attendance,
                request,
                action_type=AttendanceRequestActionType.REJECTED,
                old_status=old_status,
                new_status="reject_request",
            )

            if needs_canonical_reset:
                clear_request_override_and_recompute(
                    attendance,
                    include_in=wants_in,
                    include_out=wants_out,
                )

        except Exception:
            # Ignore errors per item to continue processing the list
            continue

    return HttpResponse("success")




@login_required
@manager_can_enter("attendance.change_attendance")
def edit_validate_attendance(request, attendance_id):
    """
    This method is used to edit and update the validate request attendance
    """
    attendance = Attendance.objects.get(id=attendance_id)
    initial = attendance.serialize()
    if request.GET.get("previous_url"):
        initial = request.GET.dict()
    else:
        if attendance.request_type != "create_request":
            initial = load_requested_data(attendance.requested_data)
        initial["request_description"] = attendance.request_description
    form = AttendanceRequestForm(initial=initial)
    form.instance.id = attendance.id
    hx_target = request.META.get("HTTP_HX_TARGET")
    if request.method == "POST":
        form = AttendanceRequestForm(request.POST, instance=copy.copy(attendance))
        if form.is_valid():
            instance = form.save()
            instance.employee_id = attendance.employee_id
            instance.id = attendance.id
            if attendance.request_type != "create_request":
                if attendance.is_validate_request_approved:
                    wants_in, wants_out = get_requested_sessions(attendance)
                    _restore_request_back_to_raw(attendance, include_in=wants_in, include_out=wants_out, prev_attendance_date=attendance.attendance_date)
                    attendance.refresh_from_db()
                    attendance.is_validate_request_approved = False
                    attendance.request_type = "revalidate_request"
                attendance.requested_data = instance.serialize()
                attendance.request_description = instance.request_description
                # set the user level validation here
                attendance.is_validate_request = True
                attendance.save()
            else:
                instance.is_validate_request_approved = False
                instance.is_validate_request = True
                instance.save()
            return HttpResponse(
                f"""
                                <script>
                                $('#editValidateAttendanceRequest').removeClass('oh-modal--show');
                                $('[data-target="#validateAttendanceRequest"][data-attendance-id={attendance.id}]').click();
                                $('#messages').html(
                                `
                                <div class="oh-alert-container">
                                <div class="oh-alert oh-alert--animated oh-alert--success">
                                Attendance request updated.
                                </div>
                                </div>
                                `
                                )
                                </script>
                                """
            )
    return render(
        request,
        "requests/attendance/update_form.html",
        {"form": form, "hx_target": hx_target},
    )


@login_required
@hx_request_required
def get_employee_shift(request):
    """
    method used to get employee shift
    """
    employee_id = request.GET.get("employee_id")
    shift = None
    if employee_id:
        employee = Employee.objects.get(id=employee_id)
        shift = employee.get_shift
    form = NewRequestForm()
    if request.GET.get("bulk") and eval_validate(request.GET.get("bulk")):
        form = BulkAttendanceRequestForm()
    form.fields["shift_id"].queryset = EmployeeShift.objects.all()
    form.fields["shift_id"].widget.attrs["hx-trigger"] = "load,change"
    form.fields["shift_id"].initial = shift
    shift_id = render_to_string(
        "requests/attendance/form_field.html",
        {
            "field": form["shift_id"],
            "shift": shift,
        },
    )
    return HttpResponse(f"{shift_id}")


# -----------------------------------------------------------------------------
# Redesigned Attendance Correction Request web flow (overrides legacy handlers)
# -----------------------------------------------------------------------------
from collections import OrderedDict

from django.shortcuts import get_object_or_404

from attendance.forms import MultipleFileField
from attendance.models import (
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestAttachment,
    AttendanceCorrectionRequestStatus,
)
from attendance.services.attendance_correction_requests import (
    AttendanceCorrectionError,
    approve_request,
    build_permission_flags,
    cancel_request,
    create_request,
    reject_request,
    revoke_request,
    update_request,
    user_can_approve_request,
    user_is_request_owner,
)
from base.methods import get_subordinate_employee_ids


class AttendanceCorrectionRequestWebForm(forms.Form):
    employee_id = forms.ModelChoiceField(queryset=Employee.objects.none(), widget=forms.HiddenInput(), required=True)
    attendance_date = forms.DateField(widget=forms.DateInput(attrs={"type": "date"}), required=True)
    attendance_clock_in = forms.TimeField(widget=forms.TimeInput(attrs={"type": "time"}), required=False)
    attendance_clock_out = forms.TimeField(widget=forms.TimeInput(attrs={"type": "time"}), required=False)
    request_description = forms.CharField(widget=forms.Textarea, required=True, label=_("Reason / Note"))
    scope = forms.ChoiceField(
        choices=[("IN", _("IN")), ("OUT", _("OUT")), ("FULL", _("IN & OUT"))],
        required=False,
        initial="FULL",
        widget=forms.HiddenInput(),
    )
    files = MultipleFileField(required=False, label=_("Attachment"))

    def __init__(self, *args, employee=None, instance=None, **kwargs):
        super().__init__(*args, **kwargs)
        if employee is not None:
            self.fields["employee_id"].queryset = Employee.objects.filter(id=employee.id)
            self.fields["employee_id"].initial = employee.id
        if instance is not None:
            self.fields["employee_id"].queryset = Employee.objects.filter(id=instance.employee_id_id)
            self.initial.setdefault("employee_id", instance.employee_id_id)
            self.initial.setdefault("attendance_date", instance.attendance_date)
            self.initial.setdefault("attendance_clock_in", instance.requested_check_in_time)
            self.initial.setdefault("attendance_clock_out", instance.requested_check_out_time)
            self.initial.setdefault("request_description", instance.reason)
            self.initial.setdefault("scope", instance.scope)
        try:
            max_date = timezone.localdate() - timedelta(days=1)
            self.fields["attendance_date"].widget.attrs["max"] = max_date.strftime("%Y-%m-%d")
        except Exception:
            pass


def _web_shift_info_for_request_obj(request_obj):
    shift = None
    try:
        shift = request_obj.employee_id.employee_work_info.shift_id
    except Exception:
        shift = None
    if not shift:
        return None
    try:
        day = request_obj.attendance_date.strftime("%A").lower()
        day_obj = EmployeeShiftDay.objects.filter(day=day).first()
        sched = EmployeeShiftSchedule.objects.filter(shift_id=shift, day=day_obj).first()
        grace = cio._resolve_grace_time(sched, shift)
        secs = int(getattr(grace, "allowed_time_in_secs", 0) or 0) if grace else 0
        return {
            "name": str(shift),
            "start": sched.start_time.strftime("%H:%M") if sched and getattr(sched, "start_time", None) else "-",
            "end": sched.end_time.strftime("%H:%M") if sched and getattr(sched, "end_time", None) else "-",
            "flexi_minutes": int(secs // 60),
        }
    except Exception:
        return None


def _web_attachment_counts(queryset):
    return {obj.id: getattr(obj, "attachment_links", None).count() if hasattr(obj, "attachment_links") else 0 for obj in queryset}


def _web_shift_info_map(queryset):
    return {obj.id: _web_shift_info_for_request_obj(obj) for obj in queryset}


def _web_history_status_filter(qs, status_value):
    status_value = (status_value or "all").strip().lower()
    mapping = {
        "approved": AttendanceCorrectionRequestStatus.APPROVED,
        "rejected": AttendanceCorrectionRequestStatus.REJECTED,
        "revoked": AttendanceCorrectionRequestStatus.REVOKED,
    }
    if status_value in mapping:
        return qs.filter(status=mapping[status_value])
    if status_value in {"canceled", "cancel"}:
        return qs.none()
    return qs


@login_required
def request_attendance_view(request):
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    can_approve = bool(employee and get_subordinate_employee_ids(type("R", (), {"user": request.user})())) or is_super
    if employee is None and not is_super:
        return HttpResponseForbidden("Employee profile required")

    status_my = (request.GET.get("status_my") or "all").strip().lower()
    approval_subtab = (request.GET.get("approval_subtab") or "active").strip().lower()
    if approval_subtab not in {"active", "history"}:
        approval_subtab = "active"
    show_approval_tab = any(
        key in request.GET for key in ("tab", "approval_subtab", "page_app", "page_app_hist", "history_month", "history_status", "history_employee_id")
    ) or (request.GET.get("tab") or "").strip().lower() == "approvals"

    history_status = (request.GET.get("history_status") or "all").strip().lower()
    history_employee_id = (request.GET.get("history_employee_id") or "").strip()
    history_month_start, history_month_end, history_month = _parse_history_month_range(request.GET.get("history_month") or request.GET.get("history_date"))
    my_month_start, my_month_end, my_month = _parse_history_month_range(request.GET.get("my_month"))
    search = (request.GET.get("search") or "").strip()

    my_qs = AttendanceCorrectionRequest.objects.filter(employee_id__employee_user_id=request.user, attendance_date__range=(my_month_start, my_month_end))
    if status_my != "all":
        mapping = {
            "waiting": AttendanceCorrectionRequestStatus.WAITING,
            "approved": AttendanceCorrectionRequestStatus.APPROVED,
            "rejected": AttendanceCorrectionRequestStatus.REJECTED,
            "revoked": AttendanceCorrectionRequestStatus.REVOKED,
            "canceled": AttendanceCorrectionRequestStatus.CANCELED,
            "cancel": AttendanceCorrectionRequestStatus.CANCELED,
        }
        if status_my in mapping:
            my_qs = my_qs.filter(status=mapping[status_my])

    subordinate_ids = set(get_subordinate_employee_ids(type("R", (), {"user": request.user})())) if employee else set()
    approvals_qs = AttendanceCorrectionRequest.objects.filter(status=AttendanceCorrectionRequestStatus.WAITING)
    if is_super:
        approvals_qs = approvals_qs.exclude(employee_id__employee_user_id=request.user)
        history_qs = AttendanceCorrectionRequest.objects.exclude(status__in=[AttendanceCorrectionRequestStatus.WAITING, AttendanceCorrectionRequestStatus.CANCELED])
    elif subordinate_ids:
        approvals_qs = approvals_qs.filter(employee_id_id__in=subordinate_ids).exclude(employee_id__employee_user_id=request.user)
        history_qs = AttendanceCorrectionRequest.objects.filter(
            employee_id_id__in=subordinate_ids,
            status__in=[
                AttendanceCorrectionRequestStatus.APPROVED,
                AttendanceCorrectionRequestStatus.REJECTED,
                AttendanceCorrectionRequestStatus.REVOKED,
            ],
        )
    else:
        approvals_qs = AttendanceCorrectionRequest.objects.none()
        history_qs = AttendanceCorrectionRequest.objects.none()

    history_qs = history_qs.filter(attendance_date__range=(history_month_start, history_month_end))
    if history_employee_id:
        history_qs = history_qs.filter(employee_id_id=history_employee_id)
    history_qs = _web_history_status_filter(history_qs, history_status)

    if search:
        my_qs = my_qs.filter(Q(reason__icontains=search) | Q(scope__icontains=search))
        approvals_qs = approvals_qs.filter(
            Q(employee_id__employee_first_name__icontains=search)
            | Q(employee_id__employee_last_name__icontains=search)
            | Q(employee_id__badge_id__icontains=search)
            | Q(reason__icontains=search)
        )
        history_qs = history_qs.filter(
            Q(employee_id__employee_first_name__icontains=search)
            | Q(employee_id__employee_last_name__icontains=search)
            | Q(employee_id__badge_id__icontains=search)
            | Q(reason__icontains=search)
        )

    my_requests = paginator_qry(my_qs.order_by("-attendance_date", "-action_at", "-id"), request.GET.get("page_my"))
    approvals = paginator_qry(approvals_qs.order_by("-attendance_date", "-created_at", "-id"), request.GET.get("page_app"))
    approval_history = paginator_qry(history_qs.order_by("-attendance_date", "-action_at", "-id"), request.GET.get("page_app_hist"))

    status_my_options = [
        ("all", _("All Statuses")),
        ("waiting", _("WAITING")),
        ("approved", _("APPROVED")),
        ("rejected", _("REJECTED")),
        ("revoked", _("REVOKED")),
        ("canceled", _("CANCELED")),
    ]
    history_status_options = [
        ("all", _("All Statuses")),
        ("approved", _("APPROVED")),
        ("rejected", _("REJECTED")),
        ("revoked", _("REVOKED")),
    ]

    history_employees = Employee.objects.filter(id__in=subordinate_ids).order_by("employee_first_name", "employee_last_name") if subordinate_ids else Employee.objects.none()

    try:
        q_my = request.GET.copy(); q_my.pop("page_my", None); pd_my = q_my.urlencode()
        q_app = request.GET.copy(); q_app.pop("page_app", None); pd_app = q_app.urlencode()
        q_app_hist = request.GET.copy(); q_app_hist.pop("page_app_hist", None); pd_app_hist = q_app_hist.urlencode()
    except Exception:
        pd_my = pd_app = pd_app_hist = ""

    current_my = list(my_requests.object_list)
    current_app = list(approvals.object_list)
    current_hist = list(approval_history.object_list)

    return render(
        request,
        "attendance/attendance_requests/view.html",
        {
            "my_requests": my_requests,
            "approvals": approvals,
            "approval_history": approval_history,
            "can_approve": can_approve,
            "search": search,
            "status_my": status_my,
            "status_my_options": status_my_options,
            "history_status": history_status,
            "history_status_options": history_status_options,
            "history_employee_id": history_employee_id,
            "history_employees": history_employees,
            "history_month": history_month,
            "my_month": my_month,
            "approval_subtab": approval_subtab,
            "show_approval_tab": show_approval_tab,
            "my_attach_counts": _web_attachment_counts(current_my),
            "app_attach_counts": _web_attachment_counts(current_app),
            "history_attach_counts": _web_attachment_counts(current_hist),
            "my_shift_info": _web_shift_info_map(current_my),
            "app_shift_info": _web_shift_info_map(current_app),
            "history_shift_info": _web_shift_info_map(current_hist),
            "history_time_surface": {obj.id: build_attendance_request_time_surface(obj) for obj in current_hist},
            "pd_my": pd_my,
            "pd_app": pd_app,
            "pd_app_hist": pd_app_hist,
        },
    )


@login_required
@hx_request_required
@transaction.atomic
def request_new(request):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")
    form = AttendanceCorrectionRequestWebForm(request.POST or None, request.FILES or None, employee=employee)
    if request.method == "POST" and form.is_valid():
        payload = {
            "attendance_date": form.cleaned_data["attendance_date"],
            "scope": form.cleaned_data.get("scope") or "FULL",
            "reason": form.cleaned_data["request_description"],
            "requested_check_in_date": form.cleaned_data["attendance_date"] if form.cleaned_data.get("attendance_clock_in") else None,
            "requested_check_in_time": form.cleaned_data.get("attendance_clock_in"),
            "requested_check_out_date": form.cleaned_data["attendance_date"] if form.cleaned_data.get("attendance_clock_out") else None,
            "requested_check_out_time": form.cleaned_data.get("attendance_clock_out"),
        }
        try:
            create_request(employee=employee, actor_user=request.user, payload=payload, uploaded_files=form.cleaned_data.get("files") or [])
        except AttendanceCorrectionError as exc:
            for field, messages_ in getattr(exc, "message_dict", {None: exc.messages}).items():
                for message in messages_ if isinstance(messages_, list) else [messages_]:
                    form.add_error(None if field == "error" else field, message)
        else:
            messages.success(request, _("Attendance correction request created."))
            return HttpResponse(render(request, "requests/attendance/request_new_form.html", {"form": AttendanceCorrectionRequestWebForm(employee=employee), "bulk": False, "form_action": reverse("request-new-attendance")}).content.decode("utf-8") + "<script>location.reload();</script>")
    return render(request, "requests/attendance/request_new_form.html", {"form": form, "bulk": False, "form_action": reverse("request-new-attendance")})


@login_required
def validate_attendance_request(request, attendance_id):
    req_obj = get_object_or_404(AttendanceCorrectionRequest, id=attendance_id)
    flags = build_permission_flags(req_obj, request.user)
    if not any(flags.values()) and not user_is_request_owner(request.user, req_obj) and not getattr(request.user, "is_superuser", False):
        return HttpResponseForbidden("Permission denied")
    final_attendance = Attendance.objects.filter(employee_id=req_obj.employee_id, attendance_date=req_obj.attendance_date).first()
    current_in_date = getattr(final_attendance, "attendance_clock_in_date", None)
    current_in = getattr(final_attendance, "attendance_clock_in", None)
    current_out_date = getattr(final_attendance, "attendance_clock_out_date", None)
    current_out = getattr(final_attendance, "attendance_clock_out", None)
    diff_data = OrderedDict([
        (_("Attendance date"), (req_obj.attendance_date, req_obj.attendance_date)),
        (_("Shift"), ("-", "-")),
        (_("Check-In Date"), (current_in_date, req_obj.requested_check_in_date)),
        (_("Check-In"), (current_in, req_obj.requested_check_in_time)),
        (_("Check-Out Date"), (current_out_date, req_obj.requested_check_out_date)),
        (_("Check-Out"), (current_out, req_obj.requested_check_out_time)),
    ])
    return render(request, "requests/attendance/individual_view.html", {
        "data": diff_data,
        "attendance": req_obj,
        "previous": req_obj.id,
        "next": req_obj.id,
        "requests_ids": None,
        "attachment_count": req_obj.attachment_links.count(),
        "shift_info": _web_shift_info_for_request_obj(req_obj),
    })


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def approve_validate_attendance_request(request, attendance_id):
    req_obj = _locked_correction_request(attendance_id)
    if req_obj is None:
        return _legacy_web_approve_attendance_request(request, attendance_id)
    if not user_can_approve_request(request.user, req_obj):
        messages.error(request, _("You do not have permission to approve this request."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    try:
        approve_request(request_obj=req_obj, actor_user=request.user)
        messages.success(request, _("Attendance request approved."))
    except AttendanceCorrectionError as exc:
        messages.error(request, "; ".join(sum(([v] if isinstance(v, str) else list(v) for v in getattr(exc, "message_dict", {"error": exc.messages}).values()), [])))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def revoke_validate_attendance_request(request, attendance_id):
    req_obj = _locked_correction_request(attendance_id)
    if req_obj is None:
        return _legacy_web_revoke_attendance_request(request, attendance_id)
    if not build_permission_flags(req_obj, request.user).get("can_revoke"):
        messages.error(request, _("You do not have permission to revoke this request."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    reason = (request.POST.get("reason") or request.GET.get("reason") or request.POST.get("comment") or "").strip() or _("Revoke by approver")
    try:
        revoke_request(request_obj=req_obj, actor_user=request.user, reason=reason)
        messages.success(request, _("Attendance request revoked."))
    except AttendanceCorrectionError as exc:
        messages.error(request, "; ".join(sum(([v] if isinstance(v, str) else list(v) for v in getattr(exc, "message_dict", {"error": exc.messages}).values()), [])))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@transaction.atomic
def cancel_attendance_request(request, attendance_id):
    req_obj = _locked_correction_request(attendance_id)
    if req_obj is None:
        return _legacy_web_cancel_attendance_request(request, attendance_id)
    if not build_permission_flags(req_obj, request.user).get("can_cancel"):
        messages.error(request, _("Only the requester can cancel a waiting request."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    try:
        cancel_request(request_obj=req_obj, actor_user=request.user)
        messages.success(request, _("Attendance request canceled."))
    except AttendanceCorrectionError as exc:
        messages.error(request, "; ".join(sum(([v] if isinstance(v, str) else list(v) for v in getattr(exc, "message_dict", {"error": exc.messages}).values()), [])))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def reject_validate_attendance_request(request, attendance_id):
    req_obj = _locked_correction_request(attendance_id)
    if req_obj is None:
        return _legacy_web_reject_attendance_request(request, attendance_id)
    if request.method != "POST":
        if not build_permission_flags(req_obj, request.user).get("can_reject"):
            return HttpResponseForbidden("Permission denied")
        return render(request, "attendance/attendance_requests/reject_form.html", {"attendance": req_obj})
    if not build_permission_flags(req_obj, request.user).get("can_reject"):
        messages.error(request, _("You do not have permission to reject this request."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    reason = (request.POST.get("comment") or request.POST.get("reason") or "").strip()
    try:
        reject_request(request_obj=req_obj, actor_user=request.user, reason=reason)
        messages.success(request, _("Attendance request rejected."))
    except AttendanceCorrectionError as exc:
        messages.error(request, "; ".join(sum(([v] if isinstance(v, str) else list(v) for v in getattr(exc, "message_dict", {"error": exc.messages}).values()), [])))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@hx_request_required
@transaction.atomic
def edit_validate_attendance(request, attendance_id):
    req_obj = get_object_or_404(AttendanceCorrectionRequest.objects.select_for_update(), id=attendance_id)
    if not build_permission_flags(req_obj, request.user).get("can_edit"):
        return HttpResponseForbidden("Permission denied")
    employee = req_obj.employee_id
    form = AttendanceCorrectionRequestWebForm(request.POST or None, request.FILES or None, employee=employee, instance=req_obj)
    if request.method == "POST" and form.is_valid():
        payload = {
            "attendance_date": form.cleaned_data["attendance_date"],
            "scope": form.cleaned_data.get("scope") or req_obj.scope,
            "reason": form.cleaned_data["request_description"],
            "requested_check_in_date": form.cleaned_data["attendance_date"] if form.cleaned_data.get("attendance_clock_in") else None,
            "requested_check_in_time": form.cleaned_data.get("attendance_clock_in"),
            "requested_check_out_date": form.cleaned_data["attendance_date"] if form.cleaned_data.get("attendance_clock_out") else None,
            "requested_check_out_time": form.cleaned_data.get("attendance_clock_out"),
        }
        try:
            update_request(request_obj=req_obj, actor_user=request.user, payload=payload, uploaded_files=form.cleaned_data.get("files") or [])
        except AttendanceCorrectionError as exc:
            for field, messages_ in getattr(exc, "message_dict", {None: exc.messages}).items():
                for message in messages_ if isinstance(messages_, list) else [messages_]:
                    form.add_error(None if field == "error" else field, message)
        else:
            messages.success(request, _("Attendance correction request updated."))
            return HttpResponse(render(request, "requests/attendance/request_new_form.html", {"form": AttendanceCorrectionRequestWebForm(employee=employee, instance=req_obj), "bulk": False, "form_action": reverse("edit-validate-attendance", args=[req_obj.id])}).content.decode("utf-8") + "<script>location.reload();</script>")
    return render(request, "requests/attendance/request_new_form.html", {"form": form, "bulk": False, "form_action": reverse("edit-validate-attendance", args=[req_obj.id])})


@login_required
@hx_request_required
def attendance_request_attachments(request, attendance_id):
    req_obj = get_object_or_404(AttendanceCorrectionRequest, id=attendance_id)
    flags = build_permission_flags(req_obj, request.user)
    if not any(flags.values()) and not user_is_request_owner(request.user, req_obj) and not getattr(request.user, "is_superuser", False):
        return HttpResponseForbidden("Permission denied")
    files = [link.attendance_request_file for link in req_obj.attachment_links.select_related("attendance_request_file").all()]
    return render(request, "attendance/attendance_requests/attachments_modal.html", {"req": req_obj, "files": files, "can_delete": flags.get("can_edit", False)})


@login_required
@transaction.atomic
def delete_attendance_request_attachment(request, attendance_id, file_id):
    if request.method != "POST":
        return HttpResponseForbidden("Method not allowed")
    req_obj = get_object_or_404(AttendanceCorrectionRequest.objects.select_for_update(), id=attendance_id)
    if not build_permission_flags(req_obj, request.user).get("can_edit"):
        messages.error(request, _("You do not have permission to delete this attachment."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    link = AttendanceCorrectionRequestAttachment.objects.filter(request_id=attendance_id, attendance_request_file_id=file_id).select_related("attendance_request_file").first()
    if not link:
        messages.error(request, _("Attachment not found."))
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    file_obj = link.attendance_request_file
    storage = getattr(getattr(file_obj, "file", None), "storage", None)
    file_name = getattr(getattr(file_obj, "file", None), "name", None)
    link.delete()
    try:
        file_obj.delete()
    finally:
        if storage and file_name:
            try:
                storage.delete(file_name)
            except Exception:
                pass
    messages.success(request, _("Attachment deleted."))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
