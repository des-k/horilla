"""
views.py

This module contains the view functions for handling HTTP requests and rendering
responses in your application.

Each view function corresponds to a specific URL route and performs the necessary
actions to handle the request, process data, and generate a response.

This module is part of the recruitment project and is intended to
provide the main entry points for interacting with the application's functionality.
"""

import logging
import uuid

from horilla.horilla_settings import DYNAMIC_URL_PATTERNS, HORILLA_DATE_FORMATS
from horilla.methods import remove_dynamic_url

logger = logging.getLogger(__name__)

import calendar
import contextlib
import io
import json
from collections import defaultdict
from datetime import date, datetime, timedelta
from urllib.parse import parse_qs

import pandas as pd
from django.contrib import messages
from django import forms
from django.core.paginator import Paginator
from django.core.validators import validate_ipv46_address
from django.db import transaction
from django.db.models import ProtectedError, Case, When, Value, IntegerField
from django.forms import ValidationError
from django.http import (
    HttpResponse,
    HttpResponseBadRequest,
    HttpResponseForbidden,
    HttpResponseRedirect,
    JsonResponse,
)
from django.shortcuts import redirect, render
from django.template.loader import render_to_string
from django.urls import reverse
from django.utils import timezone as django_timezone
from django.utils.timezone import now
from django.utils.translation import get_language, gettext as __
from django.utils.translation import gettext_lazy as _
from django.views.decorators.http import require_http_methods
from xhtml2pdf import pisa

from attendance.filters import (
    AttendanceActivityFilter,
    AttendanceActivityReGroup,
    AttendancePunchingHistoryFilter,
    AttendancePunchingHistoryReGroup,
    AttendanceFilters,
    AttendanceOverTimeFilter,
    AttendanceOvertimeReGroup,
    AttendanceReGroup,
    LateComeEarlyOutFilter,
    LateComeEarlyOutReGroup,
)
from attendance.forms import (
    AttendanceActivityExportForm,
    AttendanceExportForm,
    AttendanceForm,
    AttendanceOverTimeExportForm,
    AttendanceOverTimeForm,
    AttendanceRequestCommentForm,
    AttendanceUpdateForm,
    AttendanceValidationConditionForm,
    GraceTimeAssignForm,
    GraceTimeForm,
    LateComeEarlyOutExportForm,
    NewRequestForm,
)
from attendance.methods.utils import (
    Request,
    attendance_day_checking,
    format_time,
    is_reportingmanger,
    monthly_leave_days,
    paginator_qry,
    parse_date,
    parse_datetime,
    parse_time,
    sort_activity_dicts,
    strtime_seconds,
)
from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestStatus,
    AttendanceGeneralSetting,
    AttendancePunchingHistory,
    AttendanceLateComeEarlyOut,
    AttendanceOverTime,
    AttendanceRequestComment,
    AttendanceRequestFile,
    AttendanceValidationCondition,
    BatchAttendance,
    GraceTime,
    WorkRecords,
)
from attendance.views.handle_attendance_errors import handle_attendance_errors
from attendance.views.process_attendance_data import process_attendance_data
from attendance.services.punching_history import reconcile_attendance_punches
from attendance.services.attendance_access import can_access_attendance_scope_views, get_attendance_subject_employees, is_admin_employee
from base.forms import AttendanceAllowedIPForm
from base.methods import (
    choosesubordinates,
    closest_numbers,
    eval_validate,
    export_data,
    filtersubordinates,
    filtersubordinatesemployeemodel,
    generate_pdf,
    get_key_instances,
    get_pagination,
)
from base.models import (
    AttendanceAllowedIP,
    EmployeeShift,
    EmployeeShiftSchedule,
    TrackLateComeEarlyOut,
    WorkType,
)
from employee.filters import EmployeeFilter
from employee.models import Employee, EmployeeWorkInformation
from horilla.decorators import (
    hx_request_required,
    install_required,
    login_required,
    manager_can_enter,
    permission_required,
)
from notifications.signals import notify

# Monthly recap (Attendance → Attendances)
from attendance.services.month_params import normalize_month_yyyy_mm, require_month_yyyy_mm
from attendance.services.monthly_recap import (
    get_monthly_attendance_recap,
    get_monthly_attendance_rows,
)


def _sync_grace_time_shifts(grace_time, shifts):
    """Keep shift assignments in sync with the selected Grace Time form values."""
    selected_shifts = list(shifts or [])
    selected_ids = [shift.id for shift in selected_shifts if getattr(shift, "id", None)]

    EmployeeShift.objects.filter(grace_time_id=grace_time).exclude(id__in=selected_ids).update(
        grace_time_id=None
    )

    for shift in selected_shifts:
        if getattr(shift, "grace_time_id_id", None) != getattr(grace_time, "id", None):
            shift.grace_time_id = grace_time
            shift.save(update_fields=["grace_time_id"])


def attendance_validate(attendance):
    """
    This method is is used to check condition for at work in AttendanceValidationCondition
    model instance it return true if at work is smaller than condition
    args:
        attendance : attendance object
    """

    conditions = AttendanceValidationCondition.objects.all()
    # Set the default condition for 'at work' to 9:00 AM
    condition_for_at_work = strtime_seconds("09:00")
    if conditions.exists():
        condition_for_at_work = strtime_seconds(conditions[0].validation_at_work)
    at_work = strtime_seconds(attendance.attendance_worked_hour)
    return condition_for_at_work >= at_work


@login_required
def attendance_employee_month_view(request):
    """Attendance → Attendances: Monthly recap per employee.

    Filters (GET):
      - employee_id (or employee)
      - month in YYYY-MM
    """

    if not can_access_attendance_scope_views(user=request.user):
        return _punching_history_forbidden_response(request)

    employees_qs, _, _, default_employee_id = get_attendance_subject_employees(
        request,
        perm_codename="attendance.view_attendance",
        base_queryset=Employee.objects.filter(is_active=True).select_related("employee_work_info"),
    )

    # Resolve month
    current_month = django_timezone.localdate().strftime("%Y-%m")
    month = normalize_month_yyyy_mm(
        request.GET.get("month"),
        fallback_month=current_month,
        max_month=current_month,
    )

    # Resolve employee
    emp_id = request.GET.get("employee_id") or request.GET.get("employee")
    selected_employee = None
    if emp_id:
        try:
            selected_employee = employees_qs.filter(id=int(emp_id)).first()
        except Exception:
            selected_employee = None

    if selected_employee is None:
        selected_employee = employees_qs.filter(id=default_employee_id).first() if default_employee_id else None
        if selected_employee is None:
            selected_employee = employees_qs.first()

    rows = []
    summary = {
        "late_minutes": 0,
        "early_out_minutes": 0,
        "total_minutes": 0,
    }
    if selected_employee:
        recap = get_monthly_attendance_recap(selected_employee, month)
        rows = recap["rows"]
        summary = recap["summary"]

    context = {
        "employees": employees_qs,
        "selected_employee": selected_employee,
        "selected_month": month,
        "max_month": current_month,
        "rows": rows,
        "summary": summary,
    }
    return render(
        request,
        "attendance/attendance/attendance_monthly_recap.html",
        context,
    )


@login_required
def attendance_employee_month_export_pdf(request):
    """Export Attendance → Attendances (Monthly recap) as PDF.

    Query params (GET):
      - employee_id (required)
      - month (YYYY-MM, required)
      - lang (optional: en|id, default: en)
    """

    if not can_access_attendance_scope_views(user=request.user):
        return _punching_history_forbidden_response(request)

    employees_qs, _, _, _ = get_attendance_subject_employees(
        request,
        perm_codename="attendance.view_attendance",
        base_queryset=Employee.objects.filter(is_active=True).select_related("employee_work_info"),
    )

    emp_id = request.GET.get("employee_id")
    month = request.GET.get("month")
    lang = (request.GET.get("lang") or "en").strip().lower()
    if lang not in ("en", "id"):
        lang = "en"

    if not emp_id or not month:
        return HttpResponseBadRequest("employee_id and month are required")

    # Validate month
    try:
        month = require_month_yyyy_mm(month)
    except ValueError:
        return HttpResponseBadRequest("Invalid month format. Expected YYYY-MM")

    # Disallow future months (keep output aligned with UI)
    current_month = django_timezone.localdate().strftime("%Y-%m")
    month = normalize_month_yyyy_mm(month, fallback_month=current_month, max_month=current_month)
    year = int(month[:4])
    month_no = int(month[5:7])

    # Resolve employee within allowed queryset
    try:
        employee = employees_qs.filter(id=int(emp_id)).first()
    except Exception:
        employee = None
    if employee is None:
        return HttpResponseBadRequest("Invalid employee_id")

    # IMPORTANT: pass language into the shared helper so NOTE/Shift strings
    # match the UI rules for the requested language.
    recap = get_monthly_attendance_recap(employee, month, language=lang)
    rows = recap["rows"]

    # Header month display
    if lang == "id":
        month_names_id = [
            "Januari",
            "Februari",
            "Maret",
            "April",
            "Mei",
            "Juni",
            "Juli",
            "Agustus",
            "September",
            "Oktober",
            "November",
            "Desember",
        ]
        month_display = month_names_id[month_no - 1]
        title = "Rekap Absensi Bulanan"
    else:
        month_display = calendar.month_name[month_no]
        title = "Monthly Attendance Report"

    context = {
        "lang": lang,
        "title": title,
        "employee": employee,
        "month_display": month_display,
        "year": year,
        "rows": rows,
        "summary": recap["summary"],
    }

    filename = f"monthly_attendance_{employee.id}_{month}_{lang}.pdf"

    # Render HTML then convert to PDF using xhtml2pdf (pisa).
    # This avoids wkhtmltopdf dependency used by pdfkit.
    html_content = render_to_string("attendance/attendances/monthly_export_pdf.html", context)
    result = io.BytesIO()
    pdf_status = pisa.CreatePDF(src=html_content, dest=result)
    if pdf_status.err:
        logger.error("Error creating Monthly Recap PDF")
        return HttpResponse("Error generating PDF", status=500)

    response = HttpResponse(result.getvalue(), content_type="application/pdf")
    response["Content-Disposition"] = f'attachment; filename="{filename}"'
    return response


@login_required
@hx_request_required
def profile_attendance_tab(request):
    """
    This function is used to view attendance tab of an employee in profile view.

    Parameters:
    request (HttpRequest): The HTTP request object.
    emp_id (int): The id of the employee.

    Returns: return asset-request-tab template

    """
    user = request.user
    employee = user.employee_get
    employee_attendances = employee.employee_attendances.all()
    attendances_ids = json.dumps([instance.id for instance in employee_attendances])
    context = {
        "attendances": employee_attendances,
        "attendances_ids": attendances_ids,
    }
    return render(request, "tabs/profile-attendance-tab.html", context)


@login_required
@manager_can_enter("employee.view_employee")
def attendance_tab(request, emp_id):
    """
    This function is used to view attendance tab of an employee in individual view.

    Parameters:
    request (HttpRequest): The HTTP request object.
    emp_id (int): The id of the employee.

    Returns: return attendance-tab template
    """

    requests = AttendanceCorrectionRequest.objects.filter(
        employee_id=emp_id,
        status=AttendanceCorrectionRequestStatus.WAITING,
    )
    attendances_ids = json.dumps([instance.id for instance in requests])
    validate_attendances = Attendance.objects.filter(
        attendance_validated=False, employee_id=emp_id
    )
    validate_attendances_ids = json.dumps(
        [instance.id for instance in validate_attendances]
    )
    accounts = AttendanceOverTime.objects.filter(employee_id=emp_id)
    accounts_ids = json.dumps([instance.id for instance in accounts])

    context = {
        "requests": requests,
        "attendances_ids": attendances_ids,
        "accounts": accounts,
        "accounts_ids": accounts_ids,
        "validate_attendances": validate_attendances,
        "validate_attendances_ids": validate_attendances_ids,
    }
    return render(request, "tabs/attendance-tab.html", context=context)


@login_required
@hx_request_required
@manager_can_enter("attendance.add_attendance")
def attendance_create(request):
    """
    This method is used to render attendance create form and save if it is valid
    """
    if request.GET.get("previous_url"):
        data = request.GET.dict()
        employee_list = request.GET.getlist("employee_id")
        data["employee_id"] = employee_list
        form = AttendanceForm(initial=data)
    else:
        form = AttendanceForm()
    form = choosesubordinates(request, form, "attendance.add_attendance")
    if request.method == "POST":
        form = AttendanceForm(request.POST)
        form = choosesubordinates(request, form, "attendance.add_attendance")
        if form.is_valid():
            form.save()
            messages.success(request, _("Attendance added."))
            response = render(
                request, "attendance/attendance/form.html", {"form": form}
            )
            return HttpResponse(
                response.content.decode("utf-8") + "<script>location.reload();</script>"
            )
    return render(request, "attendance/attendance/form.html", {"form": form})


@login_required
@permission_required("attendance.add_attendance")
def attendance_excel(_request):
    """
    Generate an empty Excel template for attendance data with predefined columns.

    Returns:
        HttpResponse: An HTTP response containing an empty Excel template with predefined columns.
    """
    try:
        columns = [
            "Badge ID",
            "Shift",
            "Work type",
            "Attendance date",
            "Check-in date",
            "Check-in",
            "Check-out date",
            "Check-out",
            "Worked hour",
            "Minimum hour",
        ]
        data_frame = pd.DataFrame(columns=columns)
        response = HttpResponse(content_type="application/ms-excel")
        response["Content-Disposition"] = 'attachment; filename="my_excel_file.xlsx"'
        data_frame.to_excel(response, index=False)
        return response
    except Exception as exception:
        return HttpResponse(exception)


@login_required
@permission_required("attendance.add_attendance")
def attendance_import(request):
    """
    Save the import of attendance data from an uploaded Excel file, validate the data,
    and return an Excel file with error details if validation fails for anyone
    of the attendance data.

    Parameters:
        request (HttpRequest): The HTTP request object containing the uploaded Excel file.

    Returns:
        HttpResponse or redirect: An HTTP response with an Excel file containing error details
        if validation fails, or a redirect to the attendance view if successful.
    """
    if request.method == "POST":
        file = request.FILES["attendance_import"]
        file_extension = file.name.split(".")[-1].lower()
        data_frame = (
            pd.read_csv(file) if file_extension == "csv" else pd.read_excel(file)
        )
        attendance_dicts = data_frame.to_dict("records")
        attendance_import = process_attendance_data(attendance_dicts)
        path_info = None
        if attendance_import:
            path_info = handle_attendance_errors(attendance_import)

    created_attendance_count = len(attendance_dicts) - len(attendance_import)
    context = {
        "created_count": created_attendance_count,
        "error_count": len(attendance_import),
        "model": _("Attendance"),
        "path_info": path_info,
    }
    html = render_to_string("import_popup.html", context)
    return HttpResponse(html)


@login_required
def attendance_export(request):
    resolver_match = request.resolver_match
    if (
        resolver_match
        and resolver_match.url_name
        and resolver_match.url_name == "attendance-info-export-form"
    ):
        return render(
            request,
            "attendance/attendance/export_filter.html",
            context={
                "export": AttendanceFilters(queryset=Attendance.objects.all()),
                "export_form": AttendanceExportForm(),
            },
        )
    return export_data(
        request=request,
        model=Attendance,
        filter_class=AttendanceFilters,
        form_class=AttendanceExportForm,
        file_name="Attendance_export",
    )


@login_required
@manager_can_enter("attendance.view_attendance")
def attendance_view(request):
    """
    This method is used to view attendances.
    """
    previous_data = request.GET.urlencode()
    form = AttendanceForm()
    condition = AttendanceValidationCondition.objects.first()
    minot = strtime_seconds("00:00")
    if condition is not None and condition.minimum_overtime_to_approve is not None:
        minot = strtime_seconds(condition.minimum_overtime_to_approve)
    validate_attendances = Attendance.objects.filter(
        attendance_validated=False, employee_id__is_active=True
    )
    attendances = Attendance.objects.filter(
        attendance_validated=True, employee_id__is_active=True
    )
    # ot_attendances = Attendance.objects.filter(
    #     overtime_second__gte=minot,
    #     attendance_validated=True,
    #     employee_id__is_active=True,
    # )
    # for attendance in ot_attendances:
    #     attendance.min_ot_achieved = True
    ot_attendances = Attendance.objects.filter(
        overtime_second__gt=0,
        attendance_validated=True,
        employee_id__is_active=True,
    )
    filter_obj = AttendanceFilters(request.GET, queryset=attendances)
    attendances = filtersubordinates(
        request, filter_obj.qs, "attendance.view_attendance"
    )
    validate_attendances = AttendanceFilters(
        request.GET, queryset=validate_attendances
    ).qs
    validate_attendances = filtersubordinates(
        request, validate_attendances, "attendance.view_attendance"
    )
    ot_attendances = AttendanceFilters(request.GET, queryset=ot_attendances).qs
    ot_attendances = filtersubordinates(
        request, ot_attendances, "attendance.view_attendance"
    )
    check_attendance = Attendance.objects.all()
    if check_attendance.exists():
        template = "attendance/attendance/attendance_view.html"
    else:
        template = "attendance/attendance/attendance_empty.html"
    validate_attendances_ids = json.dumps(
        [
            instance.id
            for instance in paginator_qry(
                validate_attendances, request.GET.get("vpage")
            ).object_list
        ]
    )
    ot_attendances_ids = json.dumps(
        [
            instance.id
            for instance in paginator_qry(
                ot_attendances, request.GET.get("opage")
            ).object_list
        ]
    )
    attendances_ids = json.dumps(
        [
            instance.id
            for instance in paginator_qry(
                attendances, request.GET.get("page")
            ).object_list
        ]
    )
    return render(
        request,
        template,
        {
            "form": form,
            # "validate_attendances": paginator_qry(
            #     validate_attendances, request.GET.get("vpage")
            # ),
            # "attendances": paginator_qry(attendances, request.GET.get("page")),
            # "overtime_attendances": paginator_qry(
            #     ot_attendances, request.GET.get("opage")
            # ),
            "validate_attendances_ids": validate_attendances_ids,
            "ot_attendances_ids": ot_attendances_ids,
            "attendances_ids": attendances_ids,
            "f": filter_obj,
            "pd": previous_data,
            "gp_fields": AttendanceReGroup.fields,
        },
    )


@login_required
@hx_request_required
@manager_can_enter("attendance.change_attendance")
def attendance_update(request, obj_id):
    """
    This method render form to update attendance and save if the form is valid
    args:
        obj_id : attendance id
    """
    attendance = Attendance.objects.get(id=obj_id)
    if request.GET.get("previous_url"):
        form = AttendanceUpdateForm(initial=request.GET.dict())
    else:
        form = AttendanceUpdateForm(
            instance=attendance,
        )
    form = choosesubordinates(request, form, "attendance.change_attendance")
    if request.method == "POST":
        form = AttendanceUpdateForm(request.POST, instance=attendance)
        form = choosesubordinates(request, form, "attendance.change_attendance")
        if form.is_valid():
            form.save()
            messages.success(request, _("Attendance Updated."))
            urlencode = request.GET.urlencode()
            modified_url = f"/attendance/attendance-view/?{urlencode}"
            return HttpResponse(
                f"""
                    <script>
                        window.location.reload();
                    </script>
                """
            )
    return render(
        request,
        "attendance/attendance/update_form.html",
        {"form": form, "urlencode": request.GET.urlencode(), "obj_id": obj_id},
    )


@login_required
@permission_required("attendance.delete_attendance")
@require_http_methods(["POST"])
def attendance_delete(request, obj_id):
    """
    This method is used to delete attendance.
    args:
        obj_id : attendance id
    """
    try:
        attendance = Attendance.objects.get(id=obj_id)
        month = attendance.attendance_date
        month = month.strftime("%B").lower()
        overtime = attendance.employee_id.employee_overtime.filter(month=month).last()
        if overtime is not None:
            if attendance.attendance_overtime_approve:
                # Subtract overtime of this attendance
                total_overtime = strtime_seconds(overtime.overtime)
                attendance_overtime_seconds = strtime_seconds(
                    attendance.attendance_overtime
                )
                if total_overtime > attendance_overtime_seconds:
                    total_overtime = total_overtime - attendance_overtime_seconds
                else:
                    total_overtime = attendance_overtime_seconds - total_overtime
                overtime.overtime = format_time(total_overtime)
                overtime.save()
            try:
                attendance.delete()
                messages.success(request, _("Attendance deleted."))
            except ProtectedError as e:
                model_verbose_names_set = set()
                for obj in e.protected_objects:
                    model_verbose_names_set.add(__(obj._meta.verbose_name.capitalize()))
                model_names_str = ", ".join(model_verbose_names_set)
                messages.error(
                    request,
                    _(
                        ("An attendance entry for {} already exists.").format(
                            model_names_str
                        )
                    ),
                )
    except (Attendance.DoesNotExist, OverflowError):
        messages.error(request, _("Attendance Does not exists.."))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@permission_required("attendance.delete_attendance")
@require_http_methods(["POST"])
def attendance_bulk_delete(request):
    """
    This method is used to delete a bulk of attendances
    """
    success_count = 0
    error_messages = []
    ids = request.POST.getlist("ids", "[]")
    attendances = Attendance.objects.filter(id__in=ids)
    employee_ids = attendances.values_list("employee_id", flat=True)
    overtimes = AttendanceOverTime.objects.filter(
        employee_id__in=employee_ids
    ).in_bulk()

    with transaction.atomic():
        for attendance in attendances:
            try:
                month = attendance.attendance_date.strftime("%B").lower()
                overtime = overtimes.get(attendance.employee_id.id)

                if overtime and attendance.attendance_overtime_approve:
                    # Calculate the new overtime
                    total_overtime = strtime_seconds(overtime.overtime)
                    attendance_overtime_seconds = strtime_seconds(
                        attendance.attendance_overtime
                    )
                    total_overtime = abs(total_overtime - attendance_overtime_seconds)
                    overtime.overtime = format_time(total_overtime)
                    overtime.save()

                attendance.delete()
                success_count += 1

            except ProtectedError as e:
                model_verbose_names_set = {
                    __(obj._meta.verbose_name.capitalize())
                    for obj in e.protected_objects
                }
                model_names_str = ", ".join(model_verbose_names_set)
                error_messages.append(
                    f"An attendance entry is protected by: {model_names_str}."
                )

    # Build response messages
    if success_count:
        messages.success(request, f"{success_count} attendances deleted successfully.")
    for error in error_messages:
        messages.error(request, error)
    return redirect("/attendance/attendance-search")


@login_required
def view_my_attendance(request):
    """
    This method is used to view self attendances of employee
    """
    user = request.user
    try:
        employee = user.employee_get
    except:
        return redirect("/employee/employee-profile")
    employee = user.employee_get
    employee_attendances = employee.employee_attendances.all()
    filter = AttendanceFilters()
    if employee_attendances.exists():
        template = "attendance/own_attendance/view_own_attendances.html"
    else:
        template = "attendance/own_attendance/own_empty.html"
    attendances_ids = json.dumps(
        [
            instance.id
            for instance in paginator_qry(
                employee_attendances, request.GET.get("page")
            ).object_list
        ]
    )
    return render(
        request,
        template,
        {
            "attendances": paginator_qry(employee_attendances, request.GET.get("page")),
            "attendances_ids": attendances_ids,
            "f": filter,
            "gp_fields": AttendanceReGroup.fields,
        },
    )


@login_required
@hx_request_required
@manager_can_enter("attendance.add_attendanceovertime")
def attendance_overtime_create(request):
    """
    This method is used to render overtime creating form and save if the form is valid
    """
    form = AttendanceOverTimeForm()
    form = choosesubordinates(request, form, "attendance.add_attendanceovertime")
    if request.method == "POST":
        form = AttendanceOverTimeForm(request.POST)
        form = choosesubordinates(request, form, "attendance.add_attendanceovertime")
        if form.is_valid():
            form.save()
            messages.success(request, _("Attendance account added."))
            response = render(
                request, "attendance/attendance_account/form.html", {"form": form}
            )
            return HttpResponse(
                response.content.decode("utf-8") + "<script>location.reload();</script>"
            )
    return render(request, "attendance/attendance_account/form.html", {"form": form})


@login_required
def attendance_overtime_view(request):
    """
    This method is used to view attendance account or overtime account.
    """
    previous_data = request.GET.urlencode()
    filter_obj = AttendanceOverTimeFilter(request.GET)
    if filter_obj.qs.exists():
        template = "attendance/attendance_account/attendance_overtime_view.html"
    else:
        template = "attendance/attendance_account/overtime_empty.html"
    self_account = filter_obj.qs.filter(employee_id__employee_user_id=request.user)
    accounts = filtersubordinates(
        request, filter_obj.qs, "attendance.view_attendanceactivity"
    )
    accounts = accounts | self_account
    accounts = accounts.distinct()
    form = AttendanceOverTimeForm()
    form = choosesubordinates(request, form, "attendance.add_attendanceovertime")
    data_dict = parse_qs(previous_data)
    get_key_instances(AttendanceOverTime, data_dict)
    return render(
        request,
        template,
        {
            "accounts": paginator_qry(accounts, request.GET.get("page")),
            "form": form,
            "pd": previous_data,
            "f": filter_obj,
            "gp_fields": AttendanceOvertimeReGroup.fields,
            "filter_dict": data_dict,
        },
    )


def attendance_account_export(request):
    if request.META.get("HTTP_HX_REQUEST") == "true":
        context = {
            "export_obj": AttendanceOverTimeFilter(),
            "export_fields": AttendanceOverTimeExportForm(),
        }

        return render(
            request,
            "attendance/attendance_account/attendance_account_export_filter.html",
            context=context,
        )
    return export_data(
        request=request,
        model=AttendanceOverTime,
        filter_class=AttendanceOverTimeFilter,
        form_class=AttendanceOverTimeExportForm,
        file_name="Attendance_Account",
    )


@login_required
@manager_can_enter("attendance.change_attendanceovertime")
@hx_request_required
def attendance_overtime_update(request, obj_id):
    """
    This method is used to update attendance overtime and save if the forms is valid
    args:
        obj_id : attendance overtime id
    """
    overtime = AttendanceOverTime.objects.get(id=obj_id)
    form = AttendanceOverTimeForm(instance=overtime)
    form = choosesubordinates(request, form, "attendance.change_attendanceovertime")
    if request.method == "POST":
        form = AttendanceOverTimeForm(request.POST, instance=overtime)
        form = choosesubordinates(request, form, "attendance.change_attendanceovertime")
        if form.is_valid():
            form.save()
            messages.success(request, _("Attendance account updated successfully."))
            response = render(
                request,
                "attendance/attendance_account/update_form.html",
                {"form": form},
            )
            return HttpResponse(
                response.content.decode("utf-8") + "<script>location.reload();</script>"
            )
    return render(
        request, "attendance/attendance_account/update_form.html", {"form": form}
    )


@login_required
@permission_required("attendance.delete_attendanceoverTime")
@require_http_methods(["POST"])
def attendance_overtime_delete(request, obj_id):
    """
    This method is used to delete attendance overtime
    args:
        obj_id : attendance overtime id
    """
    previous_data = request.GET.urlencode()
    hx_target = request.META.get("HTTP_HX_TARGET", None)
    try:
        attendance = AttendanceOverTime.objects.get(id=obj_id)
        attendance.delete()
        if hx_target == "ot-table":
            messages.success(request, _("Hour account deleted."))
    except (AttendanceOverTime.DoesNotExist, OverflowError, ValueError):
        if hx_target == "ot-table":
            messages.error(request, _("Hour account not found"))
    except ProtectedError:
        if hx_target == "ot-table":
            messages.error(request, _("You cannot delete this hour account"))
    if hx_target and hx_target == "ot-table":
        hour_account = AttendanceOverTime.objects.all()
        if hour_account.exists():
            return redirect(f"/attendance/attendance-overtime-search?{previous_data}")
        else:
            return HttpResponse("<script>window.location.reload()</script>")
    elif hx_target:
        return HttpResponse()


@login_required
@permission_required("attendance.delete_attendanceovertime")
def attendance_account_bulk_delete(request):
    """
    This method is used to bulk delete for Payslip
    """
    ids = request.POST["ids"]
    ids = json.loads(ids)
    for id in ids:
        try:
            hour_account = AttendanceOverTime.objects.get(id=id)
            hour_account.delete()
            messages.success(
                request,
                _("{employee} hour account deleted.").format(
                    employee=hour_account.employee_id
                ),
            )
        except AttendanceOverTime.DoesNotExist:
            messages.error(request, _("Hour account not found."))
        except ProtectedError:
            messages.error(
                request,
                _("You cannot delete {hour_account}").format(hour_account=hour_account),
            )
    return JsonResponse({"message": "Success"})


@login_required
def attendance_activity_view(request):
    """
    This method will render a template to view all attendance activities
    """
    if not _can_access_attendance_activity(request):
        return _attendance_activity_forbidden_response(request)

    employee_options, show_employee_filter, _, _ = _get_attendance_activity_employee_scope(
        request
    )
    filter_data = _build_attendance_activity_filter_data(request)
    request_copy = filter_data.copy()
    request_copy.pop("page", None)
    previous_data = request_copy.urlencode()

    queryset = _scoped_attendance_activity_queryset(request).order_by("-pk")
    filter_obj = AttendanceActivityFilter(filter_data, queryset)
    filter_obj.form.fields["employee_id"].queryset = employee_options
    attendance_activities = filter_obj.qs.order_by("-pk")

    data_dict = parse_qs(previous_data)
    get_key_instances(AttendanceActivity, data_dict)
    keys_to_remove = [key for key, value in data_dict.items() if value in (["unknown"], [""])]
    for key in keys_to_remove:
        data_dict.pop(key)

    activity_ids = json.dumps(
        [instance.id for instance in paginator_qry(attendance_activities, None)]
    )
    paged_activities = paginator_qry(attendance_activities, request.GET.get("page"))
    _decorate_attendance_activity_payload(paged_activities)

    return render(
        request,
        "attendance/attendance_activity/attendance_activity_view.html",
        {
            "data": paged_activities,
            "pd": previous_data,
            "f": filter_obj,
            "gp_fields": AttendanceActivityReGroup.fields,
            "activity_ids": activity_ids,
            "filter_dict": data_dict,
            "show_employee_filter": show_employee_filter,
            "activity_filter_data": filter_data,
            "self_employee": getattr(request.user, "employee_get", None),
            "selected_scope_employee": _resolve_selected_scope_employee(
                employee_options, filter_data.get("employee_id")
            ),
            "employee_options": employee_options,
            "group_field": filter_data.get("field", ""),
        },
    )


def _safe_request_instance_ids(request):
    instance_ids_json = request.GET.get("instances_ids", "[]")
    if not instance_ids_json or instance_ids_json == "None":
        return "[]", []
    try:
        instance_ids = json.loads(instance_ids_json)
    except (TypeError, ValueError, json.JSONDecodeError):
        return "[]", []
    if not isinstance(instance_ids, list):
        return "[]", []
    normalized_ids = []
    for value in instance_ids:
        try:
            normalized_ids.append(int(value))
        except (TypeError, ValueError):
            continue
    return json.dumps(normalized_ids), normalized_ids


def _scoped_attendance_activity_queryset(request):
    queryset = AttendanceActivity.objects.all()
    employee_options, _, _, _ = _get_attendance_activity_employee_scope(request)
    employee_ids = list(employee_options.values_list("id", flat=True))
    if not employee_ids:
        return queryset.none()
    return queryset.filter(employee_id_id__in=employee_ids).distinct()


def _normalized_activity_language() -> str:
    lang = (get_language() or "en").lower()
    return "id" if lang.startswith("id") else "en"


def _extract_attendance_activity_objects(data):
    if data is None:
        return []
    if hasattr(data, "object_list"):
        object_list = list(data.object_list)
        if all(isinstance(obj, AttendanceActivity) for obj in object_list):
            return object_list
        data = object_list

    activities = []
    try:
        iterable = list(data)
    except TypeError:
        iterable = []

    for entry in iterable:
        if isinstance(entry, dict):
            page = entry.get("list")
            if hasattr(page, "object_list"):
                activities.extend(
                    [obj for obj in list(page.object_list) if isinstance(obj, AttendanceActivity)]
                )
                continue
        if isinstance(entry, AttendanceActivity):
            activities.append(entry)
    return activities


def _local_date_from_datetime(value):
    if not value:
        return None
    try:
        if django_timezone.is_aware(value):
            value = django_timezone.localtime(value)
        return value.date()
    except Exception:
        return None


def _format_activity_raw_time(value):
    try:
        return value.strftime("%H:%M") if value else "-"
    except Exception:
        return "-"


def _choice_display(instance, field_name):
    if not instance:
        return None
    getter = getattr(instance, f"get_{field_name}_display", None)
    try:
        if callable(getter):
            value = getter()
            if value:
                return str(value)
    except Exception:
        pass
    raw_value = getattr(instance, field_name, None)
    if raw_value in (None, ""):
        return None
    return str(raw_value)


def _location_display(location):
    if not location:
        return "-", None
    if isinstance(location, dict):
        lat = location.get("lat", location.get("latitude"))
        lng = location.get("lng", location.get("longitude"))
        if lat is not None and lng is not None:
            return f"{lat}, {lng}", f"https://www.google.com/maps?q={lat},{lng}"
    return str(location), None


def _decorate_attendance_activity_records(activities, *, language=None):
    activities = [obj for obj in (activities or []) if isinstance(obj, AttendanceActivity)]
    if not activities:
        return

    language = language or _normalized_activity_language()
    attendance_index = {}
    employee_ids = sorted({obj.employee_id_id for obj in activities if obj.employee_id_id})
    attendance_dates = sorted({obj.attendance_date for obj in activities if obj.attendance_date})
    if employee_ids and attendance_dates:
        attendance_index = {
            (att.employee_id_id, att.attendance_date): att
            for att in Attendance.objects.filter(
                employee_id_id__in=employee_ids,
                attendance_date__in=attendance_dates,
            ).select_related("shift_id", "work_type_id")
        }

    recap_cache = {}
    for activity in activities:
        recap_row = None
        if activity.employee_id_id and activity.attendance_date:
            month_key = activity.attendance_date.strftime("%Y-%m")
            cache_key = (activity.employee_id_id, month_key)
            if cache_key not in recap_cache:
                rows = get_monthly_attendance_rows(
                    activity.employee_id,
                    month_key,
                    language=language,
                )
                recap_cache[cache_key] = {
                    row.attendance_date: row
                    for row in rows
                }
            recap_row = recap_cache.get(cache_key, {}).get(activity.attendance_date)

        attendance = attendance_index.get((activity.employee_id_id, activity.attendance_date))

        activity.display_note = getattr(recap_row, "note", "-") or "-"
        activity.display_check_in = (
            getattr(recap_row, "check_in", None)
            or _format_activity_raw_time(getattr(activity, "clock_in", None))
        )
        activity.display_check_out = (
            getattr(recap_row, "check_out", None)
            or _format_activity_raw_time(getattr(activity, "clock_out", None))
        )
        activity.display_clock_in_date = _local_date_from_datetime(
            getattr(recap_row, "final_in_datetime", None)
        )
        activity.display_clock_out_date = _local_date_from_datetime(
            getattr(recap_row, "final_out_datetime", None)
        )
        activity.display_work_type = getattr(recap_row, "work_type", None) or "-"
        activity.display_shift_information = getattr(recap_row, "shift_information", None) or "-"
        activity.display_late = getattr(recap_row, "late", None) or "00:00"
        activity.display_early_out = getattr(recap_row, "early_out", None) or "00:00"

        has_final_in = bool(getattr(recap_row, "final_in_datetime", None))
        has_final_out = bool(getattr(recap_row, "final_out_datetime", None))

        in_location = None
        out_location = None
        in_image = None
        out_image = None
        in_source_label = "-"
        out_source_label = "-"
        in_mode_label = "-"
        out_mode_label = "-"

        if has_final_in:
            in_source_label = (
                _choice_display(attendance, "attendance_clock_in_channel")
                or _choice_display(activity, "clock_in_channel")
                or "-"
            )
            in_mode_label = (
                _choice_display(attendance, "attendance_clock_in_mode")
                or _choice_display(activity, "clock_in_mode")
                or getattr(recap_row, "display_in_mode", None)
                or "-"
            )
            in_location = getattr(attendance, "attendance_clock_in_location", None) or getattr(activity, "clock_in_location", None)
            in_image = getattr(attendance, "attendance_clock_in_image", None) or getattr(activity, "clock_in_image", None)

        if has_final_out:
            out_source_label = (
                _choice_display(attendance, "attendance_clock_out_channel")
                or _choice_display(activity, "clock_out_channel")
                or "-"
            )
            out_mode_label = (
                _choice_display(attendance, "attendance_clock_out_mode")
                or _choice_display(activity, "clock_out_mode")
                or getattr(recap_row, "display_out_mode", None)
                or "-"
            )
            out_location = getattr(attendance, "attendance_clock_out_location", None) or getattr(activity, "clock_out_location", None)
            out_image = getattr(attendance, "attendance_clock_out_image", None) or getattr(activity, "clock_out_image", None)

        activity.display_clock_in_source = in_source_label
        activity.display_clock_out_source = out_source_label
        activity.display_clock_in_mode = in_mode_label
        activity.display_clock_out_mode = out_mode_label
        activity.display_clock_in_image = in_image
        activity.display_clock_out_image = out_image
        activity.display_clock_in_location = in_location
        activity.display_clock_out_location = out_location
        activity.display_clock_in_location_text, activity.display_clock_in_map_url = _location_display(in_location)
        activity.display_clock_out_location_text, activity.display_clock_out_map_url = _location_display(out_location)


def _decorate_attendance_activity_payload(data, *, language=None):
    _decorate_attendance_activity_records(
        _extract_attendance_activity_objects(data),
        language=language,
    )
    return data


def _can_access_attendance_activity(request) -> bool:
    return can_access_attendance_scope_views(user=request.user)


def _attendance_activity_forbidden_response(request):
    if request.headers.get("HX-Request") == "true":
        return render(request, "decorator_404.html", status=403)
    return HttpResponseForbidden(_("You dont have permission."))


def _get_attendance_activity_employee_scope(request):
    """
    Returns:
    - employee_options: queryset employee yang boleh muncul di filter
    - show_employee_filter: apakah dropdown employee ditampilkan
    - can_view_all: apakah user punya akses global semua employee
    - default_employee_id: employee default yang dipilih untuk user ini
    """
    return get_attendance_subject_employees(
        request,
        perm_codename="attendance.view_attendanceactivity",
        base_queryset=Employee.objects.all(),
    )


def _resolve_selected_scope_employee(employee_options, selected_employee_id):
    if selected_employee_id not in (None, "", "all"):
        try:
            employee = employee_options.filter(id=selected_employee_id).first()
        except (TypeError, ValueError):
            employee = None
        if employee is not None:
            return employee
    return employee_options.first()


def _build_attendance_activity_filter_data(request):
    filter_data = request.GET.copy()
    today = django_timezone.localdate().isoformat()

    has_exact_attendance_date = bool(filter_data.get("attendance_date"))
    if not has_exact_attendance_date:
        if not filter_data.get("attendance_date_from"):
            filter_data["attendance_date_from"] = today
        if not filter_data.get("attendance_date_till"):
            filter_data["attendance_date_till"] = today

    _, _, _, default_employee_id = _get_attendance_activity_employee_scope(request)

    if default_employee_id is not None and not filter_data.get("employee_id"):
        filter_data["employee_id"] = str(default_employee_id)

    return filter_data


@login_required
def activity_single_view(request, obj_id):
    request_copy = request.GET.copy()
    request_copy.pop("instances_ids", None)
    previous_data = request_copy.urlencode()
    activity = _scoped_attendance_activity_queryset(request).filter(id=obj_id).select_related("employee_id", "shift_day").first()

    instance_ids_json, instance_ids = _safe_request_instance_ids(request)
    previous_instance, next_instance = closest_numbers(instance_ids, obj_id)
    if activity:
        _decorate_attendance_activity_records([activity])

    context = {
        "pd": previous_data,
        "activity": activity,
        "previous_instance": previous_instance,
        "next_instance": next_instance,
        "instance_ids_json": instance_ids_json,
    }
    if activity:
        attendance = Attendance.objects.filter(
            employee_id=activity.employee_id,
            attendance_date=activity.attendance_date,
        ).select_related("shift_id", "work_type_id").first()
        context["attendance"] = attendance

    return render(
        request,
        "attendance/attendance_activity/single_attendance_activity.html",
        context=context,
    )


@login_required
@permission_required("attendance.delete_attendanceactivity")
@require_http_methods(["POST", "DELETE"])
def attendance_activity_delete(request, obj_id):
    """
    This method is used to delete attendance activity
    args:
        obj_id : attendance activity id
    """
    request_copy = request.GET.copy()
    request_copy.pop("instances_ids", None)
    previous_data = request_copy.urlencode()
    try:
        AttendanceActivity.objects.get(id=obj_id).delete()
        messages.success(request, _("Attendance activity deleted"))
    except AttendanceActivity.DoesNotExist:
        messages.error(request, _("Attendance activity Does not exists.."))
    except ProtectedError:
        messages.error(request, _("You cannot delete this activity"))
    instance_ids_json, instances_list = _safe_request_instance_ids(request)
    if not instances_list:
        return redirect(f"/attendance/attendance-activity-search?{previous_data}")

    if obj_id in instances_list:
        instances_list.remove(obj_id)
    previous_instance, next_instance = closest_numbers(instances_list, obj_id)
    if next_instance is None:
        return redirect(f"/attendance/attendance-activity-search?{previous_data}")
    return redirect(
        f"/attendance/attendance-activity-single-view/{next_instance}/?{previous_data}&instances_ids={json.dumps(instances_list)}"
    )


@login_required
@permission_required("attendance.delete_attendanceactivity")
@require_http_methods(["POST"])
def attendance_activity_bulk_delete(request):
    """
    Deletes a bulk of AttendanceActivity records based on a list of IDs.
    """
    try:
        ids_json = request.POST.get("ids", "[]")

        try:
            ids = json.loads(ids_json)
        except json.JSONDecodeError:
            messages.error(request, _("Invalid list of IDs provided."))
            return HttpResponse("<script>$('.filterButton')[0].click()</script>")

        try:
            ids = [int(i) for i in ids]
        except (ValueError, TypeError):
            messages.error(request, _("Invalid list of IDs provided."))
            return HttpResponse("<script>$('.filterButton')[0].click()</script>")

        if not ids:
            messages.warning(
                request, _("No attendance activities selected for deletion.")
            )
            return HttpResponse("<script>$('.filterButton')[0].click()</script>")

        # Perform the delete operation in a transaction
        with transaction.atomic():
            activities = AttendanceActivity.objects.filter(id__in=ids)
            count = activities.count()
            activities.delete()

        if count > 0:
            messages.success(
                request,
                _("{count} attendance activities deleted successfully.").format(
                    count=count
                ),
            )
        else:
            messages.info(
                request,
                _("No matching attendance activities were found to delete."),
            )

    except Exception as e:
        logger.exception("Error during bulk delete of attendance activities")
        messages.error(
            request,
            _("Failed to delete attendance activities: {error}").format(error=str(e)),
        )

    return HttpResponse("<script>$('.filterButton')[0].click()</script>")


def _can_access_punching_history(request) -> bool:
    return can_access_attendance_scope_views(user=request.user)


def _punching_history_forbidden_response(request):
    if request.headers.get("HX-Request") == "true":
        return render(request, "decorator_404.html", status=403)
    return HttpResponseForbidden(_("You dont have permission."))


def _show_punching_history_audit_fields(request) -> bool:
    user = getattr(request, "user", None)
    employee = getattr(user, "employee_get", None) if user is not None else None
    return bool(is_admin_employee(employee=employee, user=user))


def _scoped_punching_history_queryset(request):
    queryset = AttendancePunchingHistory.objects.select_related("employee_id", "attendance_id").all()
    employee_options, _, _, _ = _get_punching_history_employee_scope(request)
    employee_ids = list(employee_options.values_list("id", flat=True))
    if not employee_ids:
        return queryset.none()
    return queryset.filter(employee_id_id__in=employee_ids).distinct()

def _get_punching_history_employee_scope(request):
    """
    Returns:
    - employee_options: queryset employee yang boleh muncul di filter
    - show_employee_filter: apakah dropdown employee ditampilkan
    - can_view_all: apakah user punya akses global semua employee
    - default_employee_id: employee default yang dipilih untuk user ini
    """
    return get_attendance_subject_employees(
        request,
        perm_codename="attendance.view_attendancepunchinghistory",
        base_queryset=Employee.objects.all(),
    )
        
def _build_punching_history_filter_data(request):
    filter_data = request.GET.copy()
    today = django_timezone.localdate().isoformat()

    if not filter_data.get("punch_date_from"):
        filter_data["punch_date_from"] = today
    if not filter_data.get("punch_date_till"):
        filter_data["punch_date_till"] = today

    _, _, _, default_employee_id = _get_punching_history_employee_scope(request)

    if default_employee_id is not None and not filter_data.get("employee_id"):
        filter_data["employee_id"] = str(default_employee_id)

    return filter_data

@login_required
def attendance_punching_history_view(request):
    if not _can_access_punching_history(request):
        return _punching_history_forbidden_response(request)

    employee_options, show_employee_filter, _, _ = _get_punching_history_employee_scope(request)

    filter_data = _build_punching_history_filter_data(request)
    request_copy = filter_data.copy()
    request_copy.pop("page", None)
    previous_data = request_copy.urlencode()

    queryset = _scoped_punching_history_queryset(request).order_by("-punch_timestamp", "-id")
    filter_obj = AttendancePunchingHistoryFilter(filter_data, queryset)
    filter_obj.form.fields["employee_id"].queryset = employee_options

    data = filter_obj.qs.order_by("-punch_timestamp", "-id")
    page_obj = paginator_qry(data, request.GET.get("page"))

    return render(
        request,
        "attendance/punching_history/punching_history_view.html",
        {
            "data": page_obj,
            "pd": previous_data,
            "f": filter_obj,
            "gp_fields": AttendancePunchingHistoryReGroup.fields,
            "punch_ids": json.dumps([instance.id for instance in page_obj]),
            "show_employee_filter": show_employee_filter,
            "punch_filter_data": filter_data,
            "show_audit_fields": _show_punching_history_audit_fields(request),
            "self_employee": getattr(request.user, "employee_get", None),
            "selected_scope_employee": _resolve_selected_scope_employee(
                employee_options, filter_data.get("employee_id")
            ),
            "employee_options": employee_options,
        },
    )

@login_required
def punching_history_single_view(request, obj_id):
    if not _can_access_punching_history(request):
        return _punching_history_forbidden_response(request)
    request_copy = request.GET.copy()
    request_copy.pop("instances_ids", None)
    previous_data = request_copy.urlencode()
    punch = _scoped_punching_history_queryset(request).filter(id=obj_id).first()
    instance_ids_json, instance_ids = _safe_request_instance_ids(request)
    previous_instance, next_instance = closest_numbers(instance_ids, obj_id)
    return render(
        request,
        "attendance/punching_history/single_punching_history.html",
        {
            "pd": previous_data,
            "punch": punch,
            "previous_instance": previous_instance,
            "next_instance": next_instance,
            "instance_ids_json": instance_ids_json,
        },
    )


def process_activity_dicts(activity_dicts):
    from attendance.views.clock_in_out import clock_in, clock_out

    if not activity_dicts:
        return []

    sorted_activity_dicts = sort_activity_dicts(activity_dicts)
    error_dicts = []  # List to store dictionaries with errors

    for activity in sorted_activity_dicts:
        badge_id = activity.get("Badge ID")
        if not badge_id:
            activity["Error 1"] = "Please add the Badge ID column in the Excel sheet."
            error_dicts.append(activity)
            continue

        employee = Employee.objects.filter(badge_id=badge_id).first()
        if not employee:
            activity["Error 2"] = "Invalid Badge ID"
            error_dicts.append(activity)
            continue

        check_in_date = parse_date(activity["In Date"], "Error 4", activity)
        check_out_date = parse_date(activity["Out Date"], "Error 5", activity)
        check_in_time = (
            parse_time(activity["Check In"])
            if not pd.isna(activity["Check In"])
            else None
        )
        check_out_time = (
            parse_time(activity["Check Out"])
            if not pd.isna(activity["Check Out"])
            else None
        )

        if any(key.startswith("Error") for key in activity.keys()):
            error_dicts.append(activity)
            continue

        if check_in_time:
            try:
                clock_in(
                    Request(
                        user=employee.employee_user_id,
                        date=check_in_date,
                        time=check_in_time,
                        datetime=django_timezone.make_aware(
                            datetime.combine(check_in_date, check_in_time)
                        ),
                    )
                )
            except Exception as e:
                activity["Error 6"] = f"Got an error in import clock in {e}"
                error_dicts.append(activity)

        if check_out_time and check_out_date:
            try:
                clock_out(
                    Request(
                        user=employee.employee_user_id,
                        date=check_out_date,
                        time=check_out_time,
                        datetime=django_timezone.make_aware(
                            datetime.combine(check_out_date, check_out_time)
                        ),
                    )
                )
            except Exception as e:
                activity["Error 7"] = f"Got an error in import clock out {e}"
                error_dicts.append(activity)

    return error_dicts


def handle_activity_import_error(error_data):

    # Directly create the DataFrame from the list of dictionaries
    data_frame = pd.DataFrame(error_data)

    # Create an HTTP response with an Excel attachment
    response = HttpResponse(content_type="application/ms-excel")
    response["Content-Disposition"] = 'attachment; filename="ImportError.xlsx"'
    data_frame.to_excel(response, index=False)

    def get_activity_error_sheet(request):
        remove_dynamic_url(path_info)
        return response

    from attendance.urls import path, urlpatterns

    # Create a unique path for the error file download
    path_info = f"activity-error-sheet-{uuid.uuid4()}"
    urlpatterns.append(path(path_info, get_activity_error_sheet, name=path_info))
    DYNAMIC_URL_PATTERNS.append(path_info)

    # Return the path information
    path_info = f"attendance/{path_info}"
    return path_info


@login_required
@permission_required("attendance.add_attendanceactivity")
def attendance_activity_import(request):
    if request.method == "POST":
        file = request.FILES["activity_import"]
        data_frame = pd.read_excel(file)
        activity_dicts = data_frame.to_dict("records")
        if activity_dicts:
            import_error_dicts = process_activity_dicts(activity_dicts)
            path_info = handle_activity_import_error(import_error_dicts)
            created_activity_count = len(activity_dicts) - len(import_error_dicts)
            context = {
                "created_count": created_activity_count,
                "error_count": len(import_error_dicts),
                "model": _("Attendance Activity"),
                "path_info": path_info,
            }
            html = render_to_string("import_popup.html", context)
            messages.success(request, _("Attendance activity imported successfully"))
            return HttpResponse(html)
    return render(request, "attendance/attendance_activity/import_activity.html")


@login_required
@permission_required("attendance.add_attendanceactivity")
def attendance_activity_import_excel(request):
    if request.method == "GET":
        data_frame = pd.DataFrame(
            columns=[
                "Badge ID",
                "Employee",
                "Attendance Date",
                "In Date",
                "Check In",
                "Check Out",
                "Out Date",
            ]
        )
        response = HttpResponse(
            content_type="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
        )
        response["Content-Disposition"] = 'attachment; filename="activity_excel.xlsx"'
        data_frame.to_excel(response, index=False)
        return response


@login_required
@permission_required("attendance.change_attendanceactivity")
def attendance_activity_export(request):
    if request.META.get("HTTP_HX_REQUEST") == "true":
        export_form = AttendanceActivityExportForm()
        context = {
            "export_form": export_form,
            "export": AttendanceActivityFilter(
                queryset=AttendanceActivity.objects.all()
            ),
        }
        return render(
            request,
            "attendance/attendance_activity/export_filter.html",
            context=context,
        )
    return export_data(
        request=request,
        model=AttendanceActivity,
        filter_class=AttendanceActivityFilter,
        form_class=AttendanceActivityExportForm,
        file_name="Attendance_activity",
    )


@login_required
def on_time_view(request):
    """
    This method render template to view all on come early out entries
    """
    total_attendances = AttendanceFilters(request.GET).qs
    ids_to_exclude = AttendanceLateComeEarlyOut.objects.filter(
        attendance_id__id__in=[attendance.id for attendance in total_attendances],
        type="late_come",
    ).values_list("attendance_id__id", flat=True)
    # Exclude attendances with related objects in AttendanceLateComeEarlyOut
    total_attendances = total_attendances.exclude(id__in=ids_to_exclude)
    context = {
        "attendances": total_attendances,
    }
    return render(
        request, "attendance/attendance/attendance_on_time.html", context=context
    )


@login_required
@install_required
def late_come_early_out_view(request):
    """
    This method render template to view all late come early out entries
    """
    filter_obj = LateComeEarlyOutFilter(request.GET)
    if filter_obj.qs.exists():
        template = "attendance/late_come_early_out/reports.html"
    else:
        template = "attendance/late_come_early_out/reports_empty.html"
    self_reports = filter_obj.qs.filter(employee_id__employee_user_id=request.user)
    reports = filtersubordinates(
        request, filter_obj.qs, "attendance.view_attendancelatecomeearlyout"
    )

    reports = reports | self_reports
    reports = reports.distinct()
    late_in_early_out_ids = json.dumps(
        [instance.id for instance in paginator_qry(reports, None)]
    )
    previous_data = request.GET.urlencode()
    data_dict = parse_qs(previous_data)
    get_key_instances(AttendanceLateComeEarlyOut, data_dict)
    return render(
        request,
        template,
        {
            "data": paginator_qry(reports, request.GET.get("page")),
            "f": filter_obj,
            "gp_fields": LateComeEarlyOutReGroup.fields,
            "filter_dict": data_dict,
            "late_in_early_out_ids": late_in_early_out_ids,
        },
    )


@login_required
@hx_request_required
def late_in_early_out_single_view(request, obj_id):
    request_copy = request.GET.copy()
    request_copy.pop("instances_ids", None)
    previous_data = request_copy.urlencode()
    late_in_early_out = AttendanceLateComeEarlyOut.objects.filter(id=obj_id).first()
    instance_ids_json, instance_ids = _safe_request_instance_ids(request)
    previous_instance, next_instance = closest_numbers(instance_ids, obj_id)
    context = {
        "late_in_early_out": late_in_early_out,
        "previous_instance": previous_instance,
        "next_instance": next_instance,
        "instance_ids_json": instance_ids_json,
        "pd": previous_data,
    }
    return render(
        request, "attendance/late_come_early_out/single_report.html", context=context
    )


@login_required
@permission_required("attendance.delete_attendancelatecomeearlyout")
@hx_request_required
@require_http_methods(["POST"])
def late_come_early_out_delete(request, obj_id):
    """
    This method is used to delete the late come early out instance
    args:
        obj_id : late come early out instance id
    """
    request_copy = request.GET.copy()
    request_copy.pop("instances_ids", None)
    previous_data = request_copy.urlencode()
    try:
        AttendanceLateComeEarlyOut.objects.get(id=obj_id).delete()
        messages.success(request, _("Late-in early-out deleted"))
    except AttendanceLateComeEarlyOut.DoesNotExist:
        messages.error(request, _("Late-in early-out does not exists.."))
    except ProtectedError:
        messages.error(request, _("You cannot delete this Late-in early-out"))
    instance_ids_json, instances_list = _safe_request_instance_ids(request)
    if not instances_list:
        return redirect(f"/attendance/late-come-early-out-search?{previous_data}")

    if obj_id in instances_list:
        instances_list.remove(obj_id)
    previous_instance, next_instance = closest_numbers(instances_list, obj_id)
    if next_instance is None:
        return redirect(f"/attendance/late-come-early-out-search?{previous_data}")
    return redirect(
        f"/attendance/late-in-early-out-single-view/{next_instance}/?{previous_data}&instances_ids={json.dumps(instances_list)}"
    )


@login_required
@permission_required("attendance.delete_attendancelatecomeearlyout")
@require_http_methods(["POST"])
def late_come_early_out_bulk_delete(request):
    """
    This method is used to delete bulk of attendances
    """
    ids = request.POST["ids"]
    ids = json.loads(ids)
    for attendance_id in ids:
        try:
            late_come = AttendanceLateComeEarlyOut.objects.get(id=attendance_id)
            late_come.delete()
            messages.success(
                request,
                _("{employee} Late-in early-out deleted.").format(
                    employee=late_come.employee_id
                ),
            )
        except (AttendanceLateComeEarlyOut.DoesNotExist, OverflowError, ValueError):
            messages.error(request, _("Attendance not found."))
    return JsonResponse({"message": "Success"})


@login_required
@permission_required("attendance.change_attendancelatecomeearlyout")
def late_come_early_out_export(request):
    """
    Export late come early out data to an Excel file.
    This view function takes a GET request and exports attendance late come early out data into an Excel file.
    The exported Excel file will include the selected fields from the AttendanceLateComeEarlyOut model.
    """
    if request.META.get("HTTP_HX_REQUEST") == "true":
        context = {
            "export": LateComeEarlyOutFilter(
                queryset=AttendanceLateComeEarlyOut.objects.all()
            ),
            "export_form": LateComeEarlyOutExportForm(),
        }

        return render(
            request,
            "attendance/late_come_early_out/export_filter.html",
            context=context,
        )
    return export_data(
        request=request,
        model=AttendanceLateComeEarlyOut,
        filter_class=LateComeEarlyOutFilter,
        form_class=LateComeEarlyOutExportForm,
        file_name="Late_come_",
    )


@login_required
@permission_required("attendance.change_attendancevalidationcondition")
@require_http_methods(["POST"])
def validation_condition_delete(request, obj_id):
    """
    This method is used to delete created validation condition
    args:
        obj_id  : validation condition id
    """
    try:
        AttendanceValidationCondition.objects.get(id=obj_id).delete()
        messages.success(request, _("validation condition deleted."))
    except AttendanceValidationCondition.DoesNotExist:
        messages.error(request, _("validation condition Does not exists.."))
    except ProtectedError:
        messages.error(request, _("You cannot delete this validation condition."))
    return redirect("/attendance/validation-condition-view")


@login_required
@require_http_methods(["POST"])
@manager_can_enter("attendance.change_attendance")
def validate_bulk_attendance(request):
    """
    This method is used to validate a bulk of attendances.
    """
    ids = json.loads(request.POST["ids"])
    validate_req_count = 0
    success_messages = []
    error_messages = []

    for obj_id in ids:
        try:
            attendance = Attendance.objects.get(id=obj_id)

            if AttendanceCorrectionRequest.objects.filter(
                employee_id=attendance.employee_id,
                attendance_date=attendance.attendance_date,
                status=AttendanceCorrectionRequestStatus.WAITING,
            ).exists():
                error_messages.append(
                    _(
                        "Pending attendance correction request for {} on {}!"
                    ).format(attendance.employee_id, attendance.attendance_date)
                )
                continue

            attendance.attendance_validated = True
            attendance.save()
            validate_req_count += 1

            # Send notification
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Your attendance for the date {attendance.attendance_date} is validated",
                verb_ar=f"تم التحقق من حضورك في تاريخ {attendance.attendance_date}",
                verb_de=f"Ihre Anwesenheit für das Datum {attendance.attendance_date} wurde bestätigt",
                verb_es=f"Se ha validado su asistencia para la fecha {attendance.attendance_date}",
                verb_fr=f"Votre présence pour la date {attendance.attendance_date} est validée",
                redirect=reverse("view-my-attendance") + f"?id={attendance.id}",
                icon="checkmark",
            )

        except Attendance.DoesNotExist:
            error_messages.append(_("Attendance not found"))
        except (OverflowError, ValueError):
            error_messages.append(_("Invalid attendance ID"))

    # Handle messages
    if validate_req_count > 0:
        messages.success(
            request, _("{} Attendances validated.").format(validate_req_count)
        )
    for msg in success_messages + error_messages:
        if "Pending" in msg:
            messages.info(request, msg)
        else:
            messages.error(request, msg)

    return JsonResponse({"message": "success"})


@login_required
@manager_can_enter("attendance.change_attendance")
def validate_this_attendance(request, obj_id):
    """
    This method is used to validate attendance
    args:
        id  : attendance id
    """
    try:
        attendance = Attendance.objects.get(id=obj_id)
        attendance.attendance_validated = True
        attendance.save()
        urlencode = request.GET.urlencode()
        modified_url = f"/attendance/attendance-view/?{urlencode}"
        messages.success(
            request,
            (
                f"{attendance.employee_id} {attendance.attendance_date.strftime('%d %b %Y') }"
                + " "
                + _("Attendance validated.")
            ),
        )
        notify.send(
            request.user.employee_get,
            recipient=attendance.employee_id.employee_user_id,
            verb=f"Your attendance for the date {attendance.attendance_date} is validated",
            verb_ar=f"تم تحقيق حضورك في تاريخ {attendance.attendance_date}",
            verb_de=f"Deine Anwesenheit für das Datum {attendance.attendance_date} ist bestätigt.",
            verb_es=f"Se valida tu asistencia para la fecha {attendance.attendance_date}.",
            verb_fr=f"Votre présence pour la date {attendance.attendance_date} est validée.",
            redirect=reverse("view-my-attendance") + f"?id={attendance.id}",
            icon="checkmark",
        )
    except (Attendance.DoesNotExist, ValueError):
        messages.error(request, _("Attendance not found"))

    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
def revalidate_this_attendance(request, obj_id):
    """
    This method is used to not validate the attendance.
    args:
        id  : attendance id
    """

    attendance = Attendance.objects.get(id=obj_id)
    if is_reportingmanger(request, attendance) or request.user.has_perm(
        "attendance.change_attendance"
    ):
        attendance.attendance_validated = False
        attendance.save()
        with contextlib.suppress(Exception):
            notify.send(
                request.user.employee_get,
                recipient=(
                    attendance.employee_id.employee_work_info.reporting_manager_id.employee_user_id
                ),
                verb=f"{attendance.employee_id} requested revalidation for \
                    {attendance.attendance_date} attendance",
                verb_ar=f"{attendance.employee_id} طلب إعادة\
                      التحقق من حضور تاريخ {attendance.attendance_date}",
                verb_de=f"{attendance.employee_id} beantragte eine Neubewertung der \
                    Teilnahme am {attendance.attendance_date}",
                verb_es=f"{attendance.employee_id} solicitó la validación nuevamente \
                    para la asistencia del {attendance.attendance_date}",
                verb_fr=f"{attendance.employee_id} a demandé une revalidation pour la \
                    présence du {attendance.attendance_date}",
                redirect=reverse("view-my-attendance") + f"?id={attendance.id}",
                icon="refresh",
            )
        return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
    return HttpResponse("You Cannot Request for others attendance")


@login_required
@manager_can_enter("attendance.change_attendance")
def approve_overtime(request, obj_id):
    """
    This method is used to approve attendance overtime
    args:
        obj_id  : attendance id
    """
    try:
        attendance = Attendance.objects.get(id=obj_id)
        attendance.attendance_overtime_approve = True
        attendance.save()
        urlencode = request.GET.urlencode()
        modified_url = f"/attendance/attendance-view/?{urlencode}"
        messages.success(
            request,
            f"{attendance.employee_id}'s {attendance.attendance_date.strftime('%d %b %Y')} overtime approved",
        )
        with contextlib.suppress(Exception):
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Your {attendance.attendance_date}'s attendance \
                    overtime approved.",
                verb_ar=f"تمت الموافقة على إضافة ساعات العمل الإضافية لتاريخ \
                    {attendance.attendance_date}.",
                verb_de=f"Die Überstunden für den {attendance.attendance_date}\
                      wurden genehmigt.",
                verb_es=f"Se ha aprobado el tiempo extra de asistencia para el \
                    {attendance.attendance_date}.",
                verb_fr=f"Les heures supplémentaires pour la date\
                      {attendance.attendance_date} ont été approuvées.",
                redirect=reverse("attendance-overtime-view") + f"?id={attendance.id}",
                icon="checkmark",
            )
    except (Attendance.DoesNotExist, OverflowError):
        messages.error(request, _("Attendance not found"))
    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@manager_can_enter("attendance.change_attendance")
def approve_bulk_overtime(request):
    """
    This method is used to approve bulk of attendance
    """
    ids = request.POST["ids"]
    ids = json.loads(ids)
    for attendance_id in ids:
        try:
            attendance = Attendance.objects.get(id=attendance_id)
            attendance.attendance_overtime_approve = True
            attendance.save()
            messages.success(request, _("Overtime approved"))
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Overtime approved for\
                      {attendance.attendance_date}'s attendance",
                verb_ar=f"تمت الموافقة على العمل الإضافي لحضور تاريخ \
                    {attendance.attendance_date}",
                verb_de=f"Überstunden für die Anwesenheit am \
                    {attendance.attendance_date} genehmigt",
                verb_es=f"Horas extra aprobadas para la asistencia del \
                    {attendance.attendance_date}",
                verb_fr=f"Heures supplémentaires approuvées pour la présence du \
                    {attendance.attendance_date}",
                redirect=reverse("attendance-overtime-view") + f"?id={attendance.id}",
                icon="checkmark",
            )
        except (Attendance.DoesNotExist, OverflowError, ValueError):
            messages.error(request, _("Attendance not found"))
    return JsonResponse({"message": "Success"})


@login_required
# @manager_can_enter("attendance.change_attendance")
def attendance_add_to_batch(request):
    """
    This method is used to add attendance to a batch
    """
    batches = BatchAttendance.objects.all()
    ids = request.GET.getlist("ids")
    if request.method == "POST":
        ids = request.GET["ids"]
        # Remove brackets and quotes, then split and convert to integers
        int_ids = [int(x.strip().strip("'")) for x in ids.strip("[]").split(",")]
        batch_id = request.POST.get("batch_attendance_id")
        if batch_id:
            batch = BatchAttendance.objects.filter(id=batch_id).first()
            for id in int_ids:
                try:
                    attendance_req = Attendance.objects.filter(id=id).first()
                    attendance_req.batch_attendance_id = batch
                    attendance_req.save()
                except Exception as e:
                    logger.error(e)
                    messages.error(request, _("Something went wrong."))
                    return HttpResponse("<script>window.location.reload()</script>")
            messages.success(request, _(f"Attendances added to {batch}."))
            return HttpResponse("<script>window.location.reload()</script>")
        else:
            messages.error(request, _("Something went wrong."))
            return HttpResponse("<script>window.location.reload()</script>")
    return render(
        request,
        "attendance/attendance/attendance_add_batch.html",
        {"batches": batches, "ids": ids},
    )


@login_required
@hx_request_required
def update_fields_based_shift(request):
    shift_id = request.GET.get("shift_id")
    hx_target = request.META.get("HTTP_HX_TARGET")

    employee_ids = (
        request.GET.get("employee_id")
        if hx_target == "attendanceUpdateForm" or hx_target == "attendanceRequestDiv"
        else request.GET.getlist("employee_id")
    )
    employee_queryset = (
        (
            Employee.objects.get(id=employee_ids)
            if hx_target == "attendanceUpdateForm"
            or hx_target == "attendanceRequestDiv"
            else Employee.objects.filter(id__in=employee_ids)
        )
        if employee_ids
        else None
    )
    attendance_date_str = request.GET.get("attendance_date")

    attendance_date = (
        datetime.strptime(attendance_date_str, "%Y-%m-%d").date()
        if attendance_date_str
        else datetime.today().date()
    )
    day = attendance_date.strftime("%A").lower()

    schedule_today = (
        EmployeeShiftSchedule.objects.filter(shift_id=shift_id, day__day=day).first()
        if shift_id
        else None
    )

    shift_start_time = schedule_today.start_time if schedule_today else ""
    shift_end_time = schedule_today.end_time if schedule_today else ""
    minimum_hour = schedule_today.minimum_working_hour if schedule_today else "00:00"

    if schedule_today and shift_end_time < shift_start_time:
        attendance_clock_out_date = (attendance_date + timedelta(days=1)).strftime(
            "%Y-%m-%d"
        )
    else:
        attendance_clock_out_date = attendance_date.strftime("%Y-%m-%d")

    if attendance_date == datetime.today().date():
        shift_end_time = datetime.now().time()
        worked_hour = "00:00"
    else:
        worked_hour = minimum_hour

    minimum_hour = attendance_day_checking(str(attendance_date), minimum_hour)

    initial_data = {
        "work_type_id": WorkType.find(request.GET.get("work_type_id")),
        "shift_id": shift_id,
        "employee_id": employee_queryset,
        "minimum_hour": minimum_hour,
        "attendance_date": attendance_date.strftime("%Y-%m-%d"),
        "attendance_clock_in": (
            shift_start_time.strftime("%H:%M") if shift_start_time else ""
        ),
        "attendance_clock_out": (
            shift_end_time.strftime("%H:%M") if shift_end_time else ""
        ),
        "attendance_worked_hour": worked_hour,
        "attendance_clock_in_date": attendance_date.strftime("%Y-%m-%d"),
        "attendance_clock_out_date": attendance_clock_out_date,
    }
    correction_form_cls = None
    if hx_target == "attendanceRequestDiv":
        try:
            from attendance.views.requests import AttendanceCorrectionRequestWebForm as correction_form_cls
        except Exception:
            correction_form_cls = None

    form = (
        AttendanceUpdateForm(initial=initial_data)
        if hx_target == "attendanceUpdateForm"
        else (
            correction_form_cls(initial=initial_data, employee=request.user.employee_get)
            if hx_target == "attendanceRequestDiv" and correction_form_cls is not None
            else (
                NewRequestForm(initial=initial_data)
                if hx_target == "attendanceRequestDiv"
                else AttendanceForm(initial=initial_data)
            )
        )
    )
    # Self-only: hide employee selector in attendance correction request form
    try:
        if isinstance(form, NewRequestForm) or form.__class__.__name__ == "AttendanceCorrectionRequestWebForm":
            self_emp_id = request.user.employee_get.id
            if 'employee_id' in form.fields:
                form.fields['employee_id'].queryset = Employee.objects.filter(id=self_emp_id)
                form.fields['employee_id'].initial = self_emp_id
                form.fields['employee_id'].widget = forms.HiddenInput()
    except Exception:
        pass


    return render(
    request,
    "attendance/attendance/update_hx_form.html",
        {"request": request, "form": form},
    )


@login_required
@hx_request_required
def update_worked_hour_field(request):
    """
    Update the worked hour field based on clock-in and clock-out times.

    This view function calculates the total worked hours for an employee
    by parsing the clock-in and clock-out dates and times from the request
    parameters. It computes the duration between the two times and formats
    the result as a string in the "HH:MM" format. The computed worked hours
    are then initialized in an AttendanceForm, which is rendered in the
    specified HTML template.
    """
    clock_in = parse_datetime(
        (
            now().strftime("%Y-%m-%d")
            if request.GET.get("create_bulk")
            else request.GET.get("attendance_clock_in_date")
        ),
        request.GET.get("attendance_clock_in"),
    )
    clock_out = parse_datetime(
        (
            now().strftime("%Y-%m-%d")
            if request.GET.get("create_bulk")
            else request.GET.get("attendance_clock_out_date")
        ),
        request.GET.get("attendance_clock_out"),
    )

    total_seconds = (
        (clock_out - clock_in).total_seconds() if clock_in and clock_out else -1
    )
    hours, minutes = divmod(max(total_seconds, 0), 3600)
    worked_hours_str = f"{int(hours):02}:{int(minutes // 60):02}"

    form = AttendanceForm(initial={"attendance_worked_hour": worked_hours_str})
    return render(
        request,
        "attendance/attendance/update_hx_form.html",
        {"request": request, "form": form},
    )


@login_required
def form_date_checking(request):
    attendance_date_str = request.POST["attendance_date"]
    minimum_hour = "00:00"
    # Converting to date type.
    attendance_date = datetime.strptime(attendance_date_str, "%Y-%m-%d").date()

    if request.POST["shift_id"]:
        shift_id = request.POST["shift_id"]
        day = attendance_date.strftime("%A").lower()
        schedule_today = EmployeeShiftSchedule.objects.filter(
            shift_id__id=shift_id, day__day=day
        ).first()

        # Checking the Shift is present in the selected attendance day.
        if schedule_today is not None:
            minimum_hour = schedule_today.minimum_working_hour

    attendance_date = str(attendance_date)
    minimum_hour = attendance_day_checking(attendance_date, minimum_hour)

    return JsonResponse(
        {
            "minimum_hour": minimum_hour,
        }
    )


@login_required
def user_request_one_view(request, id):
    """
    function used to view one user attendance request.

    Parameters:
    request (HttpRequest): The HTTP request object.

    Returns:
    GET : return one user attendance request view template
    """
    attendance_request = Attendance.objects.get(id=id)

    at_work_seconds = attendance_request.at_work_second
    hours_at_work = at_work_seconds // 3600
    minutes_at_work = (at_work_seconds % 3600) // 60
    at_work = "{:02}:{:02}".format(hours_at_work, minutes_at_work)

    over_time_seconds = attendance_request.overtime_second
    hours_over_time = over_time_seconds // 3600
    minutes_over_time = (over_time_seconds % 3600) // 60
    over_time = "{:02}:{:02}".format(hours_over_time, minutes_over_time)
    instance_ids_json, instance_ids = _safe_request_instance_ids(request)
    previous_instance, next_instance = closest_numbers(instance_ids, id)
    return render(
        request,
        "attendance/attendance/attendance_request_one.html",
        {
            "attendance_request": attendance_request,
            "at_work": at_work,
            "over_time": over_time,
            "previous_instance": previous_instance,
            "next_instance": next_instance,
            "instance_ids_json": instance_ids_json,
            "dashboard": request.GET.get("dashboard"),
        },
    )


@login_required
@hx_request_required
def get_attendance_activities(request, obj_id):
    attendance = Attendance.find(obj_id)
    return render(
        request,
        "attendance/attendance/attendance_activites_view.html",
        context={"attendance": attendance},
    )


@login_required
def hour_attendance_select(request):
    page_number = request.GET.get("page")
    context = {}

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendanceovertime"):
            employees = AttendanceOverTime.objects.all()
        else:
            employees = AttendanceOverTime.objects.filter(
                employee_id__employee_user_id=request.user
            ) | AttendanceOverTime.objects.filter(
                employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user
            )

        employee_ids = [str(emp.id) for emp in employees]
        total_count = employees.count()

        context = {"employee_ids": employee_ids, "total_count": total_count}

    return JsonResponse(context, safe=False)


@login_required
def hour_attendance_select_filter(request):
    page_number = request.GET.get("page")
    filtered = request.GET.get("filter")
    filters = json.loads(filtered) if filtered else {}

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendanceovertime"):
            employee_filter = AttendanceOverTimeFilter(
                filters, queryset=AttendanceOverTime.objects.all()
            )
        else:
            employee_filter = AttendanceOverTimeFilter(
                filters,
                queryset=AttendanceOverTime.objects.filter(
                    employee_id__employee_user_id=request.user
                )
                | AttendanceOverTime.objects.filter(
                    employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user
                ),
            )

        # Get the filtered queryset
        filtered_employees = employee_filter.qs

        employee_ids = [str(emp.id) for emp in filtered_employees]
        total_count = filtered_employees.count()

        context = {"employee_ids": employee_ids, "total_count": total_count}

        return JsonResponse(context)


@login_required
def activity_attendance_select(request):
    page_number = request.GET.get("page")

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendanceactivity"):
            employees = AttendanceActivity.objects.all()
        else:
            employees = AttendanceActivity.objects.filter(
                employee_id__employee_user_id=request.user
            ) | AttendanceActivity.objects.filter(
                employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user
            )

    employee_ids = [str(emp.id) for emp in employees]
    total_count = employees.count()

    context = {"employee_ids": employee_ids, "total_count": total_count}

    return JsonResponse(context, safe=False)


@login_required
def activity_attendance_select_filter(request):
    page_number = request.GET.get("page")
    filtered = request.GET.get("filter")
    filters = json.loads(filtered) if filtered else {}

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendanceactivity"):
            employee_filter = AttendanceActivityFilter(
                filters, queryset=AttendanceActivity.objects.all()
            )
        else:
            employee_filter = AttendanceActivityFilter(
                filters,
                queryset=AttendanceActivity.objects.filter(
                    employee_id__employee_user_id=request.user
                )
                | AttendanceActivity.objects.filter(
                    employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user
                ),
            )

        # Get the filtered queryset
        filtered_employees = employee_filter.qs

        employee_ids = [str(emp.id) for emp in filtered_employees]
        total_count = filtered_employees.count()

        context = {"employee_ids": employee_ids, "total_count": total_count}

        return JsonResponse(context)


@login_required
def latecome_attendance_select(request):
    page_number = request.GET.get("page")

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendancelatecomeearlyout"):
            employees = AttendanceLateComeEarlyOut.objects.all()
        else:
            employees = AttendanceLateComeEarlyOut.objects.filter(
                employee_id__employee_user_id=request.user
            ) | AttendanceLateComeEarlyOut.objects.filter(
                employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user
            )

    employee_ids = [str(emp.id) for emp in employees]
    total_count = employees.count()

    context = {"employee_ids": employee_ids, "total_count": total_count}

    return JsonResponse(context, safe=False)


@login_required
def latecome_attendance_select_filter(request):
    page_number = request.GET.get("page")
    filtered = request.GET.get("filter")
    filters = json.loads(filtered) if filtered else {}

    if page_number == "all":
        if request.user.has_perm("attendance.view_attendancelatecomeearlyout"):
            employee_filter = LateComeEarlyOutFilter(
                filters, queryset=AttendanceLateComeEarlyOut.objects.all()
            )
        else:
            employee_filter = LateComeEarlyOutFilter(
                filters,
                queryset=AttendanceLateComeEarlyOut.objects.filter(
                    employee_id__employee_user_id=request.user
                )
                | AttendanceLateComeEarlyOut.objects.filter(
                    employee_id__employee_work_info__reporting_manager_id__employee_user_id=request.user
                ),
            )

        # Get the filtered queryset
        filtered_employees = employee_filter.qs

        employee_ids = [str(emp.id) for emp in filtered_employees]
        total_count = filtered_employees.count()

        context = {"employee_ids": employee_ids, "total_count": total_count}

        return JsonResponse(context)


@login_required
@hx_request_required
@permission_required("attendance.add_gracetime")
def create_grace_time(request):
    """
    function used to create grace time .

    Parameters:
    request (HttpRequest): The HTTP request object.

    Returns:
    GET : return grace time form template
    """
    is_default = eval_validate(request.GET.get("default"))
    form = GraceTimeForm(initial={"is_default": is_default})
    if request.method == "POST":
        form = GraceTimeForm(request.POST)
        if form.is_valid():
            cleaned_data = form.cleaned_data
            gracetime = form.save()
            shifts = cleaned_data.get("shifts")
            _sync_grace_time_shifts(gracetime, shifts)
            messages.success(request, _("Grace time created successfully."))
            return HttpResponse("<script>window.location.reload()</script>")
    return render(
        request,
        "attendance/grace_time/grace_time_form.html",
        {"form": form, "is_default": is_default},
    )


@login_required
@hx_request_required
@permission_required("base.change_employeeshift")
def assign_shift(request, grace_id):
    gracetime = GraceTime.objects.filter(id=grace_id).first() if grace_id else None
    if gracetime:
        form = GraceTimeAssignForm()
        if request.method == "POST":
            form = GraceTimeAssignForm(request.POST)
            if form.is_valid():
                cleaned_data = form.cleaned_data
                shifts = cleaned_data.get("shifts")
                for shift in shifts:
                    shift.grace_time_id = gracetime
                    shift.save()
                messages.success(request, _("Grace time added to shifts successfully."))
                return HttpResponse("<script>window.location.reload()</script>")
        return render(
            request,
            "attendance/grace_time/assign_shift.html",
            {"form": form, "grace_time": gracetime},
        )


@login_required
@hx_request_required
@permission_required("attendance.change_gracetime")
def update_grace_time(request, grace_id):
    """
    function used to create grace time .

    Parameters:
    request (HttpRequest): The HTTP request object.
    grace_id: id of grace time object
    Returns:
    GET : return grace time form template
    """
    grace_time = GraceTime.objects.get(id=grace_id)
    form = GraceTimeForm(instance=grace_time)
    if request.method == "POST":
        form = GraceTimeForm(request.POST, instance=grace_time)
        if form.is_valid():
            cleaned_data = form.cleaned_data
            instance = form.save(commit=False)
            instance.save()
            form.save_m2m()
            _sync_grace_time_shifts(instance, cleaned_data.get("shifts"))
            messages.success(request, _("Grace time updated successfully."))
            return HttpResponse("<script>window.location.reload()</script>")
    context = {
        "form": form,
        "grace_id": grace_id,
    }
    return render(
        request, "attendance/grace_time/grace_time_form.html", context=context
    )


@login_required
@permission_required("attendance.delete_gracetime")
def delete_grace_time(request, grace_id):
    """
    function used to delete grace time .

    Parameters:
    request (HttpRequest): The HTTP request object.
    grace_id: id of grace time object
    Returns:
    GET : return grace time form template
    """
    try:
        GraceTime.objects.get(id=grace_id).delete()
        messages.success(request, _("Grace time deleted successfully."))
    except GraceTime.DoesNotExist:
        messages.error(request, _("Grace Time Does not exists.."))
    except ProtectedError:
        messages.error(request, _("Related datas exists."))
    context = {
        "condition": AttendanceValidationCondition.objects.first(),
        "default_grace_time": GraceTime.objects.filter(is_default=True).first(),
        "grace_times": GraceTime.objects.all().exclude(is_default=True),
    }

    return render(request, "attendance/grace_time/grace_time_table.html", context)


@login_required
@permission_required("attendance.update_gracetime")
def update_isactive_gracetime(request):
    """
    ajax function to update is active field in GraceTime.
    Args:
    - isChecked: Boolean value representing the state of grace time,
    - gracetimeId: Id of GraceTime object
    """
    isChecked = request.POST.get("isChecked")
    gracetimeId = request.POST.get("gracetimeId")
    gracetime = GraceTime.objects.get(id=gracetimeId)
    if isChecked == "true":
        gracetime.is_active = True
        response = {
            "type": "success",
            "message": _("Gracetime activated successfully."),
        }
    else:
        gracetime.is_active = False
        response = {
            "type": "success",
            "message": _("Gracetime deactivated successfully."),
        }
    gracetime.save()
    return JsonResponse(response)


@login_required
@permission_required("attendance.update_gracetime")
def update_gracetime_clock_in_clock_out(request):
    """
    ajax function to update is active field in grace time.
    Args:
    - isChecked: Boolean value representing the state of grace time,
    - gracetimeId: Id of PayslipAutoGenerate object
    """
    isChecked = request.POST.get("isChecked")
    gracetimeId = request.POST.get("gracetimeId")
    update = request.POST.get("update")
    garcetime = GraceTime.objects.get(id=gracetimeId)
    if update == "clock_in":
        if isChecked == "true":
            garcetime.allowed_clock_in = True
            response = {
                "type": "success",
                "message": _("Gracetime applicable on clock-In successfully."),
            }
        else:
            garcetime.allowed_clock_in = False
            response = {
                "type": "success",
                "message": _("Gracetime unapplicable on clock-In  successfully."),
            }
    elif update == "clock_out":
        if isChecked == "true":
            garcetime.allowed_clock_out = True
            response = {
                "type": "success",
                "message": _("Gracetime applicable on clock-out successfully."),
            }
        else:
            garcetime.allowed_clock_out = False
            response = {
                "type": "success",
                "message": _("Gracetime unapplicable on clock-out successfully."),
            }
    else:
        response = {
            "type": "error",
            "message": _("Something went wrong ."),
        }
    garcetime.save()
    return JsonResponse(response)


@login_required
def create_attendancerequest_comment(request, *args, **kwargs):
    return HttpResponseForbidden("Attendance request comments are disabled.")

@login_required
def view_attendancerequest_comment(request, *args, **kwargs):
    return HttpResponseForbidden("Attendance request comments are disabled.")

@login_required
def delete_attendancerequest_comment(request, *args, **kwargs):
    return HttpResponseForbidden("Attendance request comments are disabled.")

@login_required
def delete_comment_file(request):
    return HttpResponseForbidden("Attendance request comments are disabled.")

@login_required
def work_records(request):
    today = date.today()
    previous_data = request.GET.urlencode()
    context = {
        "current_date": today,
        "pd": previous_data,
    }
    return render(
        request, "attendance/work_record/work_record_view.html", context=context
    )


@login_required
@hx_request_required
def work_records_change_month(request):
    previous_data = request.GET.urlencode()
    employee_filter_form = EmployeeFilter(request.GET or None)

    employees = filtersubordinatesemployeemodel(
        request, employee_filter_form.qs, "attendance.view_attendance"
    )

    month_str = request.GET.get("month", f"{date.today().year}-{date.today().month}")
    try:
        year, month = map(int, month_str.split("-"))
    except ValueError:
        year, month = date.today().year, date.today().month

    employees = [request.user.employee_get] + list(employees)

    month_dates = [
        datetime(year, month, day).date()
        for week in calendar.monthcalendar(year, month)
        for day in week
        if day
    ]

    work_records = WorkRecords.objects.filter(
        date__in=month_dates, employee_id__in=employees
    ).select_related("employee_id", "shift_id", "attendance_id")

    work_records_dict = {(wr.employee_id.id, wr.date): wr for wr in work_records}

    data = {
        employee: [
            work_records_dict.get((employee.id, current_date))
            for current_date in month_dates
        ]
        for employee in employees
    }

    paginator = Paginator(list(data.items()), get_pagination())
    page = paginator.get_page(request.GET.get("page"))

    context = {
        "current_month_dates_list": month_dates,
        "leave_dates": monthly_leave_days(month, year),
        "data": page,
        "pd": previous_data,
        "current_date": date.today(),
        "f": employee_filter_form,
    }

    return render(request, "attendance/work_record/work_record_list.html", context)


@login_required
@permission_required("attendance.view_workrecords")
def work_record_export(request):
    try:
        month = int(request.GET.get("month") or date.today().month)
        year = int(request.GET.get("year") or date.today().year)
    except ValueError:
        return HttpResponseBadRequest("Invalid month or year parameter.")

    employees = EmployeeFilter(request.GET).qs
    records = WorkRecords.objects.filter(date__month=month, date__year=year)
    num_days = calendar.monthrange(year, month)[1]
    all_date_objects = [date(year, month, day) for day in range(1, num_days + 1)]
    leave_dates = set(monthly_leave_days(month, year))

    record_lookup = defaultdict(lambda: "ABS")
    for record in records:
        if record.date <= date.today():
            record_key = (record.employee_id, record.date)
            record_lookup[record_key] = record.work_record_type

    date_format = request.user.employee_get.get_date_format()
    format_string = HORILLA_DATE_FORMATS.get(date_format)
    formatted_dates = [day.strftime(format_string) for day in all_date_objects]
    data_rows = []

    for employee in employees:
        row_data = {"Employee": employee}
        for day, formatted_day in zip(all_date_objects, formatted_dates):
            if not day in leave_dates and day < date.today():
                row_data[formatted_day] = record_lookup.get((employee, day), "DFT")
            else:
                data = record_lookup.get((employee, day), "")
                row_data[formatted_day] = data if data != "DFT" else ""
        data_rows.append(row_data)

    columns = ["Employee"] + formatted_dates
    df = pd.DataFrame(data_rows, columns=columns)

    output = io.BytesIO()
    with pd.ExcelWriter(output, engine="xlsxwriter") as writer:
        df.to_excel(writer, index=False, sheet_name="Sheet1")
        workbook = writer.book
        worksheet = writer.sheets["Sheet1"]

        formats = {
            "ABS": workbook.add_format(
                {"bg_color": "#808080", "font_color": "#ffffff"}
            ),
            "FDP": workbook.add_format(
                {"bg_color": "#38c338", "font_color": "#ffffff"}
            ),
            "HDP": workbook.add_format(
                {"bg_color": "#dfdf52", "font_color": "#000000"}
            ),
            "CONF": workbook.add_format(
                {"bg_color": "#ed4c4c", "font_color": "#ffffff"}
            ),
            "DFT": workbook.add_format(
                {"bg_color": "#a8b1ff", "font_color": "#ffffff"}
            ),
        }

        for row_idx, row in enumerate(df.itertuples(index=False), start=1):
            for col_idx, cell_value in enumerate(row[1:], start=1):
                if cell_value in formats:
                    worksheet.write(row_idx, col_idx, cell_value, formats[cell_value])

        for col_idx, col in enumerate(df.columns):
            max_len = max(df[col].astype(str).map(len).max(), len(col))
            worksheet.set_column(col_idx, col_idx, max_len)

    output.seek(0)

    response = HttpResponse(
        output.read(),
        content_type="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
    )
    response["Content-Disposition"] = 'attachment; filename="work_record_export.xlsx"'
    return response


@login_required
@hx_request_required
@permission_required("attendance.add_attendancegeneralsetting")
def enable_timerunner(request):
    """
    This method is used to enable/disable the timerunner feature
    """

    time_runner = AttendanceGeneralSetting.objects.first()
    time_runner = time_runner if time_runner else AttendanceGeneralSetting()
    time_runner.time_runner = "time_runner" in request.GET.keys()
    time_runner.save()
    return HttpResponse("success")


@login_required
@permission_required("base.view_tracklatecomeearlyout")
def track_late_come_early_out(request):
    """
    Track Late Come & Early Out is now managed automatically and stays disabled.
    """
    messages.info(
        request,
        _("Track Late Come & Early Out is managed automatically and remains disabled."),
    )
    return redirect("attendance-settings-view")


@login_required
@permission_required("base.change_tracklatecomeearlyout")
def enable_disable_tracking_late_come_early_out(request):
    """
    Ignore web toggle attempts and keep tracking disabled at the source of truth.
    """
    tracking, _ = TrackLateComeEarlyOut.objects.get_or_create(
        defaults={"is_enable": False}
    )
    if tracking.is_enable:
        tracking.is_enable = False
        tracking.save()
    messages.info(
        request,
        _("Track Late Come & Early Out is managed automatically and remains disabled."),
    )
    return HttpResponse("<script>window.location.reload()</script>")


@login_required
def check_in_check_out_setting(request):
    """
    Check in check out setting
    """
    AttendanceGeneralSetting.objects.get_or_create(company_id=None)
    AttendanceGeneralSetting.objects.all().update(enable_check_in=False)
    attendance_settings = AttendanceGeneralSetting.objects.all().order_by("company_id__company")
    return render(
        request,
        "attendance/settings/check_in_check_out_enable_form.html",
        {"attendance_settings": attendance_settings},
    )


@login_required
@permission_required("attendance.change_attendancegeneralsetting")
def enable_disable_check_in(request):
    """
    Persist role-based attendance eligibility while keeping web Check-In/Check-Out locked.
    """
    if request.method == "POST":
        setting_id = request.POST.get("setting_Id")
        setting = AttendanceGeneralSetting.objects.filter(id=setting_id).first()
        if setting is not None:
            setting.enable_check_in = False
            setting.allow_reporting_manager_attendance = (
                request.POST.get("allow_reporting_manager_attendance") == "on"
            )
            setting.allow_admin_attendance = (
                request.POST.get("allow_admin_attendance") == "on"
            )
            setting.save()
            messages.success(request, _("Attendance access settings updated successfully."))
        else:
            messages.error(request, _("Attendance setting was not found."))
    return redirect("check-in-check-out-setting")


@login_required
@permission_required("attendance.view_attendancevalidationcondition")
def grace_time_view(request):
    """
    This method view attendance validation conditions.
    """
    condition = AttendanceValidationCondition.objects.first()
    default_grace_time = GraceTime.objects.filter(is_default=True).first()
    grace_times = GraceTime.objects.all().exclude(is_default=True)
    return render(
        request,
        "attendance/grace_time/grace_time.html",
        {
            "condition": condition,
            "default_grace_time": default_grace_time,
            "grace_times": grace_times,
        },
    )


@login_required
@permission_required("attendance.view_attendancevalidationcondition")
def validation_condition_view(request):
    """
    This method view attendance validation conditions.
    """

    condition = AttendanceValidationCondition.objects.first()
    default_grace_time = GraceTime.objects.filter(is_default=True).first()
    return render(
        request,
        "attendance/break_point/condition.html",
        {"condition": condition, "default_grace_time": default_grace_time},
    )


@login_required
@permission_required("attendance.add_attendancevalidationcondition")
def validation_condition_create(request):
    """
    This method render a form to create attendance validation conditions,
    and create if the form is valid.
    """
    form = AttendanceValidationConditionForm()
    if request.method == "POST":
        form = AttendanceValidationConditionForm(request.POST)
        if form.is_valid():
            form.save()
            messages.success(request, _("Attendance Break-point settings created."))
            form = AttendanceValidationConditionForm()
    return render(
        request,
        "attendance/break_point/condition_form.html",
        {"form": form},
    )


@login_required
@hx_request_required
@permission_required("attendance.change_attendancevalidationcondition")
def validation_condition_update(request, obj_id):
    """
    This method is used to update validation condition
    Args:
        obj_id : validation condition instance id
    """
    condition = AttendanceValidationCondition.objects.get(id=obj_id)
    form = AttendanceValidationConditionForm(instance=condition)
    if request.method == "POST":
        form = AttendanceValidationConditionForm(request.POST, instance=condition)
        if form.is_valid():
            form.save()
            messages.success(request, _("Attendance Break-point settings updated."))
    return render(
        request,
        "attendance/break_point/condition_form.html",
        {"form": form, "condition": condition},
    )


@login_required
@permission_required("attendance.add_attendance")
def allowed_ips(request):
    """
    This function is used to view the allowed ips
    """
    allowed_ips = AttendanceAllowedIP.objects.first()
    return render(
        request,
        "attendance/ip_restriction/ip_restriction.html",
        {"allowed_ips": allowed_ips},
    )


@login_required
@permission_required("attendance.add_attendance")
def enable_ip_restriction(request):
    """
    This function is used to enable the allowed ips
    """
    form = AttendanceAllowedIPForm()
    if request.method == "POST":
        ip_restiction = AttendanceAllowedIP.objects.first()

        if not ip_restiction:
            ip_restiction = AttendanceAllowedIP.objects.create(is_enabled=True)
            return HttpResponse("<script>window.location.reload()</script>")

        if not ip_restiction.is_enabled:
            ip_restiction.is_enabled = True
        elif ip_restiction.is_enabled:
            ip_restiction.is_enabled = False

        ip_restiction.save()
        return HttpResponse("<script>window.location.reload()</script>")


def validate_ip_address(self, value):
    """
    This function is used to check if the provided IP is in the ipv4 or ipv6 format.

    Args:
        value: The IP address to validate
    """
    try:
        validate_ipv46_address(value)
    except ValidationError:
        raise ValidationError("Enter a valid IPv4 or IPv6 address.")
    return value


@login_required
@permission_required("attendance.add_attendance")
def create_allowed_ips(request):
    """
    This function is used to create the allowed IPs.
    """
    if request.method == "POST":
        form = AttendanceAllowedIPForm(request.POST)
        if form.is_valid():
            ip_addresses = form.cleaned_data.get("ip_addresses")
            allowed_ips = AttendanceAllowedIP.objects.first()
            if allowed_ips:
                existing_ips = set(allowed_ips.additional_data.get("allowed_ips", []))
                new_ips = set(ip_addresses)
                duplicates = new_ips.intersection(existing_ips)

                if duplicates:
                    messages.error(
                        request, f"IP addresses already exist: {', '.join(duplicates)}"
                    )

                non_duplicates = new_ips - duplicates

                if non_duplicates:
                    allowed_ips.additional_data["allowed_ips"] = list(
                        existing_ips.union(non_duplicates)
                    )
                    allowed_ips.save()
                    messages.success(request, "IP addresses saved successfully")
                else:
                    messages.info(
                        request,
                        "All provided IP addresses are already in the allowed list.",
                    )

            else:
                AttendanceAllowedIP.objects.create(
                    is_enabled=True, additional_data={"allowed_ips": ip_addresses}
                )
                messages.success(request, "IP addresses saved successfully")

            return HttpResponse("<script>window.location.reload()</script>")
    else:
        form = AttendanceAllowedIPForm()

    return render(
        request, "attendance/ip_restriction/restrict_form.html", {"form": form}
    )


@login_required
@permission_required("attendance.delete_attendance")
def delete_allowed_ips(request):
    """
    This function is used to delete the allowed ips
    """
    try:
        ids = request.GET.getlist("id")
        allowed_ips = AttendanceAllowedIP.objects.first()
        ips = allowed_ips.additional_data["allowed_ips"]
        for id in ids:
            ips.pop(eval_validate(id))

        allowed_ips.additional_data["allowed_ips"] = ips
        allowed_ips.save()

        messages.success(request, "IP address removed successfully")
    except:
        messages.error(request, "Invalid id")
    return redirect("allowed-ips")


@login_required
@permission_required("attendance.change_attendance")
def edit_allowed_ips(request):
    """
    This function is used to edit the allowed IPs.
    """
    allowed_ips = AttendanceAllowedIP.objects.first()
    if not allowed_ips:
        messages.error(request, "No allowed IPs found.")
        return redirect("allowed-ips")

    ips = allowed_ips.additional_data.get("allowed_ips", [])
    id = request.GET.get("id")

    try:
        id = int(id)
        if id < 0 or id >= len(ips):
            raise IndexError

        initial_ip = ips[id]
        form = AttendanceAllowedIPForm(initial={"ip_addresses": initial_ip})

        if request.method == "POST":
            form = AttendanceAllowedIPForm(request.POST)
            if form.is_valid():
                new_ip = form.cleaned_data["ip_addresses"][0]

                existing_ips = set(allowed_ips.additional_data.get("allowed_ips", []))

                if new_ip in existing_ips:
                    messages.error(request, "IP address already exists.")
                else:
                    existing_ips.discard(initial_ip)
                    existing_ips.add(new_ip)

                    allowed_ips.additional_data["allowed_ips"] = list(existing_ips)
                    allowed_ips.save()
                    messages.success(request, "IP address updated successfully")
                return HttpResponse("<script>window.location.reload()</script>")

    except (ValueError, IndexError):
        messages.error(request, "Invalid ID provided.")

    return render(
        request,
        "attendance/ip_restriction/restrict_form.html",
        {"form": form, "id": id},
    )
