"""
requests.py

This module is used to register the endpoints to the attendance requests
"""

import copy
import json
from datetime import date, datetime, time
from urllib.parse import parse_qs

from django.contrib import messages
from django.core.exceptions import ValidationError
from django.db import transaction
from django.db.models import ProtectedError, Q, Count
from django.http import HttpResponse, HttpResponseRedirect, JsonResponse, HttpResponseForbidden
from django.shortcuts import redirect, render
from django.template.loader import render_to_string
from django.urls import reverse
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
    shift_schedule_today,
)
from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceLateComeEarlyOut,
    AttendanceRequestComment,
    AttendanceRequestFile,
    BatchAttendance,
)
from attendance.views.clock_in_out import early_out, late_come
import attendance.views.clock_in_out as cio
from base.methods import (
    choosesubordinates,
    closest_numbers,
    eval_validate,
    filtersubordinates,
    get_key_instances,
    is_reportingmanager,
)
from base.models import EmployeeShift, EmployeeShiftDay, EmployeeShiftSchedule
from employee.models import Employee
from horilla.decorators import (
    hx_request_required,
    login_required,
    manager_can_enter,
    permission_required,
)
from notifications.signals import notify


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
    """Sync AttendanceActivity to match Attendance for single-session mode.

    Rules:
    - Keep **exactly one** AttendanceActivity per (employee, attendance_date).
    - Activity.clock_in is NOT NULL in the model, so if Attendance check-in is missing,
      we use a placeholder clock-in (clock-out if available, else 00:00).
    - If the request changes attendance_date, we clean up old-date activities.
    """

    employee = attendance.employee_id
    target_date = attendance.attendance_date

    # If the request moved the attendance_date, clean up old-date activities.
    if prev_attendance_date and prev_attendance_date != target_date:
        old_qs = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=prev_attendance_date)
        if old_qs.exists():
            # If no activity exists on the new date, move the old ones.
            if not AttendanceActivity.objects.filter(employee_id=employee, attendance_date=target_date).exists():
                old_qs.update(attendance_date=target_date)
            else:
                # Otherwise, delete old ones to avoid duplicates across dates.
                old_qs.delete()

    # Keep the latest activity as the canonical one, delete duplicates.
    qs = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=target_date).order_by("-id")
    activity = qs.first()
    if activity:
        qs.exclude(id=activity.id).delete()
    else:
        activity = AttendanceActivity(employee_id=employee, attendance_date=target_date)

    # Ensure shift day exists
    day = attendance.attendance_day
    if not day:
        day_name = target_date.strftime("%A").lower()
        day = EmployeeShiftDay.objects.get(day=day_name)

    # Non-null clock_in placeholder (single-session skeleton support)
    clock_in_date = attendance.attendance_clock_in_date or attendance.attendance_clock_out_date or target_date
    clock_in_time = attendance.attendance_clock_in or attendance.attendance_clock_out or time(0, 0)

    activity.shift_day = day
    activity.clock_in_date = clock_in_date
    activity.clock_in = clock_in_time
    activity.in_datetime = datetime.combine(clock_in_date, clock_in_time)

    # Sync OUT fields
    if attendance.attendance_clock_out and attendance.attendance_clock_out_date:
        activity.clock_out_date = attendance.attendance_clock_out_date
        activity.clock_out = attendance.attendance_clock_out
        activity.out_datetime = datetime.combine(attendance.attendance_clock_out_date, attendance.attendance_clock_out)
    else:
        activity.clock_out_date = None
        activity.clock_out = None
        activity.out_datetime = None

    activity.save()
    return activity


def _refresh_late_come_early_out(attendance: Attendance):
    """Recompute Late Come / Early Out records using schedule-level grace time."""

    shift = attendance.shift_id
    if not shift:
        return

    day_name = attendance.attendance_date.strftime("%A").lower()
    day = EmployeeShiftDay.objects.get(day=day_name)

    # Remove existing markers for this attendance (because times may have changed)
    AttendanceLateComeEarlyOut.objects.filter(
        attendance_id=attendance, type__in=["late_come", "early_out"]
    ).delete()

    _, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)
    schedule = _get_shift_schedule(shift, day)

    if attendance.attendance_clock_in:
        late_come(attendance, start_time=start_time_sec, end_time=end_time_sec, shift=shift, schedule=schedule)

    if attendance.attendance_clock_out:
        early_out(attendance, start_time=start_time_sec, end_time=end_time_sec, shift=shift, schedule=schedule)


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
def request_attendance_view(request):
    """Attendance Requests page aligned with mobile Attendance Correction Request.

    Two tabs:
      - My Requests: current user's requests (pending + history)
      - Approvals: pending requests the current user can approve (admin/reporting manager)
    """
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = bool(getattr(request.user, "has_perm", lambda _p: False)("attendance.change_attendance"))

    # Some deployments have admin users not linked to Employee.
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    search = (request.GET.get("search") or "").strip()
    status_my = (request.GET.get("status_my") or "all").strip().lower()
    allowed_status_my = {"all", "waiting", "approved", "rejected", "canceled", "cancel"}
    if status_my not in allowed_status_my:
        status_my = "all"

    # ----------------------------
    # Build Approvals queryset
    # ----------------------------
    approvals_qs = Attendance.objects.filter(is_validate_request=True)

    # Hardening:
    # - Superuser/global approver can see all pending requests.
    # - Reporting manager can see pending requests of subordinates.
    # - Others see none.
    if is_reportingmanager(request) and not (has_global_perm or is_super):
        approvals_qs = filtersubordinates(
            request=request,
            perm="attendance.change_attendance",
            queryset=approvals_qs,
        )
    elif not (has_global_perm or is_super):
        approvals_qs = Attendance.objects.none()

    # Never include own requests in approvals list (cannot self-approve)
    approvals_qs = approvals_qs.exclude(employee_id__employee_user_id=request.user)

    # ----------------------------
    # Build My Requests queryset
    # ----------------------------
    my_qs = Attendance.objects.filter(employee_id__employee_user_id=request.user).filter(
        Q(is_validate_request=True)
        | Q(is_validate_request_approved=True)
        | Q(
            request_type__in=[
                "create_request",
                "update_request",
                "revalidate_request",
                "cancel_request",
                "reject_request",
            ]
        )
        | Q(request_description__isnull=False)
        | Q(requested_data__isnull=False)
    ).distinct()

    # My Requests status filter
    if status_my == "waiting":
        my_qs = my_qs.filter(is_validate_request=True)
    elif status_my == "approved":
        my_qs = my_qs.filter(Q(is_validate_request_approved=True) | Q(attendance_validated=True)).exclude(is_validate_request=True)
    elif status_my == "rejected":
        my_qs = my_qs.filter(request_type="reject_request")
    elif status_my in ("canceled", "cancel"):
        my_qs = my_qs.filter(request_type="cancel_request")

    # Shared search filter
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

    # Pagination (separate query params)
    page_my = request.GET.get("page_my")
    page_app = request.GET.get("page_app")

    my_requests = paginator_qry(
        my_qs.select_related("employee_id", "approved_by", "shift_id", "work_type_id").order_by("-id"),
        page_my,
    )
    approvals = paginator_qry(
        approvals_qs.select_related("employee_id", "approved_by", "shift_id", "work_type_id").order_by("-id"),
        page_app,
    )

    # Attachment counts for current page (used as badges like Work Type Requests)
    try:
        my_ids = [obj.id for obj in getattr(my_requests, "object_list", [])]
        app_ids = [obj.id for obj in getattr(approvals, "object_list", [])]
        my_attach_counts = {
            row["request_id_id"]: row["cnt"]
            for row in AttendanceRequestComment.objects.filter(request_id_id__in=my_ids)
            .values("request_id_id")
            .annotate(cnt=Count("files", distinct=True))
        }
        app_attach_counts = {
            row["request_id_id"]: row["cnt"]
            for row in AttendanceRequestComment.objects.filter(request_id_id__in=app_ids)
            .values("request_id_id")
            .annotate(cnt=Count("files", distinct=True))
        }
    except Exception:
        my_attach_counts = {}
        app_attach_counts = {}

    # Shift info for current page (name + start/end + flexi in)
    try:
        my_shift_info = _build_shift_info_map(list(getattr(my_requests, 'object_list', []) or []))
        app_shift_info = _build_shift_info_map(list(getattr(approvals, 'object_list', []) or []))
    except Exception:
        my_shift_info = {}
        app_shift_info = {}

    can_approve = bool(
        request.user.has_perm("attendance.change_attendance") or is_reportingmanager(request)
    )

    status_my_options = [
        ("all", _("All")),
        ("waiting", _("Waiting")),
        ("approved", _("Approved")),
        ("rejected", _("Rejected")),
        ("canceled", _("Canceled")),
    ]



    # Preserve filters for pagination links
    try:
        q_my = request.GET.copy()
        q_my.pop("page_my", None)
        pd_my = q_my.urlencode()
        q_app = request.GET.copy()
        q_app.pop("page_app", None)
        pd_app = q_app.urlencode()
    except Exception:
        pd_my = ""
        pd_app = ""

    return render(
        request,
        "attendance/attendance_requests/view.html",
        {
            "my_requests": my_requests,
            "approvals": approvals,
            "can_approve": can_approve,
            "search": search,
            "status_my": status_my,
            "status_my_options": status_my_options,
            "my_attach_counts": my_attach_counts,
            "app_attach_counts": app_attach_counts,
            "my_shift_info": my_shift_info,
            "app_shift_info": app_shift_info,
            "pd_my": pd_my,
            "pd_app": pd_app,
        },
    )




@login_required
@hx_request_required
def request_new(request):
    """
    This method is used to create new attendance requests
    """

    if request.GET.get("bulk") and eval_validate(request.GET.get("bulk")):
        # Attendance Correction Request (mobile parity): no bulk/batch create flow in this UI.
        return HttpResponseForbidden(_("Bulk attendance request is not available here."))
    if request.GET.get("employee_id"):
        form = NewRequestForm(initial=request.GET.dict())
    else:
        form = NewRequestForm()
    form = choosesubordinates(request, form, "attendance.change_attendance")
    employees_qs = Employee.objects.filter(
        Q(id__in=form.fields["employee_id"].queryset.values_list("id", flat=True))
        | Q(employee_user_id=request.user)
    )

    form.fields["employee_id"].queryset = employees_qs.distinct()
    form.fields["employee_id"].initial = request.user.employee_get.id
    if request.GET.get("emp_id"):
        emp_id = request.GET.get("emp_id")
        form.fields["employee_id"].queryset = Employee.objects.filter(id=emp_id)
        form.fields["employee_id"].initial = emp_id
    if request.method == "POST":
        form = NewRequestForm(request.POST, files=getattr(request, 'FILES', None))
        employees_qs = Employee.objects.filter(
            Q(id__in=form.fields["employee_id"].queryset.values_list("id", flat=True))
            | Q(employee_user_id=request.user)
        )
        form.fields["employee_id"].queryset = employees_qs.distinct()
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

            # Attach optional proof files (same as mobile/API: field name "files")
            try:
                from attendance.models import AttendanceRequestFile, AttendanceRequestComment

                uploaded = []
                if hasattr(request, "FILES"):
                    uploaded = request.FILES.getlist("files") or request.FILES.getlist("files[]") or []
                    if not uploaded:
                        f_single = request.FILES.get("file")
                        if f_single:
                            uploaded = [f_single]

                if attendance_obj and uploaded:
                    try:
                        actor_emp = request.user.employee_get
                    except Exception:
                        actor_emp = getattr(attendance_obj, "employee_id", None)

                    comment_text = (request.POST.get("request_description") or request.POST.get("reason") or "").strip()
                    c = AttendanceRequestComment.objects.create(
                        request_id=attendance_obj,
                        employee_id=actor_emp,
                        comment=(comment_text[:255] if comment_text else None),
                    )
                    for up in uploaded:
                        arf = AttendanceRequestFile.objects.create(file=up)
                        c.files.add(arf)
            except Exception:
                pass

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
            grace = getattr(shift, "grace_time_id", None)
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
                    attendance.requested_data = json.dumps(wrapped)
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
                    attendance.requested_data = json.dumps(instance.serialize())
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
        other_dict = json.loads(attendance.requested_data)

    requests_ids_json = request.GET.get("requests_ids")
    previous_instance_id = next_instance_id = attendance.pk
    if requests_ids_json:
        previous_instance_id, next_instance_id = closest_numbers(
            json.loads(requests_ids_json), attendance_id
        )

    # Attachments count (used for UI parity with Work Type Requests)
    try:
        attachment_count = (
            AttendanceRequestComment.objects.filter(request_id=attendance)
            .aggregate(cnt=Count("files", distinct=True))
            .get("cnt")
            or 0
        )
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

    # Approve request flags (these fields are NOT included in serialize/requested_data)
    attendance.attendance_validated = True
    attendance.is_validate_request_approved = True
    attendance.is_validate_request = False
    try:
        attendance.approved_by = request.user.employee_get
    except Exception:
        attendance.approved_by = None
    # Keep request_description for history
    attendance.save()

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

        requested_data = _normalize_requested_data(json.loads(attendance.requested_data))
        Attendance.objects.filter(id=attendance_id).update(**requested_data)

        # Re-fetch to ensure types are correct (TimeField -> datetime.time, etc.)
        attendance.refresh_from_db()

        # Save once more to trigger Attendance.save() side effects (e.g., overtime calc)
        attendance.attendance_validated = True
        attendance.is_validate_request_approved = True
        attendance.is_validate_request = False
        attendance.save()

    # -----------------------------------------------------------------
    # SINGLE-SESSION SYNC
    # Ensure there is exactly ONE AttendanceActivity per (employee, attendance_date)
    # and keep it aligned with the approved Attendance values.
    # -----------------------------------------------------------------
    _ensure_single_session_activity(attendance, prev_attendance_date=prev_attendance_date)
    _refresh_late_come_early_out(attendance)

    # -------------------------------------------------------------
    # FINAL spec: If approving an attendance request that effectively
    # approves an early-checkout which was previously REJECTED,
    # flip OUT status back to VALID + clear reject reason.
    # Also recompute worked hours using shift_start as baseline.
    # -------------------------------------------------------------
    try:
        if (
            getattr(attendance, "out_attendance_status", None) == "REJECTED"
            and getattr(attendance, "out_attendance_reject_reason_code", None)
            in (
                "EARLY_CHECKOUT_BEFORE_SHIFT_END",
                "EARLY_CHECKOUT_BEFORE_CUTOFF_IN",
            )
        ):
            attendance.out_attendance_status = "VALID"
            attendance.out_attendance_reject_reason_code = None

            # Recompute worked hours from max(real_in, shift_start)
            if (
                attendance.attendance_clock_in_date
                and attendance.attendance_clock_in
                and attendance.attendance_clock_out_date
                and attendance.attendance_clock_out
            ):
                shift = getattr(attendance, "shift_id", None)
                day_obj = getattr(attendance, "attendance_day", None)
                if shift and day_obj:
                    _min_h, start_sec, end_sec = shift_schedule_today(day=day_obj, shift=shift)
                    rules = cio.get_shift_rules(
                        attendance.attendance_date,
                        shift,
                        day_obj,
                        start_time_sec=start_sec,
                        end_time_sec=end_sec,
                    )
                    shift_start_dt = rules.get("shift_start_dt")
                else:
                    shift_start_dt = None

                in_dt = cio._combine_local_datetime(attendance.attendance_clock_in_date, attendance.attendance_clock_in)
                out_dt = cio._combine_local_datetime(attendance.attendance_clock_out_date, attendance.attendance_clock_out)

                worked_start_dt = max(in_dt, shift_start_dt) if shift_start_dt else in_dt
                duration_seconds = int((out_dt - worked_start_dt).total_seconds())
                if duration_seconds < 0:
                    duration_seconds = 0

                attendance.attendance_worked_hour = cio.format_time(duration_seconds)
                attendance.attendance_overtime = cio.overtime_calculation(attendance)
            attendance.save()
    except Exception:
        # Approval must not fail due to window recompute.
        pass

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

        # Only pending requests can be canceled
        if not getattr(attendance, "is_validate_request", False):
            messages.error(request, _("Only pending requests can be canceled."))
            return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))

        req_type = attendance.request_type
        req_date = attendance.attendance_date
        req_employee = attendance.employee_id

        attendance.is_validate_request_approved = False
        attendance.is_validate_request = False
        # Discard pending payload but keep request_description for history
        attendance.requested_data = None
        attendance.request_type = "cancel_request"
        try:
            attendance.approved_by = request.user.employee_get
        except Exception:
            attendance.approved_by = None
        attendance.save()

        # For create_request, remove derived daily artifacts so it won't affect reporting.
        if req_type == "create_request":
            AttendanceActivity.objects.filter(
                employee_id=req_employee,
                attendance_date=req_date,
            ).delete()
            AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()

        messages.success(request, _("Attendance request canceled."))

    except Attendance.DoesNotExist:
        messages.error(request, _("Attendance request not found"))
    except Exception:
        messages.error(request, _("Something went wrong."))

    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@manager_can_enter("attendance.change_attendance")
@transaction.atomic
def reject_validate_attendance_request(request, attendance_id):
    """Reject an attendance request (approver action).

    Aligned with mobile Attendance Correction Request:
    - Owner cannot reject own request (use cancel)
    - Only WAITING requests can be rejected
    - Keep the Attendance row for history (status=REJECTED)
    """
    try:
        # Fetch via permission-filtered queryset to ensure manager/admin scope
        qs = Attendance.objects.filter(id=attendance_id, is_validate_request=True)
        qs = filtersubordinates(
            request=request,
            perm="attendance.change_attendance",
            queryset=qs,
        )
        attendance = qs.select_for_update().get()

        # Disallow rejecting your own request
        try:
            if attendance.employee_id.employee_user_id == request.user:
                messages.error(request, _("Use cancel for your own request."))
                return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))
        except Exception:
            pass

        req_type = attendance.request_type
        req_date = attendance.attendance_date
        req_employee = attendance.employee_id

        attendance.is_validate_request_approved = False
        attendance.is_validate_request = False
        attendance.requested_data = None
        attendance.request_type = "reject_request"
        try:
            attendance.approved_by = request.user.employee_get
        except Exception:
            attendance.approved_by = None
        attendance.save()

        # For create_request, remove derived daily artifacts so it won't affect reporting.
        if req_type == "create_request":
            AttendanceActivity.objects.filter(
                employee_id=req_employee,
                attendance_date=req_date,
            ).delete()
            AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()

        messages.success(request, _("Attendance request rejected."))

    except Attendance.DoesNotExist:
        messages.error(request, _("Attendance request not found"))
    except Exception:
        messages.error(request, _("Something went wrong."))

    return HttpResponseRedirect(request.META.get("HTTP_REFERER", "/"))


@login_required
@hx_request_required
def attendance_request_attachments(request, attendance_id):
    """HTMX modal: show Attendance Request attachments."""
    attendance = Attendance.objects.filter(id=attendance_id).first()
    if not attendance:
        return render(
            request,
            "attendance/attendance_requests/attachments_modal.html",
            {"req": None, "files": []},
        )

    # Allow: owner OR manager/admin with attendance perms
    try:
        is_owner = attendance.employee_id.employee_user_id == request.user
    except Exception:
        is_owner = False

    if not (
        is_owner
        or is_reportingmanager(request)
        or request.user.has_perm("attendance.change_attendance")
        or request.user.has_perm("attendance.view_attendance")
    ):
        return HttpResponseForbidden("Permission denied")

    files = []
    try:
        comments = AttendanceRequestComment.objects.filter(request_id=attendance).prefetch_related("files")
        seen = set()
        for c in comments:
            for f in c.files.all():
                if f and f.id not in seen:
                    seen.add(f.id)
                    files.append(f)
    except Exception:
        files = []

    return render(
        request,
        "attendance/attendance_requests/attachments_modal.html",
        {"req": attendance, "files": files},
    )





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

        # Mark approved
        attendance.attendance_validated = True
        attendance.is_validate_request_approved = True
        attendance.is_validate_request = False
        attendance.save()

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

            requested_data = _normalize_requested_data(json.loads(attendance.requested_data))
            Attendance.objects.filter(id=attendance_id).update(**requested_data)
            attendance.refresh_from_db()
            attendance.save()

        # Keep single-session activity consistent
        _ensure_single_session_activity(attendance, prev_attendance_date=prev_attendance_date)
        _refresh_late_come_early_out(attendance)

        messages.success(request, _("Attendance request has been approved"))

        employee = attendance.employee_id
        notify.send(
            request.user,
            recipient=employee.employee_user_id,
            verb=f"Your attendance request for {attendance.attendance_date} is validated",
            verb_ar=f"تم التحقق من طلب حضورك في تاريخ {attendance.attendance_date}",
            verb_de=f"Ihr Anwesenheitsantrag für das Datum {attendance.attendance_date} wurde bestätigt",
            verb_es=f"Se ha validado su solicitud de asistencia para la fecha {attendance.attendance_date}",
            verb_fr=f"Votre demande de présence pour la date {attendance.attendance_date} est validée",
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
                verb=(
                    f"{employee.employee_first_name} {user_last_name}'s attendance request for "
                    f"{attendance.attendance_date} is validated"
                ),
                verb_ar=(
                    f"تم التحقق من طلب الحضور لـ {employee.employee_first_name} {user_last_name} "
                    f"في {attendance.attendance_date}"
                ),
                verb_de=(
                    f"Die Anwesenheitsanfrage von {employee.employee_first_name} {user_last_name} "
                    f"für den {attendance.attendance_date} wurde validiert"
                ),
                verb_es=(
                    f"Se ha validado la solicitud de asistencia de {employee.employee_first_name} "
                    f"{user_last_name} para el {attendance.attendance_date}"
                ),
                verb_fr=(
                    f"La demande de présence de {employee.employee_first_name} {user_last_name} "
                    f"pour le {attendance.attendance_date} a été validée"
                ),
                redirect=reverse("request-attendance-view") + f"?id={attendance.id}",
                icon="checkmark-circle-outline",
            )

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
            req_date = attendance.attendance_date
            req_employee = attendance.employee_id

            attendance.is_validate_request_approved = False
            attendance.is_validate_request = False
            attendance.requested_data = None
            attendance.request_type = "reject_request"
            try:
                attendance.approved_by = request.user.employee_get
            except Exception:
                attendance.approved_by = None
            attendance.save()

            if req_type == "create_request":
                AttendanceActivity.objects.filter(
                    employee_id=req_employee,
                    attendance_date=req_date,
                ).delete()
                AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()

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
            initial = json.loads(attendance.requested_data)
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
                attendance.requested_data = json.dumps(instance.serialize())
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
