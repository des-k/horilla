"""
requests.py

This module is used to register the endpoints to the attendance requests
"""

import copy
import json
from datetime import date, datetime, time
from urllib.parse import parse_qs

from django.contrib import messages
from django.db import transaction
from django.db.models import ProtectedError, Q
from django.http import HttpResponse, HttpResponseRedirect, JsonResponse
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
    BatchAttendance,
)
from attendance.views.clock_in_out import early_out, late_come
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
    """Ensure requested_data from JSON can be safely used in queryset.update()."""
    if not requested_data:
        return requested_data

    # AttendanceRequestForm.serialize() returns strings for time/date fields.
    # Some values may be the literal string "None".
    for key in (
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
    ):
        if key in requested_data:
            requested_data[key] = _normalize_none(requested_data[key])

    return requested_data


def _get_shift_schedule(shift, day):
    """Schedule-level lookup for grace time & cutoffs."""
    return EmployeeShiftSchedule.objects.filter(shift_id=shift, day=day).first()


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
    """
    This method is used to view the attendances for to request
    """
    requests = Attendance.objects.filter(
        is_validate_request=True,
    )
    requests = filtersubordinates(
        request=request,
        perm="attendance.view_attendance",
        queryset=requests,
    )
    requests = requests | Attendance.objects.filter(
        employee_id__employee_user_id=request.user,
        is_validate_request=True,
    )
    requests = AttendanceFilters(request.GET, requests).qs
    previous_data = request.GET.urlencode()
    data_dict = parse_qs(previous_data)
    get_key_instances(Attendance, data_dict)

    keys_to_remove = [key for key, value in data_dict.items() if value == ["unknown"]]
    for key in keys_to_remove:
        data_dict.pop(key)
    attendances = filtersubordinates(
        request=request,
        perm="attendance.view_attendance",
        queryset=Attendance.objects.all(),
    )
    attendances = attendances | Attendance.objects.filter(
        employee_id__employee_user_id=request.user
    )
    attendances = attendances.filter(
        employee_id__is_active=True,
    )
    attendances = AttendanceFilters(request.GET, attendances).qs
    filter_obj = AttendanceFilters()
    check_attendance = Attendance.objects.all()
    if check_attendance.exists():
        template = "requests/attendance/view-requests.html"
    else:
        template = "requests/attendance/requests_empty.html"
    requests_ids = json.dumps(
        [instance.id for instance in paginator_qry(requests, None).object_list]
    )
    attendances_ids = json.dumps(
        [instance.id for instance in paginator_qry(attendances, None).object_list]
    )
    requests = requests.filter(
        employee_id__is_active=True,
    )
    return render(
        request,
        template,
        {
            "requests": paginator_qry(requests, None),
            "attendances": paginator_qry(attendances, None),
            "requests_ids": requests_ids,
            "attendances_ids": attendances_ids,
            "f": filter_obj,
            "filter_dict": data_dict,
            "gp_fields": AttendanceRequestReGroup.fields,
        },
    )


@login_required
@hx_request_required
def request_new(request):
    """
    This method is used to create new attendance requests
    """

    if request.GET.get("bulk") and eval_validate(request.GET.get("bulk")):
        employee = request.user.employee_get
        if request.GET.get("employee_id"):
            form = BulkAttendanceRequestForm(initial=request.GET)
        else:
            form = BulkAttendanceRequestForm(initial={"employee_id": employee})
        if request.method == "POST":
            form = BulkAttendanceRequestForm(request.POST)
            form.instance.attendance_clock_in_date = request.POST.get("from_date")
            form.instance.attendance_date = request.POST.get("from_date")
            if form.is_valid():
                instance = form.save(commit=False)
                messages.success(request, _("Attendance request created"))
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
            {"form": form, "bulk": True},
        )
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
        form = NewRequestForm(request.POST)
        employees_qs = Employee.objects.filter(
            Q(id__in=form.fields["employee_id"].queryset.values_list("id", flat=True))
            | Q(employee_user_id=request.user)
        )
        form.fields["employee_id"].queryset = employees_qs.distinct()
        if form.is_valid():
            if form.new_instance is not None:
                form.new_instance.save()
                messages.success(request, _("New attendance request created"))
                return HttpResponse(
                    render(
                        request,
                        "requests/attendance/request_new_form.html",
                        {"form": form},
                    ).content.decode("utf-8")
                    + "<script>location.reload();</script>"
                )
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
        first_dict = empty_data
    else:
        other_dict = json.loads(attendance.requested_data)
    requests_ids_json = request.GET.get("requests_ids")
    previous_instance_id = next_instance_id = attendance.pk
    if requests_ids_json:
        previous_instance_id, next_instance_id = closest_numbers(
            json.loads(requests_ids_json), attendance_id
        )
    return render(
        request,
        "requests/attendance/individual_view.html",
        {
            "data": get_diff_dict(first_dict, other_dict, Attendance),
            "attendance": attendance,
            "previous": previous_instance_id,
            "next": next_instance_id,
            "requests_ids": requests_ids_json,
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
    prev_attendance_date = attendance.attendance_date

    # Approve request flags (these fields are NOT included in serialize/requested_data)
    attendance.attendance_validated = True
    attendance.is_validate_request_approved = True
    attendance.is_validate_request = False
    attendance.request_description = None
    attendance.save()

    # Apply requested field changes (if any)
    if attendance.requested_data:
        requested_data = _normalize_requested_data(json.loads(attendance.requested_data))
        Attendance.objects.filter(id=attendance_id).update(**requested_data)

        # Re-fetch to ensure types are correct (TimeField -> datetime.time, etc.)
        attendance.refresh_from_db()

        # Save once more to trigger Attendance.save() side effects (e.g., overtime calc)
        attendance.attendance_validated = True
        attendance.is_validate_request_approved = True
        attendance.is_validate_request = False
        attendance.request_description = None
        attendance.save()

    # -----------------------------------------------------------------
    # SINGLE-SESSION SYNC
    # Ensure there is exactly ONE AttendanceActivity per (employee, attendance_date)
    # and keep it aligned with the approved Attendance values.
    # -----------------------------------------------------------------
    _ensure_single_session_activity(attendance, prev_attendance_date=prev_attendance_date)
    _refresh_late_come_early_out(attendance)

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
def cancel_attendance_request(request, attendance_id):
    """
    This method is used to cancel attendance request
    """
    try:
        attendance = Attendance.objects.get(id=attendance_id)
        if (
            attendance.employee_id.employee_user_id == request.user
            or is_reportingmanager(request)
            or request.user.has_perm("attendance.change_attendance")
        ):
            # Keep the original request type before clearing fields
            req_type = attendance.request_type
            req_date = attendance.attendance_date
            req_employee = attendance.employee_id

            attendance.is_validate_request_approved = False
            attendance.is_validate_request = False
            attendance.request_description = None
            attendance.requested_data = None
            attendance.request_type = None

            attendance.save()

            if req_type == "create_request":
                # Single-session cleanup: remove any daily activity linked to that date
                AttendanceActivity.objects.filter(
                    employee_id=req_employee,
                    attendance_date=req_date,
                ).delete()
                AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()
                attendance.delete()
                messages.success(request, _("The requested attendance is removed."))
            else:
                messages.success(request, _("Attendance request has been rejected"))
            employee = attendance.employee_id
            notify.send(
                request.user,
                recipient=employee.employee_user_id,
                verb=f"Your attendance request for {attendance.attendance_date} is rejected",
                verb_ar=f"تم رفض طلبك للحضور في تاريخ {attendance.attendance_date}",
                verb_de=f"Ihre Anwesenheitsanfrage für {attendance.attendance_date} wurde abgelehnt",
                verb_es=f"Tu solicitud de asistencia para el {attendance.attendance_date} ha sido rechazada",
                verb_fr=f"Votre demande de présence pour le {attendance.attendance_date} est rejetée",
                icon="close-circle-outline",
            )
    except (Attendance.DoesNotExist, OverflowError):
        messages.error(request, _("Attendance request not found"))
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
    for attendance_id in ids:
        # Lock row per id to prevent partial updates in concurrent approvals
        attendance = Attendance.objects.select_for_update().get(id=attendance_id)
        prev_attendance_date = attendance.attendance_date

        # Mark approved
        attendance.attendance_validated = True
        attendance.is_validate_request_approved = True
        attendance.is_validate_request = False
        attendance.request_description = None
        attendance.save()

        # Apply requested changes
        if attendance.requested_data is not None:
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
@manager_can_enter("attendance.delete_attendance")
def bulk_reject_attendance_request(request):
    """
    This method is used to delete bulk attendance request
    """
    ids = request.POST["ids"]
    ids = json.loads(ids)
    for attendance_id in ids:
        try:
            attendance = Attendance.objects.get(id=attendance_id)
            if (
                attendance.employee_id.employee_user_id == request.user
                or is_reportingmanager(request)
                or request.user.has_perm("attendance.change_attendance")
            ):
                req_type = attendance.request_type
                emp = attendance.employee_id
                att_date = attendance.attendance_date

                attendance.is_validate_request_approved = False
                attendance.is_validate_request = False
                attendance.request_description = None
                attendance.requested_data = None
                attendance.request_type = None
                attendance.save()

                if req_type == "create_request":
                    # If the request was for creating an attendance, remove the record completely.
                    # Also clean up any activity rows created for that day (single-session).
                    AttendanceActivity.objects.filter(employee_id=emp, attendance_date=att_date).delete()
                    AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()
                    attendance.delete()
                    messages.success(request, _("The requested attendance is removed."))
                else:
                    messages.success(request, _("The requested attendance is rejected."))
                employee = attendance.employee_id
                notify.send(
                    request.user,
                    recipient=employee.employee_user_id,
                    verb=f"Your attendance request for {attendance.attendance_date} is rejected",
                    verb_ar=f"تم رفض طلبك للحضور في تاريخ {attendance.attendance_date}",
                    verb_de=f"Ihre Anwesenheitsanfrage für {attendance.attendance_date} wurde abgelehnt",
                    verb_es=f"Tu solicitud de asistencia para el {attendance.attendance_date} ha sido rechazada",
                    verb_fr=f"Votre demande de présence pour le {attendance.attendance_date} est rejetée",
                    icon="close-circle-outline",
                )
        except (Attendance.DoesNotExist, OverflowError):
            messages.error(request, _("Attendance request not found"))
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
