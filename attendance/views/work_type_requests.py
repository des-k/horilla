"""attendance/views/work_type_requests.py

Web UI (Django templates) for Attendance **Work Type Requests**.

- UI name: Work Type Requests
- DB model: attendance.WorkModeRequest (kept for backwards compatibility)

Spec:
- Allowed request depends on schedule (employee.employee_work_info.work_type_id) for the attendance_date.
- Scopes: IN/OUT single day, FULL date range.
- ON_DUTY requires attachment but may be submitted PENDING and later updated with attachment.
- Approvals list shows only WAITING_FOR_APPROVAL.
"""

from __future__ import annotations

from django.contrib import messages
from django.http import HttpResponse, HttpResponseForbidden
from django.shortcuts import get_object_or_404, render
from django.utils import timezone
from django.utils.translation import gettext_lazy as _

from attendance.forms_work_type_request import (
    WorkTypeRequestCreateForm,
    WorkTypeRequestRejectForm,
    WorkTypeRequestUpdateForm,
)
from attendance.models import (
    AttendanceRequestFile,
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestStatus,
)
from attendance.services.work_type_request_rules import apply_rejection_to_attendance, has_attachments
from attendance.methods.utils import paginator_qry
from base.methods import filtersubordinates, is_reportingmanager
from horilla.decorators import hx_request_required, login_required


def _mode_label(mode: str) -> str:
    if mode == AttendanceWorkMode.ON_DUTY:
        return "ON DUTY"
    return (mode or "").upper()


def _qs_without(request, drop_keys: list[str]) -> str:
    """Return current querystring without certain keys (used for pagination links)."""
    try:
        qd = request.GET.copy()
        for k in drop_keys:
            qd.pop(k, None)
        return qd.urlencode()
    except Exception:
        return ""


def _qs_update(request, **changes) -> str:
    """Return current querystring with selected keys updated/removed.

    - pass value=None to remove the key
    """
    try:
        qd = request.GET.copy()
        for k, v in changes.items():
            if v is None:
                qd.pop(k, None)
            else:
                qd[k] = v
        return qd.urlencode()
    except Exception:
        return ""


def _apply_sort(qs, *, sort_field: str, direction: str, secondary: str = "-id"):
    """Safe order_by helper."""
    prefix = "" if (direction or "").lower() == "asc" else "-"
    try:
        return qs.order_by(f"{prefix}{sort_field}", secondary)
    except Exception:
        return qs


@login_required
def work_type_request_view(request):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    search = (request.GET.get("search") or "").strip()

    # Shared quick filters (apply to both My Requests & Approvals)
    mode_filter = (request.GET.get("mode_filter") or "").strip().lower()
    scope_filter = (request.GET.get("scope_filter") or "").strip().lower()

    allowed_mode_filter = {
        "": None,
        "all": None,
        "wfa": AttendanceWorkMode.WFA,
        "on_duty": AttendanceWorkMode.ON_DUTY,
    }
    allowed_scope_filter = {
        "": None,
        "all": None,
        "in": "in",
        "out": "out",
        "full": "full",
    }

    if mode_filter not in allowed_mode_filter:
        mode_filter = ""
    if scope_filter not in allowed_scope_filter:
        scope_filter = ""

    # Quick filters (My Requests only)
    status_my = (request.GET.get("status_my") or "").strip().lower()
    allowed_status_my = {
        "": None,
        "all": None,
        "pending": WorkModeRequestStatus.PENDING,
        "waiting": WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        "waiting_for_approval": WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        "approved": WorkModeRequestStatus.APPROVED,
        "rejected": WorkModeRequestStatus.REJECTED,
        "canceled": WorkModeRequestStatus.CANCELED,
    }
    if status_my not in allowed_status_my:
        status_my = ""

    # Sorting (independent per table)
    allowed_sort_my = {
        "mode": "mode",
        "scope": "scope",
        "start_date": "start_date",
        "end_date": "end_date",
        "status": "status",
    }
    allowed_sort_app = {
        "employee": "employee_id__employee_first_name",
        "mode": "mode",
        "scope": "scope",
        "start_date": "start_date",
        "end_date": "end_date",
    }

    sort_my = (request.GET.get("sort_my") or "start_date").strip()
    dir_my = (request.GET.get("dir_my") or "desc").strip().lower()
    if sort_my not in allowed_sort_my:
        sort_my = "start_date"
    if dir_my not in ("asc", "desc"):
        dir_my = "desc"

    sort_app = (request.GET.get("sort_app") or "start_date").strip()
    dir_app = (request.GET.get("dir_app") or "desc").strip().lower()
    if sort_app not in allowed_sort_app:
        sort_app = "start_date"
    if dir_app not in ("asc", "desc"):
        dir_app = "desc"

    my_qs = WorkModeRequest.objects.filter(employee_id=employee)

    # Apply shared quick filters
    mode_value = allowed_mode_filter.get(mode_filter)
    if mode_value:
        my_qs = my_qs.filter(mode=mode_value)
    scope_value = allowed_scope_filter.get(scope_filter)
    if scope_value:
        my_qs = my_qs.filter(scope=scope_value)

    # Apply quick filter
    status_value = allowed_status_my.get(status_my)
    if status_value:
        my_qs = my_qs.filter(status=status_value)
    if search:
        try:
            from django.db.models import Q

            my_qs = my_qs.filter(
                Q(mode__icontains=search)
                | Q(scope__icontains=search)
                | Q(status__icontains=search)
            )
        except Exception:
            pass

    # Apply sorting
    my_qs = _apply_sort(my_qs, sort_field=allowed_sort_my[sort_my], direction=dir_my)

    # Approvals: only WAITING_FOR_APPROVAL + exclude self
    can_approve = request.user.has_perm("attendance.change_workmoderequest") or is_reportingmanager(request)

    approvals_qs = WorkModeRequest.objects.filter(status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)
    approvals_qs = filtersubordinates(
        request=request,
        queryset=approvals_qs,
        perm="attendance.change_workmoderequest",
        field="employee_id",
    ).exclude(employee_id=employee)

    # Apply shared quick filters
    if mode_value:
        approvals_qs = approvals_qs.filter(mode=mode_value)
    if scope_value:
        approvals_qs = approvals_qs.filter(scope=scope_value)

    if search:
        try:
            from django.db.models import Q

            approvals_qs = approvals_qs.filter(
                Q(employee_id__employee_first_name__icontains=search)
                | Q(employee_id__employee_last_name__icontains=search)
                | Q(mode__icontains=search)
                | Q(scope__icontains=search)
            )
        except Exception:
            pass

    approvals_qs = _apply_sort(approvals_qs, sort_field=allowed_sort_app[sort_app], direction=dir_app)

    def _sort_url(which: str, field: str) -> str:
        """Build sort link for a table.

        which: 'my'|'app'
        """
        if which == "my":
            current_sort, current_dir = sort_my, dir_my
            sort_key, dir_key, page_key = "sort_my", "dir_my", "page_my"
        else:
            current_sort, current_dir = sort_app, dir_app
            sort_key, dir_key, page_key = "sort_app", "dir_app", "page_app"

        # Toggle direction if clicking active field
        if field == current_sort:
            new_dir = "asc" if current_dir == "desc" else "desc"
        else:
            new_dir = "asc"

        return _qs_update(request, **{sort_key: field, dir_key: new_dir, page_key: None})

    context = {
        "my_requests": paginator_qry(my_qs, request.GET.get("page_my")),
        "approvals": paginator_qry(approvals_qs, request.GET.get("page_app")),
        "can_approve": bool(can_approve),
        "search": search,
        "status_my": status_my,
        "mode_filter": mode_filter,
        "scope_filter": scope_filter,
        "mode_filter_options": [
            ("", _("All")),
            ("wfa", _("WFA")),
            ("on_duty", _("ON DUTY")),
        ],
        "scope_filter_options": [
            ("", _("All")),
            ("in", _("IN")),
            ("out", _("OUT")),
            ("full", _("FULL")),
        ],
        "status_my_options": [
            ("", _("All")),
            ("pending", _("Pending")),
            ("waiting", _("Waiting for approval")),
            ("approved", _("Approved")),
            ("rejected", _("Rejected")),
            ("canceled", _("Canceled")),
        ],
        "mode_label": _mode_label,
        "pd_my": _qs_without(request, ["page_my"]),
        "pd_app": _qs_without(request, ["page_app"]),

        "sort_my": sort_my,
        "dir_my": dir_my,
        "sort_app": sort_app,
        "dir_app": dir_app,
        "sort_my_urls": {
            "mode": _sort_url("my", "mode"),
            "scope": _sort_url("my", "scope"),
            "start_date": _sort_url("my", "start_date"),
            "end_date": _sort_url("my", "end_date"),
            "status": _sort_url("my", "status"),
        },
        "sort_app_urls": {
            "employee": _sort_url("app", "employee"),
            "mode": _sort_url("app", "mode"),
            "scope": _sort_url("app", "scope"),
            "start_date": _sort_url("app", "start_date"),
            "end_date": _sort_url("app", "end_date"),
        },
    }

    return render(request, "attendance/work_type_requests/view.html", context)


@login_required
@hx_request_required
def work_type_request_attachments(request, obj_id: int):
    """HTMX modal: list attachments for a request.

    Access:
    - owner can view
    - approver/manager can view
    """
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    can_approve = request.user.has_perm("attendance.change_workmoderequest") or is_reportingmanager(request)

    if req.employee_id_id != employee.id and not can_approve:
        return HttpResponseForbidden("Not allowed")

    files = req.files.all()
    return render(
        request,
        "attendance/work_type_requests/attachments_modal.html",
        {"req": req, "files": files, "mode_label": _mode_label},
    )


@login_required
@hx_request_required
def work_type_request_create(request):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    form = WorkTypeRequestCreateForm(employee=employee)

    if request.method == "POST":
        form = WorkTypeRequestCreateForm(request.POST, request.FILES, employee=employee)
        if form.is_valid():
            instance: WorkModeRequest = form.save(commit=False)
            instance.employee_id = employee

            # Status rules
            files_in = request.FILES.getlist("files")
            if instance.mode == AttendanceWorkMode.WFA:
                instance.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
            elif instance.mode == AttendanceWorkMode.ON_DUTY:
                instance.status = (
                    WorkModeRequestStatus.WAITING_FOR_APPROVAL
                    if files_in
                    else WorkModeRequestStatus.PENDING
                )
            else:
                # Not allowed by model.clean(), but keep safe.
                instance.status = WorkModeRequestStatus.PENDING

            instance.save()

            # Save attachments
            for f in files_in:
                af = AttendanceRequestFile.objects.create(file=f)
                instance.files.add(af)

            messages.success(request, _(f"Work Type Request created ({_mode_label(instance.mode)})."))
            # reload page (modal context)
            response = render(request, "attendance/work_type_requests/form.html", {"form": form})
            return HttpResponse(response.content.decode("utf-8") + "<script>location.reload();</script>")

    return render(request, "attendance/work_type_requests/form.html", {"form": form})


@login_required
@hx_request_required
def work_type_request_update(request, obj_id: int):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    # Only the owner can add attachments/notes
    if req.employee_id_id != employee.id:
        return HttpResponseForbidden("Not allowed")

    form = WorkTypeRequestUpdateForm(initial={"reason": req.reason or ""})

    if request.method == "POST":
        form = WorkTypeRequestUpdateForm(request.POST, request.FILES)
        if form.is_valid():
            note = (form.cleaned_data.get("reason") or "").strip()
            if note:
                req.reason = note

            files_in = request.FILES.getlist("files")
            for f in files_in:
                af = AttendanceRequestFile.objects.create(file=f)
                req.files.add(af)

            # ON_DUTY: pending -> waiting_for_approval when attachments complete
            if req.mode == AttendanceWorkMode.ON_DUTY and req.status == WorkModeRequestStatus.PENDING:
                if has_attachments(req):
                    req.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL

            req.save()
            messages.success(request, _("Request updated."))
            response = render(
                request,
                "attendance/work_type_requests/update_form.html",
                {"form": form, "req": req, "mode_label": _mode_label},
            )
            return HttpResponse(response.content.decode("utf-8") + "<script>location.reload();</script>")

    return render(
        request,
        "attendance/work_type_requests/update_form.html",
        {"form": form, "req": req, "mode_label": _mode_label},
    )


@login_required
@hx_request_required
def work_type_request_cancel(request, obj_id: int):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    if req.employee_id_id != employee.id:
        return HttpResponseForbidden("Not allowed")

    if req.status not in (WorkModeRequestStatus.PENDING, WorkModeRequestStatus.WAITING_FOR_APPROVAL):
        messages.error(request, _("Only pending/waiting requests can be canceled."))
        return HttpResponse("<script>location.reload();</script>")

    req.status = WorkModeRequestStatus.CANCELED
    req.save(update_fields=["status"])
    messages.success(request, _("Request canceled."))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_approve(request, obj_id: int):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    can_approve = request.user.has_perm("attendance.change_workmoderequest") or is_reportingmanager(request)
    if not can_approve:
        return HttpResponseForbidden("No approval permission")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    if req.status != WorkModeRequestStatus.WAITING_FOR_APPROVAL:
        messages.error(request, _("Only waiting requests can be approved."))
        return HttpResponse("<script>location.reload();</script>")

    req.status = WorkModeRequestStatus.APPROVED
    req.approved_by = employee
    req.approved_at = timezone.now()
    req.save(update_fields=["status", "approved_by", "approved_at"])

    messages.success(request, _("Request approved."))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_reject(request, obj_id: int):
    employee = getattr(request.user, "employee_get", None)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    can_approve = request.user.has_perm("attendance.change_workmoderequest") or is_reportingmanager(request)
    if not can_approve:
        return HttpResponseForbidden("No approval permission")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    form = WorkTypeRequestRejectForm(
        initial={
            "reason_code": WorkModeRequestRejectReasonCode.MANUAL_REJECT,
            "reason": req.reason or "",
        }
    )

    if request.method == "POST":
        form = WorkTypeRequestRejectForm(request.POST)
        if form.is_valid():
            if req.status not in (WorkModeRequestStatus.WAITING_FOR_APPROVAL, WorkModeRequestStatus.PENDING):
                messages.error(request, _("Only pending/waiting requests can be rejected."))
                return HttpResponse("<script>location.reload();</script>")

            req.status = WorkModeRequestStatus.REJECTED
            req.reason_code = form.cleaned_data.get("reason_code")
            req.reason = (form.cleaned_data.get("reason") or "").strip() or req.reason
            req.approved_by = employee
            req.approved_at = timezone.now()
            req.save(update_fields=["status", "reason_code", "reason", "approved_by", "approved_at"])

            # Option B audit marking
            try:
                apply_rejection_to_attendance(req)
            except Exception:
                pass

            messages.success(request, _("Request rejected."))
            response = render(
                request,
                "attendance/work_type_requests/reject_form.html",
                {"form": form, "req": req, "mode_label": _mode_label},
            )
            return HttpResponse(response.content.decode("utf-8") + "<script>location.reload();</script>")

    return render(
        request,
        "attendance/work_type_requests/reject_form.html",
        {"form": form, "req": req, "mode_label": _mode_label},
    )
