"""attendance/views/work_type_requests.py

Web UI (Django templates) for Attendance **Work Type Requests**.

- UI name: Work Type Requests
- DB model: attendance.WorkModeRequest (kept for backwards compatibility)

Spec:
- Allowed request depends on schedule (employee.employee_work_info.work_type_id) for the attendance_date.
- Scopes: IN/OUT single day, FULL date range.
- ON_DUTY requires destination + attachment at create.
- Approvals list includes WAITING_FOR_APPROVAL items; ON DUTY moves there immediately after a valid create.
"""

from __future__ import annotations

from django.contrib import messages
from django.http import FileResponse, Http404, HttpResponse, HttpResponseForbidden
from django.shortcuts import get_object_or_404, render
from django.utils import timezone
from django.utils.translation import gettext_lazy as _

from attendance.forms_work_type_request import (
    WorkTypeRequestCreateForm,
    WorkTypeRequestRejectForm,
    WorkTypeRequestUpdateForm,
)
from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestActionType,
    WorkModeRequestDocumentStatus,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestStatus,
)
from attendance.services.work_type_request_rules import work_mode_request_approval_q
from attendance.services.work_type_request_exceptions import WorkModeRequestConsistencyError
from attendance.services.work_type_request_files import (
    attachment_belongs_to_request,
    build_attachment_links,
    request_can_view_attachment,
    verify_attachment_token,
)
from attendance.services.work_type_request_actions import WorkModeRequestActionError, WorkModeRequestActions
from attendance.services.work_type_request_permissions import (
    build_permission_flags,
    can_manage_as_approver,
    can_update_request,
    can_upload_document,
    is_global_work_type_approver,
    request_actor_employee,
)
from attendance.methods.utils import paginator_qry
from base.methods import filtersubordinates, get_subordinate_employee_ids
from horilla.decorators import hx_request_required, login_required


def _is_global_work_type_approver(user) -> bool:
    return is_global_work_type_approver(user)


def _subordinate_ids(request) -> list[int]:
    """Best-effort list of subordinate Employee IDs for current user."""
    try:
        return get_subordinate_employee_ids(request) or []
    except Exception:
        return []


def _can_act_on_request(request, req: WorkModeRequest) -> bool:
    return can_manage_as_approver(request, req)




def _request_actor_employee(request):
    return request_actor_employee(request)


def _request_actor_label(request, fallback):
    actor = _request_actor_employee(request)
    if actor is not None:
        return actor
    return fallback


def _is_web_update_allowed(request, req: WorkModeRequest) -> bool:
    return bool(
        can_update_request(request, req)
        or can_upload_document(request, req)
    )


def _request_remark_value(request, *keys: str):
    for key in keys:
        value = (request.POST.get(key) or request.GET.get(key) or "").strip()
        if value:
            return value
    return None


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
    """Main page: My Requests + Approvals.

    Some deployments have admin/superuser accounts that are not linked to an
    Employee profile (employee_get=None). For those users, we still want the
    page (especially Approvals) to work when they have global permission or are
    a Django superuser.
    """

    employee = _request_actor_employee(request)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)

    # Only forbid when the user is not a superuser/global approver AND has no employee.
    if employee is None and not (is_super or has_global_perm):
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
        "revoked": WorkModeRequestStatus.REVOKED,
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

    # My Requests table requires an employee profile.
    my_qs = WorkModeRequest.objects.none() if employee is None else WorkModeRequest.objects.filter(employee_id=employee)

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

    # Approvals:
    # - Global approver/superuser => see all.
    # - Reporting manager => see subordinates.
    sub_ids = _subordinate_ids(request)
    can_approve = bool(is_super or has_global_perm or bool(sub_ids))

    include_pending_on_duty = bool(is_super or has_global_perm)
    approvals_qs = WorkModeRequest.objects.filter(
        work_mode_request_approval_q(
            include_pending_on_duty=include_pending_on_duty
        )
    )
    if not (is_super or has_global_perm):
        approvals_qs = filtersubordinates(
            request=request,
            queryset=approvals_qs,
            perm="attendance.change_workmoderequest",
            field="employee_id",
        )

    # Exclude own requests from Approvals tab (admin can still view them in My Requests).
    # Self-approve is also blocked in the action endpoints for safety.
    if employee is not None:
        approvals_qs = approvals_qs.exclude(employee_id=employee)

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

    my_page = paginator_qry(my_qs, request.GET.get("page_my"))
    approvals_page = paginator_qry(approvals_qs, request.GET.get("page_app"))
    for row in getattr(my_page, "object_list", []):
        for key, value in build_permission_flags(request, row).items():
            setattr(row, key, value)
        current_version = getattr(row, "current_document_version", None)
        setattr(row, "current_document_version_number", getattr(current_version, "version_number", None))
        try:
            setattr(row, "current_document_file_count", len(row.current_document_files()))
        except Exception:
            setattr(row, "current_document_file_count", row.files.count())
    for row in getattr(approvals_page, "object_list", []):
        for key, value in build_permission_flags(request, row).items():
            setattr(row, key, value)
        current_version = getattr(row, "current_document_version", None)
        setattr(row, "current_document_version_number", getattr(current_version, "version_number", None))
        try:
            setattr(row, "current_document_file_count", len(row.current_document_files()))
        except Exception:
            setattr(row, "current_document_file_count", row.files.count())

    context = {
        "my_requests": my_page,
        "approvals": approvals_page,
        "can_approve": bool(can_approve),
        "current_user_id": getattr(request.user, "id", None),
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
            ("revoked", _("Revoked")),
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
def work_type_request_revoke(request, obj_id: int):
    employee = _request_actor_employee(request)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)
    try:
        remark = _request_remark_value(request, "reason", "remark", "note")
        WorkModeRequestActions.revoke_request(req, actor=employee, request=request, remark=remark)
    except (WorkModeRequestActionError, WorkModeRequestConsistencyError) as exc:
        messages.error(request, str(exc))
    else:
        messages.success(request, _("Request revoked."))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_document_action(request, obj_id: int, action: str):
    employee = _request_actor_employee(request)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)
    remark = (request.POST.get("remark") or request.POST.get("reason") or "").strip() or None
    try:
        if action == "verify":
            WorkModeRequestActions.verify_document(req, actor=employee, request=request, remark=remark)
            messages.success(request, _("Document verified."))
        elif action == "reject":
            WorkModeRequestActions.reject_document(req, actor=employee, request=request, remark=remark)
            messages.success(request, _("Document rejected."))
        elif action == "reopen":
            WorkModeRequestActions.reopen_document(req, actor=employee, request=request, remark=remark)
            messages.success(request, _("Document review reopened."))
        else:
            return HttpResponseForbidden("Unsupported action")
    except (WorkModeRequestActionError, WorkModeRequestConsistencyError) as exc:
        messages.error(request, str(exc))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_attachments(request, obj_id: int):
    """HTMX modal: list current + historical document versions for a request."""
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)
    if not request_can_view_attachment(request, req) and not (is_super or has_global_perm):
        return HttpResponseForbidden("Not allowed")

    versions = []
    try:
        for version in req.document_versions.all().prefetch_related("file_links__attendance_request_file"):
            files = [link.attendance_request_file for link in version.file_links.all()]
            versions.append({"version": version, "links": build_attachment_links(request, req, files)})
    except Exception:
        versions = []

    legacy_links = []
    if not versions:
        try:
            legacy_links = build_attachment_links(request, req, req.files.all())
        except Exception:
            legacy_links = []

    return render(
        request,
        "attendance/work_type_requests/attachments_modal.html",
        {
            "req": req,
            "versions": versions,
            "legacy_links": legacy_links,
            "mode_label": _mode_label,
        },
    )


@login_required
def work_type_request_attachment_download(request, obj_id: int, file_id: int):
    req = get_object_or_404(WorkModeRequest, id=obj_id)
    from attendance.models import AttendanceRequestFile

    file_obj = get_object_or_404(AttendanceRequestFile, id=file_id)
    if not attachment_belongs_to_request(req, file_obj):
        raise Http404("Attachment not found")

    allowed = False
    try:
        if getattr(request, "user", None) and getattr(request.user, "is_authenticated", False):
            allowed = request_can_view_attachment(request, req) or bool(getattr(request.user, "is_superuser", False))
    except Exception:
        allowed = False

    token = request.GET.get("token")
    if not allowed:
        return HttpResponseForbidden("Not allowed")
    if not verify_attachment_token(req.id, file_obj.id, token):
        return HttpResponseForbidden("Invalid or expired attachment token")

    try:
        file_handle = file_obj.file.open("rb")
    except Exception as exc:
        raise Http404("File missing") from exc
    filename = (getattr(file_obj.file, "name", "") or "attachment").split("/")[-1]
    return FileResponse(file_handle, as_attachment=False, filename=filename)


@login_required
@hx_request_required
def work_type_request_create(request):
    employee = _request_actor_employee(request)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    form = WorkTypeRequestCreateForm(employee=employee)

    if request.method == "POST":
        form = WorkTypeRequestCreateForm(request.POST, request.FILES, employee=employee)
        if form.is_valid():
            uploaded = request.FILES.getlist("files")
            instance = WorkModeRequestActions.create_request(
                actor=employee,
                mode=form.cleaned_data["mode"],
                scope=form.cleaned_data["scope"],
                start_date=form.cleaned_data["start_date"],
                end_date=form.cleaned_data["end_date"],
                reason=form.cleaned_data["reason"],
                duty_destination_location=form.cleaned_data.get("duty_destination_location"),
                uploaded_files=uploaded,
            )
            messages.success(request, _(f"Work Type Request created ({_mode_label(instance.mode)})."))
            response = render(request, "attendance/work_type_requests/form.html", {"form": form})
            return HttpResponse(response.content.decode("utf-8") + "<script>location.reload();</script>")

    return render(request, "attendance/work_type_requests/form.html", {"form": form})


@login_required
@hx_request_required
def work_type_request_update(request, obj_id: int):
    employee = _request_actor_employee(request)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    if req.employee_id_id != employee.id:
        return HttpResponseForbidden("Not allowed")

    if not _is_web_update_allowed(request, req):
        return HttpResponseForbidden("This request can no longer be updated")

    form = WorkTypeRequestUpdateForm(
        request_obj=req,
        initial={
            "reason": req.reason or "",
            "duty_destination_location": req.duty_destination_location or "",
        },
    )

    if request.method == "POST":
        form = WorkTypeRequestUpdateForm(request.POST, request.FILES, request_obj=req)
        if form.is_valid():
            try:
                WorkModeRequestActions.update_request(
                    req,
                    actor=employee,
                    request=request,
                    reason=form.cleaned_data.get("reason"),
                    duty_destination_location=form.cleaned_data.get("duty_destination_location"),
                    uploaded_files=request.FILES.getlist("files"),
                    remark=_request_remark_value(request, "remark", "reason", "note"),
                )
                messages.success(request, _("Request updated."))
            except WorkModeRequestActionError as exc:
                messages.error(request, str(exc))
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
    employee = _request_actor_employee(request)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    try:
        WorkModeRequestActions.cancel_request(req, actor=employee, request=request)
    except (WorkModeRequestActionError, WorkModeRequestConsistencyError) as exc:
        messages.error(request, str(exc))
    else:
        messages.success(request, _("Request canceled."))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_approve(request, obj_id: int):
    employee = _request_actor_employee(request)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    try:
        result = WorkModeRequestActions.approve_request(req, actor=employee, request=request)
    except (WorkModeRequestActionError, WorkModeRequestConsistencyError) as exc:
        messages.error(request, str(exc))
    else:
        if result.auto_rejected:
            messages.error(request, _("WFA request passed its approval cutoff and was auto-rejected."))
        else:
            messages.success(request, _("Request approved."))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_reject(request, obj_id: int):
    employee = _request_actor_employee(request)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    form = WorkTypeRequestRejectForm(
        initial={
            "reason_code": WorkModeRequestRejectReasonCode.MANUAL_REJECT,
            "reason": "",
        }
    )

    if request.method == "POST":
        form = WorkTypeRequestRejectForm(request.POST)
        if form.is_valid():
            try:
                WorkModeRequestActions.reject_request(
                    req,
                    actor=employee,
                    request=request,
                    reason_code=form.cleaned_data.get("reason_code"),
                    remark=(form.cleaned_data.get("reason") or "").strip() or None,
                )
                messages.success(request, _("Request rejected."))
            except WorkModeRequestActionError as exc:
                messages.error(request, str(exc))
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

