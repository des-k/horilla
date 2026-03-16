"""attendance/views/work_type_requests.py

Web UI (Django templates) for Attendance **Work Type Requests**.

- UI name: Work Type Requests
- DB model: attendance.WorkModeRequest (kept for backwards compatibility)

Spec:
- Allowed request depends on schedule (employee.employee_work_info.work_type_id) for the attendance_date.
- Scopes: IN/OUT single day, FULL date range.
- ON_DUTY requires attachment but may be submitted PENDING and later updated with attachment.
- Approvals list includes:
  - WAITING_FOR_APPROVAL (approvable)
  - ON_DUTY PENDING (not yet approvable; usually waiting for letter upload)
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
    WorkModeRequestDocumentStatus,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestStatus,
)
from attendance.services.work_type_request_rules import (
    apply_rejection_to_attendance,
    has_attachments,
    work_mode_request_approval_q,
)
from attendance.services.request_audit import log_request_action
from attendance.services.reconciliation import recompute_attendance_range
from attendance.methods.utils import paginator_qry
from base.methods import filtersubordinates, get_subordinate_employee_ids
from horilla.decorators import hx_request_required, login_required


def _is_global_work_type_approver(user) -> bool:
    """Treat these users as global approvers for Work Type Requests.

    Many deployments already grant admins `attendance.change_attendance` but may
    not yet grant `attendance.change_workmoderequest` (newer model). We accept
    either permission so existing admin roles keep working on web.
    """

    try:
        if getattr(user, "is_superuser", False):
            return True
        return bool(
            user.has_perm("attendance.change_workmoderequest")
            or user.has_perm("attendance.change_attendance")
        )
    except Exception:
        return False


def _subordinate_ids(request) -> list[int]:
    """Best-effort list of subordinate Employee IDs for current user."""
    try:
        return get_subordinate_employee_ids(request) or []
    except Exception:
        return []


def _can_act_on_request(request, req: WorkModeRequest) -> bool:
    """Permission guard for approve/reject/view-attachments on a specific request."""

    # Admin / global approver
    if _is_global_work_type_approver(request.user):
        return True

    # Reporting manager: only their (direct/nested) subordinates.
    try:
        return int(req.employee_id_id) in set(_subordinate_ids(request))
    except Exception:
        return False




def _set_on_duty_document_state(req: WorkModeRequest, *, has_files: bool, approved: bool = False):
    if req.mode != AttendanceWorkMode.ON_DUTY:
        return
    if not has_files:
        req.document_status = WorkModeRequestDocumentStatus.NOT_UPLOADED
        return
    req.document_status = WorkModeRequestDocumentStatus.PENDING_VERIFICATION if approved else WorkModeRequestDocumentStatus.SUBMITTED


def _log_request_action(req: WorkModeRequest, actor, *, action_type: str, old_status: str = None, new_status: str = None, remark: str = None):
    try:
        log_request_action(
            work_mode_request=req,
            actor=actor,
            action_type=action_type,
            old_status=old_status,
            new_status=new_status,
            remark=remark,
        )
    except Exception:
        pass


def _request_actor_employee(request):
    return getattr(request.user, "employee_get", None)


def _request_actor_label(request, fallback):
    actor = _request_actor_employee(request)
    if actor is not None:
        return actor
    return fallback


def _is_web_update_allowed(req: WorkModeRequest) -> bool:
    if req.status in (
        WorkModeRequestStatus.REJECTED,
        WorkModeRequestStatus.CANCELED,
        WorkModeRequestStatus.REVOKED,
    ):
        return False
    if req.mode != AttendanceWorkMode.ON_DUTY:
        return req.status in (
            WorkModeRequestStatus.PENDING,
            WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        )
    if req.status in (
        WorkModeRequestStatus.PENDING,
        WorkModeRequestStatus.WAITING_FOR_APPROVAL,
    ):
        return True
    if req.status != WorkModeRequestStatus.APPROVED:
        return False
    return req.document_status != WorkModeRequestDocumentStatus.VERIFIED


def _request_remark_value(request, *keys: str):
    for key in keys:
        value = (request.POST.get(key) or request.GET.get(key) or "").strip()
        if value:
            return value
    return None


def _save_on_duty_uploads(req: WorkModeRequest, uploaded_files, *, replace_existing: bool = False):
    if replace_existing:
        req.files.clear()
    for uploaded in uploaded_files:
        af = AttendanceRequestFile.objects.create(file=uploaded)
        req.files.add(af)


def _sync_on_duty_document_after_upload(req: WorkModeRequest):
    if req.mode != AttendanceWorkMode.ON_DUTY:
        return False

    had_approved_finalization = req.status == WorkModeRequestStatus.APPROVED
    previous_document_status = req.document_status
    previous_verified_by = req.document_verified_by_id
    previous_verified_at = req.document_verified_at

    _set_on_duty_document_state(
        req,
        has_files=has_attachments(req),
        approved=had_approved_finalization,
    )

    if req.status == WorkModeRequestStatus.PENDING and has_attachments(req):
        req.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL

    document_changed = previous_document_status != req.document_status
    verification_reset = False
    if had_approved_finalization and req.document_status != WorkModeRequestDocumentStatus.VERIFIED:
        if req.document_verified_by_id is not None or req.document_verified_at is not None:
            verification_reset = True
        req.document_verified_by = None
        req.document_verified_at = None

    return document_changed or verification_reset or previous_verified_by != req.document_verified_by_id or previous_verified_at != req.document_verified_at


def _recompute_if_needed(req: WorkModeRequest, *, should_recompute: bool):
    if should_recompute:
        recompute_attendance_range(req.employee_id, req.start_date, req.end_date)


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

    context = {
        "my_requests": paginator_qry(my_qs, request.GET.get("page_my")),
        "approvals": paginator_qry(approvals_qs, request.GET.get("page_app")),
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
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)
    try:
        if getattr(req.employee_id, "employee_user_id", None) == request.user:
            return HttpResponseForbidden("You cannot revoke your own request")
    except Exception:
        pass
    if not _can_act_on_request(request, req):
        return HttpResponseForbidden("Not allowed")
    if req.status != WorkModeRequestStatus.APPROVED:
        messages.error(request, _("Only approved requests can be revoked."))
        return HttpResponse("<script>location.reload();</script>")

    old_status = req.status
    remark = _request_remark_value(request, "reason", "remark", "note")
    req.status = WorkModeRequestStatus.REVOKED
    req.action_by = employee if employee is not None else None
    req.action_at = timezone.now()
    req.action_type = "REVOKED"
    req.action_reason = remark
    req.save(update_fields=["status", "action_by", "action_at", "action_type", "action_reason"])
    _log_request_action(req, _request_actor_label(request, employee), action_type="REVOKED", old_status=old_status, new_status=req.status, remark=remark)
    recompute_attendance_range(req.employee_id, req.start_date, req.end_date)
    messages.success(request, _("Request revoked."))
    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_document_action(request, obj_id: int, action: str):
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)
    if req.mode != AttendanceWorkMode.ON_DUTY:
        return HttpResponseForbidden("Document actions only apply to On Duty")
    try:
        if getattr(req.employee_id, "employee_user_id", None) == request.user:
            return HttpResponseForbidden("You cannot perform this action on your own request")
    except Exception:
        pass
    if not _can_act_on_request(request, req):
        return HttpResponseForbidden("Not allowed")
    if req.status != WorkModeRequestStatus.APPROVED:
        messages.error(request, _("Document actions require approved On Duty request."))
        return HttpResponse("<script>location.reload();</script>")

    remark = (request.POST.get("remark") or request.POST.get("reason") or "").strip() or None
    if action == "verify":
        if req.document_status not in (WorkModeRequestDocumentStatus.SUBMITTED, WorkModeRequestDocumentStatus.PENDING_VERIFICATION):
            messages.error(request, _("Document is not ready for verification."))
            return HttpResponse("<script>location.reload();</script>")
        previous = req.document_status
        req.document_status = WorkModeRequestDocumentStatus.VERIFIED
        req.document_verified_by = employee
        req.document_verified_at = timezone.now()
        req.action_by = employee
        req.action_at = req.document_verified_at
        req.action_type = "VERIFIED"
        req.action_reason = remark
        req.document_remark = remark
        req.save(update_fields=["document_status", "document_verified_by", "document_verified_at", "action_by", "action_at", "action_type", "action_reason", "document_remark"])
        _log_request_action(req, _request_actor_label(request, employee), action_type="VERIFIED", old_status=f"document:{previous}", new_status=f"document:{req.document_status}", remark=remark)
        recompute_attendance_range(req.employee_id, req.start_date, req.end_date)
        messages.success(request, _("Document verified."))
    elif action == "reject":
        if req.document_status not in (WorkModeRequestDocumentStatus.SUBMITTED, WorkModeRequestDocumentStatus.PENDING_VERIFICATION):
            messages.error(request, _("Document is not ready for rejection."))
            return HttpResponse("<script>location.reload();</script>")
        previous = req.document_status
        req.document_status = WorkModeRequestDocumentStatus.REJECTED
        req.action_by = employee
        req.action_at = timezone.now()
        req.action_type = WorkModeRequestActionType.DOCUMENT_REJECTED
        req.action_reason = remark
        req.document_remark = remark
        req.save(update_fields=["document_status", "action_by", "action_at", "action_type", "action_reason", "document_remark"])
        _log_request_action(req, _request_actor_label(request, employee), action_type=WorkModeRequestActionType.DOCUMENT_REJECTED, old_status=f"document:{previous}", new_status=f"document:{req.document_status}", remark=remark)
        recompute_attendance_range(req.employee_id, req.start_date, req.end_date)
        messages.success(request, _("Document rejected."))
    elif action == "reopen":
        if req.document_status not in (WorkModeRequestDocumentStatus.VERIFIED, WorkModeRequestDocumentStatus.REJECTED):
            messages.error(request, _("Only verified or rejected documents can be reopened."))
            return HttpResponse("<script>location.reload();</script>")
        previous = req.document_status
        req.document_status = WorkModeRequestDocumentStatus.PENDING_VERIFICATION if has_attachments(req) else WorkModeRequestDocumentStatus.NOT_UPLOADED
        req.document_verified_by = None
        req.document_verified_at = None
        req.action_by = employee
        req.action_at = timezone.now()
        req.action_type = "REOPENED"
        req.action_reason = remark
        req.document_remark = remark
        req.save(update_fields=["document_status", "document_verified_by", "document_verified_at", "action_by", "action_at", "action_type", "action_reason", "document_remark"])
        _log_request_action(req, _request_actor_label(request, employee), action_type="REOPENED", old_status=f"document:{previous}", new_status=f"document:{req.document_status}", remark=remark)
        recompute_attendance_range(req.employee_id, req.start_date, req.end_date)
        messages.success(request, _("Document review reopened."))
    else:
        return HttpResponseForbidden("Unsupported action")

    return HttpResponse("<script>location.reload();</script>")


@login_required
@hx_request_required
def work_type_request_attachments(request, obj_id: int):
    """HTMX modal: list attachments for a request.

    Access:
    - owner can view
    - approver/manager can view
    """
    employee = getattr(request.user, "employee_get", None)
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = _is_global_work_type_approver(request.user)
    if employee is None and not (is_super or has_global_perm):
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    # Owner can always view; otherwise must be allowed to act on this specific request.
    if employee is not None and req.employee_id_id == employee.id:
        pass
    else:
        if not _can_act_on_request(request, req):
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
    employee = _request_actor_employee(request)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    form = WorkTypeRequestCreateForm(employee=employee)

    if request.method == "POST":
        form = WorkTypeRequestCreateForm(request.POST, request.FILES, employee=employee)
        if form.is_valid():
            instance: WorkModeRequest = form.save(commit=False)
            instance.employee_id = employee
            instance.reason = (form.cleaned_data.get("reason") or "").strip()
            instance.duty_destination_location = (
                form.cleaned_data.get("duty_destination_location") or ""
            ).strip()
            instance.duty_destination_detail = (form.cleaned_data.get("duty_destination_detail") or "").strip()

            files_in = request.FILES.getlist("files")
            if instance.mode == AttendanceWorkMode.WFA:
                instance.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
            elif instance.mode == AttendanceWorkMode.ON_DUTY:
                instance.status = (
                    WorkModeRequestStatus.WAITING_FOR_APPROVAL if files_in else WorkModeRequestStatus.PENDING
                )
                _set_on_duty_document_state(instance, has_files=bool(files_in), approved=False)
            else:
                instance.status = WorkModeRequestStatus.PENDING

            instance.action_reason = None
            instance.document_remark = None
            instance.save()
            _save_on_duty_uploads(instance, files_in)

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

    if not _is_web_update_allowed(req):
        return HttpResponseForbidden("This request can no longer be updated")

    form = WorkTypeRequestUpdateForm(
        request_obj=req,
        initial={
            "reason": req.reason or "",
            "duty_destination_location": req.duty_destination_location or "",
            "duty_destination_detail": req.duty_destination_detail or "",
        },
    )

    if request.method == "POST":
        form = WorkTypeRequestUpdateForm(request.POST, request.FILES, request_obj=req)
        if form.is_valid():
            req.reason = (form.cleaned_data.get("reason") or "").strip()
            req.duty_destination_location = (
                form.cleaned_data.get("duty_destination_location") or req.duty_destination_location or ""
            ).strip()
            req.duty_destination_detail = (form.cleaned_data.get("duty_destination_detail") or "").strip()

            files_in = request.FILES.getlist("files")
            should_recompute = False
            if files_in and req.mode == AttendanceWorkMode.ON_DUTY:
                _save_on_duty_uploads(req, files_in, replace_existing=True)
                should_recompute = _sync_on_duty_document_after_upload(req)
            elif req.mode == AttendanceWorkMode.ON_DUTY:
                should_recompute = _sync_on_duty_document_after_upload(req)

            req.save()
            _recompute_if_needed(req, should_recompute=should_recompute and req.status == WorkModeRequestStatus.APPROVED)
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
    employee = _request_actor_employee(request)
    if employee is None:
        return HttpResponseForbidden("Employee profile required")

    req = get_object_or_404(WorkModeRequest, id=obj_id)

    if req.employee_id_id != employee.id:
        return HttpResponseForbidden("Not allowed")

    if req.status not in (WorkModeRequestStatus.PENDING, WorkModeRequestStatus.WAITING_FOR_APPROVAL):
        messages.error(request, _("Only pending/waiting requests can be canceled."))
        return HttpResponse("<script>location.reload();</script>")

    old_status = req.status
    req.status = WorkModeRequestStatus.CANCELED
    req.action_by = employee
    req.action_at = timezone.now()
    req.action_type = "CANCELED"
    req.action_reason = None
    req.save(update_fields=["status", "action_by", "action_at", "action_type", "action_reason"])
    _log_request_action(req, _request_actor_label(request, employee), action_type="CANCELED", old_status=old_status, new_status=req.status)
    recompute_attendance_range(req.employee_id, req.start_date, req.end_date)
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
        if getattr(req.employee_id, "employee_user_id", None) == request.user:
            return HttpResponseForbidden("You cannot approve your own request")
    except Exception:
        pass

    if not _can_act_on_request(request, req):
        return HttpResponseForbidden("Not allowed")

    if req.status != WorkModeRequestStatus.WAITING_FOR_APPROVAL:
        messages.error(request, _("Only waiting requests can be approved."))
        return HttpResponse("<script>location.reload();</script>")

    old_status = req.status
    req.status = WorkModeRequestStatus.APPROVED
    req.approved_by = employee if employee is not None else None
    req.approved_at = timezone.now()
    req.action_by = req.approved_by
    req.action_at = req.approved_at
    req.action_type = "APPROVED"
    req.action_reason = None
    if req.mode == AttendanceWorkMode.ON_DUTY:
        _set_on_duty_document_state(req, has_files=has_attachments(req), approved=True)
        req.save(update_fields=["status", "approved_by", "approved_at", "action_by", "action_at", "action_type", "action_reason", "document_status"])
    else:
        req.save(update_fields=["status", "approved_by", "approved_at", "action_by", "action_at", "action_type", "action_reason"])
    _log_request_action(req, _request_actor_label(request, employee), action_type="APPROVED", old_status=old_status, new_status=req.status)
    recompute_attendance_range(req.employee_id, req.start_date, req.end_date)

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

    try:
        if getattr(req.employee_id, "employee_user_id", None) == request.user:
            return HttpResponseForbidden("Use cancel for your own request")
    except Exception:
        pass

    if not _can_act_on_request(request, req):
        return HttpResponseForbidden("Not allowed")

    if req.status == WorkModeRequestStatus.PENDING and not (is_super or has_global_perm):
        return HttpResponseForbidden("Pending On Duty requests are not actionable for non-admin reviewers")

    form = WorkTypeRequestRejectForm(
        initial={
            "reason_code": WorkModeRequestRejectReasonCode.MANUAL_REJECT,
            "reason": "",
        }
    )

    if request.method == "POST":
        form = WorkTypeRequestRejectForm(request.POST)
        if form.is_valid():
            if req.status not in (WorkModeRequestStatus.WAITING_FOR_APPROVAL, WorkModeRequestStatus.PENDING):
                messages.error(request, _("Only pending/waiting requests can be rejected."))
                return HttpResponse("<script>location.reload();</script>")

            remark = (form.cleaned_data.get("reason") or "").strip() or None
            old_status = req.status
            req.status = WorkModeRequestStatus.REJECTED
            req.reason_code = form.cleaned_data.get("reason_code")
            req.approved_by = None
            req.approved_at = None
            req.action_by = employee if employee is not None else None
            req.action_at = timezone.now()
            req.action_type = "REJECTED"
            req.action_reason = remark
            req.save(update_fields=["status", "reason_code", "approved_by", "approved_at", "action_by", "action_at", "action_type", "action_reason"])
            _log_request_action(req, _request_actor_label(request, employee), action_type="REJECTED", old_status=old_status, new_status=req.status, remark=remark)

            try:
                apply_rejection_to_attendance(req)
            except Exception:
                recompute_attendance_range(req.employee_id, req.start_date, req.end_date)

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

