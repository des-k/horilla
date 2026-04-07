from datetime import date, datetime, timedelta, timezone, time
import calendar
import io
import json

from django import template
from django.conf import settings
from django.core.mail import EmailMessage
from django.core.exceptions import ValidationError
from django.db import transaction
from django.db.models import Case, CharField, F, Value, When, Q, Model
from django.http import FileResponse, HttpResponse, QueryDict
from django.shortcuts import get_object_or_404
from django.template.loader import render_to_string
from django.utils import timezone as dj_timezone
from django.utils.decorators import method_decorator
from rest_framework import status
from rest_framework.pagination import PageNumberPagination
from rest_framework.permissions import IsAuthenticated, AllowAny
from rest_framework.response import Response
from rest_framework.views import APIView
from rest_framework.parsers import MultiPartParser, FormParser, JSONParser
from rest_framework.renderers import JSONRenderer, BaseRenderer
from xhtml2pdf import pisa

import logging
from types import SimpleNamespace

from facedetection.models import FaceDetection, EmployeeFaceDetection
from geofencing.models import GeoFencing
from geofencing.policy import geofencing_is_effectively_enabled
from geopy.distance import geodesic

logger = logging.getLogger(__name__)

from attendance.filters import AttendanceActivityFilter
from attendance.forms import NewRequestForm, AttendanceRequestForm
from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestStatus,
    AttendanceCorrectionRequestAttachment,
    AttendanceLateComeEarlyOut,
    AttendanceRequestFile,
    AttendanceRequestActionType,
    AttendancePunchSource,
    AttendancePunchingHistory,
    EmployeeShiftDay,
    WorkModeRequest,
    AttendanceWorkMode,
    EmployeeWfhProfile,
    EmployeeWfhProfileHistory,
    WorkModeRequestDocumentStatus,
    WorkModeRequestScope,
    WorkModeRequestStatus,
    WorkModeRequestActionType,
    WorkModeRequestRejectReasonCode,
)
from attendance.views.clock_in_out import *
from attendance.views.clock_in_out import clock_out
import attendance.views.clock_in_out as cio  # Access underscore helpers excluded by import *

from attendance.services.attachment_validation import validate_uploaded_files
from attendance.services.image_compression import _extract_error_message
from attendance.services.work_type_request_rules import (
    effective_work_type,
    committed_work_type,
    punch_allowed,
    auto_reject_wfa_waiting_for_date,
    apply_rejection_to_attendance,
    has_attachments,
    work_mode_request_approval_q,
    work_mode_request_document_review_q,
    classify_work_mode_request_queue,
)
from attendance.services.activity_sync import (
    get_requested_sessions,
    mark_approved_request_channels,
    sync_single_session_activity,
    validate_requested_data_with_windows,
)
from attendance.services.punching_history import (
    capture_request_restore_snapshot,
    clear_raw_links_for_request_override,
    create_mobile_punch_history,
    humanize_mobile_error,
    reconcile_attendance_punches,
    restore_raw_state_after_request,
    update_punch_history,
)
from attendance.services.attendance_request_files import (
    attachment_belongs_to_request as attendance_attachment_belongs_to_request,
    request_can_view_attachment as attendance_request_can_view_attachment,
    verify_attachment_token as verify_attendance_attachment_token,
)
from attendance.services.attachment_contract import (
    attachment_mime_type,
    attachment_name,
    is_inline_viewable_mime_type,
)
from attendance.services.work_type_request_files import (
    attachment_belongs_to_request as work_mode_attachment_belongs_to_request,
    request_can_view_attachment as work_mode_request_can_view_attachment,
    verify_attachment_token as verify_work_mode_attachment_token,
)
from attendance.services.attendance_request_access import (
    hard_delete_request_attachment,
    user_can_approve_request,
    user_can_delete_attachment,
    user_can_manage_request,
)
from attendance.services.attendance_correction_scope_rules import load_requested_data
from attendance.services.request_audit import log_request_action
from attendance.services.work_type_request_exceptions import WorkModeRequestConsistencyError
from attendance.services.attendance_access import evaluate_attendance_access
from attendance.services.canonical_attendance_policy import (
    build_attendance_policy,
    compute_attendance_metrics,
    compute_mobile_status_metrics,
    format_decimal_minutes,
    resolve_policy_windows,
    seconds_to_decimal_minutes,
    time_to_shift_instance_dt as canonical_time_to_shift_instance_dt,
)
from attendance.services.reconciliation import recompute_attendance, recompute_attendance_range
from attendance.services.mobile_status_note import build_mobile_header_state
from attendance.services.work_type_request_actions import WorkModeRequestActions

try:
    from leave.half_day_rules import leave_breakdown_for_attendance_date
except Exception:
    leave_breakdown_for_attendance_date = None  # type: ignore
from attendance.services.attendance_correction_requests import (
    AttendanceCorrectionError,
    approve_request as approve_attendance_correction_request,
    build_permission_flags as build_attendance_correction_permission_flags,
    cancel_request as cancel_attendance_correction_request,
    create_request as create_attendance_correction_request,
    reject_request as reject_attendance_correction_request,
    revoke_request as revoke_attendance_correction_request,
    update_request as update_attendance_correction_request,
    user_can_approve_request as correction_user_can_approve_request,
    user_is_request_owner as correction_user_is_request_owner,
)
from attendance.services.request_override_recompute import clear_request_override_and_recompute
from attendance.services.month_params import normalize_month_yyyy_mm, require_month_yyyy_mm
from attendance.services.attendance_access import get_attendance_subject_employees

from attendance.views.dashboard import (
    find_expected_attendances,
    find_late_come,
    find_on_time,
)
from attendance.views.views import *
from base.backends import ConfiguredEmailBackend
from base.methods import generate_pdf, is_reportingmanager, filtersubordinates, filtersubordinatesemployeemodel, get_subordinate_employee_ids
from base.models import HorillaMailTemplate
from employee.filters import EmployeeFilter
from employee.models import Employee, EmployeeWorkInformation

from ...api_decorators.base.decorators import (
    manager_permission_required,
    permission_required,
)
from ...api_methods.base.methods import groupby_queryset, permission_based_queryset
from ...api_serializers.attendance.serializers import (
    AttendanceActivitySerializer,
    AttendanceLateComeEarlyOutSerializer,
    AttendanceOverTimeSerializer,
    AttendancePunchingHistorySerializer,
    AttendanceRequestSerializer,
    AttendanceCorrectionRequestSerializer,
    AttendanceSerializer,
    MailTemplateSerializer,
    UserAttendanceDetailedSerializer,
    UserAttendanceListSerializer,
    WorkModeRequestSerializer,
)


# Create your views here.


# -----------------------------------------------------------------------------
# Generic API helpers
# -----------------------------------------------------------------------------
def query_dict(data):
    query_dict = QueryDict("", mutable=True)
    for key, value in data.items():
        if isinstance(value, list):
            for item in value:
                query_dict.appendlist(key, item)
        else:
            query_dict.update({key: value})
    return query_dict




def _request_actor_employee(request):
    try:
        return request.user.employee_get
    except Exception:
        return None


def _log_work_mode_status_change(obj: WorkModeRequest, request, *, action_type: str, old_status: str = None, new_status: str = None, remark: str = None):
    try:
        log_request_action(
            work_mode_request=obj,
            actor=_request_actor_employee(request),
            action_type=action_type,
            old_status=old_status,
            new_status=new_status,
            remark=remark,
        )
    except Exception:
        logger.exception(
            "Failed to log work-mode status change for request=%s action=%s",
            getattr(obj, "id", None),
            action_type,
        )
        raise


def _log_attendance_request_status_change(attendance: Attendance, request, *, action_type: str, old_status: str = None, new_status: str = None, remark: str = None):
    try:
        log_request_action(
            attendance=attendance,
            actor=_request_actor_employee(request),
            action_type=action_type,
            old_status=old_status,
            new_status=new_status,
            remark=remark,
        )
    except Exception:
        logger.exception(
            "Failed to log attendance request status change for request=%s action=%s",
            getattr(attendance, "id", None),
            action_type,
        )
        raise

def _parse_filter_date(value):
    raw = (value or "").strip()
    if not raw:
        return None
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%Y/%m/%d"):
        try:
            return datetime.strptime(raw, fmt).date()
        except Exception:
            continue
    try:
        return date.fromisoformat(raw)
    except Exception:
        return None


def _parse_filter_month_range(value):
    raw = (value or "").strip()
    parsed_date = _parse_filter_date(raw)
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
                continue
        if month_start is None:
            return None
    else:
        return None

    if month_start.month == 12:
        next_month = date(month_start.year + 1, 1, 1)
    else:
        next_month = date(month_start.year, month_start.month + 1, 1)
    month_end = next_month - timedelta(days=1)
    return month_start, month_end, month_start.strftime("%Y-%m")


def _attendance_request_history_scope(request):
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
    qs = Attendance.objects.filter(request_history_filter).exclude(employee_id__employee_user_id=request.user).distinct()
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = bool(getattr(request.user, "has_perm", lambda _p: False)("attendance.change_attendance"))
    if is_super or has_global_perm:
        return qs
    if is_reportingmanager(request):
        return filtersubordinates(request=request, perm="attendance.change_attendance", queryset=qs)
    return Attendance.objects.none()


def _attendance_history_status_filter(qs, status_value):
    """History status filter compatible with both legacy Attendance and new AttendanceCorrectionRequest querysets."""
    model = getattr(qs, "model", None)
    if model is AttendanceCorrectionRequest:
        status_value = (status_value or "").strip().lower()
        if not status_value or status_value == "all":
            return qs.filter(status__in=[
                AttendanceCorrectionRequestStatus.APPROVED,
                AttendanceCorrectionRequestStatus.REJECTED,
                AttendanceCorrectionRequestStatus.REVOKED,
            ])
        mapping = {
            "waiting": AttendanceCorrectionRequestStatus.WAITING,
            "approved": AttendanceCorrectionRequestStatus.APPROVED,
            "rejected": AttendanceCorrectionRequestStatus.REJECTED,
            "revoked": AttendanceCorrectionRequestStatus.REVOKED,
            "canceled": AttendanceCorrectionRequestStatus.CANCELED,
            "cancel": AttendanceCorrectionRequestStatus.CANCELED,
        }
        wanted = mapping.get(status_value)
        return qs.filter(status=wanted) if wanted else qs
    status_value = (status_value or "").strip().lower()
    if not status_value or status_value == "all":
        return qs.exclude(is_validate_request=True)
    if status_value == "waiting":
        return qs.filter(is_validate_request=True)
    if status_value == "approved":
        return qs.filter(Q(is_validate_request_approved=True) | Q(attendance_validated=True)).exclude(is_validate_request=True)
    if status_value == "rejected":
        return qs.filter(Q(request_type="reject_request") | Q(action_type=AttendanceRequestActionType.REJECTED))
    if status_value in {"canceled", "cancel"}:
        return qs.filter(Q(request_type="cancel_request") | Q(action_type=AttendanceRequestActionType.CANCELED))
    if status_value == "revoked":
        return qs.filter(Q(request_type="revoke_request") | Q(action_type=AttendanceRequestActionType.REVOKED))
    return qs.exclude(is_validate_request=True)


def _mutable_request_data(request):
    if getattr(request, "FILES", None):
        return request.POST.copy()
    raw_data = getattr(request, "data", None)
    if hasattr(raw_data, "copy"):
        try:
            return raw_data.copy()
        except Exception:
            pass
    data = QueryDict("", mutable=True)
    if raw_data is not None:
        for key, value in dict(raw_data).items():
            if isinstance(value, (list, tuple)):
                for item in value:
                    data.appendlist(key, item)
            else:
                data[key] = value
    return data


def _uploaded_request_files(request):
    uploaded = []
    if hasattr(request, "FILES"):
        uploaded = request.FILES.getlist("files") or request.FILES.getlist("files[]") or []
        if not uploaded:
            single = request.FILES.get("file")
            if single:
                uploaded = [single]
    return uploaded


def _locked_correction_request(pk):
    try:
        return AttendanceCorrectionRequest._base_manager.select_related(None).select_for_update().get(id=pk)
    except Exception:
        return None


# -----------------------------------------------------------------------------
# Compatibility helpers retained for legacy Attendance-backed request flow
# -----------------------------------------------------------------------------
def _locked_legacy_attendance(pk):
    try:
        return Attendance.objects.select_for_update().get(id=pk)
    except Exception:
        return None


def _attachment_file_response(file_obj, disposition="download"):
    mime_type = attachment_mime_type(file_obj)
    inline_ok = disposition == "view" and is_inline_viewable_mime_type(mime_type)
    as_attachment = not inline_ok
    filename = attachment_name(file_obj)
    file_field = getattr(file_obj, "file", None)
    opened = None
    try:
        opened = file_field.open("rb")
    except Exception:
        opened = getattr(file_field, "open", lambda mode='rb': None)("rb") if file_field else None
    response = FileResponse(opened, as_attachment=as_attachment, filename=filename, content_type=mime_type)
    response["Cache-Control"] = "private, no-store"
    if inline_ok:
        response["Content-Disposition"] = f'inline; filename="{filename}"'
    else:
        response["Content-Disposition"] = f'attachment; filename="{filename}"'
    return response


def _legacy_attendance_request_payload(attendance, request):
    return AttendanceRequestSerializer(attendance, context={"request": request}).data


def _legacy_create_attendance_request(request, serializer_class):
    data = _mutable_request_data(request)
    try:
        if not data.get("employee_id") and getattr(getattr(request.user, "employee_get", None), "id", None):
            data["employee_id"] = getattr(request.user.employee_get, "id")
    except Exception:
        pass
    from attendance import forms as attendance_forms
    form = attendance_forms.NewRequestForm(data=data, files=getattr(request, "FILES", None) or None)
    if not form.is_valid():
        return Response(getattr(form, "errors", {}), status=400)
    attendance = getattr(form, "new_instance", None) or Attendance.objects.filter(id=getattr(getattr(form, "instance", None), "pk", None)).first()
    uploaded = _uploaded_request_files(request)
    for up in uploaded:
        arf = AttendanceRequestFile.objects.create(file=up)
        try:
            attendance.request_attachments.add(arf)
        except Exception:
            pass
    
    try:
        payload = serializer_class(attendance, context={"request": request}).data
    except Exception:
        payload = {"id": getattr(attendance, "id", None)}

    warnings = list(getattr(form, "window_warnings", []) or [])
    if warnings:
        payload["window_warning"] = warnings[0]
    return Response(payload, status=201)


def _legacy_update_attendance_request(request, pk, serializer_class):
    attendance = _locked_legacy_attendance(pk)
    if attendance is None:
        return Response({"error": "Attendance request not found."}, status=404)
    try:
        if getattr(attendance.employee_id, "employee_user_id", None) != request.user:
            return Response({"error": "Only the owner can edit this request."}, status=403)
    except Exception:
        return Response({"error": "Only the owner can edit this request."}, status=403)
    if not getattr(attendance, "is_validate_request", False) or getattr(attendance, "is_validate_request_approved", False):
        return Response({"error": "Approved requests cannot be edited"} if getattr(attendance, "is_validate_request_approved", False) else {"error": "Only waiting requests can be edited."}, status=400)
    data = _mutable_request_data(request)
    from attendance import forms as attendance_forms
    if hasattr(attendance, "_meta"):
        form = attendance_forms.AttendanceRequestForm(data=data, files=getattr(request, "FILES", None) or None, instance=attendance)
    else:
        form = attendance_forms.AttendanceRequestForm(data=data, files=getattr(request, "FILES", None) or None)
    if not form.is_valid():
        return Response(getattr(form, "errors", {}), status=400)
    attendance = form.save()
    uploaded = _uploaded_request_files(request)
    for up in uploaded:
        arf = AttendanceRequestFile.objects.create(file=up)
        try:
            attendance.request_attachments.add(arf)
        except Exception:
            pass
    
    try:
        payload = serializer_class(attendance, context={"request": request}).data
    except Exception:
        payload = {"id": getattr(attendance, "id", None)}

    warnings = list(getattr(form, "window_warnings", []) or [])
    if warnings:
        payload["window_warning"] = warnings[0]
    return Response(payload, status=200)


def _legacy_approve_attendance_request(request, attendance):
    if not user_can_approve_request(request.user, attendance):
        return Response({"error": "You do not have permission to approve this request."}, status=403)
    ok, warning = validate_requested_data_with_windows(attendance)
    if not ok:
        return Response({"error": warning or "Requested attendance cannot be approved."}, status=400)
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
    attendance.action_at = dj_timezone.now()
    try:
        attendance.save(update_fields=[
            "attendance_validated",
            "is_validate_request_approved",
            "is_validate_request",
            "action_by",
            "action_type",
            "action_at",
        ])
    except Exception:
        attendance.save()
    _log_attendance_request_status_change(attendance, request, action_type=AttendanceRequestActionType.APPROVED, old_status=getattr(attendance, "request_type", None) or "waiting_request", new_status="approved")
    requested_data = _normalize_requested_data(load_requested_data(getattr(attendance, "requested_data", None)))
    if requested_data:
        Attendance.objects.filter(id=attendance.id).update(**requested_data)
    try:
        attendance.refresh_from_db()
    except Exception:
        pass
    _mark_approved_request_channels(attendance)
    _detach_request_overridden_raw_links(attendance, include_in=wants_in, include_out=wants_out)
    result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
    final_attendance = result.attendance if result is not None else attendance
    
    try:
        payload = AttendanceRequestSerializer(final_attendance, context={"request": request}).data
    except Exception:
        payload = {"id": getattr(final_attendance, "id", None), "request_type": getattr(final_attendance, "request_type", None)}

    if warning:
        payload["window_warning"] = warning
    return Response(payload, status=200)


def _legacy_cancel_attendance_request(request, attendance):
    try:
        if attendance.employee_id.employee_user_id != request.user:
            return Response({"error": "Only the requester can cancel this request."}, status=403)
    except Exception:
        return Response({"error": "Only the requester can cancel this request."}, status=403)
    if not getattr(attendance, "is_validate_request", False) or getattr(attendance, "is_validate_request_approved", False):
        return Response({"error": "Only waiting requests can be canceled."}, status=400)
    wants_in, wants_out = get_requested_sessions(attendance)
    old_status = getattr(attendance, "request_type", None) or "waiting_request"
    was_create_request = getattr(attendance, "request_type", None) == "create_request"
    attendance.is_validate_request = False
    attendance.is_validate_request_approved = False
    attendance.request_type = "cancel_request"
    attendance.action_type = AttendanceRequestActionType.CANCELED
    try:
        attendance.action_by = request.user.employee_get
    except Exception:
        attendance.action_by = None
    attendance.action_at = dj_timezone.now()
    _log_attendance_request_status_change(attendance, request, action_type=AttendanceRequestActionType.CANCELED, old_status=old_status, new_status="cancel_request")
    final_attendance = attendance
    if was_create_request:
        final_attendance = clear_request_override_and_recompute(attendance, include_in=wants_in, include_out=wants_out)
    
    try:
        payload = AttendanceRequestSerializer(final_attendance, context={"request": request}).data
    except Exception:
        payload = {"id": getattr(final_attendance, "id", None), "request_type": getattr(final_attendance, "request_type", None)}

    return Response(payload, status=200)


def _legacy_revoke_attendance_request(request, attendance, reason=None):
    if not getattr(attendance, "is_validate_request_approved", False):
        return Response({"error": "Attendance request not found."}, status=404)
    if getattr(attendance.employee_id, "employee_user_id", None) == request.user:
        return Response({"error": "You cannot revoke your own approved request."}, status=403)
    can_act = False
    try:
        can_act = bool(_can_act_on_employee(request.user, attendance.employee_id))
    except Exception:
        can_act = False
    if not (can_act or user_can_approve_request(request.user, attendance)):
        return Response({"error": "You do not have permission to revoke this request."}, status=403)
    wants_in, wants_out = get_requested_sessions(attendance)
    old_status = getattr(attendance, "request_type", None) or "approved"
    _restore_request_back_to_raw(attendance, include_in=wants_in, include_out=wants_out, prev_attendance_date=attendance.attendance_date)
    attendance.is_validate_request_approved = False
    attendance.is_validate_request = False
    attendance.request_type = "revoke_request"
    attendance.action_type = AttendanceRequestActionType.REVOKED
    attendance.action_at = dj_timezone.now()
    try:
        attendance.action_by = request.user.employee_get
    except Exception:
        attendance.action_by = None
    try:
        attendance.save(update_fields=[
            "is_validate_request_approved",
            "is_validate_request",
            "request_type",
            "action_type",
            "action_at",
            "action_by",
        ])
    except Exception:
        attendance.save()
    _log_attendance_request_status_change(attendance, request, action_type=AttendanceRequestActionType.REVOKED, old_status=old_status, new_status="revoke_request", remark=reason)
    result = recompute_attendance(attendance.employee_id, attendance.attendance_date)
    final_attendance = result.attendance if result is not None else attendance
    
    try:
        payload = AttendanceRequestSerializer(final_attendance, context={"request": request}).data
    except Exception:
        payload = {"id": getattr(final_attendance, "id", None), "request_type": getattr(final_attendance, "request_type", None)}
    return Response(payload, status=200)


def _legacy_reject_attendance_request(request, attendance, reason):
    if not reason:
        return Response({"error": "Reject reason is required."}, status=400)
    if getattr(attendance.employee_id, "employee_user_id", None) == request.user:
        return Response({"error": "Use cancel for your own request."}, status=403)
    can_act = False
    try:
        can_act = bool(_can_act_on_employee(request.user, attendance.employee_id))
    except Exception:
        can_act = False
    if not (can_act or user_can_approve_request(request.user, attendance)):
        return Response({"error": "You do not have permission to reject this request."}, status=403)
    wants_in, wants_out = get_requested_sessions(attendance)
    was_create_request = getattr(attendance, "request_type", None) == "create_request"
    attendance.is_validate_request = False
    attendance.is_validate_request_approved = False
    attendance.request_type = "reject_request"
    attendance.action_type = AttendanceRequestActionType.REJECTED
    attendance.action_at = dj_timezone.now()
    try:
        attendance.action_by = request.user.employee_get
    except Exception:
        attendance.action_by = None
    _log_attendance_request_status_change(attendance, request, action_type=AttendanceRequestActionType.REJECTED, old_status=getattr(attendance, "request_type", None) or "waiting_request", new_status="reject_request", remark=reason)
    final_attendance = attendance
    if was_create_request:
        final_attendance = clear_request_override_and_recompute(attendance, include_in=wants_in, include_out=wants_out)
    
    try:
        payload = AttendanceRequestSerializer(final_attendance, context={"request": request}).data
    except Exception:
        payload = {"id": getattr(final_attendance, "id", None), "request_type": getattr(final_attendance, "request_type", None)}
    return Response(payload, status=200)




# -----------------------------------------------------------------------------
# Active request/history scoping helpers
# -----------------------------------------------------------------------------
def _request_user_lookup_value(request):
    user = getattr(request, "user", None)
    value = getattr(user, "pk", None) or getattr(user, "id", None)
    if value is None:
        value = getattr(getattr(user, "employee_get", None), "id", None)
    return value if value is not None else -1

def _attendance_correction_history_scope(request):
    qs = AttendanceCorrectionRequest.objects.exclude(employee_id__employee_user_id=_request_user_lookup_value(request))
    is_super = bool(getattr(request.user, "is_superuser", False))
    has_global_perm = bool(getattr(request.user, "has_perm", lambda _p: False)("attendance.change_attendance"))
    if is_super or has_global_perm:
        return qs
    if is_reportingmanager(request):
        sub_ids = _subordinate_employee_ids(request)
        if not sub_ids:
            return AttendanceCorrectionRequest.objects.none()
        return qs.filter(employee_id__id__in=sub_ids)
    return AttendanceCorrectionRequest.objects.none()


def _attendance_correction_history_status_filter(qs, status_value):
    status_value = (status_value or "").strip().lower()
    if not status_value or status_value == "all":
        return qs.filter(status__in=[AttendanceCorrectionRequestStatus.APPROVED, AttendanceCorrectionRequestStatus.REJECTED, AttendanceCorrectionRequestStatus.REVOKED])
    mapping = {
        "waiting": AttendanceCorrectionRequestStatus.WAITING,
        "approved": AttendanceCorrectionRequestStatus.APPROVED,
        "rejected": AttendanceCorrectionRequestStatus.REJECTED,
        "revoked": AttendanceCorrectionRequestStatus.REVOKED,
        "canceled": AttendanceCorrectionRequestStatus.CANCELED,
        "cancel": AttendanceCorrectionRequestStatus.CANCELED,
    }
    wanted = mapping.get(status_value)
    return qs.filter(status=wanted) if wanted else qs


def _work_mode_history_scope(request):
    qs = WorkModeRequest.objects.all().exclude(employee_id__employee_user_id=request.user)
    include_all = _is_admin_with_perm(request, "attendance.change_workmoderequest")
    if not include_all:
        sub_ids = _subordinate_employee_ids(request)
        if not sub_ids:
            return WorkModeRequest.objects.none()
        qs = qs.filter(employee_id__id__in=sub_ids)
    return qs


def _work_mode_history_status_filter(qs, status_value):
    status_value = (status_value or "").strip().lower()
    if not status_value or status_value == "all":
        return qs.exclude(status=WorkModeRequestStatus.PENDING)
    mapping = {
        "waiting": WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        "waiting_for_approval": WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        "approved": WorkModeRequestStatus.APPROVED,
        "rejected": WorkModeRequestStatus.REJECTED,
        "revoked": WorkModeRequestStatus.REVOKED,
        "canceled": WorkModeRequestStatus.CANCELED,
        "cancel": WorkModeRequestStatus.CANCELED,
    }
    wanted = mapping.get(status_value)
    return qs.filter(status=wanted) if wanted else qs.exclude(status=WorkModeRequestStatus.PENDING)


def _approval_scope_employee_options(request, *, work_type=False):
    queryset = Employee.objects.all().order_by("employee_first_name", "employee_last_name", "id")
    if work_type:
        if not _is_admin_with_perm(request, "attendance.change_workmoderequest"):
            subordinate_ids = _subordinate_employee_ids(request)
            if not subordinate_ids:
                queryset = Employee.objects.none()
            else:
                queryset = queryset.filter(id__in=subordinate_ids)
    else:
        is_super = bool(getattr(request.user, "is_superuser", False))
        has_global_perm = bool(getattr(request.user, "has_perm", lambda _p: False)("attendance.change_attendance"))
        if not (is_super or has_global_perm):
            if is_reportingmanager(request):
                queryset = filtersubordinatesemployeemodel(request, queryset, "attendance.change_attendance")
            else:
                queryset = Employee.objects.none()
    employee = getattr(getattr(request.user, "employee_get", None), "id", None)
    if employee is not None:
        queryset = queryset.exclude(id=employee)
    return [
        {
            "id": emp.id,
            "employee_first_name": (getattr(emp, "employee_first_name", "") or "").strip(),
            "employee_last_name": (getattr(emp, "employee_last_name", "") or "").strip(),
            "name": (f"{(getattr(emp, 'employee_first_name', '') or '').strip()} {(getattr(emp, 'employee_last_name', '') or '').strip()}").strip() or f"Employee #{emp.id}",
        }
        for emp in queryset.distinct()
    ]


def _is_attendance_exempt_manager(employee) -> bool:
    """Return True if employee should be excluded from IN/OUT attendance.

    Custom rule requested: if an employee is a reporting manager of at least one
    other employee, they act as "approver-only" and use an external attendance
    system. They can still approve, but must not punch or be counted as missing.
    """

    try:
        return (
            EmployeeWorkInformation.objects.filter(reporting_manager_id=employee)
            .only("id")
            .exists()
        )
    except Exception:
        return False


# -----------------------------------------------------------------------------
# Active mobile single-session helpers
# -----------------------------------------------------------------------------
# Work-mode helpers (WFO/WFA/ON_DUTY)
# -----------------------------------------------------------------------------
def _pick_work_mode_request(employee, target_date: date, want: str):
    """Return the *effective* WorkModeRequest for the given date.

    Kept for backward compatibility; core resolution is delegated to
    ``attendance.services.work_type_request_rules``.
    """
    return effective_work_type(employee, target_date, want).request


def _resolve_effective_work_type(employee, target_date: date, want: str):
    """Return tuple (mode, source, request)."""
    eff = effective_work_type(employee, target_date, want)
    return eff.mode, eff.source, eff.request


def _resolve_committed_work_type(employee, target_date: date, want: str):
    """Return the committed/read-model work mode for display surfaces.

    Pending or waiting requests must not change the visible IN/OUT work mode on the
    Check In / Check Out screen before approval. Request state still flows through
    the dedicated request-status fields.
    """
    eff = committed_work_type(employee, target_date, want)
    return eff.mode, eff.source, eff.request


def _mode_from_request(req) -> str:
    # Compatibility helper
    return req.mode if req else AttendanceWorkMode.WFO


def _is_punch_allowed(mode: str, req, source: str):
    from attendance.services.work_type_request_rules import EffectiveWorkType
    return punch_allowed(EffectiveWorkType(mode=mode, source=source, request=req))

def _requires_proof(mode: str) -> bool:
    return mode in (AttendanceWorkMode.WFA, AttendanceWorkMode.WFH, AttendanceWorkMode.ON_DUTY)


def _is_model_instance(value):
    return isinstance(value, Model)


def _object_id(value):
    if value is None:
        return None
    pk = getattr(value, "pk", None)
    if pk not in (None, ""):
        return pk
    obj_id = getattr(value, "id", None)
    if obj_id not in (None, ""):
        return obj_id
    return value if isinstance(value, int) else None


def _default_geo_config():
    return SimpleNamespace(wfh_start=True, wfh_radius_in_meters=250)


def _company_obj_and_id(employee):
    company = None
    try:
        company = employee.get_company()
    except Exception:
        company = getattr(getattr(employee, "employee_work_info", None), "company_id", None)
    company_id = _object_id(company)
    if company_id is None:
        nested_company_id = getattr(getattr(employee, "employee_work_info", None), "company_id_id", None)
        if nested_company_id not in (None, ""):
            company_id = nested_company_id
    return company, company_id


def _company_wfh_radius(employee):
    config = _get_company_geofencing(employee)
    return int(getattr(config, "wfh_radius_in_meters", 250) or 250)


def _get_company_geofencing(employee):
    company, company_id = _company_obj_and_id(employee)
    if company_id is None:
        return _default_geo_config()
    if company is not None and not _is_model_instance(company):
        return _default_geo_config()
    config = GeoFencing.objects.filter(company_id_id=company_id).first()
    if config is None:
        return _default_geo_config()
    if not getattr(config, "wfh_radius_in_meters", None) or int(config.wfh_radius_in_meters or 0) <= 0:
        config.wfh_radius_in_meters = 250
        config.save(update_fields=["wfh_radius_in_meters"])
    return config


def _get_wfh_profile(employee):
    employee_id = _object_id(employee)
    if employee_id is None or not _is_model_instance(employee):
        return None
    defaults = {"home_radius_in_meters": _company_wfh_radius(employee)}
    return EmployeeWfhProfile.objects.get_or_create(employee_id=employee_id, defaults=defaults)[0]


def _maps_link(lat, lng):
    if lat is None or lng is None:
        return None
    return f"https://maps.google.com/?q={lat},{lng}"


def _serialize_wfh_history(history_qs):
    items = []
    for item in history_qs.order_by("-acted_at", "-id")[:20]:
        items.append({
            "id": item.id,
            "action_type": item.action_type,
            "old_home_latitude": item.old_home_latitude,
            "old_home_longitude": item.old_home_longitude,
            "old_radius_in_meters": item.old_radius_in_meters,
            "new_home_latitude": item.new_home_latitude,
            "new_home_longitude": item.new_home_longitude,
            "new_radius_in_meters": item.new_radius_in_meters,
            "old_face_image": item.old_face_image,
            "new_face_image": item.new_face_image,
            "acted_at": item.acted_at.isoformat() if item.acted_at else None,
            "acted_by": getattr(item.acted_by, "id", None),
            "acted_by_name": str(item.acted_by) if getattr(item, "acted_by", None) else None,
            "notes": item.notes,
        })
    return items


def _has_wfh_home_reset_permission(user):
    return bool(
        user
        and (
            getattr(user, "is_superuser", False)
            or user.has_perm("attendance.reset_wfh_home_geofence")
        )
    )


def _has_wfh_face_reset_permission(user):
    return bool(
        user
        and (
            getattr(user, "is_superuser", False)
            or user.has_perm("attendance.reset_wfh_face_detection")
        )
    )


def _serialize_wfh_profile(employee):
    profile = _get_wfh_profile(employee)
    employee_id = _object_id(employee)
    face = None
    if employee_id is not None and _is_model_instance(employee):
        face = EmployeeFaceDetection.objects.filter(employee_id_id=employee_id).first()
    if profile is None:
        return {
            "home_latitude": None,
            "home_longitude": None,
            "google_maps_link": None,
            "radius_in_meters": _company_wfh_radius(employee),
            "is_home_configured": False,
            "requires_home_reconfiguration": False,
            "requires_face_reenrollment": False,
            "face_image": getattr(face.image, "url", None) if face and getattr(face, "image", None) else None,
            "history": [],
        }
    return {
        "home_latitude": profile.home_latitude,
        "home_longitude": profile.home_longitude,
        "google_maps_link": _maps_link(profile.home_latitude, profile.home_longitude),
        "radius_in_meters": profile.home_radius_in_meters,
        "is_home_configured": bool(profile.is_home_configured and profile.home_latitude is not None and profile.home_longitude is not None),
        "requires_home_reconfiguration": bool(profile.requires_home_reconfiguration),
        "requires_face_reenrollment": bool(profile.requires_face_reenrollment),
        "face_image": getattr(face.image, "url", None) if face and getattr(face, "image", None) else None,
        "history": _serialize_wfh_history(profile.employee.wfh_profile_history.all()) if _is_model_instance(employee) else [],
    }


def _log_wfh_history(*, employee, action_type, acted_by=None, old_lat=None, old_lng=None, old_radius=None, new_lat=None, new_lng=None, new_radius=None, old_face_image=None, new_face_image=None, notes=None):
    EmployeeWfhProfileHistory.objects.create(
        employee=employee,
        action_type=action_type,
        acted_by=acted_by,
        old_home_latitude=old_lat,
        old_home_longitude=old_lng,
        old_radius_in_meters=old_radius,
        new_home_latitude=new_lat,
        new_home_longitude=new_lng,
        new_radius_in_meters=new_radius,
        old_face_image=old_face_image,
        new_face_image=new_face_image,
        notes=notes,
    )


def _validate_wfh_punch(employee, mode, location, *, direction, actor=None):
    if mode != AttendanceWorkMode.WFH:
        return None
    profile = _get_wfh_profile(employee)
    config = _get_company_geofencing(employee)
    if location is None:
        return "Location is required for WFH attendance."
    if profile.requires_face_reenrollment:
        return "Face detection Anda telah di-reset. Silakan lakukan konfigurasi ulang foto wajah sebelum check-in atau check-out."
    if profile.requires_home_reconfiguration or not profile.is_home_configured or profile.home_latitude is None or profile.home_longitude is None:
        return "Lokasi rumah WFH Anda telah di-reset. Silakan setup ulang lokasi rumah sebelum check-in atau check-out."
    if config and getattr(config, "wfh_start", True):
        try:
            lat = float(location.get("lat") if isinstance(location, dict) else location["lat"])
            lng = float(location.get("lng") if isinstance(location, dict) else location["lng"])
            meters = geodesic((profile.home_latitude, profile.home_longitude), (lat, lng)).meters
        except Exception:
            return "Location is required for WFH attendance."
        if meters > float(profile.home_radius_in_meters or config.wfh_radius_in_meters or 250):
            return "Anda berada di luar radius lokasi rumah yang diizinkan untuk WFH."
    return None

def _effective_document_status_or_none(req) -> str | None:
    if not req:
        return None
    resolver = getattr(req, "effective_document_status", None)
    if callable(resolver):
        try:
            return resolver()
        except Exception:
            return getattr(req, "document_status", None)
    return getattr(req, "document_status", None)


def _session_on_duty_benefit_active(*, mode: str, req, punch_dt) -> bool:
    """ON Duty benefit applies only when the punch exists for that session.

    For request-based ON Duty, supporting document must be VERIFIED.
    Scheduled ON Duty without a request still grants the session benefit once the
    corresponding punch exists.
    """

    if mode != AttendanceWorkMode.ON_DUTY or punch_dt is None:
        return False

    if req is None:
        return True

    if getattr(req, "status", None) != WorkModeRequestStatus.APPROVED:
        return False

    return _effective_document_status_or_none(req) == WorkModeRequestDocumentStatus.VERIFIED


def _neutralize_on_duty_session_metrics(*, in_mode: str, in_req, in_punch_dt, out_mode: str, out_req, out_punch_dt, late_by_hhmm, checked_out_early: bool, checked_out_early_by_hhmm):
    if _session_on_duty_benefit_active(mode=in_mode, req=in_req, punch_dt=in_punch_dt):
        late_by_hhmm = None
    if _session_on_duty_benefit_active(mode=out_mode, req=out_req, punch_dt=out_punch_dt):
        checked_out_early = False
        checked_out_early_by_hhmm = None
    return late_by_hhmm, checked_out_early, checked_out_early_by_hhmm

def _parse_location_payload(request) -> dict | None:
    """Parse location payload from request.data (multipart or JSON).
    Accepts:
      - location: dict or JSON string
      - lat/lng/accuracy/provider/captured_at
      - latitude/longitude
    """
    data = getattr(request, "data", {}) or {}
    loc = data.get("location", None)
    if loc:
        if isinstance(loc, str):
            try:
                loc = json.loads(loc)
            except Exception:
                loc = None
        if isinstance(loc, dict):
            return loc

    # Flat keys
    lat = data.get("lat", None) or data.get("latitude", None)
    lng = data.get("lng", None) or data.get("longitude", None)
    if lat is None or lng is None:
        return None

    def _to_float(v):
        try:
            return float(v)
        except Exception:
            return None

    lat_f = _to_float(lat)
    lng_f = _to_float(lng)
    if lat_f is None or lng_f is None:
        return None

    payload = {"lat": lat_f, "lng": lng_f}

    acc = data.get("accuracy", None)
    if acc is not None:
        try:
            payload["accuracy"] = float(acc)
        except Exception:
            payload["accuracy"] = acc

    provider = data.get("provider", None) or data.get("source", None)
    if provider:
        payload["provider"] = str(provider)

    captured_at = data.get("captured_at", None) or data.get("timestamp", None)
    if captured_at:
        payload["captured_at"] = str(captured_at)

    return payload


def _is_admin_with_perm(request, perm_codename: str) -> bool:
    """Admin permission helper.

    Backward compatibility:
    - Superuser is always treated as allowed.
    - Treat `attendance.change_attendance` as an admin approval permission for
      work-type requests too (many installs grant this to admins).
    """
    try:
        user = getattr(request, "user", None)
        if not user:
            return False
        if getattr(user, "is_superuser", False):
            return True
        if user.has_perm(perm_codename):
            return True
        if perm_codename == "attendance.change_workmoderequest" and user.has_perm(
            "attendance.change_attendance"
        ):
            return True
        return False
    except Exception:
        return False


def _subordinate_employee_ids(request):
    try:
        return get_subordinate_employee_ids(request) or []
    except Exception:
        return []


def _is_supervisor_of(request, employee_id: int) -> bool:
    """True if request.user is in the reporting chain above `employee_id`."""
    try:
        sub_ids = _subordinate_employee_ids(request)
        return int(employee_id) in set(map(int, sub_ids or []))
    except Exception:
        return False


def _can_act_on_employee(request, employee_id: int, perm_codename: str, allow_owner: bool = False) -> bool:
    """Admin (has perm) OR supervisor of employee. Optionally allow owner.

    IMPORTANT: Even if user is admin with perm, disallow acting on their own request unless allow_owner=True.
    """
    my_emp_id = None
    try:
        my_emp = request.user.employee_get
        my_emp_id = int(getattr(my_emp, "id", 0) or 0)
    except Exception:
        my_emp_id = None

    is_owner = my_emp_id is not None and int(my_emp_id) == int(employee_id)

    # Block self-action unless explicitly allowed
    if is_owner and not allow_owner:
        return False

    if _is_admin_with_perm(request, perm_codename):
        return True

    if allow_owner and is_owner:
        return True

    return _is_supervisor_of(request, employee_id)


# -----------------------------------------------------------------------------
def _api_now(request) -> datetime:
    """
    Resolve a request datetime.

    Priority:
    1) request.datetime (if injected by a wrapper)
    2) timezone-aware now() if USE_TZ
    3) naive datetime.now()
    """
    dt_attr = getattr(request, "datetime", None)
    if dt_attr:
        return dt_attr
    if getattr(settings, "USE_TZ", False):
        return dj_timezone.localtime(dj_timezone.now())
    return datetime.now()


def _api_today(request, dt_now: datetime) -> date:
    """Resolve a request date if provided, otherwise use dt_now.date()."""
    d_attr = getattr(request, "date", None)
    return d_attr if isinstance(d_attr, date) else dt_now.date()


def _coerce_datetime_like(dt_value: datetime | None, ref_dt: datetime) -> datetime | None:
    """Ensure dt_value has the same timezone-awareness as ref_dt.

    - If USE_TZ=True and dt_value is naive, make it aware using ref_dt.tzinfo (or current timezone).
    - If USE_TZ=True and dt_value is aware, convert to ref_dt's timezone for safe comparison.
    - If USE_TZ=False and dt_value is aware, make it naive.
    """
    if dt_value is None:
        return None

    use_tz = getattr(settings, "USE_TZ", False)

    if use_tz:
        # ref tzinfo: prefer ref_dt, fallback to Django current timezone.
        ref_tz = ref_dt.tzinfo if dj_timezone.is_aware(ref_dt) and ref_dt.tzinfo else dj_timezone.get_current_timezone()

        if dj_timezone.is_naive(dt_value):
            return dj_timezone.make_aware(dt_value, ref_tz)

        # dt_value aware: normalize to ref_tz for consistent comparisons
        try:
            return dj_timezone.localtime(dt_value, ref_tz)
        except Exception:
            return dt_value

    # USE_TZ=False
    if dj_timezone.is_aware(dt_value):
        try:
            return dj_timezone.make_naive(dt_value)
        except Exception:
            return dt_value
    return dt_value


def _normalize_none(value):
    """Normalize common empty string values to Python None."""
    if value is None:
        return None
    if isinstance(value, str) and value.strip() in ("", "None", "null", "NULL"):
        return None
    return value


def _format_minimum_hour(value):
    """Return minimum working hour in HH:MM (string) or None."""
    if value is None:
        return None
    # Already HH:MM / HH:MM:SS string
    if isinstance(value, str):
        s = value.strip()
        if not s or s.lower() in ("none", "null"):
            return None
        # Keep only HH:MM if seconds present
        if len(s) >= 5 and s[2] == ":":
            return s[:5]
        return s
    # datetime.time
    try:
        return value.strftime("%H:%M")
    except Exception:
        pass
    # timedelta (best effort)
    try:
        total_seconds = int(value.total_seconds())
        if total_seconds < 0:
            return None
        h = (total_seconds // 3600) % 24
        m = (total_seconds % 3600) // 60
        return f"{h:02d}:{m:02d}"
    except Exception:
        return str(value)



def _normalize_requested_data(requested_data: dict) -> dict:
    """Normalize JSON-requested_data so it can be used safely in queryset.update().

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


def _api_resolve_attendance_date_and_day(shift, dt_now: datetime):
    """
    Apply Horilla night-shift noon-to-noon rule to resolve attendance_date and day.

    Strategy:
    - Prefer resolving the day via EmployeeShiftSchedule for the employee's shift.
    - Fall back to any EmployeeShiftDay row if no schedule row exists.

    Returns:
        attendance_date, day_obj, minimum_hour, start_time_sec, end_time_sec, now_hhmm, now_sec
    """
    date_today = dt_now.date()
    now_hhmm = dt_now.strftime("%H:%M")
    now_sec = strtime_seconds(now_hhmm)
    mid_day_sec = strtime_seconds("12:00")

    def _resolve_for_date(d: date):
        weekday = d.strftime("%A").lower()

        schedule = None
        try:
            schedule = cio.EmployeeShiftSchedule.objects.filter(
                shift_id=shift, day__day=weekday
            ).select_related("day").first()
        except Exception:
            schedule = None

        if schedule:
            day_obj = schedule.day
            minimum_hour = schedule.minimum_working_hour or "00:00"
            try:
                start_time_sec = strtime_seconds(schedule.start_time.strftime("%H:%M")) if schedule.start_time else 0
                end_time_sec = strtime_seconds(schedule.end_time.strftime("%H:%M")) if schedule.end_time else 0
            except Exception:
                start_time_sec, end_time_sec = 0, 0
            return day_obj, minimum_hour, start_time_sec, end_time_sec

        # Fallback (best-effort)
        day_obj = EmployeeShiftDay.objects.filter(day=weekday).first()
        if not day_obj:
            return None, "00:00", 0, 0
        minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day_obj, shift=shift)
        return day_obj, minimum_hour, start_time_sec, end_time_sec

    attendance_date = date_today
    day, minimum_hour, start_time_sec, end_time_sec = _resolve_for_date(date_today)

    is_night_shift = start_time_sec > end_time_sec and start_time_sec != end_time_sec

    if is_night_shift and mid_day_sec > now_sec:
        date_yesterday = date_today - timedelta(days=1)
        attendance_date = date_yesterday
        day, minimum_hour, start_time_sec, end_time_sec = _resolve_for_date(date_yesterday)

    return attendance_date, day, minimum_hour, start_time_sec, end_time_sec, now_hhmm, now_sec

def _seconds_to_hhmm(total_seconds: int | None) -> str | None:
    try:
        seconds = max(0, int(total_seconds or 0))
    except Exception:
        return None
    hours = (seconds // 3600) % 24
    minutes = (seconds % 3600) // 60
    return f"{hours:02d}:{minutes:02d}"


def _seconds_to_minute_display(total_seconds: int | float | None) -> str | None:
    try:
        seconds = max(0, int(total_seconds or 0))
    except Exception:
        return None
    return format_decimal_minutes(seconds_to_decimal_minutes(seconds))


def _truncate_dt_to_minute(value: datetime | None) -> datetime | None:
    if value is None:
        return None
    try:
        return value.replace(second=0, microsecond=0)
    except Exception:
        return value


def _compute_mobile_effective_start_and_earliest_checkout(
    *,
    shift_start_dt: datetime | None,
    shift_end_dt: datetime | None,
    actual_check_in_dt: datetime | None,
    clock_in_type: str | None,
    flex_seconds: int | None,
    schedule=None,
    minimum_hour: str | None = None,
    leave_kind: str | None = None,
    check_in_cutoff_dt: datetime | None = None,
):
    """Return (effective_start_dt, earliest_checkout_dt, valid_check_in).

    This helper is for mobile note / early-checkout semantics only.
    It intentionally uses full shift duration (shift_end - shift_start), not
    minimum working hour.
    """

    if not (shift_start_dt and shift_end_dt):
        return None, None, True

    policy = build_attendance_policy(
        schedule=schedule,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
        minimum_hour=minimum_hour or "00:00",
        leave_kind=leave_kind,
        check_in_cutoff_dt=check_in_cutoff_dt,
    )
    effective_start_dt, earliest_checkout_dt, valid_check_in, _checkin_window_end_dt, _checkout_start_dt = compute_mobile_status_metrics(
        policy,
        actual_check_in_dt=actual_check_in_dt,
        clock_in_type=clock_in_type,
        flex_seconds=int(flex_seconds or 0),
    )
    return effective_start_dt, earliest_checkout_dt, valid_check_in


def _compute_canonical_mobile_note_metrics(
    *,
    attendance_date: date,
    dt_now: datetime,
    attendance,
    schedule,
    shift_start_dt: datetime | None,
    shift_end_dt: datetime | None,
    minimum_hour: str | None,
    leave_kind: str | None,
    clock_in_type: str | None,
    grace_seconds: int | None,
    grace_out_seconds: int | None = 0,
    check_in_cutoff_dt: datetime | None = None,
):
    if not attendance:
        return None, None, True, None, None

    shift_start_dt = _coerce_datetime_like(shift_start_dt, dt_now) if shift_start_dt else None
    shift_end_dt = _coerce_datetime_like(shift_end_dt, dt_now) if shift_end_dt else None
    check_in_cutoff_dt = _coerce_datetime_like(check_in_cutoff_dt, dt_now) if check_in_cutoff_dt else None

    actual_in_t = getattr(attendance, "attendance_clock_in", None)
    actual_out_t = getattr(attendance, "attendance_clock_out", None)
    actual_in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
    actual_out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date

    actual_in_dt = None
    actual_out_dt = None
    if actual_in_t:
        actual_in_dt = _truncate_dt_to_minute(
            _coerce_datetime_like(datetime.combine(actual_in_date, actual_in_t), dt_now)
        )
    if actual_out_t:
        actual_out_dt = _truncate_dt_to_minute(
            _coerce_datetime_like(datetime.combine(actual_out_date, actual_out_t), dt_now)
        )

    policy = build_attendance_policy(
        schedule=schedule,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
        minimum_hour=minimum_hour or "00:00",
        leave_kind=leave_kind,
        check_in_cutoff_dt=check_in_cutoff_dt,
    )
    _effective_start_dt, earliest_checkout_dt, valid_check_in, _checkin_window_end_dt, _checkout_start_dt = compute_mobile_status_metrics(
        policy,
        actual_check_in_dt=actual_in_dt,
        clock_in_type=clock_in_type,
        flex_seconds=int(grace_seconds or 0),
    )
    metrics = compute_attendance_metrics(
        policy,
        final_in_dt=actual_in_dt,
        final_out_dt=actual_out_dt,
        grace_seconds=int(grace_seconds or 0),
        clock_in_type=clock_in_type,
        is_presence_only=False,
        early_out_grace_seconds=int(grace_out_seconds or 0),
    )
    return metrics, earliest_checkout_dt, valid_check_in, actual_in_dt, actual_out_dt


def _shift_bounds_for_note_context(attendance_date: date, start_time_sec, end_time_sec):
    try:
        start_hhmm = _seconds_to_hhmm(int(start_time_sec))
        end_hhmm = _seconds_to_hhmm(int(end_time_sec))
        if not start_hhmm or not end_hhmm:
            return None, None
        shift_start_dt = timezone.make_aware(datetime.combine(attendance_date, datetime.strptime(start_hhmm, "%H:%M").time()))
        shift_end_dt = timezone.make_aware(datetime.combine(attendance_date, datetime.strptime(end_hhmm, "%H:%M").time()))
        if int(start_time_sec) > int(end_time_sec) and int(start_time_sec) != int(end_time_sec):
            shift_end_dt = shift_end_dt + timedelta(days=1)
        return shift_start_dt, shift_end_dt
    except Exception:
        return None, None


def _note_time_to_shift_instance_dt(
    threshold_time: time | None,
    *,
    shift_start_dt: datetime | None,
    shift_end_dt: datetime | None,
):
    if not (threshold_time and shift_start_dt and shift_end_dt):
        return None

    return canonical_time_to_shift_instance_dt(
        threshold_time,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
    )


def _build_mobile_header_note_context(employee, shift, attendance_date: date, day, start_time_sec, end_time_sec) -> dict:
    payload = {
        "header_note_leave_breakdown": None,
        "header_note_effective_minimum_hour": None,
        "header_note_effective_duration_seconds": None,
    }

    shift_start_dt, shift_end_dt = _shift_bounds_for_note_context(attendance_date, start_time_sec, end_time_sec)
    if not (shift_start_dt and shift_end_dt):
        return payload

    leave_breakdown = None
    if leave_breakdown_for_attendance_date is not None:
        try:
            leave_breakdown = leave_breakdown_for_attendance_date(employee, attendance_date) or None
        except Exception:
            leave_breakdown = None

    payload["header_note_leave_breakdown"] = leave_breakdown

    if leave_breakdown == "full_day":
        payload["header_note_effective_minimum_hour"] = "00:00"
        payload["header_note_effective_duration_seconds"] = 0
        return payload

    effective_start_dt = shift_start_dt
    effective_end_dt = shift_end_dt

    schedule = None
    try:
        weekday = day.day if getattr(day, "day", None) else attendance_date.strftime("%A").lower()
        schedule = cio.EmployeeShiftSchedule.objects.filter(
            shift_id=shift, day__day=weekday
        ).select_related("day").first()
    except Exception:
        schedule = None

    policy = build_attendance_policy(
        schedule=schedule,
        shift_start_dt=shift_start_dt,
        shift_end_dt=shift_end_dt,
        minimum_hour="00:00",
        leave_kind=leave_breakdown,
        check_in_cutoff_dt=None,
    )
    effective_start_dt = policy.late_reference_dt or shift_start_dt
    effective_end_dt = policy.nominal_policy_end_dt or shift_end_dt
    duration_seconds = int(policy.required_work_seconds or 0)
    payload["header_note_effective_duration_seconds"] = duration_seconds
    payload["header_note_effective_minimum_hour"] = policy.minimum_hour if leave_breakdown in {"first_half", "second_half"} else _seconds_to_hhmm(duration_seconds)
    return payload


def _ensure_single_session_activity(attendance: Attendance, prev_attendance_date: date | None = None) -> AttendanceActivity:
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


def _restore_request_back_to_raw(attendance: Attendance, *, include_in: bool, include_out: bool, prev_attendance_date: date | None = None):
    return restore_raw_state_after_request(
        attendance,
        include_in=include_in,
        include_out=include_out,
    )


class ClockInAPIView(APIView):
    """Mobile Clock-In (single-session + hybrid mode)."""

    permission_classes = [IsAuthenticated]
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def post(self, request):
        dt_now = _api_now(request)
        image = request.FILES.get("image")
        location = _parse_location_payload(request)
        employee, work_info = employee_exists(request)
        punch_log = None

        def _reject(message, http_status):
            if punch_log is not None:
                update_punch_history(punch_log, accepted=False, reason=humanize_mobile_error(message, direction="in"))
            return Response({"error": message}, status=http_status)

        if not employee or work_info is None:
            return Response({"error": "Missing work information or employee details."}, status=status.HTTP_400_BAD_REQUEST)

        access = evaluate_attendance_access(employee=employee, user=getattr(request, "user", None))
        if not access.allowed:
            return Response({"error": access.message or "Attendance is disabled for this employee."}, status=status.HTTP_403_FORBIDDEN)

        try:
            punch_log = create_mobile_punch_history(
                request=request,
                employee=employee,
                attendance_date=None,
                punch_timestamp=dt_now,
                direction="in",
                image=image,
                location=location,
                reason=None,
            )
        except ValidationError as error:
            return Response({"error": _extract_error_message(error)}, status=status.HTTP_400_BAD_REQUEST)

        shift = work_info.shift_id
        date_today = _api_today(request, dt_now)
        attendance_date, day, minimum_hour, start_time_sec, end_time_sec, now_hhmm, _ = _api_resolve_attendance_date_and_day(shift, dt_now)
        update_punch_history(punch_log, attendance_date=attendance_date)

        in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        if in_mode == AttendanceWorkMode.WFO:
            return _reject("WFO attendance must be recorded via biometric device.", status.HTTP_403_FORBIDDEN)
        wfh_error = _validate_wfh_punch(employee, in_mode, location, direction="in", actor=employee)
        if wfh_error:
            return _reject(wfh_error, status.HTTP_403_FORBIDDEN)

        if not _is_punch_allowed(in_mode, in_req, in_source):
            msg = "Request is required." if not in_req else "Request is not approved yet."
            if in_mode == AttendanceWorkMode.ON_DUTY and in_req:
                msg = "On Duty request is not active."
            if in_mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH} and in_req and in_req.status != WorkModeRequestStatus.APPROVED:
                msg = f"{in_mode.upper()} requires an approved request before clock-in."
            return _reject(msg, status.HTTP_403_FORBIDDEN)

        existing = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        if existing and getattr(existing, "attendance_clock_in", None):
            update_punch_history(punch_log, attendance=existing)
            return _reject("Already clocked-in", status.HTTP_400_BAD_REQUEST)

        try:
            rules = cio.get_shift_rules(
                attendance_date,
                shift,
                day,
                start_time_sec=start_time_sec,
                end_time_sec=end_time_sec,
            )
        except Exception:
            rules = {"cutoff_in_dt": None}

        grace_seconds = int((rules or {}).get("grace_seconds") or 0)
        cutoff_in_dt = rules.get("cutoff_in_dt")
        cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now) if cutoff_in_dt else None
        check_in_window_start_dt = rules.get("check_in_window_start_dt")
        check_in_window_end_dt = rules.get("check_in_window_end_dt") or cutoff_in_dt
        check_in_window_start_dt = _coerce_datetime_like(check_in_window_start_dt, dt_now) if check_in_window_start_dt else None
        check_in_window_end_dt = _coerce_datetime_like(check_in_window_end_dt, dt_now) if check_in_window_end_dt else None

        leave_kind_for_today = None
        if leave_breakdown_for_attendance_date is not None:
            try:
                leave_kind_for_today = leave_breakdown_for_attendance_date(employee, attendance_date) or None
            except Exception:
                leave_kind_for_today = None

        if leave_kind_for_today in {"first_half", "second_half"}:
            try:
                policy_for_today = build_attendance_policy(
                    schedule=rules.get("schedule") if isinstance(rules, dict) else None,
                    shift_start_dt=rules.get("shift_start_dt") if isinstance(rules, dict) else None,
                    shift_end_dt=rules.get("shift_end_dt") if isinstance(rules, dict) else None,
                    minimum_hour=minimum_hour,
                    leave_kind=leave_kind_for_today,
                    check_in_cutoff_dt=check_in_window_end_dt,
                )
                _effective_policy_end_dt, half_day_checkin_window_end_dt, _half_day_checkout_start_dt = resolve_policy_windows(
                    policy_for_today,
                    actual_check_in_dt=None,
                    clock_in_type=rules.get("clock_in_type") if isinstance(rules, dict) else None,
                    flex_seconds=grace_seconds,
                )
                check_in_window_end_dt = half_day_checkin_window_end_dt or check_in_window_end_dt
            except Exception:
                pass

        try:
            auto_reject_wfa_waiting_for_date(employee=employee, target_date=attendance_date, now_dt=dt_now, cutoff_in_dt=cutoff_in_dt, cutoff_out_dt=None)
            in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        except Exception:
            pass

        if check_in_window_start_dt and dt_now < check_in_window_start_dt:
            return _reject("Check-in window has not started yet.", status.HTTP_400_BAD_REQUEST)
        if check_in_window_end_dt and dt_now > check_in_window_end_dt:
            return _reject("Check-in cut-off has passed.", status.HTTP_400_BAD_REQUEST)

        if _requires_proof(in_mode):
            if not image:
                return _reject("Photo is required.", status.HTTP_400_BAD_REQUEST)
            if not location:
                return _reject("Location is required.", status.HTTP_400_BAD_REQUEST)

        try:
            clock_in_attendance_and_activity(
                employee=employee,
                date_today=date_today,
                attendance_date=attendance_date,
                day=day,
                now_hhmm=now_hhmm,
                shift=shift,
                minimum_hour=minimum_hour,
                start_time_sec=start_time_sec,
                end_time_sec=end_time_sec,
                in_datetime=dt_now,
                clock_in_image=image,
                clock_in_mode=in_mode,
                clock_in_location=location,
                work_mode_request=in_req,
                is_presensi_only=(in_mode == AttendanceWorkMode.ON_DUTY),
                clock_in_channel="mobile",
                raw_punch_history=punch_log,
            )
        except ValidationError as error:
            return _reject(_extract_error_message(error), status.HTTP_400_BAD_REQUEST)

        out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")
        attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        update_punch_history(punch_log, attendance=attendance, attendance_date=attendance_date, work_mode=in_mode, related_work_mode_request=in_req, decision_source=getattr(attendance, "reconciliation_source", None) if attendance else None)
        reconcile_attendance_punches(employee=employee, attendance_date=attendance_date)

        earliest_check_out_hhmm = None
        invalid_check_in = False
        late_by_hhmm = None
        _note_in_dt = None
        _note_out_dt = None
        try:
            leave_kind_for_note = None
            if leave_breakdown_for_attendance_date is not None:
                try:
                    leave_kind_for_note = leave_breakdown_for_attendance_date(employee, attendance_date) or None
                except Exception:
                    leave_kind_for_note = None
            shift_start_dt, shift_end_dt = _shift_bounds_for_note_context(attendance_date, start_time_sec, end_time_sec)
            metrics_for_note, earliest_check_out_dt, valid_check_in_for_note, _note_in_dt, _note_out_dt = _compute_canonical_mobile_note_metrics(
                attendance_date=attendance_date,
                dt_now=dt_now,
                attendance=attendance,
                schedule=rules.get("schedule") if isinstance(rules, dict) else None,
                shift_start_dt=shift_start_dt,
                shift_end_dt=shift_end_dt,
                minimum_hour=minimum_hour,
                leave_kind=leave_kind_for_note,
                clock_in_type=rules.get("clock_in_type") if isinstance(rules, dict) else None,
                grace_seconds=grace_seconds,
                grace_out_seconds=0,
                check_in_cutoff_dt=rules.get("check_in_window_end_dt") if isinstance(rules, dict) else None,
            )
            invalid_check_in = bool(_note_in_dt and not valid_check_in_for_note)
            if metrics_for_note is not None:
                late_s = int(getattr(metrics_for_note, "late_seconds", 0) or 0)
                if late_s > 0:
                    late_by_hhmm = _seconds_to_minute_display(late_s)
            if earliest_check_out_dt:
                earliest_check_out_hhmm = earliest_check_out_dt.strftime("%H:%M")
        except Exception:
            earliest_check_out_hhmm = None
            invalid_check_in = False
            late_by_hhmm = None

        late_by_hhmm, _ignored_checked_out_early, _ignored_checked_out_early_by = _neutralize_on_duty_session_metrics(
            in_mode=in_mode,
            in_req=in_req,
            in_punch_dt=_note_in_dt,
            out_mode=out_mode,
            out_req=out_req,
            out_punch_dt=_note_out_dt,
            late_by_hhmm=late_by_hhmm,
            checked_out_early=False,
            checked_out_early_by_hhmm=None,
        )

        response_payload = {
            "message": "Clocked-In",
            "attendance_date": str(attendance_date),
            "has_attendance": bool(attendance),
            "first_check_in": attendance.attendance_clock_in.strftime("%I:%M %p") if attendance and getattr(attendance, "attendance_clock_in", None) else None,
            "last_check_out": attendance.attendance_clock_out.strftime("%I:%M %p") if attendance and getattr(attendance, "attendance_clock_out", None) else None,
            "missing_check_in": False,
            "invalid_check_in": bool(invalid_check_in),
            "late_by": late_by_hhmm,
            "work_hours_below_minimum": False,
            "checked_out_early": False,
            "checked_out_early_by": None,
            "in_mode": in_mode,
            "out_mode": out_mode,
            "work_mode_request_id": getattr(in_req, "id", None),
            "in_work_type": in_mode,
            "out_work_type": out_mode,
            "in_work_type_source": in_source,
            "out_work_type_source": out_source,
            "in_work_type_request_id": getattr(in_req, "id", None),
            "out_work_type_request_id": getattr(out_req, "id", None),
            "wfh_profile": _serialize_wfh_profile(employee),
            "in_work_type_request_status": getattr(in_req, "status", None),
            "out_work_type_request_status": getattr(out_req, "status", None),
            "wfh_profile": _serialize_wfh_profile(employee),
            "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
            "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
            "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
            "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
            "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
            "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,
            "minimum_working_hour": _format_minimum_hour(minimum_hour),
            "earliest_check_out": earliest_check_out_hhmm,
            "server_now": dt_now.isoformat(),
            "server_time": dt_now.strftime("%H:%M"),
        }
        response_payload.update(build_mobile_header_state(response_payload))
        return Response(response_payload, status=status.HTTP_200_OK)


class ClockOutAPIView(APIView):
    """Mobile Clock-Out (single-session + hybrid mode)."""

    permission_classes = [IsAuthenticated]
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def post(self, request):
        dt_now = _api_now(request)
        image = request.FILES.get("image")
        location = _parse_location_payload(request)
        employee, work_info = employee_exists(request)
        punch_log = None

        def _reject(message, http_status, attendance=None, attendance_date=None):
            if punch_log is not None:
                update_punch_history(
                    punch_log,
                    accepted=False,
                    reason=humanize_mobile_error(message, direction="out"),
                    attendance=attendance,
                    attendance_date=attendance_date,
                )
            return Response({"error": message}, status=http_status)

        if not employee or work_info is None:
            return Response({"error": "Missing work information or employee details."}, status=status.HTTP_400_BAD_REQUEST)

        access = evaluate_attendance_access(employee=employee, user=getattr(request, "user", None))
        if not access.allowed:
            return Response({"error": access.message or "Attendance is disabled for this employee."}, status=status.HTTP_403_FORBIDDEN)

        try:
            punch_log = create_mobile_punch_history(
                request=request,
                employee=employee,
                attendance_date=None,
                punch_timestamp=dt_now,
                direction="out",
                image=image,
                location=location,
                reason=None,
            )
        except ValidationError as error:
            return Response({"error": _extract_error_message(error)}, status=status.HTTP_400_BAD_REQUEST)

        shift = work_info.shift_id
        attendance_date, day, minimum_hour, start_time_sec, end_time_sec, _, now_sec = _api_resolve_attendance_date_and_day(shift, dt_now)
        update_punch_history(punch_log, attendance_date=attendance_date)
        out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")

        if out_mode == AttendanceWorkMode.WFO:
            return _reject("WFO attendance must be recorded via biometric device.", status.HTTP_403_FORBIDDEN)
        wfh_error = _validate_wfh_punch(employee, out_mode, location, direction="out", actor=employee)
        if wfh_error:
            return _reject(wfh_error, status.HTTP_403_FORBIDDEN, attendance_date=attendance_date)
        if not _is_punch_allowed(out_mode, out_req, out_source):
            msg = "Request is required." if not out_req else "Request is not approved yet."
            if out_mode == AttendanceWorkMode.ON_DUTY and out_req:
                msg = "On Duty request is not active."
            if out_mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH} and out_req and out_req.status != WorkModeRequestStatus.APPROVED:
                msg = f"{out_mode.upper()} requires an approved request before clock-out."
            return _reject(msg, status.HTTP_403_FORBIDDEN)

        try:
            rules = cio.get_shift_rules(
                attendance_date,
                shift,
                day,
                start_time_sec=start_time_sec,
                end_time_sec=end_time_sec,
            )
        except Exception:
            rules = {"cutoff_in_dt": None, "cutoff_out_dt": None}

        grace_seconds = int((rules or {}).get("grace_seconds") or 0)
        window_end_dt = rules.get("check_out_window_end_dt") or rules.get("cutoff_out_dt")
        window_end_dt = _coerce_datetime_like(window_end_dt, dt_now) if window_end_dt else None

        try:
            _cutoff_in_tmp = rules.get("cutoff_in_dt")
            _cutoff_in_tmp = _coerce_datetime_like(_cutoff_in_tmp, dt_now) if _cutoff_in_tmp else None
            auto_reject_wfa_waiting_for_date(employee=employee, target_date=attendance_date, now_dt=dt_now, cutoff_in_dt=_cutoff_in_tmp, cutoff_out_dt=window_end_dt)
            out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")
        except Exception:
            pass

        if window_end_dt and dt_now > window_end_dt:
            return _reject("Check-out window has ended. Please submit an attendance request.", status.HTTP_400_BAD_REQUEST, attendance_date=attendance_date)

        if _requires_proof(out_mode):
            if not image:
                return _reject("Photo is required.", status.HTTP_400_BAD_REQUEST, attendance_date=attendance_date)
            if not location:
                return _reject("Location is required.", status.HTTP_400_BAD_REQUEST, attendance_date=attendance_date)

        existing_att = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        existing_out_rejected = bool(existing_att and getattr(existing_att, "out_attendance_status", None) == "REJECTED")
        allow_update = (out_mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH, AttendanceWorkMode.ON_DUTY}) or existing_out_rejected

        try:
            attendance, missing_check_in = cio.clock_out_attendance_and_activity(
                employee=employee,
                attendance_date=attendance_date,
                shift=shift,
                minimum_hour=minimum_hour,
                out_datetime=dt_now,
                day=day,
                clock_out_image=image,
                clock_out_mode=out_mode,
                clock_out_location=location,
                work_mode_request=out_req,
                is_presensi_only=(out_mode == AttendanceWorkMode.ON_DUTY),
                allow_update_clock_out=allow_update,
                raise_if_already_clocked_out=(not allow_update),
                clock_out_channel="mobile",
                raw_punch_history=punch_log,
            )
        except ValidationError as error:
            return _reject(_extract_error_message(error), status.HTTP_400_BAD_REQUEST, attendance=existing_att, attendance_date=attendance_date)
        except Exception as error:
            logger.exception("clock_out_attendance_and_activity failed")
            return _reject(str(error), status.HTTP_400_BAD_REQUEST, attendance=existing_att, attendance_date=attendance_date)

        in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        update_punch_history(punch_log, attendance=attendance, attendance_date=attendance_date, work_mode=out_mode, related_work_mode_request=out_req, decision_source=getattr(attendance, "reconciliation_source", None) if attendance else None)
        reconcile_attendance_punches(employee=employee, attendance_date=attendance_date)

        worked_below_minimum = False
        checked_out_early = False
        checked_out_early_by = None
        earliest_check_out_hhmm = None
        invalid_check_in = False
        first_check_in = attendance.attendance_clock_in.strftime("%I:%M %p") if attendance and getattr(attendance, "attendance_clock_in", None) else None
        last_check_out = attendance.attendance_clock_out.strftime("%I:%M %p") if attendance and getattr(attendance, "attendance_clock_out", None) else None
        late_by_hhmm = None
        earliest_check_out_dt = None
        _note_in_dt = None
        _note_out_dt = None

        try:
            leave_kind_for_note = None
            if leave_breakdown_for_attendance_date is not None:
                try:
                    leave_kind_for_note = leave_breakdown_for_attendance_date(employee, attendance_date) or None
                except Exception:
                    leave_kind_for_note = None
            shift_start_dt, shift_end_dt = _shift_bounds_for_note_context(attendance_date, start_time_sec, end_time_sec)
            grace_out_sec = 0
            try:
                resolved_grace = cio._resolve_grace_time(rules.get("schedule") if isinstance(rules, dict) else None, shift)
                if resolved_grace and getattr(resolved_grace, "allowed_clock_out", False):
                    grace_out_sec = int(getattr(resolved_grace, "allowed_time_in_secs", 0) or 0)
            except Exception:
                grace_out_sec = 0
            metrics_for_note, earliest_check_out_dt, valid_check_in_for_note, _note_in_dt, _note_out_dt = _compute_canonical_mobile_note_metrics(
                attendance_date=attendance_date,
                dt_now=dt_now,
                attendance=attendance,
                schedule=rules.get("schedule") if isinstance(rules, dict) else None,
                shift_start_dt=shift_start_dt,
                shift_end_dt=shift_end_dt,
                minimum_hour=minimum_hour,
                leave_kind=leave_kind_for_note,
                clock_in_type=rules.get("clock_in_type") if isinstance(rules, dict) else None,
                grace_seconds=grace_seconds,
                grace_out_seconds=grace_out_sec,
                check_in_cutoff_dt=rules.get("check_in_window_end_dt") if isinstance(rules, dict) else None,
            )
            invalid_check_in = bool(_note_in_dt and not valid_check_in_for_note)
            if metrics_for_note is not None:
                late_s = int(getattr(metrics_for_note, "late_seconds", 0) or 0)
                if late_s > 0:
                    late_by_hhmm = _seconds_to_minute_display(late_s)
                early_s = int(getattr(metrics_for_note, "early_out_seconds", 0) or 0)
                if early_s > 0:
                    checked_out_early = True
                    checked_out_early_by = _seconds_to_minute_display(early_s)
            if earliest_check_out_dt:
                earliest_check_out_hhmm = earliest_check_out_dt.strftime("%H:%M")
        except Exception:
            invalid_check_in = False
            earliest_check_out_hhmm = None
            late_by_hhmm = None
            checked_out_early = False
            checked_out_early_by = None

        late_by_hhmm, checked_out_early, checked_out_early_by = _neutralize_on_duty_session_metrics(
            in_mode=in_mode,
            in_req=in_req,
            in_punch_dt=_note_in_dt,
            out_mode=out_mode,
            out_req=out_req,
            out_punch_dt=_note_out_dt,
            late_by_hhmm=late_by_hhmm,
            checked_out_early=checked_out_early,
            checked_out_early_by_hhmm=checked_out_early_by,
        )

        try:
            min_formatted = _format_minimum_hour(minimum_hour)
            worked_hour_value = getattr(attendance, "attendance_worked_hour", None) or "00:00"
            if attendance and getattr(attendance, "attendance_clock_in", None) and getattr(attendance, "attendance_clock_out", None) and min_formatted:
                worked_below_minimum = strtime_seconds(worked_hour_value) < strtime_seconds(min_formatted)
        except Exception:
            worked_below_minimum = False

        note_context = _build_mobile_header_note_context(
            employee=employee,
            shift=shift,
            attendance_date=attendance_date,
            day=day,
            start_time_sec=start_time_sec,
            end_time_sec=end_time_sec,
        )
        note_effective_seconds = note_context.get("header_note_effective_duration_seconds")
        note_work_hours_below_minimum = False
        note_work_hours_shortfall = None
        try:
            worked_seconds_value = strtime_seconds(getattr(attendance, "attendance_worked_hour", None) or "00:00")
        except Exception:
            worked_seconds_value = 0
        if attendance and getattr(attendance, "attendance_clock_in", None) and getattr(attendance, "attendance_clock_out", None) and note_effective_seconds is not None and int(note_effective_seconds) > 0:
            try:
                if int(worked_seconds_value) < int(note_effective_seconds):
                    note_work_hours_below_minimum = True
                    short_s = int(note_effective_seconds) - int(worked_seconds_value)
                    note_work_hours_shortfall = _seconds_to_minute_display(short_s)
            except Exception:
                note_work_hours_below_minimum = False

        response_payload = {
            "message": "Clocked-Out",
            "attendance_date": str(attendance_date),
            "has_attendance": bool(attendance),
            "first_check_in": first_check_in,
            "last_check_out": last_check_out,
            "missing_check_in": bool(missing_check_in),
            "invalid_check_in": bool(invalid_check_in),
            "updated": bool(allow_update),
            "late_by": late_by_hhmm,
            "work_hours_below_minimum": bool(worked_below_minimum),
            "checked_out_early": bool(checked_out_early),
            "checked_out_early_by": checked_out_early_by,
            "work_hours_shortfall": None,
            "in_mode": in_mode,
            "out_mode": out_mode,
            "work_mode_request_id": getattr(out_req, "id", None),
            "in_work_type": in_mode,
            "out_work_type": out_mode,
            "in_work_type_source": in_source,
            "out_work_type_source": out_source,
            "in_work_type_request_id": getattr(in_req, "id", None),
            "out_work_type_request_id": getattr(out_req, "id", None),
            "wfh_profile": _serialize_wfh_profile(employee),
            "in_work_type_request_status": getattr(in_req, "status", None),
            "out_work_type_request_status": getattr(out_req, "status", None),
            "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
            "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
            "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
            "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
            "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
            "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,
            "minimum_working_hour": _format_minimum_hour(minimum_hour),
            "earliest_check_out": earliest_check_out_hhmm,
            "header_note_work_hours_below_minimum": bool(note_work_hours_below_minimum),
            "header_note_work_hours_shortfall": note_work_hours_shortfall,
            "server_now": dt_now.isoformat(),
            "server_time": dt_now.strftime("%H:%M"),
        }
        response_payload.update(note_context)
        response_payload.update(build_mobile_header_state(response_payload))
        return Response(response_payload, status=status.HTTP_200_OK)


class AttendanceView(APIView):
    """
    Handles CRUD operations for attendance records.

    Methods:
        get_queryset(request, type): Returns filtered attendance records.
        get(request, pk=None, type=None): Retrieves a specific record or a list of records.
        post(request): Creates a new attendance record.
        put(request, pk): Updates an existing attendance record.
        delete(request, pk): Deletes an attendance record and adjusts related overtime if needed.
    """

    permission_classes = [IsAuthenticated]
    filterset_class = AttendanceFilters

    def get_queryset(self, request=None, type=None):
        # Handle schema generation for DRF-YASG
        if getattr(self, "swagger_fake_view", False) or request is None:
            return Attendance.objects.none()
        if type == "ot":

            condition = AttendanceValidationCondition.objects.first()
            minot = strtime_seconds("00:30")
            if condition is not None:
                minot = strtime_seconds(condition.minimum_overtime_to_approve)
                queryset = Attendance.objects.filter(
                    overtime_second__gte=minot,
                    attendance_validated=True,
                )

        elif type == "validated":
            queryset = Attendance.objects.filter(attendance_validated=True)
        elif type == "non-validated":
            queryset = Attendance.objects.filter(attendance_validated=False)
        else:
            queryset = Attendance.objects.all()
        user = request.user
        # checking user level permissions
        perm = "attendance.view_attendance"
        queryset = permission_based_queryset(user, perm, queryset, user_obj=True)
        return queryset

    def get(self, request, pk=None, type=None):
        # individual object workflow
        if pk:
            attendance = get_object_or_404(Attendance, pk=pk)
            serializer = AttendanceSerializer(instance=attendance)
            return Response(serializer.data, status=200)
        # permission based querysete
        attendances = self.get_queryset(request, type)
        # filtering queryset
        attendances_filter_queryset = self.filterset_class(
            request.GET, queryset=attendances
        ).qs
        field_name = request.GET.get("groupby_field", None)
        if field_name:
            url = request.build_absolute_uri()
            return groupby_queryset(
                request, url, field_name, attendances_filter_queryset
            )
        # pagination workflow
        paginater = PageNumberPagination()
        page = paginater.paginate_queryset(attendances_filter_queryset, request)
        serializer = AttendanceSerializer(page, many=True)
        return paginater.get_paginated_response(serializer.data)

    @manager_permission_required("attendance.add_attendance")
    def post(self, request):
        serializer = AttendanceSerializer(data=request.data)
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)
        employee_id = request.data.get("employee_id")
        attendance_date = request.data.get("attendance_date", date.today())
        if Attendance.objects.filter(
            employee_id=employee_id, attendance_date=attendance_date
        ).exists():
            return Response(
                {
                    "error": [
                        "Attendance for this employee on the current date already exists."
                    ]
                },
                status=400,
            )
        return Response(serializer.errors, status=400)

    @method_decorator(permission_required("attendance.change_attendance"))
    def put(self, request, pk):
        try:
            attendance = Attendance.objects.get(id=pk)
        except Attendance.DoesNotExist:
            return Response({"detail": "Attendance record not found."}, status=404)

        serializer = AttendanceSerializer(instance=attendance, data=request.data)

        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)

        # Customize error message for unique constraint
        serializer_errors = serializer.errors
        if "non_field_errors" in serializer.errors:
            unique_error_msg = (
                "The fields employee_id, attendance_date must make a unique set."
            )
            if unique_error_msg in serializer.errors["non_field_errors"]:
                serializer_errors = {
                    "non_field_errors": [
                        "The employee already has attendance on this date."
                    ]
                }
        return Response(serializer_errors, status=400)

    @method_decorator(permission_required("attendance.delete_attendance"))
    def delete(self, request, pk):
        attendance = Attendance.objects.get(id=pk)
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
                return Response({"status", "deleted"}, status=200)
            except Exception as error:
                return Response({"error:", f"{error}"}, status=400)
        else:
            try:
                attendance.delete()
                return Response({"status", "deleted"}, status=200)
            except Exception as error:
                return Response({"error:", f"{error}"}, status=400)


class ValidateAttendanceView(APIView):
    """
    Validates an attendance record and sends a notification to the employee.

    Method:
        put(request, pk): Marks the attendance as validated and notifies the employee.
    """

    permission_classes = [IsAuthenticated]

    def put(self, request, pk):
        attendance = Attendance.objects.filter(id=pk).update(attendance_validated=True)
        attendance = Attendance.objects.filter(id=pk).first()
        try:
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Your attendance for the date {attendance.attendance_date} is validated",
                verb_ar=f"تم تحقيق حضورك في تاريخ {attendance.attendance_date}",
                verb_de=f"Deine Anwesenheit für das Datum {attendance.attendance_date} ist bestätigt.",
                verb_es=f"Se valida tu asistencia para la fecha {attendance.attendance_date}.",
                verb_fr=f"Votre présence pour la date {attendance.attendance_date} est validée.",
                redirect="/attendance/view-my-attendance",
                icon="checkmark",
                api_redirect=f"/api/attendance/attendance?employee_id{attendance.employee_id}",
            )
        except:
            pass
        return Response(status=200)


class OvertimeApproveView(APIView):
    """
    Approves overtime for an attendance record and sends a notification to the employee.

    Method:
        put(request, pk): Marks the overtime as approved and notifies the employee.
    """

    permission_classes = [IsAuthenticated]

    def put(self, request, pk):
        try:
            attendance = Attendance.objects.filter(id=pk).update(
                attendance_overtime_approve=True
            )
        except Exception as E:
            return Response({"error": str(E)}, status=400)

        attendance = Attendance.objects.filter(id=pk).first()
        try:
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Your {attendance.attendance_date}'s attendance overtime approved.",
                verb_ar=f"تمت الموافقة على إضافة ساعات العمل الإضافية لتاريخ {attendance.attendance_date}.",
                verb_de=f"Die Überstunden für den {attendance.attendance_date} wurden genehmigt.",
                verb_es=f"Se ha aprobado el tiempo extra de asistencia para el {attendance.attendance_date}.",
                verb_fr=f"Les heures supplémentaires pour la date {attendance.attendance_date} ont été approuvées.",
                redirect="/attendance/attendance-overtime-view",
                icon="checkmark",
                api_redirect="/api/attendance/attendance-hour-account/",
            )
        except:
            pass
        return Response(status=200)


class AttendanceRequestView(APIView):
    serializer_class = AttendanceCorrectionRequestSerializer
    compat_serializer_class = AttendanceRequestSerializer
    permission_classes = [IsAuthenticated]
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def get(self, request, pk=None):
        if pk:
            req_obj = AttendanceCorrectionRequest.objects.filter(id=pk).first()
            if req_obj is None:
                legacy_attendance = Attendance.objects.filter(id=pk).first()
                if legacy_attendance is not None:
                    return Response(self.compat_serializer_class(legacy_attendance, context={"request": request}).data, status=200)
                return Response({"error": "Attendance request not found."}, status=404)
            flags = build_attendance_correction_permission_flags(req_obj, request.user)
            if not any([flags.get("can_edit"), flags.get("can_cancel"), flags.get("can_approve"), flags.get("can_reject"), flags.get("can_revoke")]) and not correction_user_is_request_owner(request.user, req_obj) and not getattr(request.user, "is_superuser", False):
                return Response({"error": "You do not have permission to view this request."}, status=status.HTTP_403_FORBIDDEN)
            return Response(AttendanceCorrectionRequestSerializer(req_obj, context={"request": request}).data, status=200)

        approval_view = (request.GET.get("approval_view") or "").strip().lower()
        month_range = _parse_filter_month_range(request.GET.get("month") or request.GET.get("date")) or _parse_filter_month_range(dj_timezone.localdate().strftime("%Y-%m"))
        history_month_start, history_month_end, _ = _parse_filter_month_range(request.GET.get("month") or request.GET.get("date")) or month_range
        status_filter = (request.GET.get("status") or "all").strip().lower()
        mine_only = (request.GET.get("mine") or "").strip().lower() in {"1", "true", "yes"}

        approvals_qs = AttendanceCorrectionRequest.objects.filter(status=AttendanceCorrectionRequestStatus.WAITING).exclude(employee_id__employee_user_id=_request_user_lookup_value(request))
        if not getattr(request.user, "is_superuser", False):
            sub_ids = _subordinate_employee_ids(request)
            if sub_ids:
                approvals_qs = approvals_qs.filter(employee_id__id__in=sub_ids)
            else:
                approvals_qs = AttendanceCorrectionRequest.objects.none()

        my_qs = AttendanceCorrectionRequest.objects.filter(employee_id__employee_user_id=_request_user_lookup_value(request))

        if approval_view == "history":
            requests = _attendance_correction_history_scope(request)
            employee_id = (request.GET.get("employee_id") or "").strip()
            if employee_id:
                requests = requests.filter(employee_id_id=employee_id)
            requests = requests.filter(attendance_date__range=(history_month_start, history_month_end))
            requests = _attendance_history_status_filter(requests, request.GET.get("status"))
            try:
                history_has_results = requests.exists()
            except Exception:
                history_has_results = True
            if not history_has_results:
                requests = _attendance_request_history_scope(request)
                if employee_id:
                    requests = requests.filter(employee_id_id=employee_id)
                requests = requests.filter(attendance_date__range=(history_month_start, history_month_end))
                requests = _attendance_history_status_filter(requests, request.GET.get("status"))
        elif mine_only:
            requests = my_qs.filter(attendance_date__range=(month_range[0], month_range[1]))
            if status_filter != "all":
                status_mapping = {
                    "waiting": AttendanceCorrectionRequestStatus.WAITING,
                    "approved": AttendanceCorrectionRequestStatus.APPROVED,
                    "rejected": AttendanceCorrectionRequestStatus.REJECTED,
                    "revoked": AttendanceCorrectionRequestStatus.REVOKED,
                    "canceled": AttendanceCorrectionRequestStatus.CANCELED,
                    "cancel": AttendanceCorrectionRequestStatus.CANCELED,
                }
                if status_filter in status_mapping:
                    requests = requests.filter(status=status_mapping[status_filter])
        else:
            requests = AttendanceCorrectionRequest.objects.filter(Q(id__in=approvals_qs.values("id")) | Q(id__in=my_qs.values("id"))).distinct()

        try:
            has_results = requests.exists()
        except Exception:
            has_results = True
        if not has_results and approval_view != "history":
            user_lookup = _request_user_lookup_value(request)
            approvals_legacy = Attendance.objects.filter(is_validate_request=True).exclude(employee_id__employee_user_id=user_lookup)
            approvals_legacy = filtersubordinates(request, perm="attendance.change_attendance", queryset=approvals_legacy)
            owner_base_qs = Attendance.objects.filter(employee_id__employee_user_id=user_lookup)
            my_legacy = owner_base_qs.filter(Q(action_type__isnull=False) | Q(is_validate_request=True) | Q(is_validate_request_approved=True))
            if mine_only:
                requests = my_legacy.filter(attendance_date__range=(month_range[0], month_range[1]))
            else:
                requests = (approvals_legacy | my_legacy).distinct()
                requests = AttendanceFilters(request.GET, queryset=requests).qs
        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(requests.order_by("-attendance_date", "-action_at", "-id"), request)
        serializer_source = page
        serializer_class = self.serializer_class if getattr(getattr(page, "paginator", None), "object_list", getattr(requests, "model", None)) is AttendanceCorrectionRequest or getattr(requests, "model", None) is AttendanceCorrectionRequest else self.compat_serializer_class
        serializer = serializer_class(page, many=True, context={"request": request})
        response = pagenation.get_paginated_response(serializer.data)
        if approval_view == "history":
            response.data["employee_options"] = _approval_scope_employee_options(request, work_type=False)
        return response

    @transaction.atomic
    def post(self, request):
        uploaded = _uploaded_request_files(request)
        try:
            validate_uploaded_files(uploaded)
        except ValidationError as ve:
            transaction.set_rollback(True)
            return Response({"files": getattr(ve, "messages", [str(ve)])}, status=400)
        data = _mutable_request_data(request)
        # Legacy form path remains for compatibility when new correction fields are absent.
        if not any(k in data for k in ("scope", "requested_check_in_time", "requested_check_out_time", "requested_check_in_date", "requested_check_out_date")):
            return _legacy_create_attendance_request(request, self.compat_serializer_class)
        try:
            employee = request.user.employee_get
        except Exception:
            return Response({"error": "Employee profile not found."}, status=400)
        try:
            req_obj = create_attendance_correction_request(employee=employee, actor_user=request.user, payload=data, uploaded_files=uploaded)
        except AttendanceCorrectionError as exc:
            return Response(getattr(exc, "message_dict", {"error": exc.messages if hasattr(exc, "messages") else str(exc)}), status=400)
        serializer = self.serializer_class(req_obj, context={"request": request})
        return Response(serializer.data, status=201)

    @transaction.atomic
    def put(self, request, pk):
        req_obj = _locked_correction_request(pk)
        if req_obj is None:
            return _legacy_update_attendance_request(request, pk, self.compat_serializer_class)
        flags = build_attendance_correction_permission_flags(req_obj, request.user)
        if not flags.get("can_edit"):
            return Response({"error": "Only the owner can edit a waiting request."}, status=status.HTTP_403_FORBIDDEN)
        uploaded = _uploaded_request_files(request)
        try:
            validate_uploaded_files(uploaded)
        except ValidationError as ve:
            transaction.set_rollback(True)
            return Response({"files": getattr(ve, "messages", [str(ve)])}, status=400)
        data = _mutable_request_data(request)
        try:
            req_obj = update_attendance_correction_request(request_obj=req_obj, actor_user=request.user, payload=data, uploaded_files=uploaded)
        except AttendanceCorrectionError as exc:
            return Response(getattr(exc, "message_dict", {"error": exc.messages if hasattr(exc, "messages") else str(exc)}), status=400)
        return Response(self.serializer_class(req_obj, context={"request": request}).data, status=200)


class AttendanceRequestApproveView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        req_obj = _locked_correction_request(pk)
        if req_obj is None:
            attendance = _locked_legacy_attendance(pk)
            if attendance is None:
                return Response({"error": "Attendance request not found."}, status=404)
            return _legacy_approve_attendance_request(request, attendance)
        if not correction_user_can_approve_request(request.user, req_obj):
            return Response({"error": "You do not have permission to approve this request."}, status=status.HTTP_403_FORBIDDEN)
        try:
            req_obj = approve_attendance_correction_request(request_obj=req_obj, actor_user=request.user)
        except AttendanceCorrectionError as exc:
            return Response(getattr(exc, "message_dict", {"error": exc.messages if hasattr(exc, "messages") else str(exc)}), status=400)
        return Response(AttendanceCorrectionRequestSerializer(req_obj, context={"request": request}).data, status=200)


class AttendanceRequestRevokeView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        req_obj = _locked_correction_request(pk)
        reason = ((getattr(request, "data", {}) or {}).get("reason") or (getattr(request, "data", {}) or {}).get("comment") or "").strip()
        if req_obj is None:
            attendance = _locked_legacy_attendance(pk)
            if attendance is None:
                return Response({"error": "Attendance request not found."}, status=404)
            return _legacy_revoke_attendance_request(request, attendance, reason=reason)
        flags = build_attendance_correction_permission_flags(req_obj, request.user)
        if not flags.get("can_revoke"):
            return Response({"error": "You do not have permission to revoke this request."}, status=status.HTTP_403_FORBIDDEN)
        try:
            req_obj = revoke_attendance_correction_request(request_obj=req_obj, actor_user=request.user, reason=reason)
        except AttendanceCorrectionError as exc:
            return Response(getattr(exc, "message_dict", {"error": exc.messages if hasattr(exc, "messages") else str(exc)}), status=400)
        return Response(AttendanceCorrectionRequestSerializer(req_obj, context={"request": request}).data, status=200)


class AttendanceRequestCancelView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        req_obj = _locked_correction_request(pk)
        if req_obj is None:
            attendance = _locked_legacy_attendance(pk)
            if attendance is None:
                return Response({"error": "Attendance request not found."}, status=404)
            return _legacy_cancel_attendance_request(request, attendance)
        flags = build_attendance_correction_permission_flags(req_obj, request.user)
        if not flags.get("can_cancel"):
            return Response({"error": "Only the requester can cancel a waiting request."}, status=status.HTTP_403_FORBIDDEN)
        try:
            req_obj = cancel_attendance_correction_request(request_obj=req_obj, actor_user=request.user)
        except AttendanceCorrectionError as exc:
            return Response(getattr(exc, "message_dict", {"error": exc.messages if hasattr(exc, "messages") else str(exc)}), status=400)
        return Response(AttendanceCorrectionRequestSerializer(req_obj, context={"request": request}).data, status=200)


class AttendanceRequestRejectView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        req_obj = _locked_correction_request(pk)
        reason = ((getattr(request, "data", {}) or {}).get("reason") or (getattr(request, "data", {}) or {}).get("comment") or "").strip()
        if req_obj is None:
            attendance = _locked_legacy_attendance(pk)
            if attendance is None:
                return Response({"error": "Attendance request not found."}, status=404)
            return _legacy_reject_attendance_request(request, attendance, reason)
        flags = build_attendance_correction_permission_flags(req_obj, request.user)
        if not flags.get("can_reject"):
            return Response({"error": "You do not have permission to reject this request."}, status=status.HTTP_403_FORBIDDEN)
        try:
            req_obj = reject_attendance_correction_request(request_obj=req_obj, actor_user=request.user, reason=reason)
        except AttendanceCorrectionError as exc:
            return Response(getattr(exc, "message_dict", {"error": exc.messages if hasattr(exc, "messages") else str(exc)}), status=400)
        return Response(AttendanceCorrectionRequestSerializer(req_obj, context={"request": request}).data, status=200)


class AttendanceRequestAttachmentDownloadView(APIView):
    permission_classes = [AllowAny]

    def get(self, request, attendance_id, file_id, disposition="download"):
        req_obj = get_object_or_404(AttendanceCorrectionRequest, id=attendance_id)
        link_or_file = get_object_or_404(AttendanceCorrectionRequestAttachment, request_id=attendance_id, attendance_request_file_id=file_id)
        file_obj = getattr(link_or_file, "attendance_request_file", link_or_file)
        token = request.GET.get("token")
        token_valid = verify_attendance_attachment_token(req_obj.id, file_obj.id, token)
        is_authenticated = bool(getattr(request.user, "is_authenticated", False))
        has_authenticated_access = is_authenticated and attendance_request_can_view_attachment(request, req_obj)
        if not (token_valid or has_authenticated_access):
            if token:
                return Response({"error": "Invalid or expired attachment token."}, status=403)
            return Response({"error": "You do not have permission to access this attachment."}, status=403)
        return _attachment_file_response(file_obj, disposition=disposition)

    def delete(self, request, attendance_id, file_id, disposition="download"):
        req_obj = get_object_or_404(AttendanceCorrectionRequest, id=attendance_id)
        link_or_file = get_object_or_404(AttendanceCorrectionRequestAttachment, request_id=attendance_id, attendance_request_file_id=file_id)
        file_obj = getattr(link_or_file, "attendance_request_file", link_or_file)
        try:
            flags = build_attendance_correction_permission_flags(req_obj, request.user)
            can_delete = flags.get("can_edit")
        except Exception:
            can_delete = False
        if not can_delete:
            try:
                if not user_can_delete_attachment(request.user, req_obj):
                    return Response({"error": "You do not have permission to delete this attachment."}, status=403)
            except Exception:
                return Response({"error": "You do not have permission to delete this attachment."}, status=403)
        try:
            hard_delete_request_attachment(req_obj, file_obj)
            return Response(status=204)
        except Exception:
            pass
        try:
            link_or_file.delete()
        except Exception:
            pass
        storage = getattr(getattr(file_obj, "file", None), "storage", None)
        file_name = getattr(getattr(file_obj, "file", None), "name", None)
        try:
            file_obj.delete()
        finally:
            if storage and file_name:
                try:
                    storage.delete(file_name)
                except Exception:
                    pass
        return Response(status=204)


class WorkModeRequestAttachmentAccessView(APIView):
    permission_classes = [AllowAny]

    def get(self, request, pk, file_id, disposition="download"):
        req = get_object_or_404(WorkModeRequest, id=pk)
        file_obj = get_object_or_404(AttendanceRequestFile, id=file_id)
        if not work_mode_attachment_belongs_to_request(req, file_obj):
            return Response({"error": "Attachment not found for this request."}, status=404)

        token = request.GET.get("token")
        token_valid = verify_work_mode_attachment_token(req.id, file_obj.id, token)
        is_authenticated = bool(getattr(request.user, "is_authenticated", False))
        has_authenticated_access = is_authenticated and (
            work_mode_request_can_view_attachment(request, req) or bool(getattr(request.user, "is_superuser", False))
        )
        if not (token_valid or has_authenticated_access):
            if token:
                return Response({"error": "Invalid or expired attachment token."}, status=403)
            return Response({"error": "You do not have permission to access this attachment."}, status=403)

        return _attachment_file_response(file_obj, disposition=disposition)


def _work_mode_request_text(data, *keys):
    try:
        for key in keys:
            value = data.get(key)
            if value is None:
                continue
            value = str(value).strip()
            if value:
                return value
    except Exception:
        pass
    return None


class WorkModeRequestView(APIView):
    """CRUD for WorkModeRequest (WFA / WFH / ON_DUTY).

    Final rules:
    - WFA allows optional supporting documents with version history only.
    - ON DUTY documents create reviewable versions.
    - Owner-only update/cancel/upload rules are enforced by centralized action services.
    """

    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def get(self, request, pk=None):
        if pk:
            obj = get_object_or_404(WorkModeRequest, pk=pk)
            emp_id = getattr(obj, "employee_id_id", None) or obj.employee_id.id
            if not _can_act_on_employee(
                request,
                emp_id,
                "attendance.view_workmoderequest",
                allow_owner=True,
            ) and not _can_act_on_employee(
                request,
                emp_id,
                "attendance.change_workmoderequest",
                allow_owner=True,
            ):
                return Response(
                    {"error": "You do not have permission to view this request."},
                    status=status.HTTP_403_FORBIDDEN,
                )
            return Response(self.serializer_class(obj, context={"request": request}).data, status=200)

        qs = WorkModeRequest.objects.all()
        scoped_qs = filtersubordinates(request, qs, perm="attendance.view_workmoderequest")
        try:
            own_qs = qs.filter(employee_id=request.user.employee_get)
        except Exception:
            own_qs = qs.none()
        qs = (scoped_qs | own_qs).distinct()

        if request.GET.get("mine") in ("1", "true", "True"):
            qs = own_qs

        month_range = _parse_filter_month_range(request.GET.get("month") or request.GET.get("date"))
        if month_range:
            month_start, month_end, _ = month_range
            qs = qs.filter(start_date__lte=month_end, end_date__gte=month_start)

        status_q = request.GET.get("status")
        if status_q:
            qs = qs.filter(status=status_q)

        mode_q = request.GET.get("mode") or request.GET.get("work_type")
        if mode_q:
            qs = qs.filter(mode=mode_q)

        scope_q = request.GET.get("scope")
        if scope_q:
            qs = qs.filter(scope=scope_q)

        ordered = qs.order_by("-id")
        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(ordered, request)
        serializer = self.serializer_class(page, many=True, context={"request": request})
        response = pagenation.get_paginated_response(serializer.data)
        return response

    def _collect_uploaded_files(self, request):
        uploaded = []
        if hasattr(request, "FILES"):
            uploaded = request.FILES.getlist("files") or request.FILES.getlist("files[]") or []
            if not uploaded:
                f_single = request.FILES.get("file")
                if f_single:
                    uploaded = [f_single]
        validate_uploaded_files(uploaded)
        return uploaded

    def _materialize_request_data(self, request):
        raw = request.data
        if hasattr(raw, "lists"):
            data = {}
            file_values = set()
            if hasattr(request, "FILES"):
                for values in request.FILES.lists():
                    for value in values[1]:
                        file_values.add(id(value))
            for key, values in raw.lists():
                filtered = [value for value in values if id(value) not in file_values]
                if not filtered:
                    continue
                data[key] = filtered if len(filtered) > 1 else filtered[0]
            return data
        if hasattr(raw, "items"):
            return {key: value for key, value in raw.items()}
        return dict(raw)

    @transaction.atomic
    def post(self, request):
        data = self._materialize_request_data(request)

        if not data.get("mode") and data.get("work_mode"):
            data["mode"] = data.get("work_mode")
        if not data.get("mode") and data.get("work_type"):
            data["mode"] = data.get("work_type")
        note_value = _work_mode_request_text(data, "reason", "note", "description")
        if note_value and not data.get("reason"):
            data["reason"] = note_value
        if note_value and not data.get("note"):
            data["note"] = note_value
        if not data.get("start_date") and data.get("date"):
            data["start_date"] = data.get("date")
        if not data.get("end_date") and data.get("start_date"):
            data["end_date"] = data.get("start_date")

        my_emp = _request_actor_employee(request)
        if my_emp is None:
            return Response(
                {"employee_id": ["An employee profile is required to create this request."]},
                status=status.HTTP_403_FORBIDDEN,
            )

        data["employee_id"] = getattr(my_emp, "id", my_emp)

        try:
            uploaded = self._collect_uploaded_files(request)
        except ValidationError as exc:
            return Response({"files": exc.messages}, status=status.HTTP_400_BAD_REQUEST)

        serializer = self.serializer_class(data=data, context={"request": request})
        if not serializer.is_valid():
            return Response(serializer.errors, status=400)

        try:
            obj = WorkModeRequestActions.create_request(
                actor=my_emp,
                mode=serializer.validated_data["mode"],
                scope=serializer.validated_data["scope"],
                start_date=serializer.validated_data["start_date"],
                end_date=serializer.validated_data["end_date"],
                reason=serializer.validated_data["reason"],
                duty_destination_location=serializer.validated_data.get("duty_destination_location"),
                uploaded_files=uploaded,
            )
        except WorkModeRequestConsistencyError as exc:
            return Response({"error": str(exc)}, status=409)
        except ValidationError as exc:
            return Response({"error": exc.messages if hasattr(exc, "messages") else str(exc)}, status=400)

        return Response(self.serializer_class(obj, context={"request": request}).data, status=200)

    @transaction.atomic
    def patch(self, request, pk):
        return self._patch_or_put(request, pk)

    @transaction.atomic
    def put(self, request, pk):
        return self._patch_or_put(request, pk)

    def _patch_or_put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)

        data = self._materialize_request_data(request)
        forbidden = {
            "mode", "work_type", "work_mode", "scope", "start_date", "end_date", "employee_id",
            "status", "approved_by", "approved_at", "action_type", "action_by", "action_at", "document_status",
            "document_verified_by", "document_verified_at",
        }
        if any(k in data for k in forbidden):
            return Response(
                {"error": "You can only update note, destination, and attachments from this endpoint."},
                status=400,
            )

        try:
            uploaded = self._collect_uploaded_files(request)
        except ValidationError as exc:
            return Response({"files": exc.messages}, status=status.HTTP_400_BAD_REQUEST)

        note = _work_mode_request_text(data, "reason", "note", "description")
        remark = _work_mode_request_text(data, "remark", "comment", "action_note")
        try:
            WorkModeRequestActions.update_request(
                obj,
                actor=_request_actor_employee(request),
                request=request,
                reason=note,
                duty_destination_location=data.get("duty_destination_location"),
                uploaded_files=uploaded,
                remark=remark,
            )
        except WorkModeRequestConsistencyError as exc:
            return Response({"error": str(exc)}, status=409)
        except ValidationError as exc:
            return Response({"error": exc.messages if hasattr(exc, "messages") else str(exc)}, status=400)

        return Response(self.serializer_class(obj, context={"request": request}).data, status=200)

class WorkModeRequestApprovalsView(APIView):
    """List actionable requests for managers/admins."""

    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer

    def get(self, request):
        now_dt = _api_now(request)
        today = now_dt.date()
        try:
            emp_ids = []
            if _is_admin_with_perm(request, "attendance.change_workmoderequest"):
                emp_ids = list(
                    WorkModeRequest.objects.filter(
                        mode=AttendanceWorkMode.WFA,
                        status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
                        start_date__lte=today,
                        end_date__gte=today,
                    ).values_list("employee_id", flat=True).distinct()
                )
            else:
                emp_ids = _subordinate_employee_ids(request)

            from employee.models import Employee
            for eid in emp_ids:
                emp = Employee.objects.filter(id=eid).first()
                if not emp:
                    continue
                shift = None
                try:
                    shift = emp.employee_work_info.shift_id
                except Exception:
                    shift = None
                if not shift:
                    continue
                day = EmployeeShiftDay.objects.filter(day=today.strftime("%A").lower()).first()
                if not day:
                    continue
                try:
                    _min_hour, start_sec, end_sec = shift_schedule_today(day=day, shift=shift)
                except Exception:
                    start_sec, end_sec = 0, 0

                try:
                    rules = cio.get_shift_rules(today, shift, day, start_time_sec=start_sec, end_time_sec=end_sec)
                except Exception:
                    rules = {"cutoff_in_dt": None, "cutoff_out_dt": None}

                auto_reject_wfa_waiting_for_date(
                    employee=emp,
                    target_date=today,
                    now_dt=now_dt,
                    cutoff_in_dt=rules.get("cutoff_in_dt"),
                    cutoff_out_dt=rules.get("cutoff_out_dt"),
                )
        except Exception:
            pass

        include_pending_on_duty = _is_admin_with_perm(request, "attendance.change_workmoderequest")
        queue = (request.GET.get("queue") or "approval").strip().lower()

        if queue == "history":
            qs = _work_mode_history_scope(request)
            employee_id = (request.GET.get("employee_id") or "").strip()
            if employee_id:
                qs = qs.filter(employee_id_id=employee_id)
            history_month_start, history_month_end, _ = _parse_filter_month_range(
                request.GET.get("month") or request.GET.get("date")
            ) or _parse_filter_month_range(dj_timezone.localdate().strftime("%Y-%m"))
            qs = qs.filter(start_date__lte=history_month_end, end_date__gte=history_month_start)
            qs = _work_mode_history_status_filter(qs, request.GET.get("status"))
            ordered = list(qs.order_by("-id"))
            filtered = []
            for req in ordered:
                try:
                    queue_type = classify_work_mode_request_queue(req)
                except WorkModeRequestConsistencyError:
                    logger.exception(
                        "Skipping inconsistent work-mode request %s while building queue %s",
                        getattr(req, "id", None),
                        queue,
                    )
                    continue
                if queue_type in {"approval", "document_review"}:
                    continue
                filtered.append(req)
            ordered = filtered
        else:
            if queue == "document_review":
                queue_q = work_mode_request_document_review_q()
            elif queue == "all":
                queue_q = work_mode_request_approval_q(include_pending_on_duty=include_pending_on_duty) | work_mode_request_document_review_q()
            else:
                queue_q = work_mode_request_approval_q(include_pending_on_duty=include_pending_on_duty)

            qs = WorkModeRequest.objects.filter(queue_q).exclude(employee_id__employee_user_id=request.user)

            if not include_pending_on_duty:
                sub_ids = _subordinate_employee_ids(request)
                if not sub_ids:
                    qs = qs.none()
                else:
                    qs = qs.filter(employee_id__id__in=sub_ids)

            ordered = list(qs.order_by("-id"))
            if queue in {"approval", "document_review", "all"}:
                filtered = []
                for req in ordered:
                    try:
                        queue_type = classify_work_mode_request_queue(req)
                    except WorkModeRequestConsistencyError:
                        logger.exception(
                            "Skipping inconsistent work-mode request %s while building queue %s",
                            getattr(req, "id", None),
                            queue,
                        )
                        continue
                    if queue == "approval" and queue_type != "approval":
                        continue
                    if queue == "document_review" and queue_type != "document_review":
                        continue
                    if queue == "all" and queue_type not in {"approval", "document_review"}:
                        continue
                    filtered.append(req)
                ordered = filtered
        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(ordered, request)
        serializer = self.serializer_class(page, many=True, context={"request": request})
        response = pagenation.get_paginated_response(serializer.data)
        if queue == "history":
            response.data["employee_options"] = _approval_scope_employee_options(request, work_type=True)
        return response


class WorkModeRequestApproveView(APIView):
    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer

    @transaction.atomic
    def put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)
        try:
            result = WorkModeRequestActions.approve_request(obj, actor=_request_actor_employee(request), request=request, now_dt=dj_timezone.now())
        except WorkModeRequestConsistencyError as exc:
            return Response({"error": str(exc)}, status=409)
        except ValidationError as exc:
            return Response({"error": exc.messages if hasattr(exc, "messages") else str(exc)}, status=400)
        data = self.serializer_class(obj, context={"request": request}).data
        if result.auto_rejected:
            return Response({**data, "error": "Work Type request passed its approval cutoff and was auto-rejected."}, status=400)
        return Response(data, status=200)


class WorkModeRequestRejectView(APIView):
    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer

    @transaction.atomic
    def put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)
        comment_text = _work_mode_request_text(
            request.data if hasattr(request, "data") else {},
            "comment",
            "reason",
            "remark",
            "action_note",
            "note",
        )
        try:
            WorkModeRequestActions.reject_request(
                obj,
                actor=_request_actor_employee(request),
                request=request,
                reason_code=WorkModeRequestRejectReasonCode.MANUAL_REJECT,
                remark=(str(comment_text).strip() if comment_text is not None else None),
            )
        except WorkModeRequestConsistencyError as exc:
            return Response({"error": str(exc)}, status=409)
        except ValidationError as exc:
            return Response({"error": exc.messages if hasattr(exc, "messages") else str(exc)}, status=400)
        return Response(self.serializer_class(obj, context={"request": request}).data, status=200)


class WorkModeRequestCancelView(APIView):
    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer

    @transaction.atomic
    def put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)
        remark = _work_mode_request_text(
            request.data if hasattr(request, "data") else {},
            "remark",
            "comment",
            "action_note",
            "reason",
        )
        try:
            WorkModeRequestActions.cancel_request(obj, actor=_request_actor_employee(request), request=request, remark=remark)
        except WorkModeRequestConsistencyError as exc:
            return Response({"error": str(exc)}, status=409)
        except ValidationError as exc:
            return Response({"error": exc.messages if hasattr(exc, "messages") else str(exc)}, status=400)
        return Response(self.serializer_class(obj, context={"request": request}).data, status=200)


class WorkModeRequestDocumentActionView(APIView):
    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer

    @transaction.atomic
    def put(self, request, pk, action):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)
        remark = _work_mode_request_text(
            request.data if hasattr(request, "data") else {},
            "reason",
            "comment",
            "remark",
            "action_note",
            "note",
        )

        try:
            if action == "revoke":
                WorkModeRequestActions.revoke_request(obj, actor=_request_actor_employee(request), request=request, remark=remark)
            elif action == "verify":
                WorkModeRequestActions.verify_document(obj, actor=_request_actor_employee(request), request=request, remark=remark)
            elif action == "reject-document":
                WorkModeRequestActions.reject_document(obj, actor=_request_actor_employee(request), request=request, remark=remark)
            elif action == "reopen-document":
                WorkModeRequestActions.reopen_document(obj, actor=_request_actor_employee(request), request=request, remark=remark)
            else:
                return Response({"error": "Unsupported action."}, status=400)
        except WorkModeRequestConsistencyError as exc:
            return Response({"error": str(exc)}, status=409)
        except ValidationError as exc:
            return Response({"error": exc.messages if hasattr(exc, "messages") else str(exc)}, status=400)
        return Response(self.serializer_class(obj, context={"request": request}).data, status=200)



class AttendanceOverTimeView(APIView):
    """
    Manages CRUD operations for attendance overtime records.

    Methods:
        get(request, pk=None): Retrieves a specific overtime record by `pk` or a list of records with filtering and pagination.
        post(request): Creates a new overtime record.
        put(request, pk): Updates an existing overtime record.
        delete(request, pk): Deletes an overtime record.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request, pk=None):
        if pk:
            attendance_ot = get_object_or_404(AttendanceOverTime, pk=pk)
            serializer = AttendanceOverTimeSerializer(attendance_ot)
            return Response(serializer.data, status=200)

        filterset_class = AttendanceOverTimeFilter(request.GET)
        queryset = filterset_class.qs
        self_account = queryset.filter(employee_id__employee_user_id=request.user)
        permission_based_queryset = filtersubordinates(
            request, queryset, "attendance.view_attendanceovertime"
        )
        queryset = permission_based_queryset | self_account
        field_name = request.GET.get("groupby_field", None)
        if field_name:
            # groupby workflow
            url = request.build_absolute_uri()
            return groupby_queryset(request, url, field_name, queryset)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(queryset, request)
        serializer = AttendanceOverTimeSerializer(page, many=True)
        return pagenation.get_paginated_response(serializer.data)

    @manager_permission_required("attendance.add_attendanceovertime")
    def post(self, request):
        serializer = AttendanceOverTimeSerializer(data=request.data)
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)
        return Response(serializer.errors, status=400)

    @manager_permission_required("attendance.change_attendanceovertime")
    def put(self, request, pk):
        attendance_ot = get_object_or_404(AttendanceOverTime, pk=pk)
        serializer = AttendanceOverTimeSerializer(
            instance=attendance_ot, data=request.data
        )
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)
        return Response(serializer.errors, status=400)

    @method_decorator(permission_required("attendance.delete_attendanceovertime"))
    def delete(self, request, pk):
        attendance = get_object_or_404(AttendanceOverTime, pk=pk)
        attendance.delete()

        return Response({"message": "Overtime deleted successfully"}, status=204)


class LateComeEarlyOutView(APIView):
    """
    Handles retrieval and deletion of late come and early out records.

    Methods:
        get(request, pk=None): Retrieves a list of late come and early out records with filtering.
        delete(request, pk=None): Deletes a specific late come or early out record by `pk`.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request, pk=None):
        data = LateComeEarlyOutFilter(request.GET)
        serializer = AttendanceLateComeEarlyOutSerializer(data.qs, many=True)
        return Response(serializer.data, status=200)

    def delete(self, request, pk=None):
        attendance = get_object_or_404(AttendanceLateComeEarlyOut, pk=pk)
        attendance.delete()
        return Response({"message": "Attendance deleted successfully"}, status=204)


class AttendanceActivityView(APIView):
    """Retrieve permission-scoped attendance activity records."""

    permission_classes = [IsAuthenticated]

    def get_queryset(self, request):
        queryset = AttendanceActivity.objects.select_related("employee_id").all()
        employee_options, _, _, _ = get_attendance_subject_employees(
            request,
            perm_codename="attendance.view_attendanceactivity",
            base_queryset=Employee.objects.all(),
        )
        employee_ids = list(employee_options.values_list("id", flat=True))
        if not employee_ids:
            return queryset.none()
        return queryset.filter(employee_id_id__in=employee_ids)

    def get(self, request, pk=None):
        queryset = self.get_queryset(request)
        if pk is not None:
            activity = get_object_or_404(queryset, pk=pk)
            serializer = AttendanceActivitySerializer(activity)
            return Response(serializer.data, status=200)

        queryset = AttendanceActivityFilter(request.GET, queryset=queryset).qs
        serializer = AttendanceActivitySerializer(queryset.order_by("-attendance_date", "-id"), many=True)
        return Response(serializer.data, status=200)




class EmployeeWfhHomeSetupAPIView(APIView):
    permission_classes = [IsAuthenticated]

    def post(self, request):
        employee = request.user.employee_get
        profile = _get_wfh_profile(employee)
        location = _parse_location_payload(request)
        if not location:
            return Response({"error": "Location is required."}, status=status.HTTP_400_BAD_REQUEST)
        try:
            lat = float(location.get("lat"))
            lng = float(location.get("lng"))
        except Exception:
            return Response({"error": "Invalid location payload."}, status=status.HTTP_400_BAD_REQUEST)
        old_lat = profile.home_latitude
        old_lng = profile.home_longitude
        old_radius = profile.home_radius_in_meters
        config = _get_company_geofencing(employee)
        profile.home_latitude = lat
        profile.home_longitude = lng
        profile.home_radius_in_meters = int(getattr(config, "wfh_radius_in_meters", 250) or 250)
        profile.is_home_configured = True
        profile.requires_home_reconfiguration = False
        profile.home_configured_at = dj_timezone.now()
        profile.home_configured_by = employee
        profile.save()
        action = EmployeeWfhProfileHistory.ActionType.HOME_RECONFIGURED if old_lat is not None and old_lng is not None else EmployeeWfhProfileHistory.ActionType.HOME_INITIAL_SET
        _log_wfh_history(
            employee=employee,
            action_type=action,
            acted_by=employee,
            old_lat=old_lat,
            old_lng=old_lng,
            old_radius=old_radius if old_lat is not None and old_lng is not None else None,
            new_lat=lat,
            new_lng=lng,
            new_radius=profile.home_radius_in_meters,
        )
        return Response({"detail": "WFH home location saved.", "wfh_profile": _serialize_wfh_profile(employee)}, status=status.HTTP_200_OK)


class AdminResetWfhHomeAPIView(APIView):
    permission_classes = [IsAuthenticated]

    def post(self, request):
        if not _has_wfh_home_reset_permission(request.user):
            return Response({"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN)
        employee_id = request.data.get("employee_id")
        if not employee_id:
            return Response({"error": "employee_id is required"}, status=status.HTTP_400_BAD_REQUEST)
        employee = get_object_or_404(Employee, pk=employee_id)
        profile = _get_wfh_profile(employee)
        _log_wfh_history(
            employee=employee,
            action_type=EmployeeWfhProfileHistory.ActionType.HOME_RESET,
            acted_by=getattr(request.user, "employee_get", None),
            old_lat=profile.home_latitude,
            old_lng=profile.home_longitude,
            old_radius=profile.home_radius_in_meters if profile.home_latitude is not None and profile.home_longitude is not None else None,
            notes="Admin reset WFH home geofence",
        )
        profile.requires_home_reconfiguration = True
        profile.last_home_reset_at = dj_timezone.now()
        profile.last_home_reset_by = getattr(request.user, "employee_get", None)
        profile.save(update_fields=["requires_home_reconfiguration", "last_home_reset_at", "last_home_reset_by"])
        return Response({"detail": "WFH home geofence reset.", "wfh_profile": _serialize_wfh_profile(employee)}, status=status.HTTP_200_OK)


class AdminResetWfhFaceAPIView(APIView):
    permission_classes = [IsAuthenticated]

    def post(self, request):
        if not _has_wfh_face_reset_permission(request.user):
            return Response({"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN)
        employee_id = request.data.get("employee_id")
        if not employee_id:
            return Response({"error": "employee_id is required"}, status=status.HTTP_400_BAD_REQUEST)
        employee = get_object_or_404(Employee, pk=employee_id)
        profile = _get_wfh_profile(employee)
        face = EmployeeFaceDetection.objects.filter(employee_id=employee).first()
        old_face = getattr(face.image, "url", None) if face and getattr(face, "image", None) else None
        _log_wfh_history(
            employee=employee,
            action_type=EmployeeWfhProfileHistory.ActionType.FACE_RESET,
            acted_by=getattr(request.user, "employee_get", None),
            old_face_image=old_face,
            notes="Admin reset WFH face detection",
        )
        profile.requires_face_reenrollment = True
        profile.last_face_reset_at = dj_timezone.now()
        profile.last_face_reset_by = getattr(request.user, "employee_get", None)
        profile.save(update_fields=["requires_face_reenrollment", "last_face_reset_at", "last_face_reset_by"])
        return Response({"detail": "WFH face detection reset.", "wfh_profile": _serialize_wfh_profile(employee)}, status=status.HTTP_200_OK)


class MobileAttendanceSettingsAPIView(APIView):
    permission_classes = [IsAuthenticated]

    def get(self, request):
        employee = request.user.employee_get
        company, company_id = _company_obj_and_id(employee)

        if company_id is None or (company is not None and not _is_model_instance(company)):
            face_detection = SimpleNamespace(start=True)
        else:
            face_detection = FaceDetection.objects.filter(company_id_id=company_id).first()
            if face_detection is None:
                face_detection = SimpleNamespace(start=True)
            elif not face_detection.start:
                face_detection.start = True
                face_detection.save(update_fields=["start"])

        geofencing_enabled = geofencing_is_effectively_enabled(company=company) if company_id is not None else False
        geo_config = _get_company_geofencing(employee)
        profile = _get_wfh_profile(employee)

        return Response(
            {
                "face_detection_enabled": bool(getattr(face_detection, "start", True)),
                "location_enabled": True,
                "location_capture_enabled": True,
                "geofencing_enabled": geofencing_enabled,
                "wfh_geofencing_enabled": bool(getattr(geo_config, "wfh_start", True)),
                "wfh_radius_in_meters": int(getattr(geo_config, "wfh_radius_in_meters", 250) or 250),
                "requires_home_reconfiguration": bool(getattr(profile, "requires_home_reconfiguration", False)),
                "requires_face_reenrollment": bool(getattr(profile, "requires_face_reenrollment", False)),
                "has_home_location_configured": bool(getattr(profile, "is_home_configured", False) and getattr(profile, "home_latitude", None) is not None and getattr(profile, "home_longitude", None) is not None),
                "read_only": True,
            },
            status=status.HTTP_200_OK,
        )

class TodayAttendance(APIView):
    """
    Provides the ratio of marked attendances to expected attendances for the current day.

    Method:
        get(request): Calculates and returns the attendance ratio for today.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):

        today = datetime.today()
        week_day = today.strftime("%A").lower()

        on_time = find_on_time(request, today=today, week_day=week_day)
        late_come = find_late_come(start_date=today)
        late_come_obj = len(late_come)

        marked_attendances = late_come_obj + on_time

        expected_attendances = find_expected_attendances(week_day=week_day)
        marked_attendances_ratio = 0
        if expected_attendances != 0:
            marked_attendances_ratio = (
                f"{(marked_attendances / expected_attendances) * 100:.2f}"
            )

        return Response(
            {"marked_attendances_ratio": marked_attendances_ratio}, status=200
        )


class OfflineEmployeesCountView(APIView):
    """
    Retrieves the count of active employees who have not clocked in today.

    Method:
        get(request): Returns the number of active employees who are not yet clocked in.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        is_manager = (
            EmployeeWorkInformation.objects.filter(
                reporting_manager_id=request.user.employee_get
            )
            .only("id")
            .exists()
        )

        if request.user.has_perm("employee.view_enployee") or is_manager:
            count = (
                EmployeeFilter({"not_in_yet": date.today()})
                .qs.exclude(employee_work_info__isnull=True)
                .filter(is_active=True)
                .count()
            )
            return Response({"count": count}, status=200)
        return Response(
            {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
        )


class OfflineEmployeesListView(APIView):
    """
    Lists active employees who have not clocked in today, including their leave status.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        user = request.user
        employee = getattr(user, "employee_get", None)
        today = date.today()

        # Manager access: get employees reporting to current user
        managed_employee_ids = EmployeeWorkInformation.objects.filter(
            reporting_manager_id=employee
        ).values_list("employee_id", flat=True)

        # Superusers or users with view permission see all employees
        if user.has_perm("employee.view_employee"):
            base_queryset = Employee.objects.all()
        elif managed_employee_ids.exists():
            base_queryset = Employee.objects.filter(id__in=managed_employee_ids)
        else:
            return Response(
                {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
            )

        # Apply filtering for offline employees
        filtered_qs = (
            EmployeeFilter({"not_in_yet": today}, queryset=base_queryset)
            .qs.exclude(employee_work_info__isnull=True)
            .filter(is_active=True)
            .select_related("employee_work_info")  # optimize joins
        )

        # Get leave status for the filtered employees
        leave_status = self.get_leave_status(filtered_qs)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(leave_status, request)
        return pagenation.get_paginated_response(page)

    def get_leave_status(self, queryset):

        today = date.today()
        queryset = queryset.distinct()
        # Annotate each employee with their leave status
        employees_with_leave_status = queryset.annotate(
            leave_status=Case(
                # Define different cases based on leave requests and attendance
                When(
                    leaverequest__start_date__lte=today,
                    leaverequest__end_date__gte=today,
                    leaverequest__status="approved",
                    then=Value("On Leave"),
                ),
                When(
                    leaverequest__start_date__lte=today,
                    leaverequest__end_date__gte=today,
                    leaverequest__status="requested",
                    then=Value("Waiting Approval"),
                ),
                When(
                    leaverequest__start_date__lte=today,
                    leaverequest__end_date__gte=today,
                    then=Value("Canceled / Rejected"),
                ),
                When(
                    employee_attendances__attendance_date=today, then=Value("Working")
                ),
                default=Value("Expected working"),  # Default status
                output_field=CharField(),
            ),
            job_position_id=F("employee_work_info__job_position_id"),
        ).values(
            "employee_first_name",
            "employee_last_name",
            "leave_status",
            "employee_profile",
            "id",
            "job_position_id",
        )

        for employee in employees_with_leave_status:

            if employee["employee_profile"]:
                employee["employee_profile"] = (
                    settings.MEDIA_URL + employee["employee_profile"]
                )
        return employees_with_leave_status



class CheckingStatus(APIView):
    """Mobile-friendly daily attendance status (single-session + hybrid mode)."""

    permission_classes = [IsAuthenticated]

    def get(self, request):
        employee = request.user.employee_get
        dt_now = _api_now(request)
        server_now_iso = dt_now.isoformat()
        server_time_hhmm = dt_now.strftime("%H:%M")

        # If client provides a target date (e.g., Attendance Correction form), compute shift rules for that date
        # while keeping server_now/server_time based on real current time.
        target_date_str = (request.GET.get('attendance_date') or request.GET.get('date') or '').strip()
        if target_date_str:
            try:
                from datetime import datetime as _dt
                # Use 12:01 to avoid night-shift noon-to-noon adjustment for historical/future dates
                d = _dt.strptime(target_date_str, '%Y-%m-%d').date()
                dt_now = dt_now.replace(year=d.year, month=d.month, day=d.day, hour=12, minute=1, second=0, microsecond=0)
            except Exception:
                pass

        access = evaluate_attendance_access(employee=employee, user=getattr(request, "user", None))
        if not access.allowed:
            attendance_date = dt_now.date()
            payload = {
                "status": True,
                "attendance_enabled": False,
                "attendance_exempt_reason": access.reason_code,
                "attendance_disabled_reason": access.reason_code,
                "attendance_disabled_message": access.message,
                "blocked_roles": list(access.blocked_roles),
                "role_flags": {
                    "is_reporting_manager": access.is_reporting_manager,
                    "is_admin": access.is_admin,
                },
                "attendance_role_settings": {
                    "allow_reporting_manager_attendance": access.allow_reporting_manager_attendance,
                    "allow_admin_attendance": access.allow_admin_attendance,
                },
                "message": access.message,
                "has_attendance": False,
                "attendance_date": attendance_date.strftime("%Y-%m-%d"),
                "first_check_in": None,
                "last_check_out": None,
                "late_by": None,
                "planned_check_out": None,
                "work_hours_below_minimum": False,
                "work_hours_shortfall": None,
                "checked_out_early": False,
                "checked_out_early_by": None,
                "worked_hours": "00:00",
                "worked_seconds": 0,
                "is_working": False,
                "missing_check_in": False,
                "check_in_cutoff_has_passed": False,
                "check_out_cutoff_has_passed": False,
                "can_clock_in": False,
                "can_clock_out": False,
                "can_update_clock_out": False,
                "can_check_in": False,
                "can_check_out": False,
                "check_in_window_start": None,
                "check_in_window_end": None,
                "check_out_window_start": None,
                "check_out_window_end": None,
                "check_in_block_reason": "ATTENDANCE_DISABLED",
                "check_out_block_reason": "ATTENDANCE_DISABLED",
                "in_mode": AttendanceWorkMode.WFO,
                "out_mode": AttendanceWorkMode.WFO,
                "in_work_type": AttendanceWorkMode.WFO,
                "out_work_type": AttendanceWorkMode.WFO,
                "in_work_type_source": "schedule",
                "out_work_type_source": "schedule",
                "in_work_type_request_id": None,
                "out_work_type_request_id": None,
                "wfh_profile": _serialize_wfh_profile(employee),
                "in_work_type_request_status": None,
                "out_work_type_request_status": None,
                "in_request_status": None,
                "out_request_status": None,
                "in_request_scope": None,
                "out_request_scope": None,
                "in_work_mode_request_id": None,
                "out_work_mode_request_id": None,
                "in_attendance_status": None,
                "out_attendance_status": None,
                "in_attendance_reject_reason_code": None,
                "out_attendance_reject_reason_code": None,
                "in_related_work_type_request_id": None,
                "out_related_work_type_request_id": None,
                "shift_start": None,
                "shift_end": None,
                "grace_time": 0,
                "clock_in_type": "after",
                "minimum_working_hour": None,
                "check_in_cutoff_time": None,
                "check_out_cutoff_time": None,
                "requires_photo_in": False,
                "requires_location_in": False,
                "requires_photo_out": False,
                "requires_location_out": False,
                "is_presensi_only": False,
                "server_now": server_now_iso,
                "server_time": server_time_hhmm,
            }
            payload.update(build_mobile_header_state(payload))
            return Response(payload, status=status.HTTP_200_OK)

        # Resolve shift
        shift = None
        try:
            shift = employee.employee_work_info.shift_id
        except Exception:
            shift = None

        # If shift missing, return minimal safe response (no mobile punch)
        # Keep response shape stable for mobile UI (include work type & audit fields).
        if not shift:
            attendance_date = dt_now.date()

            try:
                in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
                out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")
                display_in_mode, display_in_source, _display_in_req = _resolve_committed_work_type(employee, attendance_date, "in")
                display_out_mode, display_out_source, _display_out_req = _resolve_committed_work_type(employee, attendance_date, "out")
            except Exception:
                in_mode, in_source, in_req = (AttendanceWorkMode.WFO, "schedule", None)
                out_mode, out_source, out_req = (AttendanceWorkMode.WFO, "schedule", None)
                display_in_mode, display_in_source = (AttendanceWorkMode.WFO, "schedule")
                display_out_mode, display_out_source = (AttendanceWorkMode.WFO, "schedule")

            payload = {
                "status": False,
                "attendance_enabled": True,
                "attendance_exempt_reason": None,
                "attendance_disabled_reason": None,
                "attendance_disabled_message": None,
                "blocked_roles": [],
                "role_flags": {
                    "is_reporting_manager": access.is_reporting_manager,
                    "is_admin": access.is_admin,
                },
                "attendance_role_settings": {
                    "allow_reporting_manager_attendance": access.allow_reporting_manager_attendance,
                    "allow_admin_attendance": access.allow_admin_attendance,
                },
                "has_attendance": False,
                "attendance_date": attendance_date.strftime("%Y-%m-%d"),
                "first_check_in": None,
                "last_check_out": None,
                "late_by": None,
                "planned_check_out": None,
                "work_hours_below_minimum": False,
                "work_hours_shortfall": None,
                "checked_out_early": False,
                "checked_out_early_by": None,
                "worked_hours": "00:00",
                "worked_seconds": 0,
                "is_working": False,
                "missing_check_in": False,
                "check_in_cutoff_has_passed": False,
                "check_out_cutoff_has_passed": False,
                "can_clock_in": False,
                "can_clock_out": False,
                "can_update_clock_out": False,
                "can_check_in": False,
                "can_check_out": False,
                "check_in_window_start": None,
                "check_in_window_end": None,
                "check_out_window_start": None,
                "check_out_window_end": None,
                "check_in_block_reason": "SHIFT_NOT_ASSIGNED",
                "check_out_block_reason": "SHIFT_NOT_ASSIGNED",
                "in_mode": display_in_mode,
                "out_mode": display_out_mode,
                "in_work_type": display_in_mode,
                "out_work_type": display_out_mode,
                "in_work_type_source": display_in_source,
                "out_work_type_source": display_out_source,
                "in_requested_work_type": getattr(in_req, "mode", None),
                "out_requested_work_type": getattr(out_req, "mode", None),
                "in_work_type_request_id": getattr(in_req, "id", None),
                "out_work_type_request_id": getattr(out_req, "id", None),
                "in_work_type_request_status": getattr(in_req, "status", None),
                "out_work_type_request_status": getattr(out_req, "status", None),
                "in_request_status": getattr(in_req, "status", None),
                "out_request_status": getattr(out_req, "status", None),
                "in_request_scope": getattr(in_req, "scope", None),
                "out_request_scope": getattr(out_req, "scope", None),
                "in_work_mode_request_id": getattr(in_req, "id", None),
                "out_work_mode_request_id": getattr(out_req, "id", None),
                "in_attendance_status": None,
                "out_attendance_status": None,
                "in_attendance_reject_reason_code": None,
                "out_attendance_reject_reason_code": None,
                "in_related_work_type_request_id": None,
                "out_related_work_type_request_id": None,
                "shift_start": None,
                "shift_end": None,
                "grace_time": 0,
                "clock_in_type": "after",
                "minimum_working_hour": None,
                "check_in_cutoff_time": None,
                "check_out_cutoff_time": None,
                "requires_photo_in": False,
                "requires_location_in": False,
                "requires_photo_out": False,
                "requires_location_out": False,
                "is_presensi_only": False,
                "server_now": server_now_iso,
                "server_time": server_time_hhmm,
            }
            payload.update(build_mobile_header_state(payload))
            return Response(payload, status=status.HTTP_200_OK)

        # Resolve attendance_date + day (night shift aware)
        (
            attendance_date,
            day,
            min_hour,
            start_time_sec,
            end_time_sec,
            now_hhmm,
            now_sec,
        ) = _api_resolve_attendance_date_and_day(shift, dt_now)

        # Schedule & cutoffs



        rules = {}


        try:


            rules = cio.get_shift_rules(


                attendance_date,


                shift,


                day,


                start_time_sec=start_time_sec,


                end_time_sec=end_time_sec,


            )


        except Exception:


            rules = {


                "schedule": None,


                "grace_seconds": 0,


                "cutoff_in_dt": None,


                "cutoff_out_dt": None,


            }



        schedule = rules.get("schedule")


        grace_seconds = int(rules.get("grace_seconds") or 0)
        clock_in_type = str(rules.get("clock_in_type") or "after")
        try:
            resolved_grace = cio._resolve_grace_time(schedule, shift)
            if resolved_grace and (getattr(resolved_grace, "allowed_clock_in", True) or grace_seconds > 0):
                clock_in_type = getattr(resolved_grace, "clock_in_type", "after") or "after"
        except Exception:
            clock_in_type = str(rules.get("clock_in_type") or "after")


        cutoff_in_dt = rules.get("cutoff_in_dt")
        cutoff_out_dt = rules.get("cutoff_out_dt")

        # Windows (FINAL spec)
        shift_start_dt = rules.get("shift_start_dt")
        shift_end_dt = rules.get("shift_end_dt")
        check_in_window_start_dt = rules.get("check_in_window_start_dt")
        check_in_window_end_dt = rules.get("check_in_window_end_dt")
        check_out_window_start_dt = rules.get("check_out_window_start_dt")
        check_out_window_end_dt = rules.get("check_out_window_end_dt")

        cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now) if cutoff_in_dt else None
        cutoff_out_dt = _coerce_datetime_like(cutoff_out_dt, dt_now) if cutoff_out_dt else None
        shift_start_dt = _coerce_datetime_like(shift_start_dt, dt_now) if shift_start_dt else None
        shift_end_dt = _coerce_datetime_like(shift_end_dt, dt_now) if shift_end_dt else None
        check_in_window_start_dt = _coerce_datetime_like(check_in_window_start_dt, dt_now) if check_in_window_start_dt else None
        check_in_window_end_dt = _coerce_datetime_like(check_in_window_end_dt, dt_now) if check_in_window_end_dt else None
        check_out_window_start_dt = _coerce_datetime_like(check_out_window_start_dt, dt_now) if check_out_window_start_dt else None
        check_out_window_end_dt = _coerce_datetime_like(check_out_window_end_dt, dt_now) if check_out_window_end_dt else None

        # Ensure window fields are ALWAYS present (even if shift rule helper
        # couldn't compute them). This keeps the mobile UI free from hardcoded
        # window math and supports fresh installs.
        DEFAULT_EARLY_CHECKIN_MIN = 120
        DEFAULT_LATE_CHECKIN_MIN = 120
        DEFAULT_EARLY_CHECKOUT_GRACE_MIN = 0
        DEFAULT_MAX_LATE_CHECKOUT_HOURS = 12

        try:
            if (check_in_window_start_dt is None) and shift_start_dt:
                check_in_window_start_dt = shift_start_dt - timedelta(minutes=DEFAULT_EARLY_CHECKIN_MIN)
            if (check_in_window_end_dt is None) and shift_start_dt:
                check_in_window_end_dt = cutoff_in_dt or (shift_start_dt + timedelta(minutes=DEFAULT_LATE_CHECKIN_MIN))

            if (check_out_window_start_dt is None) and shift_end_dt:
                check_out_window_start_dt = shift_end_dt - timedelta(minutes=DEFAULT_EARLY_CHECKOUT_GRACE_MIN)
            if (check_out_window_end_dt is None) and shift_end_dt:
                check_out_window_end_dt = cutoff_out_dt or (shift_end_dt + timedelta(hours=DEFAULT_MAX_LATE_CHECKOUT_HOURS))
        except Exception:
            pass

        # Legacy cutoff flags (kept for backwards compatibility)
        check_in_cutoff_has_passed = bool(cutoff_in_dt and dt_now > cutoff_in_dt)
        check_out_cutoff_has_passed = bool(cutoff_out_dt and dt_now > cutoff_out_dt)

        # Auto reject WFA waiting requests after cutoff (FINAL spec)
        try:
            auto_reject_wfa_waiting_for_date(
                employee=employee,
                target_date=attendance_date,
                now_dt=dt_now,
                cutoff_in_dt=cutoff_in_dt,
                cutoff_out_dt=cutoff_out_dt,
            )
        except Exception:
            pass

        # Resolve punch-gating work type (pending requests can still block punch).
        in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")

        # Resolve committed/display work type separately so pending requests do not
        # change the visible IN/OUT mode before approval.
        display_in_mode, display_in_source, _display_in_req = _resolve_committed_work_type(employee, attendance_date, "in")
        display_out_mode, display_out_source, _display_out_req = _resolve_committed_work_type(employee, attendance_date, "out")

        # Attendance row
        attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        clock_in_t = getattr(attendance, "attendance_clock_in", None) if attendance else None
        clock_out_t = getattr(attendance, "attendance_clock_out", None) if attendance else None
        leave_kind_for_note = None
        if leave_breakdown_for_attendance_date is not None:
            try:
                leave_kind_for_note = leave_breakdown_for_attendance_date(employee, attendance_date) or None
            except Exception:
                leave_kind_for_note = None
        policy_for_note = build_attendance_policy(
            schedule=schedule,
            shift_start_dt=shift_start_dt,
            shift_end_dt=shift_end_dt,
            minimum_hour=min_hour,
            leave_kind=leave_kind_for_note,
            check_in_cutoff_dt=check_in_window_end_dt,
        )
        grace_out_sec = 0
        try:
            resolved_grace = cio._resolve_grace_time(schedule, shift)
            if resolved_grace and getattr(resolved_grace, "allowed_clock_out", False):
                grace_out_sec = int(getattr(resolved_grace, "allowed_time_in_secs", 0) or 0)
        except Exception:
            grace_out_sec = 0

        status_actual_in_dt = None
        if attendance and clock_in_t:
            actual_in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
            status_actual_in_dt = _coerce_datetime_like(datetime.combine(actual_in_date, clock_in_t), dt_now)

        if leave_kind_for_note in {"first_half", "second_half"}:
            try:
                _status_policy_end_dt, half_day_checkin_window_end_dt, half_day_checkout_start_dt = resolve_policy_windows(
                    policy_for_note,
                    actual_check_in_dt=status_actual_in_dt,
                    clock_in_type=clock_in_type,
                    flex_seconds=grace_seconds,
                )
                check_in_window_end_dt = half_day_checkin_window_end_dt or check_in_window_end_dt
                check_out_window_start_dt = half_day_checkout_start_dt or check_out_window_start_dt
            except Exception:
                pass

        # If this attendance is presence-only (for example, final verified On Duty),
        # force worked hours to 00:00.
        is_presensi_only = bool(attendance and getattr(attendance, "is_presensi_only", False))

        out_punch_status = getattr(attendance, "out_attendance_status", None) if attendance else None
        out_rejected = bool(out_punch_status == "REJECTED")

        # Worked hours calculation
        worked_seconds = 0
        is_working = False
        in_dt = None
        if attendance and not is_presensi_only:
            if clock_in_t:
                in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
                in_dt = _coerce_datetime_like(datetime.combine(in_date, clock_in_t), dt_now)

                # FINAL spec: if checked-in earlier than shift_start, start counting at shift_start.
                # If OUT punch exists but was REJECTED, treat as not checked-out yet.
                has_valid_out = bool(clock_out_t and not out_rejected)

                if not has_valid_out:
                    is_working = True
                    try:
                        worked_seconds = compute_attendance_metrics(
                            policy_for_note,
                            final_in_dt=in_dt,
                            final_out_dt=dt_now,
                            grace_seconds=grace_seconds,
                            clock_in_type=clock_in_type,
                            is_presence_only=False,
                        ).worked_seconds
                    except Exception:
                        worked_seconds = 0
                else:
                    out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date
                    out_dt = _truncate_dt_to_minute(_coerce_datetime_like(datetime.combine(out_date, clock_out_t), dt_now))
                    try:
                        worked_seconds = compute_attendance_metrics(
                            policy_for_note,
                            final_in_dt=in_dt,
                            final_out_dt=out_dt,
                            grace_seconds=grace_seconds,
                            clock_in_type=clock_in_type,
                            is_presence_only=False,
                        ).worked_seconds
                    except Exception:
                        worked_seconds = 0
            elif clock_out_t:
                # missing check-in computation uses AttendanceActivity placeholder if available
                activity = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
                if activity and getattr(activity, "clock_in_date", None) and getattr(activity, "clock_in", None) and getattr(activity, "clock_out_date", None) and getattr(activity, "clock_out", None):
                    in_dt = _coerce_datetime_like(datetime.combine(activity.clock_in_date, activity.clock_in), dt_now)
                    out_dt = _coerce_datetime_like(datetime.combine(activity.clock_out_date, activity.clock_out), dt_now)
                    try:
                        worked_seconds = compute_attendance_metrics(
                            policy_for_note,
                            final_in_dt=in_dt,
                            final_out_dt=out_dt,
                            grace_seconds=grace_seconds,
                            clock_in_type=clock_in_type,
                            is_presence_only=False,
                        ).worked_seconds
                    except Exception:
                        worked_seconds = 0
                else:
                    worked_seconds = 0

        worked_minutes = max(0, int(worked_seconds // 60))
        worked_hours = f"{worked_minutes//60:02d}:{worked_minutes%60:02d}"

        metrics_for_note = None
        note_in_dt = None
        note_out_dt = None
        if attendance and not is_presensi_only:
            try:
                note_in_dt = in_dt
                if note_in_dt is None and clock_in_t:
                    in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
                    note_in_dt = _coerce_datetime_like(datetime.combine(in_date, clock_in_t), dt_now)
                if clock_out_t and not out_rejected:
                    out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date
                    note_out_dt = _coerce_datetime_like(datetime.combine(out_date, clock_out_t), dt_now)
                metrics_for_note = compute_attendance_metrics(
                    policy_for_note,
                    final_in_dt=note_in_dt,
                    final_out_dt=note_out_dt,
                    grace_seconds=grace_seconds,
                    clock_in_type=clock_in_type,
                    is_presence_only=False,
                    early_out_grace_seconds=grace_out_sec,
                )
            except Exception:
                metrics_for_note = None

        # Action permissions
        in_allowed = _is_punch_allowed(in_mode, in_req, in_source)
        out_allowed = _is_punch_allowed(out_mode, out_req, out_source)

        requires_photo_in = _requires_proof(in_mode)
        requires_location_in = _requires_proof(in_mode)
        requires_photo_out = _requires_proof(out_mode)
        requires_location_out = _requires_proof(out_mode)

        # Window selection (FINAL spec)
        in_window_start = check_in_window_start_dt
        in_window_end = check_in_window_end_dt

        # Window end is fixed at cutoff_out when available (per spec); fallback to helper-computed end.
        out_window_end = cutoff_out_dt or check_out_window_end_dt

        earliest_check_out_dt = None
        effective_start_dt = None
        valid_check_in_for_note = True

        if out_mode == AttendanceWorkMode.ON_DUTY:
            # ON_DUTY uses the same checkout window boundaries as normal attendance.
            out_window_start = check_out_window_start_dt
            try:
                effective_start_dt, earliest_check_out_dt, valid_check_in_for_note = _compute_mobile_effective_start_and_earliest_checkout(
                    shift_start_dt=shift_start_dt,
                    shift_end_dt=shift_end_dt,
                    actual_check_in_dt=in_dt,
                    clock_in_type=clock_in_type,
                    flex_seconds=grace_seconds,
                    schedule=schedule,
                    minimum_hour=min_hour,
                    leave_kind=leave_kind_for_note,
                    check_in_cutoff_dt=check_in_window_end_dt,
                )
            except Exception:
                effective_start_dt, earliest_check_out_dt, valid_check_in_for_note = None, None, True
        else:
            out_window_start = check_out_window_start_dt
            try:
                effective_start_dt, earliest_check_out_dt, valid_check_in_for_note = _compute_mobile_effective_start_and_earliest_checkout(
                    shift_start_dt=shift_start_dt,
                    shift_end_dt=shift_end_dt,
                    actual_check_in_dt=in_dt,
                    clock_in_type=clock_in_type,
                    flex_seconds=grace_seconds,
                    schedule=schedule,
                    minimum_hour=min_hour,
                    leave_kind=leave_kind_for_note,
                    check_in_cutoff_dt=check_in_window_end_dt,
                )
            except Exception:
                effective_start_dt, earliest_check_out_dt, valid_check_in_for_note = None, None, True

        # Missing/invalid check-in flag for UI messaging.
        # Compute this only after valid_check_in_for_note has been resolved above,
        # otherwise the status endpoint can crash when an existing IN punch is present.
        invalid_check_in = bool(clock_in_t and not valid_check_in_for_note)
        # Existing IN punches must never be surfaced as "missing check in" in mobile
        # note/status payloads. Treat true absence of IN separately from an invalid/out-of-window
        # punch so status remains consistent with canonical attendance/recap surfaces.
        missing_check_in = (
            (not clock_in_t)
            and (
                bool(clock_out_t)
                or (bool(check_in_cutoff_has_passed) and not bool(check_out_cutoff_has_passed))
            )
        )

        def _in_window_ok(start_dt, end_dt) -> bool:
            if start_dt and dt_now < start_dt:
                return False
            if end_dt and dt_now > end_dt:
                return False
            return True

        in_window_ok = _in_window_ok(in_window_start, in_window_end)
        out_window_ok = _in_window_ok(out_window_start, out_window_end)

        # Block reasons for mobile UI (FINAL spec)
        check_in_block_reason = None
        check_out_block_reason = None

        if clock_in_t or clock_out_t:
            check_in_block_reason = "ALREADY_PUNCHED"
        elif not in_allowed:
            check_in_block_reason = "MODE_NOT_ALLOWED"
        elif in_window_start and dt_now < in_window_start:
            check_in_block_reason = "BEFORE_WINDOW_START"
        elif in_window_end and dt_now > in_window_end:
            check_in_block_reason = "AFTER_WINDOW_END"

        # Can check-in? (FINAL spec)
        can_clock_in = (
            (not bool(clock_in_t))
            and (not bool(clock_out_t))
            and in_allowed
            and in_window_ok
        )

        # Can update checkout?
        can_update_clock_out = (
            bool(clock_out_t)
            and out_allowed
            and out_window_ok
            and ((out_mode in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH, AttendanceWorkMode.ON_DUTY}) or out_rejected)
        )

        # Can check-out? (FINAL spec)
        can_clock_out = False
        if not out_allowed:
            check_out_block_reason = "MODE_NOT_ALLOWED"
        elif out_window_start and dt_now < out_window_start:
            check_out_block_reason = "BEFORE_WINDOW_START"
        elif out_window_end and dt_now > out_window_end:
            check_out_block_reason = "AFTER_WINDOW_END"
        else:
            # within window
            if clock_out_t:
                can_clock_out = can_update_clock_out
                if not can_clock_out:
                    check_out_block_reason = "ALREADY_CHECKED_OUT"
            else:
                # allow clock-out even when check-in is missing (single-session placeholder)
                can_clock_out = True

        # Suggested action (for mobile)
        suggested_action = None
        if can_clock_out:
            suggested_action = "clock_out"
        elif can_clock_in:
            suggested_action = "clock_in"

        # Shift context
        def _sec_to_hhmm(sec_val):
            try:
                s = int(sec_val)
            except Exception:
                return None
            if s < 0:
                return None
            h = (s // 3600) % 24
            m = (s % 3600) // 60
            return f"{h:02d}:{m:02d}"

        # Derived helpers for mobile UI (optional; safe defaults when absent)
        planned_check_out_hhmm = None
        if earliest_check_out_dt:
            try:
                planned_check_out_hhmm = earliest_check_out_dt.strftime("%H:%M")
            except Exception:
                planned_check_out_hhmm = None
        if planned_check_out_hhmm is None:
            planned_check_out_hhmm = _sec_to_hhmm(end_time_sec)
        late_by_hhmm = None
        work_hours_below_minimum = False
        work_hours_shortfall_hhmm = None
        checked_out_early = False
        checked_out_early_by_hhmm = None

        if attendance and not is_presensi_only:
            try:
                is_night_shift = start_time_sec > end_time_sec and start_time_sec != end_time_sec
            except Exception:
                is_night_shift = False

            if metrics_for_note is not None and clock_in_t:
                try:
                    late_s = int(getattr(metrics_for_note, "late_seconds", 0) or 0)
                    if late_s > 0:
                        late_by_hhmm = _seconds_to_minute_display(late_s)
                except Exception:
                    late_by_hhmm = None

            # Below-minimum and shortfall are only meaningful after clock-out
            min_hhmm = _format_minimum_hour(min_hour)
            if clock_in_t and clock_out_t and min_hhmm:
                try:
                    min_s = strtime_seconds(min_hhmm)
                    if min_s and int(worked_seconds) < int(min_s):
                        work_hours_below_minimum = True
                        short_s = int(min_s) - int(worked_seconds)
                        work_hours_shortfall_hhmm = _seconds_to_minute_display(short_s)
                except Exception:
                    pass

            if metrics_for_note is not None and clock_out_t and not out_rejected:
                try:
                    early_s = int(getattr(metrics_for_note, "early_out_seconds", 0) or 0)
                    if early_s > 0:
                        checked_out_early = True
                        checked_out_early_by_hhmm = _seconds_to_minute_display(early_s)
                except Exception:
                    checked_out_early = False
                    checked_out_early_by_hhmm = None

        late_by_hhmm, checked_out_early, checked_out_early_by_hhmm = _neutralize_on_duty_session_metrics(
            in_mode=in_mode,
            in_req=in_req,
            in_punch_dt=clock_in_t,
            out_mode=out_mode,
            out_req=out_req,
            out_punch_dt=clock_out_t,
            late_by_hhmm=late_by_hhmm,
            checked_out_early=checked_out_early,
            checked_out_early_by_hhmm=checked_out_early_by_hhmm,
        )

        note_context = _build_mobile_header_note_context(
            employee=employee,
            shift=shift,
            attendance_date=attendance_date,
            day=day,
            start_time_sec=start_time_sec,
            end_time_sec=end_time_sec,
        )
        note_effective_seconds = note_context.get("header_note_effective_duration_seconds")
        note_work_hours_below_minimum = False
        note_work_hours_shortfall_hhmm = None
        if clock_in_t and clock_out_t and note_effective_seconds is not None and int(note_effective_seconds) > 0:
            try:
                if int(worked_seconds) < int(note_effective_seconds):
                    note_work_hours_below_minimum = True
                    short_s = int(note_effective_seconds) - int(worked_seconds)
                    note_work_hours_shortfall_hhmm = _seconds_to_minute_display(short_s)
            except Exception:
                note_work_hours_below_minimum = False

        payload = {
            "status": (False if is_presensi_only else bool(is_working)),
            "attendance_enabled": True,
            "attendance_exempt_reason": None,
            "attendance_disabled_reason": None,
            "attendance_disabled_message": None,
            "blocked_roles": [],
            "role_flags": {
                "is_reporting_manager": access.is_reporting_manager,
                "is_admin": access.is_admin,
            },
            "attendance_role_settings": {
                "allow_reporting_manager_attendance": access.allow_reporting_manager_attendance,
                "allow_admin_attendance": access.allow_admin_attendance,
            },
            "has_attendance": bool(attendance),
            "attendance_date": attendance_date.strftime("%Y-%m-%d"),

            "clock_in_time": clock_in_t.strftime("%H:%M") if clock_in_t else None,
            "clock_out_time": clock_out_t.strftime("%H:%M") if clock_out_t else None,
            "clock_in": clock_in_t.strftime("%I:%M %p") if clock_in_t else None,
            "clock_out": clock_out_t.strftime("%I:%M %p") if clock_out_t else None,

            "first_check_in": clock_in_t.strftime("%I:%M %p") if clock_in_t else None,
            "last_check_out": clock_out_t.strftime("%I:%M %p") if clock_out_t else None,

            "worked_hours": "00:00" if is_presensi_only else worked_hours,
            "worked_seconds": 0 if is_presensi_only else int(worked_seconds),
            "is_working": False if is_presensi_only else bool(is_working),

            "shift_start": _sec_to_hhmm(start_time_sec),
            "shift_end": _sec_to_hhmm(end_time_sec),
            "grace_time": int(grace_seconds),
            "clock_in_type": clock_in_type,
            "minimum_working_hour": _format_minimum_hour(min_hour),

            "check_in_cutoff_time": cutoff_in_dt.strftime("%H:%M") if cutoff_in_dt else None,
            "check_out_cutoff_time": cutoff_out_dt.strftime("%H:%M") if cutoff_out_dt else None,
            "check_in_cutoff_has_passed": bool(check_in_cutoff_has_passed),
            "check_out_cutoff_has_passed": bool(check_out_cutoff_has_passed),

            "missing_check_in": bool(missing_check_in),
            "invalid_check_in": bool(invalid_check_in),

            # Option B (per punch audit status)
            "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
            "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
            "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
            "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
            "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
            "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,

            # Work-mode
            "in_mode": display_in_mode,
            "out_mode": display_out_mode,
            "in_work_type": display_in_mode,
            "out_work_type": display_out_mode,
            "in_work_type_source": display_in_source,
            "out_work_type_source": display_out_source,
            "in_requested_work_type": getattr(in_req, 'mode', None),
            "out_requested_work_type": getattr(out_req, 'mode', None),
            "in_work_type_request_id": getattr(in_req, 'id', None),
            "out_work_type_request_id": getattr(out_req, 'id', None),
            "in_work_type_request_status": getattr(in_req, 'status', None),
            "out_work_type_request_status": getattr(out_req, 'status', None),
            "in_request_status": getattr(in_req, "status", None),
            "out_request_status": getattr(out_req, "status", None),
            "in_request_scope": getattr(in_req, "scope", None),
            "out_request_scope": getattr(out_req, "scope", None),
            "in_work_mode_request_id": getattr(in_req, "id", None),
            "out_work_mode_request_id": getattr(out_req, "id", None),

            # Gating flags
            "can_clock_in": bool(can_clock_in),
            "can_clock_out": bool(can_clock_out),
            "can_update_clock_out": bool(can_update_clock_out),
            # New (FINAL spec) keys
            "can_check_in": bool(can_clock_in),
            "can_check_out": bool(can_clock_out),
            "check_in_window_start": in_window_start.strftime("%H:%M") if in_window_start else None,
            "check_in_window_end": in_window_end.strftime("%H:%M") if in_window_end else None,
            "check_out_window_start": out_window_start.strftime("%H:%M") if out_window_start else None,
            "earliest_check_out": earliest_check_out_dt.strftime("%H:%M") if earliest_check_out_dt else None,
            "check_out_window_end": out_window_end.strftime("%H:%M") if out_window_end else None,
            "check_in_block_reason": check_in_block_reason,
            "check_out_block_reason": check_out_block_reason,
            "suggested_action": suggested_action,
            "update_check_out": bool(can_update_clock_out),  # legacy key for existing mobile UI

            # Proof requirements (mobile uses this to show camera/GPS)
            "requires_photo_in": bool(requires_photo_in),
            "requires_location_in": bool(requires_location_in),
            "requires_photo_out": bool(requires_photo_out),
            "requires_location_out": bool(requires_location_out),

            # Presence-only
            "is_presensi_only": bool(is_presensi_only),

            "server_now": server_now_iso,
            "server_time": server_time_hhmm,
        }

        # Optional helper fields used by mobile UI for status notes.
        # Keep these stable for backward compatibility.
        payload.update(
            {
                "late_check_in": bool(late_by_hhmm),
                "late_by": late_by_hhmm,
                "planned_check_out": planned_check_out_hhmm,
                "work_hours_below_minimum": bool(work_hours_below_minimum),
                "work_hours_shortfall": work_hours_shortfall_hhmm,
                "checked_out_early": bool(checked_out_early),
                "checked_out_early_by": checked_out_early_by_hhmm,
                "header_note_work_hours_below_minimum": bool(note_work_hours_below_minimum),
                "header_note_work_hours_shortfall": note_work_hours_shortfall_hhmm,
            }
        )
        payload.update(note_context)

        # Attach proof URLs & locations (audit)
        if attendance:
            try:
                if getattr(attendance, "attendance_clock_in_image", None):
                    payload["clock_in_image"] = attendance.attendance_clock_in_image.url
            except Exception:
                pass
            try:
                if getattr(attendance, "attendance_clock_out_image", None):
                    payload["clock_out_image"] = attendance.attendance_clock_out_image.url
            except Exception:
                pass
            # Location fields may be JSON
            try:
                payload["clock_in_location"] = getattr(attendance, "attendance_clock_in_location", None)
            except Exception:
                pass
            try:
                payload["clock_out_location"] = getattr(attendance, "attendance_clock_out_location", None)
            except Exception:
                pass
        payload.update(build_mobile_header_state(payload))
        return Response(payload, status=status.HTTP_200_OK)

class MailTemplateView(APIView):
    """
    Retrieves a list of recruitment mail templates.

    Method:
        get(request): Returns all recruitment mail templates.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        instances = HorillaMailTemplate.objects.all()
        serializer = MailTemplateSerializer(instances, many=True)
        return Response(serializer.data, status=200)

class ConvertedMailTemplateConvert(APIView):
    """
    Renders a recruitment mail template with data from a specified employee.

    Method:
        put(request): Renders the mail template body with employee and user data and returns the result.
    """

    permission_classes = [IsAuthenticated]

    def put(self, request):
        template_id = request.data.get("template_id", None)
        employee_id = request.data.get("employee_id", None)
        employee = Employee.objects.filter(id=employee_id).first()
        bdy = HorillaMailTemplate.objects.filter(id=template_id).first()
        template_bdy = template.Template(bdy.body)
        context = template.Context(
            {"instance": employee, "self": request.user.employee_get}
        )
        render_bdy = template_bdy.render(context)
        return Response(render_bdy)
class OfflineEmployeeMailsend(APIView):
    """
    Sends an email with attachments and rendered templates to a specified employee.

    Method:
        post(request): Renders email templates with employee and user data, attaches files, and sends the email.
    """

    permission_classes = [IsAuthenticated]

    def post(self, request):
        employee_id = request.POST.get("employee_id")
        subject = request.POST.get("subject", "")
        bdy = request.POST.get("body", "")
        other_attachments = request.FILES.getlist("other_attachments")
        attachments = [
            (file.name, file.read(), file.content_type) for file in other_attachments
        ]
        email_backend = ConfiguredEmailBackend()
        host = email_backend.dynamic_username
        employee = Employee.objects.get(id=employee_id)
        template_attachment_ids = request.POST.getlist("template_attachments")
        bodys = list(
            HorillaMailTemplate.objects.filter(
                id__in=template_attachment_ids
            ).values_list("body", flat=True)
        )
        for html in bodys:
            # Due to not having a solid template we first need to pass the context
            template_bdy = template.Template(html)
            context = template.Context(
                {"instance": employee, "self": request.user.employee_get}
            )
            render_bdy = template_bdy.render(context)
            attachments.append(
                (
                    "Document",
                    generate_pdf(render_bdy, {}, path=False, title="Document").content,
                    "application/pdf",
                )
            )

        template_bdy = template.Template(bdy)
        context = template.Context(
            {"instance": employee, "self": request.user.employee_get}
        )
        render_bdy = template_bdy.render(context)

        email = EmailMessage(
            subject,
            render_bdy,
            host,
            [employee.employee_work_info.email],
        )
        email.content_subtype = "html"

        email.attachments = attachments
        try:
            email.send()
            if employee.employee_work_info.email:
                return Response(f"Mail sent to {employee.get_full_name()}")
            else:
                return Response(f"Email not set for {employee.get_full_name()}")
        except Exception as e:
            return Response("Something went wrong")


class UserAttendanceView(APIView):
    permission_classes = [IsAuthenticated]
    serializer_class = UserAttendanceDetailedSerializer

    def get(self, request):
        employee_id = request.user.employee_get.id

        attendance_queryset = Attendance.objects.filter(
            employee_id=employee_id
        ).order_by("-id")

        paginator = PageNumberPagination()
        paginator.page_size = 20
        page = paginator.paginate_queryset(attendance_queryset, request)

        serializer = self.serializer_class(page, many=True)
        return paginator.get_paginated_response(serializer.data)


class AttendancePunchingHistoryPagination(PageNumberPagination):
    page_size = 20
    page_size_query_param = "page_size"
    max_page_size = 100


class AttendancePunchingHistoryAPIView(APIView):
    """Mobile API for raw attendance punches only."""

    permission_classes = [IsAuthenticated]
    pagination_class = AttendancePunchingHistoryPagination

    def _parse_date(self, raw_value, fallback):
        if not raw_value:
            return fallback
        try:
            return datetime.strptime(str(raw_value), "%Y-%m-%d").date()
        except Exception:
            return fallback

    def _parse_bool(self, raw_value):
        if raw_value is None or raw_value == "":
            return None
        value = str(raw_value).strip().lower()
        if value in {"1", "true", "yes", "y"}:
            return True
        if value in {"0", "false", "no", "n"}:
            return False
        return None

    def _employee_name(self, employee):
        if not employee:
            return "-"
        name = f"{getattr(employee, 'employee_first_name', '')} {getattr(employee, 'employee_last_name', '')}".strip()
        return name or f"Employee #{employee.id}"

    def _employee_scope(self, request):
        employee_qs, show_filter, can_view_all, default_employee_id = get_attendance_subject_employees(
            request,
            perm_codename="attendance.view_attendancepunchinghistory",
            base_queryset=Employee.objects.all().order_by("employee_first_name", "employee_last_name", "id"),
        )
        employees = list(employee_qs)
        options = [{"id": emp.id, "name": self._employee_name(emp)} for emp in employees]
        return options, show_filter, can_view_all, default_employee_id

    def _normalize_employee_scope(self, scope_result):
        if len(scope_result) == 4:
            return scope_result
        if len(scope_result) == 3:
            employee_options, show_employee_filter, default_employee_id = scope_result
            has_all_option = any(str(item.get("id")) == "all" for item in employee_options if isinstance(item, dict))
            can_view_all = bool(has_all_option or show_employee_filter)
            return employee_options, show_employee_filter, can_view_all, default_employee_id
        raise ValueError("Unexpected employee scope result shape")

    def get_queryset(self, request):
        queryset = AttendancePunchingHistory.objects.select_related("employee_id", "attendance_id").all()
        employee_qs, _, _, _ = get_attendance_subject_employees(
            request,
            perm_codename="attendance.view_attendancepunchinghistory",
            base_queryset=Employee.objects.all(),
        )
        employee_ids = list(employee_qs.values_list("id", flat=True))
        if not employee_ids:
            return queryset.none()
        return queryset.filter(employee_id_id__in=employee_ids)

    def get(self, request):
        today = dj_timezone.localdate()
        start_date = self._parse_date(request.GET.get("start_date"), today)
        end_date = self._parse_date(request.GET.get("end_date"), today)
        if start_date > end_date:
            start_date, end_date = end_date, start_date

        employee_options, show_employee_filter, can_view_all, default_employee_id = self._normalize_employee_scope(self._employee_scope(request))
        allow_all_employees = bool(can_view_all and show_employee_filter)
        if allow_all_employees:
            employee_options = [{"id": "all", "name": "All Employee"}] + employee_options

        allowed_employee_ids = {str(item["id"]) for item in employee_options if item.get("id") is not None}

        raw_selected_employee_id = request.GET.get("employee_id")
        if raw_selected_employee_id is None or raw_selected_employee_id == "":
            selected_employee_id = default_employee_id if default_employee_id is not None else None
        else:
            raw_selected_employee_id = str(raw_selected_employee_id).strip().lower()
            if raw_selected_employee_id in {"all", "0"}:
                selected_employee_id = "all" if allow_all_employees else default_employee_id
            else:
                try:
                    candidate_employee_id = int(raw_selected_employee_id)
                except Exception:
                    candidate_employee_id = None
                selected_employee_id = candidate_employee_id if candidate_employee_id is not None else default_employee_id

        if selected_employee_id is not None and str(selected_employee_id) not in allowed_employee_ids:
            selected_employee_id = default_employee_id if default_employee_id is not None else None

        queryset = self.get_queryset(request).filter(
            punch_timestamp__date__gte=start_date,
            punch_timestamp__date__lte=end_date,
        )

        if selected_employee_id not in (None, "all"):
            queryset = queryset.filter(employee_id_id=selected_employee_id)

        source = (request.GET.get("source") or "").strip().lower()
        valid_sources = {choice[0] for choice in AttendancePunchSource.choices}
        if source in valid_sources:
            queryset = queryset.filter(source=source)

        accepted_to_attendance = self._parse_bool(request.GET.get("accepted_to_attendance"))
        if accepted_to_attendance is not None:
            queryset = queryset.filter(accepted_to_attendance=accepted_to_attendance)

        queryset = queryset.order_by("-punch_timestamp", "-id")

        paginator = self.pagination_class()
        page = paginator.paginate_queryset(queryset, request)
        serializer = AttendancePunchingHistorySerializer(page, many=True, context={"request": request})
        response = paginator.get_paginated_response(serializer.data)
        response.data["start_date"] = start_date.isoformat()
        response.data["end_date"] = end_date.isoformat()
        response.data["selected_employee_id"] = selected_employee_id
        response.data["show_employee_filter"] = show_employee_filter
        response.data["employee_options"] = employee_options
        response.data["allow_all_employees"] = allow_all_employees
        return response


class AttendanceTypeAccessCheck(APIView):
    permission_classes = [IsAuthenticated]

    def get(self, request):
        user = request.user
        employee_id = user.employee_get.id

        if user.has_perm("attendance.view_attendance"):
            return Response(status=200)

        is_manager = (
            EmployeeWorkInformation.objects.filter(reporting_manager_id=employee_id)
            .only("id")
            .exists()
        )

        if is_manager:
            return Response(status=200)

        return Response(
            {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
        )

class UserAttendanceDetailedView(APIView):
    permission_classes = [IsAuthenticated]

    def get(self, request, id):
        attendance = get_object_or_404(Attendance, pk=id)
        if attendance.employee_id == request.user.employee_get:
            serializer = UserAttendanceDetailedSerializer(attendance)
            return Response(serializer.data, status=200)
        return Response(
            {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
        )


class PDFRenderer(BaseRenderer):
    media_type = "application/pdf"
    format = "pdf"
    charset = None
    render_style = "binary"

    def render(self, data, accepted_media_type=None, renderer_context=None):
        if data is None:
            return b""
        if isinstance(data, (bytes, bytearray)):
            return bytes(data)
        if isinstance(data, str):
            return data.encode("utf-8")
        try:
            return json.dumps(data).encode("utf-8")
        except Exception:
            return str(data).encode("utf-8")



class AttendanceMonthlyRecapAPIView(APIView):
    """Attendance → Attendances (Monthly recap) rows.

    Query params (GET):
      - employee_id (optional; defaults to the logged-in user)
      - month (optional; YYYY-MM; defaults to current month)
      - lang (optional; en|id; defaults to request language or en)

    Response:
      {"rows": [{no, date, shift_information, check_in, check_out, work_type, late, early_out, note, is_off}]}
    """

    permission_classes = [IsAuthenticated]

    def _resolve_language(self, request) -> str:
        lang = (request.GET.get("lang") or getattr(request, "LANGUAGE_CODE", "en") or "en")
        lang = lang.split("-")[0].lower().strip()
        return "id" if lang == "id" else "en"

    def _resolve_month(self, request, *, strict: bool = False) -> str:
        current_month = dj_timezone.localdate().strftime("%Y-%m")
        month_raw = (request.GET.get("month") or "").strip()
        if not month_raw:
            return current_month

        try:
            month = require_month_yyyy_mm(month_raw)
        except ValueError:
            if strict:
                raise
            month = current_month

        return normalize_month_yyyy_mm(
            month,
            fallback_month=current_month,
            max_month=current_month,
        )

    def _allowed_employees_qs(self, request):
        return get_attendance_subject_employees(
            request,
            perm_codename="attendance.view_attendance",
            base_queryset=Employee.objects.filter(is_active=True).select_related("employee_work_info"),
        )

    def get(self, request):
        from attendance.services.monthly_recap import get_monthly_attendance_recap

        month = self._resolve_month(request)
        lang = self._resolve_language(request)

        employees_qs, show_employee_filter, can_view_all, default_employee_id = self._allowed_employees_qs(request)

        # Resolve employee
        emp_id_raw = request.GET.get("employee_id")
        selected_employee = None
        if emp_id_raw:
            try:
                selected_employee = employees_qs.filter(id=int(emp_id_raw)).first()
            except Exception:
                selected_employee = None

            if selected_employee is None:
                return Response({"error": "Invalid employee_id"}, status=status.HTTP_400_BAD_REQUEST)
        else:
            selected_employee = employees_qs.filter(id=default_employee_id).first() if default_employee_id else None
            if selected_employee is None:
                selected_employee = employees_qs.first()

        if selected_employee is None:
            return Response(
                {
                    "employee_id": None,
                    "selected_employee_id": None,
                    "month": month,
                    "lang": lang,
                    "show_employee_filter": show_employee_filter,
                    "allow_all_employees": bool(can_view_all and show_employee_filter),
                    "employee_options": [
                        {"id": emp.id, "name": f"{(emp.employee_first_name or '').strip()} {(emp.employee_last_name or '').strip()}".strip() or f"Employee #{emp.id}"}
                        for emp in employees_qs
                    ],
                    "summary": {
                        "late_minutes": 0,
                        "early_out_minutes": 0,
                        "total_minutes": 0,
                    },
                    "rows": [],
                },
                status=200,
            )

        recap = get_monthly_attendance_recap(selected_employee, month, language=lang)
        rows = recap["rows"]
        payload_rows = [
            {
                "no": r.no,
                "date": r.attendance_date.strftime("%Y-%m-%d"),
                "shift_information": r.shift_information,
                "check_in": r.check_in,
                "check_out": r.check_out,
                "work_type": r.work_type,
                "late": r.late,
                "early_out": r.early_out,
                "late_minutes": format_decimal_minutes(getattr(r, "late_minutes", 0) or 0),
                "early_out_minutes": format_decimal_minutes(getattr(r, "early_out_minutes", 0) or 0),
                "note": r.note,
                "is_off": bool(getattr(r, "is_off", False)),
            }
            for r in rows
        ]
        return Response(
            {
                "employee_id": selected_employee.id,
                "selected_employee_id": selected_employee.id,
                "month": month,
                "lang": lang,
                "show_employee_filter": show_employee_filter,
                "allow_all_employees": bool(can_view_all and show_employee_filter),
                "employee_options": [
                    {"id": emp.id, "name": f"{(emp.employee_first_name or '').strip()} {(emp.employee_last_name or '').strip()}".strip() or f"Employee #{emp.id}"}
                    for emp in employees_qs
                ],
                "summary": recap["summary"],
                "rows": payload_rows,
            },
            status=200,
        )


class AttendanceMonthlyRecapExportPDFAPIView(AttendanceMonthlyRecapAPIView):
    """Export Attendance → Attendances (Monthly recap) as PDF for mobile/API clients."""

    permission_classes = [IsAuthenticated]
    renderer_classes = [PDFRenderer, JSONRenderer]

    def get(self, request):
        try:
            month = self._resolve_month(request, strict=bool((request.GET.get("month") or "").strip()))
        except ValueError:
            return Response({"error": "Invalid month format. Expected YYYY-MM"}, status=status.HTTP_400_BAD_REQUEST)
        lang = self._resolve_language(request)
        employees_qs, show_employee_filter, can_view_all, default_employee_id = self._allowed_employees_qs(request)

        emp_id_raw = request.GET.get("employee_id")
        if not emp_id_raw:
            return Response({"error": "employee_id is required"}, status=status.HTTP_400_BAD_REQUEST)

        try:
            employee = employees_qs.filter(id=int(emp_id_raw)).first()
        except Exception:
            employee = None

        if employee is None:
            return Response({"error": "Invalid employee_id"}, status=status.HTTP_400_BAD_REQUEST)

        from attendance.services.monthly_recap import get_monthly_attendance_recap

        recap = get_monthly_attendance_recap(employee, month, language=lang)
        rows = recap["rows"]
        year = int(month[:4])
        month_no = int(month[5:7])

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
        html_content = render_to_string("attendance/attendances/monthly_export_pdf.html", context)
        result = io.BytesIO()
        pdf_status = pisa.CreatePDF(src=html_content, dest=result)
        if pdf_status.err:
            logger.error("Error creating Monthly Recap PDF via API")
            return Response({"error": "Error generating PDF"}, status=status.HTTP_500_INTERNAL_SERVER_ERROR)

        response = HttpResponse(result.getvalue(), content_type="application/pdf")
        response["Content-Disposition"] = f'attachment; filename="{filename}"'
        return response
