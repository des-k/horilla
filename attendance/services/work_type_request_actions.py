from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime
from typing import Iterable, Optional

from django.core.exceptions import ValidationError
from django.db import transaction
from django.utils import timezone

from attendance.models import (
    AttendanceRequestFile,
    AttendanceWorkMode,
    EmployeeShiftDay,
    WorkModeRequest,
    WorkModeRequestActionType,
    WorkModeRequestDocumentStatus,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestScope,
    WorkModeRequestStatus,
    WorkModeRequestDocumentVersion,
    WorkModeRequestDocumentVersionFile,
)
from attendance.services.request_audit import log_request_action
from attendance.services.reconciliation import recompute_attendance_range
from attendance.services.attachment_validation import validate_uploaded_files
from attendance.services.work_type_request_permissions import (
    can_approve_request,
    can_cancel_request,
    can_manage_as_approver,
    can_reject_document,
    can_reject_request,
    can_reopen_document,
    can_revoke_request,
    can_update_request,
    can_upload_document,
    can_verify_document,
    is_owner,
)
from attendance.services.work_type_request_rules import (
    apply_rejection_to_attendance,
    validate_work_type_request,
)
from attendance.views.clock_in_out import get_shift_rules
from attendance.methods.utils import shift_schedule_today


class WorkModeRequestActionError(ValidationError):
    pass


@dataclass
class WorkModeRequestActionResult:
    request: WorkModeRequest
    recomputed: bool = False
    auto_rejected: bool = False


class WorkModeRequestActions:
    @staticmethod
    def _remark(value: Optional[str]) -> Optional[str]:
        if value is None:
            return None
        value = str(value).strip()
        return value or None

    @staticmethod
    def _now(now_dt: Optional[datetime] = None) -> datetime:
        return now_dt or timezone.now()

    @staticmethod
    def _touch_action(
        req: WorkModeRequest,
        *,
        actor,
        action_type: str,
        remark: Optional[str] = None,
        when: Optional[datetime] = None,
    ) -> None:
        when = WorkModeRequestActions._now(when)
        req.action_by = actor
        req.action_at = when
        req.action_type = action_type
        req.action_reason = WorkModeRequestActions._remark(remark)

    @staticmethod
    def _audit(
        req: WorkModeRequest,
        *,
        actor,
        action_type: str,
        old_status: Optional[str] = None,
        new_status: Optional[str] = None,
        remark: Optional[str] = None,
        metadata: Optional[dict] = None,
    ) -> None:
        log_request_action(
            work_mode_request=req,
            actor=actor,
            action_type=action_type,
            old_status=old_status,
            new_status=new_status,
            remark=remark,
            metadata=metadata,
        )

    @staticmethod
    def _version_status_for_upload(req: WorkModeRequest) -> str:
        if req.mode == AttendanceWorkMode.WFA:
            return WorkModeRequestDocumentStatus.SUBMITTED
        return (
            WorkModeRequestDocumentStatus.PENDING_VERIFICATION
            if req.status == WorkModeRequestStatus.APPROVED
            else WorkModeRequestDocumentStatus.SUBMITTED
        )

    @staticmethod
    def _current_version(req: WorkModeRequest) -> Optional[WorkModeRequestDocumentVersion]:
        current = getattr(req, "current_document_version", None)
        if current is not None:
            return current
        resolver = getattr(req, "resolve_current_document_version", None)
        if callable(resolver):
            return resolver()
        return None

    @staticmethod
    def _apply_current_version_to_request(
        req: WorkModeRequest,
        version: Optional[WorkModeRequestDocumentVersion],
    ) -> None:
        req.current_document_version = version
        req.sync_legacy_files_from_current_version()

        if version is None:
            req.sync_root_document_fields_from_current_version()
            if req.mode == AttendanceWorkMode.ON_DUTY and req.status == WorkModeRequestStatus.WAITING_FOR_APPROVAL:
                req.status = WorkModeRequestStatus.PENDING
            return

        if req.mode == AttendanceWorkMode.WFA:
            req.sync_root_document_fields_from_current_version()
            return

        req.sync_root_document_fields_from_current_version()
        if req.status == WorkModeRequestStatus.PENDING and version.file_links.exists():
            req.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL

    @staticmethod
    def _create_document_version(
        req: WorkModeRequest,
        *,
        actor,
        uploaded_files: Iterable,
        remark: Optional[str] = None,
        when: Optional[datetime] = None,
    ) -> WorkModeRequestDocumentVersion:
        when = WorkModeRequestActions._now(when)
        uploaded_files = list(uploaded_files or [])
        validate_uploaded_files(uploaded_files)
        if not uploaded_files:
            raise WorkModeRequestActionError("At least one file is required to create a document version.")

        current = WorkModeRequestActions._current_version(req)
        next_number = 1
        if current is not None:
            next_number = max(1, int(getattr(current, "version_number", 0) or 0) + 1)
        else:
            last = req.document_versions.order_by("-version_number").first()
            next_number = int(getattr(last, "version_number", 0) or 0) + 1 if last else 1

        req.document_versions.filter(is_current=True).update(is_current=False)
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=req,
            version_number=next_number,
            is_current=True,
            status=WorkModeRequestActions._version_status_for_upload(req),
            submitted_by=actor,
            submitted_at=when,
            review_remark=None,
            reviewed_by=None,
            reviewed_at=None,
        )
        created_ids = []
        for uploaded in uploaded_files:
            stored = AttendanceRequestFile.objects.create(file=uploaded)
            WorkModeRequestDocumentVersionFile.objects.create(
                version=version,
                attendance_request_file=stored,
            )
            created_ids.append(stored.id)

        req.document_verified_by = None
        req.document_verified_at = None
        req.document_remark = None
        WorkModeRequestActions._apply_current_version_to_request(req, version)
        WorkModeRequestActions._touch_action(
            req,
            actor=actor,
            action_type=WorkModeRequestActionType.DOCUMENT_UPLOADED,
            remark=remark,
            when=when,
        )
        WorkModeRequestActions._audit(
            req,
            actor=actor,
            action_type=WorkModeRequestActionType.DOCUMENT_UPLOADED,
            old_status=f"document:{getattr(current, 'status', WorkModeRequestDocumentStatus.NOT_UPLOADED) if current else WorkModeRequestDocumentStatus.NOT_UPLOADED}",
            new_status=f"document:{version.status}",
            remark=remark,
            metadata={
                "version_number": version.version_number,
                "file_ids": created_ids,
                "reupload": bool(current),
            },
        )
        return version

    @staticmethod
    def _recompute(req: WorkModeRequest) -> None:
        recompute_attendance_range(req.employee_id, req.start_date, req.end_date)

    @staticmethod
    def _cutoff_due_datetime(req: WorkModeRequest, *, now_dt: Optional[datetime] = None) -> Optional[datetime]:
        if req.mode != AttendanceWorkMode.WFA:
            return None
        now_dt = WorkModeRequestActions._now(now_dt)
        today = timezone.localdate(now_dt)
        if not (req.start_date <= today <= req.end_date):
            return None

        shift = getattr(getattr(req.employee_id, "employee_work_info", None), "shift_id", None)
        if not shift:
            return None
        day = EmployeeShiftDay.objects.filter(day=today.strftime("%A").lower()).first()
        if not day:
            return None
        try:
            _minimum_hour, start_sec, end_sec = shift_schedule_today(day=day, shift=shift)
        except Exception:
            start_sec, end_sec = 0, 0
        rules = get_shift_rules(today, shift, day, start_time_sec=start_sec, end_time_sec=end_sec)
        if req.scope == WorkModeRequestScope.OUT:
            return rules.get("cutoff_out_dt")
        return rules.get("cutoff_in_dt")

    @staticmethod
    def _auto_reject_for_cutoff(
        req: WorkModeRequest,
        *,
        actor=None,
        now_dt: Optional[datetime] = None,
    ) -> Optional[WorkModeRequestActionResult]:
        due_dt = WorkModeRequestActions._cutoff_due_datetime(req, now_dt=now_dt)
        now_dt = WorkModeRequestActions._now(now_dt)
        if due_dt is None or now_dt <= due_dt:
            return None

        old_status = req.status
        if req.scope == WorkModeRequestScope.IN:
            reason_code = WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_IN_PASSED
        elif req.scope == WorkModeRequestScope.OUT:
            reason_code = WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_OUT_PASSED
        else:
            reason_code = WorkModeRequestRejectReasonCode.AUTO_REJECT_CUTOFF_FULL_PASSED

        req.status = WorkModeRequestStatus.REJECTED
        req.reason_code = reason_code
        req.approved_by = None
        req.approved_at = None
        WorkModeRequestActions._touch_action(
            req,
            actor=actor,
            action_type=WorkModeRequestActionType.AUTO_REJECTED,
            remark=str(reason_code),
            when=now_dt,
        )
        req.save(update_fields=[
            "status",
            "reason_code",
            "approved_by",
            "approved_at",
            "action_by",
            "action_at",
            "action_type",
            "action_reason",
        ])
        WorkModeRequestActions._audit(
            req,
            actor=actor,
            action_type=WorkModeRequestActionType.AUTO_REJECTED,
            old_status=old_status,
            new_status=req.status,
            remark=str(reason_code),
            metadata={
                "cutoff_due_at": due_dt.isoformat() if due_dt else None,
                "reason_code": reason_code,
                "action_at": now_dt.isoformat(),
                "action_reason": str(reason_code),
            },
        )
        apply_rejection_to_attendance(req)
        return WorkModeRequestActionResult(request=req, recomputed=True, auto_rejected=True)

    @staticmethod
    @transaction.atomic
    def create_request(
        *,
        actor,
        mode: str,
        scope: str,
        start_date,
        end_date,
        reason: str,
        duty_destination_location: Optional[str] = None,
        duty_destination_detail: Optional[str] = None,
        uploaded_files: Optional[Iterable] = None,
    ) -> WorkModeRequest:
        reason = (reason or "").strip()
        destination = (duty_destination_location or "").strip() or None
        detail = (duty_destination_detail or "").strip() or None
        validate_work_type_request(
            employee=actor,
            mode=mode,
            scope=scope,
            start_date=start_date,
            end_date=end_date,
            instance_id=None,
        )
        if mode == AttendanceWorkMode.ON_DUTY and not destination:
            raise WorkModeRequestActionError("Destination location is required for ON DUTY requests.")

        req = WorkModeRequest.objects.create(
            employee_id=actor,
            mode=mode,
            scope=scope,
            start_date=start_date,
            end_date=end_date,
            reason=reason,
            duty_destination_location=destination,
            duty_destination_detail=detail,
            status=WorkModeRequestStatus.PENDING,
            action_type=WorkModeRequestActionType.CREATED,
        )
        uploaded_files = list(uploaded_files or [])
        if mode == AttendanceWorkMode.WFA:
            req.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
            if uploaded_files:
                WorkModeRequestActions._create_document_version(req, actor=actor, uploaded_files=uploaded_files)
            else:
                req.current_document_version = None
                req.document_status = WorkModeRequestDocumentStatus.NOT_UPLOADED
        elif mode == AttendanceWorkMode.ON_DUTY and uploaded_files:
            WorkModeRequestActions._create_document_version(req, actor=actor, uploaded_files=uploaded_files)
        else:
            req.current_document_version = None
            req.document_status = WorkModeRequestDocumentStatus.NOT_UPLOADED
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.CREATED)
        req.save()
        WorkModeRequestActions._audit(
            req,
            actor=actor,
            action_type=WorkModeRequestActionType.CREATED,
            old_status=None,
            new_status=req.status,
            metadata={
                "mode": req.mode,
                "scope": req.scope,
                "start_date": req.start_date.isoformat(),
                "end_date": req.end_date.isoformat(),
            },
        )
        return req

    @staticmethod
    @transaction.atomic
    def update_request(
        req: WorkModeRequest,
        *,
        actor,
        reason: Optional[str] = None,
        duty_destination_location: Optional[str] = None,
        duty_destination_detail: Optional[str] = None,
        uploaded_files: Optional[Iterable] = None,
        remark: Optional[str] = None,
        request=None,
    ) -> WorkModeRequestActionResult:
        uploaded_files = list(uploaded_files or [])
        has_non_file_changes = any(
            value is not None
            for value in (reason, duty_destination_location, duty_destination_detail)
        )
        if request is not None and has_non_file_changes and not can_update_request(request, req):
            raise WorkModeRequestActionError("This request can no longer be updated.")
        if request is not None and uploaded_files and not can_upload_document(request, req):
            raise WorkModeRequestActionError("You cannot upload documents for this request.")

        old_status = req.status
        if reason is not None:
            reason = str(reason).strip()
            if not reason:
                raise WorkModeRequestActionError("Reason / Notes is required.")
            req.reason = reason
        if req.mode == AttendanceWorkMode.ON_DUTY:
            if duty_destination_location is not None:
                req.duty_destination_location = str(duty_destination_location).strip()
            if duty_destination_detail is not None:
                req.duty_destination_detail = str(duty_destination_detail).strip()
            if not str(req.duty_destination_location or "").strip():
                raise WorkModeRequestActionError("Destination location is required for ON DUTY requests.")

        changed = False
        if uploaded_files:
            WorkModeRequestActions._create_document_version(
                req,
                actor=actor,
                uploaded_files=uploaded_files,
                remark=remark,
            )
            changed = True

        action_type = WorkModeRequestActionType.UPDATED
        if changed:
            action_type = WorkModeRequestActionType.DOCUMENT_UPLOADED
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=action_type, remark=remark)
        req.save()
        WorkModeRequestActions._audit(
            req,
            actor=actor,
            action_type=action_type,
            old_status=old_status,
            new_status=req.status,
            remark=remark,
            metadata={
                "uploaded_new_version": changed,
                "current_document_version": getattr(req.current_document_version, "version_number", None),
            },
        )
        recomputed = bool(changed and req.mode == AttendanceWorkMode.ON_DUTY and req.status == WorkModeRequestStatus.APPROVED)
        if recomputed:
            WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=recomputed)

    @staticmethod
    @transaction.atomic
    def cancel_request(req: WorkModeRequest, *, actor, request=None, remark: Optional[str] = None) -> WorkModeRequestActionResult:
        if request is not None and not can_cancel_request(request, req):
            raise WorkModeRequestActionError("You do not have permission to cancel this request.")
        if req.status not in {WorkModeRequestStatus.PENDING, WorkModeRequestStatus.WAITING_FOR_APPROVAL}:
            raise WorkModeRequestActionError("Only pending or waiting requests can be canceled.")
        old_status = req.status
        req.status = WorkModeRequestStatus.CANCELED
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.CANCELED, remark=remark)
        req.save(update_fields=["status", "action_by", "action_at", "action_type", "action_reason"])
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.CANCELED, old_status=old_status, new_status=req.status, remark=remark)
        WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)

    @staticmethod
    @transaction.atomic
    def approve_request(req: WorkModeRequest, *, actor, request=None, now_dt: Optional[datetime] = None) -> WorkModeRequestActionResult:
        if request is not None and not can_approve_request(request, req):
            raise WorkModeRequestActionError("You do not have permission to approve this request.")
        if req.status != WorkModeRequestStatus.WAITING_FOR_APPROVAL:
            raise WorkModeRequestActionError("Only waiting requests can be approved.")

        auto_rejected = WorkModeRequestActions._auto_reject_for_cutoff(req, actor=actor, now_dt=now_dt)
        if auto_rejected is not None:
            return auto_rejected

        old_status = req.status
        now_dt = WorkModeRequestActions._now(now_dt)
        req.status = WorkModeRequestStatus.APPROVED
        req.reason_code = None
        req.approved_by = actor
        req.approved_at = now_dt
        current_version = WorkModeRequestActions._current_version(req)
        if current_version is not None and req.mode == AttendanceWorkMode.ON_DUTY:
            current_version.status = WorkModeRequestDocumentStatus.PENDING_VERIFICATION
            current_version.reviewed_by = None
            current_version.reviewed_at = None
            current_version.review_remark = None
            current_version.save(update_fields=["status", "reviewed_by", "reviewed_at", "review_remark"])
            WorkModeRequestActions._apply_current_version_to_request(req, current_version)
        elif req.mode == AttendanceWorkMode.ON_DUTY:
            req.document_status = WorkModeRequestDocumentStatus.NOT_UPLOADED
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.APPROVED, when=now_dt)
        req.save()
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.APPROVED, old_status=old_status, new_status=req.status)
        WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)

    @staticmethod
    @transaction.atomic
    def reject_request(
        req: WorkModeRequest,
        *,
        actor,
        request=None,
        reason_code: Optional[str] = None,
        remark: Optional[str] = None,
    ) -> WorkModeRequestActionResult:
        if request is not None and not can_reject_request(request, req):
            raise WorkModeRequestActionError("You do not have permission to reject this request.")
        if req.status not in {WorkModeRequestStatus.WAITING_FOR_APPROVAL, WorkModeRequestStatus.PENDING}:
            raise WorkModeRequestActionError("Request cannot be rejected in this status.")
        old_status = req.status
        req.status = WorkModeRequestStatus.REJECTED
        req.reason_code = reason_code or WorkModeRequestRejectReasonCode.MANUAL_REJECT
        req.approved_by = None
        req.approved_at = None
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.REJECTED, remark=remark)
        req.save(update_fields=[
            "status",
            "reason_code",
            "approved_by",
            "approved_at",
            "action_by",
            "action_at",
            "action_type",
            "action_reason",
        ])
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.REJECTED, old_status=old_status, new_status=req.status, remark=remark)
        apply_rejection_to_attendance(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)

    @staticmethod
    @transaction.atomic
    def revoke_request(req: WorkModeRequest, *, actor, request=None, remark: Optional[str] = None) -> WorkModeRequestActionResult:
        if request is not None and not can_revoke_request(request, req):
            raise WorkModeRequestActionError("You do not have permission to revoke this request.")
        if req.status != WorkModeRequestStatus.APPROVED:
            raise WorkModeRequestActionError("Only approved requests can be revoked.")
        old_status = req.status
        req.status = WorkModeRequestStatus.REVOKED
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.REVOKED, remark=remark)
        req.save(update_fields=["status", "action_by", "action_at", "action_type", "action_reason"])
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.REVOKED, old_status=old_status, new_status=req.status, remark=remark)
        WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)

    @staticmethod
    @transaction.atomic
    def verify_document(req: WorkModeRequest, *, actor, request=None, remark: Optional[str] = None) -> WorkModeRequestActionResult:
        if req.mode != AttendanceWorkMode.ON_DUTY:
            raise WorkModeRequestActionError("WFA documents do not use document review workflow.")
        if request is not None and not can_verify_document(request, req):
            raise WorkModeRequestActionError("You do not have permission to verify this document.")
        version = WorkModeRequestActions._current_version(req)
        if version is None:
            raise WorkModeRequestActionError("No current document version found.")
        old_status = req.document_status
        now_dt = timezone.now()
        version.status = WorkModeRequestDocumentStatus.VERIFIED
        version.reviewed_by = actor
        version.reviewed_at = now_dt
        version.review_remark = WorkModeRequestActions._remark(remark)
        version.save(update_fields=["status", "reviewed_by", "reviewed_at", "review_remark"])
        WorkModeRequestActions._apply_current_version_to_request(req, version)
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.VERIFIED, remark=remark, when=now_dt)
        req.save(update_fields=[
            "current_document_version",
            "document_status",
            "document_verified_by",
            "document_verified_at",
            "document_remark",
            "action_by",
            "action_at",
            "action_type",
            "action_reason",
        ])
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.VERIFIED, old_status=f"document:{old_status}", new_status=f"document:{req.document_status}", remark=remark, metadata={"version_number": version.version_number})
        WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)

    @staticmethod
    @transaction.atomic
    def reject_document(req: WorkModeRequest, *, actor, request=None, remark: Optional[str] = None) -> WorkModeRequestActionResult:
        if req.mode != AttendanceWorkMode.ON_DUTY:
            raise WorkModeRequestActionError("WFA documents do not use document review workflow.")
        if request is not None and not can_reject_document(request, req):
            raise WorkModeRequestActionError("You do not have permission to reject this document.")
        version = WorkModeRequestActions._current_version(req)
        if version is None:
            raise WorkModeRequestActionError("No current document version found.")
        old_status = req.document_status
        version.status = WorkModeRequestDocumentStatus.REJECTED
        version.reviewed_by = actor
        version.reviewed_at = timezone.now()
        version.review_remark = WorkModeRequestActions._remark(remark)
        version.save(update_fields=["status", "reviewed_by", "reviewed_at", "review_remark"])
        WorkModeRequestActions._apply_current_version_to_request(req, version)
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.DOCUMENT_REJECTED, remark=remark)
        req.save(update_fields=["current_document_version", "document_status", "document_verified_by", "document_verified_at", "document_remark", "action_by", "action_at", "action_type", "action_reason"])
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.DOCUMENT_REJECTED, old_status=f"document:{old_status}", new_status=f"document:{req.document_status}", remark=remark, metadata={"version_number": version.version_number})
        WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)

    @staticmethod
    @transaction.atomic
    def reopen_document(req: WorkModeRequest, *, actor, request=None, remark: Optional[str] = None) -> WorkModeRequestActionResult:
        if req.mode != AttendanceWorkMode.ON_DUTY:
            raise WorkModeRequestActionError("WFA documents do not use document review workflow.")
        if request is not None and not can_reopen_document(request, req):
            raise WorkModeRequestActionError("You do not have permission to reopen this document.")
        version = WorkModeRequestActions._current_version(req)
        if version is None:
            raise WorkModeRequestActionError("No current document version found.")
        old_status = req.document_status
        version.status = WorkModeRequestDocumentStatus.PENDING_VERIFICATION
        version.reviewed_by = None
        version.reviewed_at = None
        # Reopen starts a fresh review state on the current version.
        # The reopen remark is kept in the request action log, not as a lingering review verdict.
        version.review_remark = None
        version.save(update_fields=["status", "reviewed_by", "reviewed_at", "review_remark"])
        WorkModeRequestActions._apply_current_version_to_request(req, version)
        WorkModeRequestActions._touch_action(req, actor=actor, action_type=WorkModeRequestActionType.REOPENED, remark=remark)
        req.save(update_fields=["current_document_version", "document_status", "document_verified_by", "document_verified_at", "document_remark", "action_by", "action_at", "action_type", "action_reason"])
        WorkModeRequestActions._audit(req, actor=actor, action_type=WorkModeRequestActionType.REOPENED, old_status=f"document:{old_status}", new_status=f"document:{req.document_status}", remark=remark, metadata={"version_number": version.version_number})
        WorkModeRequestActions._recompute(req)
        return WorkModeRequestActionResult(request=req, recomputed=True)
