"""
models.py

This module is used to register models for attendance app

"""

import contextlib
import datetime as dt
import json
from datetime import date, datetime, timedelta

from django.apps import apps
from django.core.exceptions import ValidationError
from django.db import models
from django.db.models import Q
from django.utils import timezone
from django.utils.translation import gettext_lazy as _

from attendance.methods.utils import (
    MONTH_MAPPING,
    attendance_date_validate,
    format_time,
    get_diff_dict,
    strtime_seconds,
    validate_hh_mm_ss_format,
    validate_time_format,
    validate_time_in_minutes,
)
from attendance.services.image_compression import compress_model_image_field
from base.horilla_company_manager import HorillaCompanyManager
from base.methods import is_company_leave, is_holiday
from base.models import Company, EmployeeShift, EmployeeShiftDay, WorkType
from employee.models import Employee
from horilla.methods import get_horilla_model_class
from horilla.models import HorillaModel, upload_path
from horilla_audit.models import HorillaAuditInfo, HorillaAuditLog

# to skip the migration issue with the old migrations
_validate_time_in_minutes = validate_time_in_minutes


# Create your models here.


class AttendanceWorkMode(models.TextChoices):
    """Work mode used for attendance punches."""
    WFO = "wfo", _("WFO")
    WFA = "wfa", _("WFA")
    ON_DUTY = "on_duty", _("On Duty")


class WorkModeRequestScope(models.TextChoices):
    """Scope of a work-mode request."""
    IN = "in", _("IN")
    OUT = "out", _("OUT")
    FULL = "full", _("FULL (IN & OUT)")


class WorkModeRequestStatus(models.TextChoices):
    """Approval status for a work-mode request."""
    PENDING = "pending", _("Pending")
    WAITING_FOR_APPROVAL = "waiting_for_approval", _("Waiting For Approval")
    APPROVED = "approved", _("Approved")
    REJECTED = "rejected", _("Rejected")
    REVOKED = "revoked", _("Revoked")
    CANCELED = "canceled", _("Canceled")


class WorkModeRequestDocumentStatus(models.TextChoices):
    NOT_UPLOADED = "not_uploaded", _("Not Uploaded")
    SUBMITTED = "submitted", _("Submitted")
    PENDING_VERIFICATION = "pending_verification", _("Pending Verification")
    VERIFIED = "verified", _("Verified")
    REJECTED = "rejected", _("Rejected")


class PunchDecisionStatus(models.TextChoices):
    ACCEPTED = "accepted", _("Accepted")
    NOT_ACCEPTED = "not_accepted", _("Not Accepted")
    INVALID = "invalid", _("Invalid")
    SUPERSEDED = "superseded", _("Superseded")


class GraceClockInType(models.TextChoices):
    AFTER = "after", _("After")
    BEFORE_AND_AFTER = "before_after", _("Before & After")


class WorkModeRequestActionType(models.TextChoices):
    """Audit action applied to a work-mode request."""
    CREATED = "CREATED", _("Created")
    UPDATED = "UPDATED", _("Updated")
    DOCUMENT_UPLOADED = "DOCUMENT_UPLOADED", _("Document Uploaded")
    APPROVED = "APPROVED", _("Approved")
    REJECTED = "REJECTED", _("Rejected")
    AUTO_REJECTED = "AUTO_REJECTED", _("Auto Rejected")
    DOCUMENT_REJECTED = "DOCUMENT_REJECTED", _("Document Rejected")
    VERIFIED = "VERIFIED", _("Verified")
    REVOKED = "REVOKED", _("Revoked")
    REOPENED = "REOPENED", _("Reopened")
    CANCELED = "CANCELED", _("Canceled")


class AttendanceRequestActionType(models.TextChoices):
    """Audit action applied to an attendance correction request."""
    APPROVED = "APPROVED", _("Approved")
    REJECTED = "REJECTED", _("Rejected")
    CANCELED = "CANCELED", _("Canceled")
    REVOKED = "REVOKED", _("Revoked")


class WorkModeRequestRejectReasonCode(models.TextChoices):
    """Reason code for REJECTED WorkModeRequest."""
    MANUAL_REJECT = "MANUAL_REJECT", _("Manual Reject")
    AUTO_REJECT_CUTOFF_IN_PASSED = "AUTO_REJECT_CUTOFF_IN_PASSED", _("Auto Reject: Cutoff IN Passed")
    AUTO_REJECT_CUTOFF_OUT_PASSED = "AUTO_REJECT_CUTOFF_OUT_PASSED", _("Auto Reject: Cutoff OUT Passed")
    AUTO_REJECT_CUTOFF_FULL_PASSED = "AUTO_REJECT_CUTOFF_FULL_PASSED", _("Auto Reject: Cutoff FULL Passed")

    # Attendance punch reject reasons (Option B)
    EARLY_CHECKOUT_BEFORE_SHIFT_END = (
        "EARLY_CHECKOUT_BEFORE_SHIFT_END",
        _("Early check-out before shift end"),
    )
    EARLY_CHECKOUT_BEFORE_CUTOFF_IN = (
        "EARLY_CHECKOUT_BEFORE_CUTOFF_IN",
        _("Early check-out before cutoff-in"),
    )


class AttendancePunchStatus(models.TextChoices):
    """Audit status for a punch (IN/OUT) after request decision."""
    VALID = "VALID", _("Valid")
    REJECTED = "REJECTED", _("Rejected")


class AttendanceChannel(models.TextChoices):
    """Explicit source/channel persisted on final attendance and activity."""
    MOBILE = "mobile", _("Mobile")
    BIOMETRIC = "biometric", _("Biometric")
    APPROVED_REQUEST = "approved_request", _("Approved Request")
    CORRECTION_REQUEST = "correction_request", _("Correction Request")
    AUTO = "auto", _("Auto")
    MANUAL = "manual", _("Manual")
    API = "api", _("API")


class AttendancePunchSource(models.TextChoices):
    """Source of a raw punch entry."""
    MOBILE = "mobile", _("Mobile")
    BIOMETRIC = "biometric", _("Biometric")
    API = "api", _("API")
    UNKNOWN = "unknown", _("Unknown")


class AttendancePunchDirection(models.TextChoices):
    """Direction of a raw punch event."""
    IN = "in", _("IN")
    OUT = "out", _("OUT")
    UNKNOWN = "unknown", _("Unknown")


class AttendanceActivity(HorillaModel):
    """
    AttendanceActivity model
    """

    employee_id = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        related_name="employee_attendance_activities",
        verbose_name=_("Employee"),
    )
    attendance_date = models.DateField(
        null=True,
        validators=[attendance_date_validate],
        verbose_name=_("Attendance Date"),
    )
    shift_day = models.ForeignKey(
        EmployeeShiftDay,
        null=True,
        on_delete=models.DO_NOTHING,
        verbose_name=_("Shift Day"),
    )
    in_datetime = models.DateTimeField(null=True, blank=True)
    clock_in_date = models.DateField(null=True, blank=True, verbose_name=_("In Date"))
    clock_in = models.TimeField(null=True, blank=True, verbose_name=_("Check In"))
    clock_in_channel = models.CharField(
        max_length=32,
        null=True,
        blank=True,
        choices=AttendanceChannel.choices,
        verbose_name=_("Check-In Source"),
    )
    clock_out_date = models.DateField(null=True, blank=True, verbose_name=_("Out Date"))
    out_datetime = models.DateTimeField(null=True, blank=True)
    clock_out = models.TimeField(null=True, blank=True, verbose_name=_("Check Out"))
    clock_out_channel = models.CharField(
        max_length=32,
        null=True,
        blank=True,
        choices=AttendanceChannel.choices,
        verbose_name=_("Check-Out Source"),
    )
    objects = HorillaCompanyManager(
        related_company_field="employee_id__employee_work_info__company_id"
    )
    clock_in_image = models.ImageField(upload_to=upload_path, null=True, blank=True)
    clock_out_image = models.ImageField(upload_to=upload_path, null=True, blank=True)

    clock_in_mode = models.CharField(
        max_length=20,
        null=True,
        blank=True,
        choices=AttendanceWorkMode.choices,
        default=AttendanceWorkMode.WFO,
        verbose_name=_("Clock-In Mode"),
    )
    clock_out_mode = models.CharField(
        max_length=20,
        null=True,
        blank=True,
        choices=AttendanceWorkMode.choices,
        default=AttendanceWorkMode.WFO,
        verbose_name=_("Clock-Out Mode"),
    )

    # Location payload stored for audit purposes (no geofencing).
    # Expected keys (example): {"lat": 0.0, "lng": 0.0, "accuracy": 10, "provider": "gps", "captured_at": "..."}
    clock_in_location = models.JSONField(null=True, blank=True, verbose_name=_("Clock-In Location"))
    clock_out_location = models.JSONField(null=True, blank=True, verbose_name=_("Clock-Out Location"))

    # Which request enabled this punch (if any).
    work_mode_request_id = models.ForeignKey(
        "attendance.WorkModeRequest",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="attendance_activities",
        verbose_name=_("Work Mode Request"),
    )
    reconciliation_source = models.CharField(max_length=64, null=True, blank=True, verbose_name=_("Final Source"))
    reconciliation_note = models.CharField(max_length=255, null=True, blank=True, verbose_name=_("Final Note"))
    late_minutes = models.PositiveIntegerField(default=0, verbose_name=_("Late Minutes"))
    early_out_minutes = models.PositiveIntegerField(default=0, verbose_name=_("Early Out Minutes"))

    class Meta:
        """
        Meta class to add some additional options
        """

        ordering = ["-attendance_date", "employee_id__employee_first_name", "clock_in"]
        constraints = [
            models.UniqueConstraint(
                fields=["employee_id", "attendance_date"],
                name="uniq_activity_employee_date",
            )
        ]
    def duration(self):
        """Return duration in seconds when both IN and OUT are available."""

        if not (self.clock_in_date and self.clock_in and self.clock_out_date and self.clock_out):
            return 0

        clock_in_datetime = datetime.combine(self.clock_in_date, self.clock_in)
        clock_out_datetime = datetime.combine(self.clock_out_date, self.clock_out)
        time_difference = clock_out_datetime - clock_in_datetime
        return max(0, time_difference.total_seconds())

    def save(self, *args, **kwargs):
        compress_model_image_field(self, "clock_in_image")
        compress_model_image_field(self, "clock_out_image")
        super().save(*args, **kwargs)

    def __str__(self):
        return (
            f"{self.employee_id} - {self.attendance_date} - "
            f"{self.clock_in or '-'} - {self.clock_out or '-'}"
        )


class AttendancePunchingHistory(HorillaModel):
    """Dedicated raw punch history for audit/debugging."""

    employee_id = models.ForeignKey(
        Employee,
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="employee_punching_histories",
        verbose_name=_("Employee"),
    )
    attendance_id = models.ForeignKey(
        "attendance.Attendance",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="punching_history_entries",
        verbose_name=_("Attendance"),
    )
    attendance_date = models.DateField(null=True, blank=True, verbose_name=_("Attendance Date"))
    punch_timestamp = models.DateTimeField(verbose_name=_("Punch Timestamp"))
    source = models.CharField(
        max_length=24,
        choices=AttendancePunchSource.choices,
        default=AttendancePunchSource.UNKNOWN,
        verbose_name=_("Source"),
    )
    punch_direction = models.CharField(
        max_length=12,
        choices=AttendancePunchDirection.choices,
        default=AttendancePunchDirection.UNKNOWN,
        verbose_name=_("Punch Direction"),
    )
    device_info = models.CharField(max_length=255, null=True, blank=True, verbose_name=_("Device Info"))
    photo = models.ImageField(upload_to=upload_path, null=True, blank=True, verbose_name=_("Photo"))
    location = models.JSONField(null=True, blank=True, verbose_name=_("Location"))
    accepted_to_attendance = models.BooleanField(default=False, verbose_name=_("Accepted to Attendance"))
    reason = models.CharField(max_length=255, null=True, blank=True, verbose_name=_("Reason"))
    decision_status = models.CharField(
        max_length=24,
        choices=PunchDecisionStatus.choices,
        default=PunchDecisionStatus.NOT_ACCEPTED,
        verbose_name=_("Decision Status"),
    )
    decision_source = models.CharField(max_length=64, null=True, blank=True, verbose_name=_("Decision Source"))
    work_mode = models.CharField(
        max_length=20,
        null=True,
        blank=True,
        choices=AttendanceWorkMode.choices,
        verbose_name=_("Work Mode"),
    )
    related_work_mode_request = models.ForeignKey(
        "attendance.WorkModeRequest",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="punching_history_entries",
        verbose_name=_("Related Work Mode Request"),
    )
    raw_payload = models.JSONField(null=True, blank=True, verbose_name=_("Raw Payload"))
    raw_employee_identifier = models.CharField(max_length=128, null=True, blank=True, verbose_name=_("Raw Employee Identifier"))

    objects = HorillaCompanyManager(
        related_company_field="employee_id__employee_work_info__company_id"
    )

    class Meta:
        ordering = ["-punch_timestamp", "-id"]
        verbose_name = _("Attendance Punching History")
        verbose_name_plural = _("Attendance Punching Histories")

    @property
    def employee_display(self):
        return self.employee_id or self.raw_employee_identifier or "-"

    @property
    def location_display(self):
        if not isinstance(self.location, dict):
            return "-"
        lat = self.location.get("lat", self.location.get("latitude"))
        lng = self.location.get("lng", self.location.get("longitude"))
        if lat is None or lng is None:
            return "-"
        return f"{lat}, {lng}"

    @property
    def google_maps_url(self):
        if not isinstance(self.location, dict):
            return None
        lat = self.location.get("lat", self.location.get("latitude"))
        lng = self.location.get("lng", self.location.get("longitude"))
        if lat is None or lng is None:
            return None
        return f"https://www.google.com/maps?q={lat},{lng}"

    def save(self, *args, **kwargs):
        compress_model_image_field(self, "photo")
        super().save(*args, **kwargs)

    def __str__(self):
        employee = self.employee_id or self.raw_employee_identifier or "Unknown"
        return f"{employee} - {self.punch_timestamp}"


class BatchAttendance(HorillaModel):
    """
    Batch attendance model
    """

    title = models.CharField(max_length=150, verbose_name=_("Title"))

    def __str__(self):
        return f"{self.title}-{self.id}"



class WorkModeRequest(HorillaModel):
    """
    Work mode request used to control whether an employee may punch from mobile.

    Notes:
    - WFA requires APPROVED status before punch is allowed.
    - ON_DUTY may allow punching while PENDING (business rule enforced in API layer).
    - WFO is not expected to be requested (WFO comes from biometric device), but the choice
      is kept for completeness and data consistency.
    """

    employee_id = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        related_name="work_mode_requests",
        verbose_name=_("Employee"),
    )

    mode = models.CharField(
        max_length=20,
        choices=AttendanceWorkMode.choices,
        verbose_name=_("Mode"),
    )

    scope = models.CharField(
        max_length=10,
        choices=WorkModeRequestScope.choices,
        default=WorkModeRequestScope.FULL,
        verbose_name=_("Scope"),
    )

    start_date = models.DateField(verbose_name=_("Start Date"))
    end_date = models.DateField(verbose_name=_("End Date"))

    status = models.CharField(
        max_length=32,
        choices=WorkModeRequestStatus.choices,
        default=WorkModeRequestStatus.PENDING,
        verbose_name=_("Status"),
    )

    reason_code = models.CharField(
        max_length=64,
        null=True,
        blank=True,
        choices=WorkModeRequestRejectReasonCode.choices,
        verbose_name=_("Reject Reason Code"),
    )

    reason = models.TextField(null=True, blank=True, verbose_name=_("Reason"))
    action_reason = models.TextField(null=True, blank=True, verbose_name=_("Action Reason"))

    files = models.ManyToManyField(
        "attendance.AttendanceRequestFile",
        blank=True,
        related_name="work_mode_requests",
        verbose_name=_("Files"),
    )

    approved_by = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        null=True,
        blank=True,
        related_name="approved_work_mode_requests",
        verbose_name=_("Approved By"),
    )
    approved_at = models.DateTimeField(null=True, blank=True, verbose_name=_("Approved At"))
    action_by = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        null=True,
        blank=True,
        related_name="acted_work_mode_requests",
        verbose_name=_("Action By"),
    )
    action_at = models.DateTimeField(null=True, blank=True, verbose_name=_("Action At"))
    action_type = models.CharField(
        max_length=32,
        null=True,
        blank=True,
        choices=WorkModeRequestActionType.choices,
        verbose_name=_("Action Type"),
    )
    document_status = models.CharField(
        max_length=32,
        choices=WorkModeRequestDocumentStatus.choices,
        default=WorkModeRequestDocumentStatus.NOT_UPLOADED,
        verbose_name=_("Document Status"),
    )
    document_remark = models.TextField(null=True, blank=True, verbose_name=_("Document Remark"))
    document_verified_by = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        null=True,
        blank=True,
        related_name="verified_work_mode_requests",
        verbose_name=_("Document Verified By"),
    )
    document_verified_at = models.DateTimeField(null=True, blank=True, verbose_name=_("Document Verified At"))
    current_document_version = models.ForeignKey(
        "attendance.WorkModeRequestDocumentVersion",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="+",
        verbose_name=_("Current Document Version"),
    )
    duty_destination_location = models.CharField(max_length=255, null=True, blank=True, verbose_name=_("Duty Destination Location"))
    duty_destination_detail = models.TextField(null=True, blank=True, verbose_name=_("Duty Destination Detail"))

    objects = HorillaCompanyManager(
        related_company_field="employee_id__employee_work_info__company_id"
    )

    class Meta:
        ordering = ["-start_date", "-id"]
        verbose_name = _("Work Mode Request")
        verbose_name_plural = _("Work Mode Requests")

    def __str__(self) -> str:
        return f"{self.employee_id} - {self.mode} ({self.scope}) - {self.start_date} to {self.end_date}"

    @property
    def requires_pre_approval(self) -> bool:
        return self.mode == AttendanceWorkMode.WFA

    def is_active_for_date(self, target_date: date) -> bool:
        """Returns True if the request covers the date and is not in a terminal inactive state."""
        if self.status in {
            WorkModeRequestStatus.REJECTED,
            WorkModeRequestStatus.CANCELED,
            WorkModeRequestStatus.REVOKED,
        }:
            return False
        return self.start_date <= target_date <= self.end_date

    def covers_in(self) -> bool:
        return self.scope in (WorkModeRequestScope.IN, WorkModeRequestScope.FULL)

    def covers_out(self) -> bool:
        return self.scope in (WorkModeRequestScope.OUT, WorkModeRequestScope.FULL)

    @property
    def is_document_locked(self) -> bool:
        return self.effective_document_status() == WorkModeRequestDocumentStatus.VERIFIED

    def resolve_current_document_version(self):
        version = getattr(self, "current_document_version", None)
        if version is not None:
            return version
        try:
            return self.document_versions.filter(is_current=True).select_related(
                "reviewed_by", "submitted_by"
            ).prefetch_related("file_links__attendance_request_file").first()
        except Exception as exc:
            logger.exception(
                "Failed to resolve current document version for work mode request %s",
                getattr(self, "id", None),
            )
            raise WorkModeRequestConsistencyError(
                f"Failed to resolve current document version for request {getattr(self, 'id', None)}"
            ) from exc

    def current_document_files(self):
        version = self.resolve_current_document_version()
        if version is None:
            return []
        try:
            return [
                link.attendance_request_file
                for link in version.file_links.select_related("attendance_request_file")
                if getattr(link, "attendance_request_file", None)
            ]
        except Exception as exc:
            logger.exception(
                "Failed to resolve current document files for work mode request %s",
                getattr(self, "id", None),
            )
            raise WorkModeRequestConsistencyError(
                f"Failed to resolve current document files for request {getattr(self, 'id', None)}"
            ) from exc

    def effective_document_status(self) -> str:
        """Version-led document status.

        Root request fields are kept as compatibility mirrors, but current behavior
        should follow the current document version whenever it exists.
        """
        version = self.resolve_current_document_version()
        if version is None:
            return WorkModeRequestDocumentStatus.NOT_UPLOADED
        if self.mode == AttendanceWorkMode.WFA:
            return WorkModeRequestDocumentStatus.SUBMITTED
        return getattr(version, "status", None) or WorkModeRequestDocumentStatus.NOT_UPLOADED

    def effective_document_remark(self):
        version = self.resolve_current_document_version()
        if version is None or self.mode == AttendanceWorkMode.WFA:
            return None
        return getattr(version, "review_remark", None)

    def effective_document_reviewed_by(self):
        version = self.resolve_current_document_version()
        if version is None or self.mode == AttendanceWorkMode.WFA:
            return None
        return getattr(version, "reviewed_by", None)

    def effective_document_reviewed_at(self):
        version = self.resolve_current_document_version()
        if version is None or self.mode == AttendanceWorkMode.WFA:
            return None
        return getattr(version, "reviewed_at", None)

    @property
    def current_document_version_number(self):
        version = self.resolve_current_document_version()
        return getattr(version, "version_number", None) if version is not None else None

    @property
    def current_document_file_count(self) -> int:
        try:
            return len(self.current_document_files() or [])
        except WorkModeRequestConsistencyError:
            logger.exception(
                "Failed to calculate current document file count for work mode request %s",
                getattr(self, "id", None),
            )
            return 0

    @property
    def effective_document_status_label(self) -> str:
        raw = self.effective_document_status()
        if self.mode == AttendanceWorkMode.WFA:
            return _("Supporting Attachment Uploaded") if raw != WorkModeRequestDocumentStatus.NOT_UPLOADED else _("Not Uploaded")
        mapping = {
            WorkModeRequestDocumentStatus.NOT_UPLOADED: _("Not Uploaded"),
            WorkModeRequestDocumentStatus.SUBMITTED: _("Submitted"),
            WorkModeRequestDocumentStatus.PENDING_VERIFICATION: _("Pending Verification"),
            WorkModeRequestDocumentStatus.VERIFIED: _("Verified"),
            WorkModeRequestDocumentStatus.REJECTED: _("Rejected"),
        }
        return mapping.get(raw, raw)

    def sync_root_document_fields_from_current_version(self):
        """Keep legacy root fields aligned with the current version.

        These root fields remain for backward compatibility with older callers and
        queries, but the version entity is the source of truth.
        """
        self.document_status = self.effective_document_status()
        self.document_remark = self.effective_document_remark()
        self.document_verified_by = self.effective_document_reviewed_by()
        self.document_verified_at = self.effective_document_reviewed_at()

    def sync_legacy_files_from_current_version(self):
        """Keep legacy M2M in sync with current version only for backwards compatibility."""
        try:
            current_ids = [obj.id for obj in self.current_document_files() if getattr(obj, "id", None)]
            self.files.set(current_ids)
        except Exception as exc:
            logger.exception(
                "Failed to sync legacy files from current version for work mode request %s",
                getattr(self, "id", None),
            )
            raise WorkModeRequestConsistencyError(
                f"Failed to sync legacy files for request {getattr(self, 'id', None)}"
            ) from exc

    @staticmethod
    def _employee_display_name(employee) -> str | None:
        if not employee:
            return None
        try:
            full_name = f"{employee.employee_first_name} {employee.employee_last_name}".strip()
            return full_name or str(employee)
        except Exception:
            return str(employee)

    @staticmethod
    def _user_display_name(user) -> str | None:
        if not user:
            return None
        full_name = f"{getattr(user, 'first_name', '')} {getattr(user, 'last_name', '')}".strip()
        return full_name or getattr(user, 'username', None) or getattr(user, 'email', None) or str(user)

    def _latest_action_log(self, *, action_type: str | None = None):
        logs = self.action_logs.select_related("actor", "created_by")
        if action_type:
            logs = logs.filter(action_type=action_type)
        return logs.order_by("-acted_at", "-id").first()

    @property
    def action_actor_display(self) -> str | None:
        if self.action_by_id:
            return self._employee_display_name(self.action_by)
        log = self._latest_action_log()
        if log is None:
            return None
        return self._employee_display_name(getattr(log, "actor", None)) or self._user_display_name(getattr(log, "created_by", None))

    @property
    def approved_actor_display(self) -> str | None:
        if self.approved_by_id:
            return self._employee_display_name(self.approved_by)
        log = self._latest_action_log(action_type=WorkModeRequestActionType.APPROVED)
        if log is None:
            return None
        return self._employee_display_name(getattr(log, "actor", None)) or self._user_display_name(getattr(log, "created_by", None))

    @property
    def action_effective_at(self):
        if self.action_at:
            return self.action_at
        log = self._latest_action_log()
        return getattr(log, "acted_at", None) if log else self.approved_at

    def clean(self):
        super().clean()
        if self.end_date and self.start_date and self.end_date < self.start_date:
            raise ValidationError({"end_date": _("End date cannot be earlier than start date.")})

        # WFO should not be requested; keep it invalid at model level to prevent UI misuse.
        if self.mode == AttendanceWorkMode.WFO:
            raise ValidationError({"mode": _("WFO should not be requested. Use WFA or On Duty.")})


class WorkModeRequestDocumentVersion(HorillaModel):
    work_mode_request = models.ForeignKey(
        "attendance.WorkModeRequest",
        on_delete=models.CASCADE,
        related_name="document_versions",
        verbose_name=_("Work Mode Request"),
    )
    version_number = models.PositiveIntegerField(default=1, verbose_name=_("Version Number"))
    is_current = models.BooleanField(default=False, verbose_name=_("Current Version"))
    status = models.CharField(
        max_length=32,
        choices=WorkModeRequestDocumentStatus.choices,
        default=WorkModeRequestDocumentStatus.SUBMITTED,
        verbose_name=_("Review Status"),
    )
    submitted_by = models.ForeignKey(
        Employee,
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="submitted_work_mode_document_versions",
        verbose_name=_("Submitted By"),
    )
    submitted_at = models.DateTimeField(default=timezone.now, verbose_name=_("Submitted At"))
    reviewed_by = models.ForeignKey(
        Employee,
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="reviewed_work_mode_document_versions",
        verbose_name=_("Reviewed By"),
    )
    reviewed_at = models.DateTimeField(null=True, blank=True, verbose_name=_("Reviewed At"))
    review_remark = models.TextField(null=True, blank=True, verbose_name=_("Review Remark"))

    class Meta:
        ordering = ["-version_number", "-id"]
        unique_together = (("work_mode_request", "version_number"),)
        verbose_name = _("Work Mode Request Document Version")
        verbose_name_plural = _("Work Mode Request Document Versions")

    def __str__(self):
        return f"{self.work_mode_request_id} - v{self.version_number}"


class WorkModeRequestDocumentVersionFile(HorillaModel):
    version = models.ForeignKey(
        "attendance.WorkModeRequestDocumentVersion",
        on_delete=models.CASCADE,
        related_name="file_links",
        verbose_name=_("Document Version"),
    )
    attendance_request_file = models.ForeignKey(
        "attendance.AttendanceRequestFile",
        on_delete=models.PROTECT,
        related_name="work_mode_document_links",
        verbose_name=_("Attachment"),
    )

    class Meta:
        ordering = ["id"]
        verbose_name = _("Work Mode Request Document File")
        verbose_name_plural = _("Work Mode Request Document Files")

    def __str__(self):
        return f"{self.version_id} - {self.attendance_request_file_id}"



class AttendanceRequestAuditLog(HorillaModel):
    attendance = models.ForeignKey(
        "attendance.Attendance",
        on_delete=models.CASCADE,
        null=True,
        blank=True,
        related_name="action_logs",
        verbose_name=_("Attendance Request"),
    )
    work_mode_request = models.ForeignKey(
        "attendance.WorkModeRequest",
        on_delete=models.CASCADE,
        null=True,
        blank=True,
        related_name="action_logs",
        verbose_name=_("Work Mode Request"),
    )
    actor = models.ForeignKey(
        Employee,
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="attendance_action_logs",
        verbose_name=_("Actor"),
    )
    action_type = models.CharField(max_length=32, verbose_name=_("Action Type"))
    old_status = models.CharField(max_length=64, null=True, blank=True, verbose_name=_("Old Status"))
    new_status = models.CharField(max_length=64, null=True, blank=True, verbose_name=_("New Status"))
    remark = models.TextField(null=True, blank=True, verbose_name=_("Remark"))
    acted_at = models.DateTimeField(default=timezone.now, verbose_name=_("Acted At"))

    class Meta:
        ordering = ["-acted_at", "-id"]
        verbose_name = _("Attendance Action Audit Log")
        verbose_name_plural = _("Attendance Action Audit Logs")

    def __str__(self):
        target = self.work_mode_request or self.attendance
        return f"{self.action_type} - {target}"


class Attendance(HorillaModel):
    """
    Attendance model
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
    status = [
        ("create_request", _("Create Request")),
        ("update_request", _("Update Request")),
        ("revalidate_request", _("Re-validate Request")),
        ("revoke_request", _("Revoke Request")),
        ("cancel_request", _("Cancel Request")),
        ("reject_request", _("Reject Request")),
    ]

    employee_id = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        null=True,
        related_name="employee_attendances",
        verbose_name=_("Employee"),
    )
    attendance_date = models.DateField(
        null=False,
        validators=[attendance_date_validate],
        verbose_name=_("Attendance date"),
    )
    shift_id = models.ForeignKey(
        EmployeeShift, on_delete=models.SET_NULL, null=True, verbose_name=_("Shift")
    )
    work_type_id = models.ForeignKey(
        WorkType,
        null=True,
        blank=True,
        on_delete=models.SET_NULL,  # 796
        verbose_name=_("Work Type"),
    )
    attendance_day = models.ForeignKey(
        EmployeeShiftDay,
        on_delete=models.DO_NOTHING,
        null=True,
        verbose_name=_("Attendance day"),
    )
    attendance_clock_in_date = models.DateField(
        null=True, verbose_name=_("Check-In Date")
    )
    attendance_clock_in = models.TimeField(
        null=True, verbose_name=_("Check-In"), help_text=_("First Check-In Time")
    )
    attendance_clock_in_channel = models.CharField(
        max_length=32,
        null=True,
        blank=True,
        choices=AttendanceChannel.choices,
        verbose_name=_("Check-In Source"),
    )
    attendance_clock_in_punch = models.ForeignKey(
        "attendance.AttendancePunchingHistory",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="linked_attendance_clock_ins",
        verbose_name=_("Linked Check-In Punch"),
    )
    attendance_clock_out_date = models.DateField(
        null=True, verbose_name=_("Check-Out Date")
    )
    attendance_clock_out = models.TimeField(
        null=True, verbose_name=_("Check-Out"), help_text=_("Last Check-Out Time")
    )
    attendance_clock_out_channel = models.CharField(
        max_length=32,
        null=True,
        blank=True,
        choices=AttendanceChannel.choices,
        verbose_name=_("Check-Out Source"),
    )
    attendance_clock_out_punch = models.ForeignKey(
        "attendance.AttendancePunchingHistory",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="linked_attendance_clock_outs",
        verbose_name=_("Linked Check-Out Punch"),
    )
    attendance_worked_hour = models.CharField(
        null=True,
        default="00:00",
        max_length=10,
        validators=[validate_time_format],
        verbose_name=_("Worked Hours"),
    )
    minimum_hour = models.CharField(
        max_length=10,
        default="00:00",
        validators=[validate_time_format],
        verbose_name=_("Minimum hour"),
    )
    batch_attendance_id = models.ForeignKey(
        BatchAttendance,
        null=True,
        blank=True,
        on_delete=models.PROTECT,
        verbose_name=_("Batch Attendance"),
    )
    attendance_overtime = models.CharField(
        default="00:00",
        validators=[validate_time_format],
        max_length=10,
        verbose_name=_("Overtime"),
    )
    attendance_overtime_approve = models.BooleanField(
        default=False, verbose_name=_("Overtime Approve")
    )
    attendance_validated = models.BooleanField(
        default=False, verbose_name=_("Attendance Validate")
    )
    at_work_second = models.IntegerField(null=True, blank=True)
    overtime_second = models.IntegerField(
        null=True, blank=True, verbose_name=_("Overtime In Second")
    )
    approved_overtime_second = models.IntegerField(default=0)
    is_validate_request = models.BooleanField(
        default=False, verbose_name=_("Is validate request")
    )
    is_bulk_request = models.BooleanField(default=False, editable=False)
    is_validate_request_approved = models.BooleanField(
        default=False, verbose_name=_("Is validate request approved")
    )
    request_description = models.TextField(
        null=True, verbose_name=_("Request Description")
    )
    request_type = models.CharField(
        max_length=18, null=True, choices=status, default="update_request"
    )
    is_holiday = models.BooleanField(default=False)
    requested_data = models.JSONField(null=True, editable=False)
    request_attachments = models.ManyToManyField(
        "AttendanceRequestFile",
        blank=True,
        related_name="attendance_requests",
    )
    request_restore_snapshot = models.JSONField(
        null=True,
        blank=True,
        editable=False,
        verbose_name=_("Request Restore Snapshot"),
    )
    action_by = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        null=True,
        blank=True,
        related_name="attendance_request_actions",
        verbose_name=_("Action By"),
        editable=False,
    )
    action_at = models.DateTimeField(null=True, blank=True, verbose_name=_("Action At"))
    action_type = models.CharField(
        max_length=16,
        null=True,
        blank=True,
        choices=AttendanceRequestActionType.choices,
        verbose_name=_("Action Type"),
        editable=False,
    )
    objects = HorillaCompanyManager(
        related_company_field="employee_id__employee_work_info__company_id"
    )
    history = HorillaAuditLog(
        related_name="history_set",
        bases=[
            HorillaAuditInfo,
        ],
    )
    attendance_clock_in_image = models.ImageField(upload_to=upload_path, null=True, blank=True)
    attendance_clock_out_image = models.ImageField(upload_to=upload_path, null=True, blank=True)

    # Hybrid work mode + audit data
    attendance_clock_in_mode = models.CharField(
        max_length=20,
        null=True,
        blank=True,
        choices=AttendanceWorkMode.choices,
        default=AttendanceWorkMode.WFO,
        verbose_name=_("Check-In Mode"),
    )
    attendance_clock_out_mode = models.CharField(
        max_length=20,
        null=True,
        blank=True,
        choices=AttendanceWorkMode.choices,
        default=AttendanceWorkMode.WFO,
        verbose_name=_("Check-Out Mode"),
    )

    # Audit status per punch (Option B)
    in_attendance_status = models.CharField(
        max_length=16,
        null=True,
        blank=True,
        choices=AttendancePunchStatus.choices,
        verbose_name=_("IN Attendance Status"),
    )
    out_attendance_status = models.CharField(
        max_length=16,
        null=True,
        blank=True,
        choices=AttendancePunchStatus.choices,
        verbose_name=_("OUT Attendance Status"),
    )

    in_attendance_reject_reason_code = models.CharField(
        max_length=64,
        null=True,
        blank=True,
        choices=WorkModeRequestRejectReasonCode.choices,
        verbose_name=_("IN Reject Reason Code"),
    )
    out_attendance_reject_reason_code = models.CharField(
        max_length=64,
        null=True,
        blank=True,
        choices=WorkModeRequestRejectReasonCode.choices,
        verbose_name=_("OUT Reject Reason Code"),
    )

    # Related request IDs used for punch decisions (per IN/OUT)
    in_related_work_type_request_id = models.IntegerField(null=True, blank=True)
    out_related_work_type_request_id = models.IntegerField(null=True, blank=True)

    attendance_clock_in_location = models.JSONField(
        null=True, blank=True, verbose_name=_("Check-In Location")
    )
    attendance_clock_out_location = models.JSONField(
        null=True, blank=True, verbose_name=_("Check-Out Location")
    )

    # Final verified On Duty attendances are presence-only; provisional/request-only
    # On Duty still follows normal attendance calculation until document verification.
    is_presensi_only = models.BooleanField(
        default=False,
        verbose_name=_("Presence Only"),
        help_text=_("If enabled, worked hours and overtime are not calculated for this attendance."),
    )

    # Which work-mode request applied to this attendance (if any).
    work_mode_request_id = models.ForeignKey(
        "attendance.WorkModeRequest",
        on_delete=models.SET_NULL,
        null=True,
        blank=True,
        related_name="attendances",
        verbose_name=_("Work Mode Request"),
    )
    reconciliation_source = models.CharField(max_length=64, null=True, blank=True, verbose_name=_("Final Source"))
    reconciliation_note = models.CharField(max_length=255, null=True, blank=True, verbose_name=_("Final Note"))
    late_minutes = models.PositiveIntegerField(default=0, verbose_name=_("Late Minutes"))
    early_out_minutes = models.PositiveIntegerField(default=0, verbose_name=_("Early Out Minutes"))

    class Meta:
        """
        Meta class to add some additional options
        """

        unique_together = ("employee_id", "attendance_date")
        permissions = [
            ("change_validateattendance", "Validate Attendance"),
            ("change_approveovertime", "Change Approve Overtime"),
        ]
        ordering = [
            "-attendance_date",
            "employee_id__employee_first_name",
            "attendance_clock_in",
        ]
        verbose_name = _("Attendance")
        verbose_name_plural = _("Attendances")

    def check_min_ot(self):
        """
        Method to check the min ot for the attendance
        """

    def is_night_shift(self):
        """
        check is night shift or not
        """
        day = self.attendance_day
        if day is None:
            return False
        schedule = day.day_schedule.filter(shift_id=self.shift_id).first()
        if not schedule:
            return False
        return schedule.is_night_shift

    def __str__(self) -> str:
        return f"{self.employee_id.employee_first_name} \
            {self.employee_id.employee_last_name} - {self.attendance_date}"

    def activities(self):
        """
        This method is used to return the activites and count of activites comes for an attendance
        """
        activities = AttendanceActivity.objects.filter(
            attendance_date=self.attendance_date, employee_id=self.employee_id
        )
        return {"query": activities, "count": activities.count()}

    def requested_fields(self):
        """
        This method will returns the value difference fields
        """
        keys = []
        if self.requested_data is not None:
            from attendance.services.attendance_correction_scope_rules import load_requested_data
            data = load_requested_data(self.requested_data)
            diffs = get_diff_dict(self.serialize(), data)
            keys = diffs.keys()
        return keys

    def get_last_clock_out(self, null_activity=False):
        """
        This method is used to get the last attendance activity if exists
        """
        activities = AttendanceActivity.objects.filter(
            employee_id=self.employee_id,
            attendance_date=self.attendance_date,
            clock_out__isnull=null_activity,
        ).order_by("id")
        return activities.last()

    def get_at_work_from_activities(self):
        """
        This method is used to retun the at work calculated from the activities
        """
        activities = AttendanceActivity.objects.filter(
            attendance_date=self.attendance_date, employee_id=self.employee_id
        ).order_by("clock_in")
        at_work_seconds = 0
        now_dt = timezone.now()
        current_tz = timezone.get_current_timezone()
        use_tz = timezone.is_aware(now_dt)

        def normalize_dt(value, date_value=None, time_value=None):
            if value is None and date_value and time_value:
                value = datetime.combine(date_value, time_value)
            if value is None:
                return None
            if use_tz:
                if timezone.is_naive(value):
                    return timezone.make_aware(value, current_tz)
                return timezone.localtime(value, current_tz)
            if timezone.is_aware(value):
                return timezone.localtime(value, current_tz).replace(tzinfo=None)
            return value

        for activity in activities:
            in_dt = normalize_dt(
                getattr(activity, "in_datetime", None),
                getattr(activity, "clock_in_date", None),
                getattr(activity, "clock_in", None),
            )
            if in_dt is None:
                continue

            out_dt = normalize_dt(
                getattr(activity, "out_datetime", None),
                getattr(activity, "clock_out_date", None),
                getattr(activity, "clock_out", None),
            )
            if out_dt is None:
                out_dt = now_dt

            diffs = out_dt - in_dt
            at_work_seconds = at_work_seconds + max(0, diffs.total_seconds())
        return at_work_seconds

    def hours_pending(self):
        """
        This method will returns difference between minimum_hour and attendance_worked_hour
        """
        minimum_hours = strtime_seconds(self.minimum_hour)
        worked_hour = strtime_seconds(self.attendance_worked_hour)
        pending_seconds = minimum_hours - worked_hour
        if pending_seconds < 0:
            return "00:00"
        pending_hours = format_time(pending_seconds)
        return pending_hours

    def adjust_minimum_hour(self):
        """
        Set minimum_hour to 00:00 if the attendance date falls on a holiday or company leave.
        """
        if is_holiday(self.attendance_date) or is_company_leave(self.attendance_date):
            self.minimum_hour = "00:00"
            self.is_holiday = True

    def update_attendance_overtime(self):
        """
        Calculate and update attendance overtime and worked seconds.
        """
        self.attendance_overtime = format_time(
            max(
                0,
                (
                    strtime_seconds(self.attendance_worked_hour)
                    - strtime_seconds(self.minimum_hour)
                ),
            )
        )
        self.at_work_second = strtime_seconds(self.attendance_worked_hour)
        self.overtime_second = strtime_seconds(self.attendance_overtime)

    def handle_overtime_conditions(self):
        condition = AttendanceValidationCondition.objects.first()
        if self.is_validate_request:
            self.is_validate_request_approved = self.attendance_validated = False

        if condition:
            # Handle overtime cutoff
            if condition.overtime_cutoff:
                cutoff_seconds = strtime_seconds(condition.overtime_cutoff)
                if self.overtime_second > cutoff_seconds:
                    self.overtime_second = cutoff_seconds
                    self.attendance_overtime = format_time(cutoff_seconds)

            # Auto-approve overtime if conditions are met
            if condition.auto_approve_ot and self.overtime_second >= strtime_seconds(
                condition.minimum_overtime_to_approve
            ):
                self.attendance_overtime_approve = True

    def save(self, *args, **kwargs):
        update_fields = kwargs.get("update_fields")
        if update_fields is not None and set(update_fields) == {"request_restore_snapshot"}:
            # Snapshot-only updates are lightweight metadata writes used to restore
            # attendance request overrides later. They must not trigger overtime/
            # worked-hour recalculation because core attendance facts did not change.
            return super().save(*args, **kwargs)

        if update_fields is not None:
            expanded_update_fields = set(update_fields)
            trigger_fields = {
                "attendance_clock_in",
                "attendance_clock_in_date",
                "attendance_clock_out",
                "attendance_clock_out_date",
                "attendance_worked_hour",
                "attendance_overtime",
                "minimum_hour",
                "is_presensi_only",
            }
            if expanded_update_fields & trigger_fields:
                expanded_update_fields.update(
                    {
                        "attendance_worked_hour",
                        "attendance_overtime",
                        "at_work_second",
                        "overtime_second",
                        "minimum_hour",
                        "attendance_day",
                    }
                )
                kwargs["update_fields"] = list(expanded_update_fields)
                update_fields = kwargs["update_fields"]

        compress_model_image_field(self, "attendance_clock_in_image")
        compress_model_image_field(self, "attendance_clock_out_image")
        if self.is_presensi_only:
            # Presence-only attendances (for example, final verified On Duty) must
            # not affect hour calculations.
            self.attendance_worked_hour = "00:00"
            self.minimum_hour = "00:00"

        self.update_attendance_overtime()
        self.attendance_day = EmployeeShiftDay.objects.get(
            day=self.attendance_date.strftime("%A").lower()
        )
        prev_attendance_approved = False
        self.adjust_minimum_hour()

        # Handle overtime cutoff and auto-approval
        self.handle_overtime_conditions()

        if self.pk is not None:
            # Get the previous values of the boolean field
            prev_state = Attendance.objects.get(pk=self.pk)
            prev_attendance_approved = prev_state.attendance_overtime_approve

        # super().save(*args, **kwargs)  #commend this line, it take too much time to complete
        employee_ot = self.employee_id.employee_overtime.filter(
            month=self.attendance_date.strftime("%B").lower(),
            year=self.attendance_date.year,
        ).first()
        if employee_ot:
            # Update if exists
            self.update_ot(employee_ot)
        else:
            # Create and update in one call
            employee_ot = self.create_ot()
            self.update_ot(employee_ot)
        approved = self.attendance_overtime_approve
        attendance_account = self.employee_id.employee_overtime.filter(
            month=self.attendance_date.strftime("%B").lower(),
            year=self.attendance_date.year,
        ).first()
        total_ot_seconds = attendance_account.overtime_second
        if approved and prev_attendance_approved is False:
            self.approved_overtime_second = self.overtime_second
            total_ot_seconds = total_ot_seconds + self.approved_overtime_second
        elif not approved:
            total_ot_seconds = total_ot_seconds - self.approved_overtime_second
            self.approved_overtime_second = 0
        attendance_account.overtime = format_time(total_ot_seconds)
        attendance_account.save()
        super().save(*args, **kwargs)

    def serialize(self):
        """
        Used to serialize attendance instance
        """
        # Return a dictionary containing the data you want to store
        # strftime("%d %b %Y") date
        # strftime("%I:%M %p") time
        serialized_data = {
            "employee_id": self.employee_id.id,
            "attendance_date": str(self.attendance_date),
            "attendance_clock_in_date": str(self.attendance_clock_in_date),
            "attendance_clock_in": str(self.attendance_clock_in),
            "attendance_clock_out": str(self.attendance_clock_out),
            "attendance_clock_out_date": str(self.attendance_clock_out_date),
            "attendance_clock_in_mode": self.attendance_clock_in_mode,
            "attendance_clock_out_mode": self.attendance_clock_out_mode,
            "attendance_clock_in_location": self.attendance_clock_in_location,
            "attendance_clock_out_location": self.attendance_clock_out_location,
            "is_presensi_only": self.is_presensi_only,
            "work_mode_request_id": self.work_mode_request_id.id if self.work_mode_request_id else "",
            "shift_id": self.shift_id.id if self.shift_id else "",
            "work_type_id": self.work_type_id.id if self.work_type_id else "",
            "attendance_worked_hour": self.attendance_worked_hour,
            "minimum_hour": self.minimum_hour,
            "batch_attendance_id": (
                self.batch_attendance_id.id if self.batch_attendance_id else ""
            ),
            # Add other fields you want to store
        }
        return serialized_data

    def delete(self, *args, **kwargs):
        # Custom delete logic
        # Perform additional operations before deleting the object
        with contextlib.suppress(Exception):
            AttendanceActivity.objects.filter(
                attendance_date=self.attendance_date, employee_id=self.employee_id
            ).delete()
            employee_ot = self.employee_id.employee_overtime.filter(
                month=self.attendance_date.strftime("%B").lower(),
                year=self.attendance_date.strftime("%Y"),
            )
        if employee_ot.exists():
            self.update_ot(employee_ot.first())
        # Call the superclass delete() method to delete the object
        super().delete(*args, **kwargs)

        # Perform additional operations after deleting the object

    def create_ot(self):
        """
        Create a new Hour Account instance if it doesn't exist for a specific month and year.
        Returns:
            AttendanceOverTime: The created or fetched AttendanceOverTime instance.
        """
        # Create or fetch the AttendanceOverTime instance
        employee_ot, created = AttendanceOverTime.objects.get_or_create(
            employee_id=self.employee_id,
            month=self.attendance_date.strftime("%B").lower(),
            year=self.attendance_date.year,
        )

        # Update only if the fields are available
        if self.attendance_overtime_approve:
            employee_ot.overtime = self.attendance_overtime

        if self.attendance_validated:
            employee_ot.hour_account = self.attendance_worked_hour

        employee_ot.save()
        return employee_ot

    def update_ot(self, employee_ot):
        """
        Update the hour account for the given employee.

        Args:
            employee_ot (obj): AttendanceOverTime instance
        """
        if apps.is_installed("leave"):
            approved_leave_requests = self.employee_id.leaverequest_set.filter(
                start_date__lte=self.attendance_date,
                end_date__gte=self.attendance_date,
                status="approved",
            )
        else:
            approved_leave_requests = []

        # Create exclude condition using Q objects
        exclude_condition = Q()
        if approved_leave_requests:
            # Combine multiple conditions for the exclude clause
            for leave in approved_leave_requests:
                exclude_condition |= Q(
                    attendance_date__range=(leave.start_date, leave.end_date)
                )

        # Filter month attendances in a single query
        month_attendances = (
            Attendance.objects.filter(
                employee_id=self.employee_id,
                attendance_date__month=self.attendance_date.month,
                attendance_date__year=self.attendance_date.year,
                attendance_validated=True,
            )
            .exclude(exclude_condition)
            .values("minimum_hour", "at_work_second")
        )

        # Calculate hour balance and hours pending in a single loop
        hour_balance = 0
        minimum_hour_second = 0
        for attendance in month_attendances:
            required_work_second = strtime_seconds(attendance["minimum_hour"])
            at_work_second = min(required_work_second, attendance["at_work_second"])
            hour_balance += at_work_second
            minimum_hour_second += required_work_second

        hours_pending = minimum_hour_second - hour_balance
        employee_ot.worked_hours = format_time(hour_balance)
        employee_ot.pending_hours = format_time(hours_pending)
        employee_ot.save()

        return employee_ot

    def clean(self, *args, **kwargs):
        super().clean(*args, **kwargs)
        now = datetime.now().time()
        today = datetime.today().date()

        # Convert to time if it's a string
        if isinstance(self.attendance_clock_out, str):
            out_time = datetime.strptime(self.attendance_clock_out, "%H:%M:%S").time()
        else:
            out_time = self.attendance_clock_out

        if self.attendance_clock_in_date and self.attendance_date and self.attendance_clock_in_date < self.attendance_date:
            raise ValidationError(
                {
                    "attendance_clock_in_date": "Attendance check-in date cannot be earlier than attendance date"
                }
            )

        if (
            self.attendance_clock_out_date
            and self.attendance_clock_in_date
            and self.attendance_clock_out_date < self.attendance_clock_in_date
        ):
            raise ValidationError(
                {
                    "attendance_clock_out_date": "Attendance check-out date cannot be earlier than check-in date"
                }
            )

        if self.attendance_clock_out_date and self.attendance_clock_out_date >= today and out_time is not None:
            if out_time > now:
                raise ValidationError(
                    {"attendance_clock_out": "Check-out time cannot be in the future"}
                )


class AttendanceRequestFile(HorillaModel):
    file = models.FileField(upload_to=upload_path)


class AttendanceRequestComment(HorillaModel):
    """
    AttendanceRequestComment Model
    """

    request_id = models.ForeignKey(Attendance, on_delete=models.CASCADE)
    employee_id = models.ForeignKey(Employee, on_delete=models.CASCADE)
    files = models.ManyToManyField(AttendanceRequestFile, blank=True)
    comment = models.TextField(null=True, verbose_name=_("Comment"), max_length=255)

    def __str__(self) -> str:
        return f"{self.comment}"


class AttendanceOverTime(HorillaModel):
    """
    AttendanceOverTime model
    """

    employee_id = models.ForeignKey(
        Employee,
        on_delete=models.PROTECT,
        related_name="employee_overtime",
        verbose_name=_("Employee"),
    )
    month = models.CharField(
        max_length=10,
        verbose_name=_("Month"),
    )
    month_sequence = models.PositiveSmallIntegerField(default=0)
    year = models.CharField(
        default=datetime.now().strftime("%Y"),
        null=True,
        max_length=10,
        verbose_name=_("Year"),
    )
    worked_hours = models.CharField(
        max_length=10,
        default="00:00",
        null=True,
        validators=[validate_time_format],
        verbose_name=_("Worked Hours"),
    )
    pending_hours = models.CharField(
        max_length=10,
        default="00:00",
        null=True,
        validators=[validate_time_format],
        verbose_name=_("Pending Hours"),
    )
    overtime = models.CharField(
        max_length=20,
        default="00:00",
        validators=[validate_time_format],
        verbose_name=_("Overtime Hours"),
    )
    hour_account_second = models.IntegerField(
        default=0,
        null=True,
        verbose_name=_("Worked Seconds"),
    )
    hour_pending_second = models.IntegerField(
        default=0,
        null=True,
        verbose_name=_("Pending Seconds"),
    )
    overtime_second = models.IntegerField(
        default=0,
        null=True,
        verbose_name=_("Overtime Seconds"),
    )
    objects = HorillaCompanyManager(
        related_company_field="employee_id__employee_work_info__company_id"
    )

    class Meta:
        """
        Meta class to add some additional options
        """

        unique_together = [("employee_id"), ("month"), ("year")]
        ordering = ["-year", "-month_sequence"]
        verbose_name = _("Hour Account")
        verbose_name_plural = _("Hour Accounts")

    def clean(self):
        try:
            year = int(self.year)
            if not (1900 <= year <= 2100):
                raise ValidationError(
                    {"year": _("Year must be an integer value between 1900 and 2100")}
                )
        except (ValueError, TypeError):
            raise ValidationError(
                {"year": _("Year must be an integer value between 1900 and 2100")}
            )

    def month_days(self):
        """
        this method is used to create new AttendanceOvertime's instance if there
        is no existing for a specific month and year
        """
        month = self.month_sequence + 1
        year = int(self.year)
        start_date = date(year, month, 1)
        if month == 12:
            end_date = date(year + 1, 1, 1) - timedelta(days=1)
        else:
            end_date = date(year, month + 1, 1) - timedelta(days=1)
        return start_date, end_date

    def not_validated_hrs(self):
        """
        This method will return not validated hours in a month
        """
        hrs_to_vlaidate = sum(
            list(
                Attendance.objects.filter(
                    attendance_date__month=MONTH_MAPPING[self.month],
                    attendance_date__year=self.year,
                    employee_id=self.employee_id,
                    attendance_validated=False,
                ).values_list("at_work_second", flat=True)
            )
        )
        return format_time(hrs_to_vlaidate)

    def not_approved_ot_hrs(self):
        """
        This method will return the overtime hours to be approved
        """
        hrs_to_approve = sum(
            list(
                Attendance.objects.filter(
                    attendance_date__month=MONTH_MAPPING[self.month],
                    attendance_date__year=self.year,
                    employee_id=self.employee_id,
                    attendance_validated=True,
                    attendance_overtime_approve=False,
                ).values_list("overtime_second", flat=True)
            )
        )
        return format_time(hrs_to_approve)

    def get_month_index(self):
        """
        This method will return the index of the month
        """
        return MONTH_MAPPING[self.month]

    def save(self, *args, **kwargs):
        self.hour_account_second = strtime_seconds(self.worked_hours)
        self.hour_pending_second = strtime_seconds(self.pending_hours)
        self.overtime_second = strtime_seconds(self.overtime)
        month_name = self.month.split("-")[0]
        months = [
            "january",
            "february",
            "march",
            "april",
            "may",
            "june",
            "july",
            "august",
            "september",
            "october",
            "november",
            "december",
        ]
        self.month_sequence = months.index(month_name)
        super().save(*args, **kwargs)


class AttendanceLateComeEarlyOut(HorillaModel):
    """
    AttendanceLateComeEarlyOut model
    """

    choices = [
        ("late_come", _("Late Come")),
        ("early_out", _("Early Out")),
    ]

    attendance_id = models.ForeignKey(
        Attendance,
        on_delete=models.PROTECT,
        related_name="late_come_early_out",
        verbose_name=_("Attendance"),
    )
    employee_id = models.ForeignKey(
        Employee,
        on_delete=models.DO_NOTHING,
        null=True,
        related_name="late_come_early_out",
        verbose_name=_("Employee"),
        editable=False,
    )
    type = models.CharField(max_length=20, choices=choices, verbose_name=_("Type"))
    objects = HorillaCompanyManager(
        related_company_field="employee_id__employee_work_info__company_id"
    )
    created_at = models.DateTimeField(auto_now_add=True, null=True)

    def get_penalties_count(self):
        """
        This method is used to return the total penalties in the late early instance
        """
        return self.penaltyaccounts_set.count()

    def save(self, *args, **kwargs) -> None:
        if self.attendance_id_id:
            self.employee_id = self.attendance_id.employee_id
        super().save(*args, **kwargs)

    class Meta:
        """
        Meta class to add some additional options
        """

        unique_together = [("attendance_id"), ("type")]
        ordering = ["-attendance_id__attendance_date"]

    def __str__(self) -> str:
        return f"{self.attendance_id.employee_id.employee_first_name} \
            {self.attendance_id.employee_id.employee_last_name} - {self.type}"


class AttendanceValidationCondition(HorillaModel):
    """
    AttendanceValidationCondition model
    """

    validation_at_work = models.CharField(
        max_length=10,
        validators=[validate_time_format],
        verbose_name=_("Worked Hours Auto Approve Till"),
    )
    minimum_overtime_to_approve = models.CharField(
        blank=True, null=True, max_length=10, validators=[validate_time_format]
    )
    overtime_cutoff = models.CharField(
        blank=True, null=True, max_length=10, validators=[validate_time_format]
    )
    auto_approve_ot = models.BooleanField(
        default=False, verbose_name=_("Auto Approve OT")
    )
    company_id = models.ManyToManyField(Company, blank=True, verbose_name=_("Company"))
    objects = HorillaCompanyManager()

    def clean(self):
        """
        This method is used to perform some custom validations
        """
        super().clean()
        if not self.id and AttendanceValidationCondition.objects.exists():
            raise ValidationError(_("You cannot add more conditions."))


class GraceTime(HorillaModel):
    """
    Model for saving Grace time
    """

    allowed_time = models.CharField(
        default="00:00:00",
        validators=[validate_hh_mm_ss_format],
        max_length=10,
        verbose_name=_("Allowed Time"),
    )
    allowed_time_in_secs = models.IntegerField()
    allowed_clock_in = models.BooleanField(
        default=True,
        help_text=_("Allcocate this grace time for Check-In Attendance"),
        verbose_name=_("Allowed Clock-In"),
    )
    allowed_clock_out = models.BooleanField(
        default=False,
        help_text=_("Allcocate this grace time for Check-Out Attendance"),
        verbose_name=_("Allowed Clock-Out"),
    )
    clock_in_type = models.CharField(
        max_length=24,
        choices=GraceClockInType.choices,
        default=GraceClockInType.AFTER,
        verbose_name=_("Clock-In Type"),
    )
    is_default = models.BooleanField(default=False)

    company_id = models.ManyToManyField(Company, blank=True, verbose_name=_("Company"))
    objects = HorillaCompanyManager()

    def __str__(self) -> str:
        return str(f"{self.allowed_time} - Hours")

    def clean(self):
        """
        This method is used to perform some custom validations
        """
        super().clean()
        if self.is_default:
            if GraceTime.objects.filter(is_default=True).exclude(id=self.id).exists():
                raise ValidationError(
                    _("There is already a default grace time that exists.")
                )

        allowed_time = self.allowed_time
        is_default = self.is_default
        exclude_default = not is_default

        if (
            GraceTime.objects.filter(allowed_time=allowed_time)
            .exclude(is_default=exclude_default)
            .exclude(id=self.id)
            .exists()
        ):
            raise ValidationError(
                {
                    "allowed_time": _(
                        "There is already an existing grace time with this allowed time."
                    )
                }
            )

    def save(self, *args, **kwargs):
        allowed_time = self.allowed_time
        hours, minutes, secs = allowed_time.split(":")

        hours_int = int(hours)
        minutes_int = int(minutes)
        secs_int = int(secs)

        hours_str = f"{hours_int:02d}"
        minutes_str = f"{minutes_int:02d}"
        secs_str = f"{secs_int:02d}"

        self.allowed_time = f"{hours_str}:{minutes_str}:{secs_str}"
        self.allowed_time_in_secs = hours_int * 3600 + minutes_int * 60 + secs_int
        super().save(*args, **kwargs)


class AttendanceGeneralSetting(HorillaModel):
    """
    AttendanceGeneralSettings
    """

    time_runner = models.BooleanField(default=True)
    enable_check_in = models.BooleanField(
        default=False,
        verbose_name=_("Enable Check in/Check out"),
        help_text=_(
            "Enabling this feature allows employees to record their attendance using the Check-In/Check-Out button."
        ),
    )
    allow_reporting_manager_attendance = models.BooleanField(
        default=False,
        verbose_name=_("Allow Reporting Manager Attendance"),
        help_text=_(
            "Allow employees who act as reporting managers to perform attendance actions."
        ),
    )
    allow_admin_attendance = models.BooleanField(
        default=False,
        verbose_name=_("Allow Admin Attendance"),
        help_text=_(
            "Allow admin users to perform attendance actions."
        ),
    )
    company_id = models.ForeignKey(Company, on_delete=models.CASCADE, null=True)
    objects = HorillaCompanyManager()

    def save(self, *args, **kwargs):
        """
        Lock web Check In/Check Out in disabled state.
        """
        self.enable_check_in = False
        super().save(*args, **kwargs)


class WorkRecords(models.Model):
    """
    WorkRecord Model
    """

    choices = [
        ("FDP", _("Present")),
        ("HDP", _("Half Day Present")),
        ("ABS", _("Absent")),
        ("HD", _("Holiday/Company Leave")),
        ("CONF", _("Conflict")),
        ("DFT", _("Draft")),
    ]

    record_name = models.CharField(max_length=250, null=True, blank=True)
    work_record_type = models.CharField(max_length=10, null=True, choices=choices)
    employee_id = models.ForeignKey(
        Employee, on_delete=models.CASCADE, verbose_name=_("Employee")
    )
    date = models.DateField(null=True, blank=True)
    at_work = models.CharField(
        null=True,
        blank=True,
        validators=[
            validate_time_format,
        ],
        default="00:00",
        max_length=10,
    )  # 841
    min_hour = models.CharField(
        null=True,
        blank=True,
        validators=[
            validate_time_format,
        ],
        default="00:00",
        max_length=10,
    )
    at_work_second = models.IntegerField(null=True, blank=True, default=0)
    min_hour_second = models.IntegerField(null=True, blank=True, default=0)
    note = models.TextField(max_length=255)
    message = models.CharField(max_length=30, null=True, blank=True)
    is_attendance_record = models.BooleanField(default=False)
    attendance_id = models.ForeignKey(
        Attendance, on_delete=models.SET_NULL, blank=True, null=True
    )
    is_leave_record = models.BooleanField(default=False)
    if apps.is_installed("leave"):
        leave_request_id = models.ForeignKey(
            "leave.LeaveRequest",
            on_delete=models.SET_NULL,
            blank=True,
            null=True,
        )
    shift_id = models.ForeignKey(
        EmployeeShift, on_delete=models.SET_NULL, blank=True, null=True
    )
    day_percentage = models.FloatField(default=0)
    last_update = models.DateTimeField(null=True, blank=True)
    objects = HorillaCompanyManager("employee_id__employee_work_info__company_id")

    def title_message(self):
        title_message = self.message
        if title_message == "Leave":
            if apps.is_installed("leave"):
                title_message += f" | {self.leave_request_id.leave_type_id}"
        return title_message

    def save(self, *args, **kwargs):
        self.last_update = timezone.now()

        super().save(*args, **kwargs)

    def clean(self):
        super().clean()
        if not 0.0 <= self.day_percentage <= 1.0:
            raise ValidationError(_("Day percentage must be between 0.0 and 1.0"))

    def __str__(self):
        return (
            self.record_name
            if self.record_name is not None
            else f"{self.work_record_type}-{self.date}-{self.employee_id}"
        )

    class Meta:
        verbose_name = _("Work Record")
        verbose_name_plural = _("Work Records")
        # unique_together = ['date', 'employee_id']
