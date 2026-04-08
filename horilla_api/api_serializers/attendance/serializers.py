import logging
from datetime import date
from django.utils import timezone as dj_timezone
from django.core.exceptions import ValidationError
from rest_framework import serializers

from attendance.models import *
from base.models import HorillaMailTemplate
from base.methods import get_subordinate_employee_ids

from attendance.services.work_type_request_rules import (
    coerce_work_type_payload,
    validate_work_type_request,
)
from attendance.services.work_type_request_exceptions import WorkModeRequestConsistencyError
from attendance.services.work_type_request_permissions import build_permission_flags

logger = logging.getLogger(__name__)
from attendance.services.attendance_request_files import (
    build_attachment_metadata as build_attendance_attachment_metadata,
    build_attachment_url as build_attendance_attachment_url,
)
from attendance.services.work_type_request_files import (
    build_attachment_metadata as build_work_mode_attachment_metadata,
    build_attachment_url as build_work_mode_attachment_url,
)
from attendance.services.attendance_request_presentation import (
    build_attendance_request_time_surface,
)
from attendance.services.attendance_correction_requests import build_permission_flags as build_attendance_correction_permission_flags
from horilla_api.utils.private_media_urls import build_employee_profile_api_url


class AttendanceSerializer(serializers.ModelSerializer):
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    shift_name = serializers.CharField(source="shift_id.employee_shift", read_only=True)
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_profile_url = serializers.SerializerMethodField(read_only=True)
    # Direct attachments uploaded on the attendance request
    attachments = serializers.SerializerMethodField(read_only=True)
    attachment_urls = serializers.SerializerMethodField(read_only=True)
    # Alias for UI parity with Work Type Requests
    file_urls = serializers.SerializerMethodField(read_only=True)

    # Status label for mobile UI (WAITING / APPROVED / REJECTED / CANCEL)
    status = serializers.SerializerMethodField(read_only=True)
    request_status = serializers.SerializerMethodField(read_only=True)
    action_by_name = serializers.SerializerMethodField(read_only=True)

    work_type = serializers.CharField(source="work_type_id.work_type", read_only=True)

    class Meta:
        model = Attendance
        exclude = [
            "overtime_second",
            "at_work_second",
            "attendance_day",
            "request_description",
            "approved_overtime_second",
            "request_type",
            "requested_data",
            "is_validate_request",
            "is_validate_request_approved",
            "attendance_overtime",
        ]

    def validate(self, data):
        # Check if attendance exists for the employee on the current date
        if self.instance:
            return data
        employee_id = data.get("employee_id")
        attendance_date = data.get("attendance_date", date.today())
        if Attendance.objects.filter(
            employee_id=employee_id, attendance_date=attendance_date
        ).exists():
            raise ValidationError(
                ("Attendance for this employee on the current date already exists.")
            )
        return data

    def get_attachments(self, obj):
        try:
            from attendance.services.attendance_request_access import iter_request_attachments
            request = self.context.get("request") if hasattr(self, "context") else None
            attachments = []
            for f in iter_request_attachments(obj):
                try:
                    attachments.append(
                        build_attendance_attachment_metadata(
                            request,
                            obj,
                            f,
                            include_delete_url=False,
                        )
                    )
                except Exception:
                    continue
            return attachments
        except Exception:
            return []

    def get_attachment_urls(self, obj):
        return [item.get("url") for item in self.get_attachments(obj) if item.get("url")]

    def get_file_urls(self, obj):
        # Backward/UX compatibility with WorkModeRequestSerializer
        return self.get_attachment_urls(obj)

    def get_employee_profile_url(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(getattr(obj, "employee_id", None), request=request)


class AttendanceRequestSerializer(serializers.ModelSerializer):
    """Compatibility serializer for legacy Attendance-backed request rows.

    This serializer intentionally supports both the new
    ``AttendanceCorrectionRequest`` entity and legacy ``Attendance`` request rows
    so older endpoints/tests can keep working during cleanup. New correction
    endpoints should prefer ``AttendanceCorrectionRequestSerializer``.
    """
    employee_first_name = serializers.CharField(source="employee_id.employee_first_name", read_only=True)
    employee_last_name = serializers.CharField(source="employee_id.employee_last_name", read_only=True)
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_profile_url = serializers.SerializerMethodField(read_only=True)
    reason = serializers.SerializerMethodField(read_only=True)
    request_description = serializers.SerializerMethodField(read_only=True)
    status = serializers.SerializerMethodField(read_only=True)
    request_status = serializers.SerializerMethodField(read_only=True)
    action_by_name = serializers.SerializerMethodField(read_only=True)
    attachments = serializers.SerializerMethodField(read_only=True)
    attachment_urls = serializers.SerializerMethodField(read_only=True)
    file_urls = serializers.SerializerMethodField(read_only=True)
    proposed_attendance_clock_in = serializers.SerializerMethodField(read_only=True)
    proposed_attendance_clock_out = serializers.SerializerMethodField(read_only=True)
    proposed_attendance_clock_in_date = serializers.SerializerMethodField(read_only=True)
    proposed_attendance_clock_out_date = serializers.SerializerMethodField(read_only=True)
    final_attendance_clock_in = serializers.SerializerMethodField(read_only=True)
    final_attendance_clock_out = serializers.SerializerMethodField(read_only=True)
    final_attendance_clock_in_date = serializers.SerializerMethodField(read_only=True)
    final_attendance_clock_out_date = serializers.SerializerMethodField(read_only=True)
    effective_attendance_clock_in = serializers.SerializerMethodField(read_only=True)
    effective_attendance_clock_out = serializers.SerializerMethodField(read_only=True)
    effective_attendance_clock_in_date = serializers.SerializerMethodField(read_only=True)
    effective_attendance_clock_out_date = serializers.SerializerMethodField(read_only=True)
    can_edit = serializers.SerializerMethodField(read_only=True)
    can_cancel = serializers.SerializerMethodField(read_only=True)
    can_approve = serializers.SerializerMethodField(read_only=True)
    can_reject = serializers.SerializerMethodField(read_only=True)
    can_revoke = serializers.SerializerMethodField(read_only=True)

    class Meta:
        model = AttendanceCorrectionRequest
        fields = [
            "id", "employee_id", "employee_first_name", "employee_last_name", "badge_id",
            "employee_profile_url", "attendance_date", "scope",
            "requested_check_in_date", "requested_check_in_time",
            "requested_check_out_date", "requested_check_out_time",
            "reason", "request_description", "status", "request_status",
            "action_reason", "action_type", "action_at", "approved_at", "rejected_at", "revoked_at", "canceled_at",
            "action_by_name", "attachments", "attachment_urls", "file_urls",
            "proposed_attendance_clock_in", "proposed_attendance_clock_out",
            "proposed_attendance_clock_in_date", "proposed_attendance_clock_out_date",
            "final_attendance_clock_in", "final_attendance_clock_out",
            "final_attendance_clock_in_date", "final_attendance_clock_out_date",
            "effective_attendance_clock_in", "effective_attendance_clock_out",
            "effective_attendance_clock_in_date", "effective_attendance_clock_out_date",
            "can_edit", "can_cancel", "can_approve", "can_reject", "can_revoke",
        ]

    def _is_legacy_attendance(self, obj):
        return isinstance(obj, Attendance) or getattr(obj, "requested_data", None) is not None

    def _requested_payload(self, obj):
        if self._is_legacy_attendance(obj):
            try:
                from attendance.services.attendance_correction_scope_rules import load_requested_data
                return load_requested_data(getattr(obj, "requested_data", None))
            except Exception:
                return {}
        return {}

    def _fmt_time(self, value):
        try:
            if value is None or value == "":
                return None
            if hasattr(value, "strftime"):
                return value.strftime("%H:%M")
            text = str(value).strip()
            return text[:5] if len(text) >= 5 and text[2:3] == ":" else text
        except Exception:
            return value

    def _fmt_date(self, value):
        try:
            if value is None or value == "":
                return None
            if hasattr(value, "strftime"):
                return value.strftime("%Y-%m-%d")
            text = str(value).strip()
            return text[:10] if len(text) >= 10 else text
        except Exception:
            return value

    def _final_attendance(self, obj):
        if self._is_legacy_attendance(obj):
            return obj
        return Attendance.objects.filter(employee_id=obj.employee_id, attendance_date=obj.attendance_date).first()

    def get_reason(self, obj):
        return getattr(obj, "reason", None) or getattr(obj, "request_description", None)

    def get_request_description(self, obj):
        return self.get_reason(obj)

    def get_status(self, obj):
        status = getattr(obj, "status", None)
        if isinstance(status, (list, tuple, dict, set)):
            status = None
        if status:
            return status
        action = getattr(obj, "action_type", None)
        mapping = {
            AttendanceRequestActionType.APPROVED: "APPROVED",
            AttendanceRequestActionType.REJECTED: "REJECTED",
            AttendanceRequestActionType.REVOKED: "REVOKED",
            AttendanceRequestActionType.CANCELED: "CANCELED",
        }
        if action in mapping:
            return mapping[action]
        if getattr(obj, "is_validate_request", False):
            return "WAITING"
        if getattr(obj, "is_validate_request_approved", False):
            return "APPROVED"
        req_type = (getattr(obj, "request_type", None) or "").strip().lower()
        mapping2 = {"cancel_request": "CANCELED", "revoke_request": "REVOKED", "reject_request": "REJECTED"}
        return mapping2.get(req_type, req_type.upper() or None)

    def get_request_status(self, obj):
        return self.get_status(obj)

    def get_action_type(self, obj):
        action = getattr(obj, "action_type", None)
        if action:
            return str(action)
        status_value = self.get_status(obj)
        return status_value

    def get_employee_profile_url(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(getattr(obj, "employee_id", None), request=request)

    def get_action_by_name(self, obj):
        try:
            return obj.action_actor_display
        except Exception:
            actor = getattr(obj, "action_by", None)
            if actor is None:
                return None
            try:
                return f"{actor.employee_first_name} {actor.employee_last_name}".strip() or str(actor)
            except Exception:
                return str(actor)

    def get_attachments(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        out = []
        try:
            from attendance.services.attendance_request_access import iter_request_attachments
            file_iter = iter_request_attachments(obj)
        except Exception:
            file_iter = []
        for file_obj in file_iter:
            if not file_obj:
                continue
            try:
                out.append(build_attendance_attachment_metadata(request, obj, file_obj, include_delete_url=False))
            except Exception:
                continue
        return out

    def get_attachment_urls(self, obj):
        return [item.get("url") for item in self.get_attachments(obj) if item.get("url")]

    def get_file_urls(self, obj):
        return self.get_attachment_urls(obj)

    def get_proposed_attendance_clock_in(self, obj):
        if self._is_legacy_attendance(obj):
            return self._fmt_time(self._requested_payload(obj).get("attendance_clock_in"))
        return self._fmt_time(obj.requested_check_in_time)

    def get_proposed_attendance_clock_out(self, obj):
        if self._is_legacy_attendance(obj):
            return self._fmt_time(self._requested_payload(obj).get("attendance_clock_out"))
        return self._fmt_time(obj.requested_check_out_time)

    def get_proposed_attendance_clock_in_date(self, obj):
        if self._is_legacy_attendance(obj):
            return self._fmt_date(self._requested_payload(obj).get("attendance_clock_in_date"))
        return self._fmt_date(obj.requested_check_in_date)

    def get_proposed_attendance_clock_out_date(self, obj):
        if self._is_legacy_attendance(obj):
            return self._fmt_date(self._requested_payload(obj).get("attendance_clock_out_date"))
        return self._fmt_date(obj.requested_check_out_date)

    def get_final_attendance_clock_in(self, obj):
        att = self._final_attendance(obj)
        return self._fmt_time(getattr(att, "attendance_clock_in", None))

    def get_final_attendance_clock_out(self, obj):
        att = self._final_attendance(obj)
        return self._fmt_time(getattr(att, "attendance_clock_out", None))

    def get_final_attendance_clock_in_date(self, obj):
        att = self._final_attendance(obj)
        return self._fmt_date(getattr(att, "attendance_clock_in_date", None))

    def get_final_attendance_clock_out_date(self, obj):
        att = self._final_attendance(obj)
        return self._fmt_date(getattr(att, "attendance_clock_out_date", None))

    def get_effective_attendance_clock_in(self, obj):
        if self._is_legacy_attendance(obj):
            return self.get_proposed_attendance_clock_in(obj) or self.get_final_attendance_clock_in(obj)
        if getattr(obj, "status", None) == AttendanceCorrectionRequestStatus.APPROVED and obj.requested_check_in_time:
            return self._fmt_time(obj.requested_check_in_time)
        return self.get_final_attendance_clock_in(obj)

    def get_effective_attendance_clock_out(self, obj):
        if self._is_legacy_attendance(obj):
            return self.get_proposed_attendance_clock_out(obj) or self.get_final_attendance_clock_out(obj)
        if getattr(obj, "status", None) == AttendanceCorrectionRequestStatus.APPROVED and obj.requested_check_out_time:
            return self._fmt_time(obj.requested_check_out_time)
        return self.get_final_attendance_clock_out(obj)

    def get_effective_attendance_clock_in_date(self, obj):
        if self._is_legacy_attendance(obj):
            return self.get_proposed_attendance_clock_in_date(obj) or self.get_final_attendance_clock_in_date(obj)
        if getattr(obj, "status", None) == AttendanceCorrectionRequestStatus.APPROVED and obj.requested_check_in_date:
            return self._fmt_date(obj.requested_check_in_date)
        return self.get_final_attendance_clock_in_date(obj)

    def get_effective_attendance_clock_out_date(self, obj):
        if self._is_legacy_attendance(obj):
            return self.get_proposed_attendance_clock_out_date(obj) or self.get_final_attendance_clock_out_date(obj)
        if getattr(obj, "status", None) == AttendanceCorrectionRequestStatus.APPROVED and obj.requested_check_out_date:
            return self._fmt_date(obj.requested_check_out_date)
        return self.get_final_attendance_clock_out_date(obj)

    def _perm(self, obj, key):
        request = self.context.get("request") if hasattr(self, "context") else None
        user = getattr(request, "user", None)
        if self._is_legacy_attendance(obj):
            try:
                from attendance.services.attendance_request_access import user_can_approve_request as legacy_can_approve, user_is_request_owner as legacy_is_owner
                is_owner = legacy_is_owner(user, obj)
                can_approve = legacy_can_approve(user, obj) and bool(getattr(obj, "is_validate_request", False))
                flags = {
                    "can_edit": bool(is_owner and getattr(obj, "is_validate_request", False) and not getattr(obj, "is_validate_request_approved", False)),
                    "can_cancel": bool(is_owner and getattr(obj, "is_validate_request", False) and not getattr(obj, "is_validate_request_approved", False)),
                    "can_approve": bool(can_approve),
                    "can_reject": bool(can_approve),
                    "can_revoke": bool(legacy_can_approve(user, obj) and getattr(obj, "is_validate_request_approved", False)),
                }
            except Exception:
                flags = {}
        else:
            flags = build_attendance_correction_permission_flags(obj, user)
        return flags.get(key, False)

    def get_can_edit(self, obj):
        return self._perm(obj, "can_edit")

    def get_can_cancel(self, obj):
        return self._perm(obj, "can_cancel")

    def get_can_approve(self, obj):
        return self._perm(obj, "can_approve")

    def get_can_reject(self, obj):
        return self._perm(obj, "can_reject")

    def get_can_revoke(self, obj):
        return self._perm(obj, "can_revoke")


class AttendanceOverTimeSerializer(serializers.ModelSerializer):
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    employee_profile_url = serializers.SerializerMethodField(read_only=True)
    # Direct attachments uploaded on the attendance request
    attachment_urls = serializers.SerializerMethodField(read_only=True)
    # Alias for UI parity with Work Type Requests
    file_urls = serializers.SerializerMethodField(read_only=True)

    class Meta:
        model = AttendanceOverTime
        fields = [
            "id",
            "employee_first_name",
            "employee_last_name",
            "employee_profile_url",
            "badge_id",
            "employee_id",
            "month",
            "year",
            "worked_hours",
            "pending_hours",
            "overtime",
        ]

    def get_attachment_urls(self, obj):
        try:
            from attendance.services.attendance_request_access import iter_request_attachments
            urls = []
            seen = set()
            for f in iter_request_attachments(obj):
                try:
                    u = getattr(getattr(f, 'file', None), 'url', None)
                    if u and u not in seen:
                        seen.add(u)
                        urls.append(u)
                except Exception:
                    continue
            return urls
        except Exception:
            return []

    def get_file_urls(self, obj):
        # Backward/UX compatibility with WorkModeRequestSerializer
        return self.get_attachment_urls(obj)

    def get_employee_profile_url(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(getattr(obj, "employee_id", None), request=request)


class AttendanceLateComeEarlyOutSerializer(serializers.ModelSerializer):
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )

    class Meta:
        model = AttendanceLateComeEarlyOut
        fields = "__all__"




class AttendanceCorrectionRequestSerializer(AttendanceRequestSerializer):
    """Active serializer for the new ``AttendanceCorrectionRequest`` contract."""

    class Meta(AttendanceRequestSerializer.Meta):
        model = AttendanceCorrectionRequest
        fields = [
            "id", "employee_id", "employee_first_name", "employee_last_name", "badge_id",
            "employee_profile_url", "attendance_date", "scope",
            "requested_check_in_date", "requested_check_in_time",
            "requested_check_out_date", "requested_check_out_time",
            "reason", "status", "request_status",
            "action_reason", "action_type", "action_at", "approved_at", "rejected_at", "revoked_at", "canceled_at",
            "action_by_name", "attachments", "attachment_urls", "file_urls",
            "proposed_attendance_clock_in", "proposed_attendance_clock_out",
            "proposed_attendance_clock_in_date", "proposed_attendance_clock_out_date",
            "final_attendance_clock_in", "final_attendance_clock_out",
            "final_attendance_clock_in_date", "final_attendance_clock_out_date",
            "effective_attendance_clock_in", "effective_attendance_clock_out",
            "effective_attendance_clock_in_date", "effective_attendance_clock_out_date",
            "can_edit", "can_cancel", "can_approve", "can_reject", "can_revoke",
        ]

    def _is_legacy_attendance(self, obj):
        return False

class AttendanceActivitySerializer(serializers.ModelSerializer):
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    clock_in_channel_display = serializers.SerializerMethodField(read_only=True)
    clock_out_channel_display = serializers.SerializerMethodField(read_only=True)

    class Meta:
        model = AttendanceActivity
        fields = "__all__"

    def get_clock_in_channel_display(self, obj):
        try:
            return obj.get_clock_in_channel_display()
        except Exception:
            return getattr(obj, "clock_in_channel", None)

    def get_clock_out_channel_display(self, obj):
        try:
            return obj.get_clock_out_channel_display()
        except Exception:
            return getattr(obj, "clock_out_channel", None)


class WorkModeRequestSerializer(serializers.ModelSerializer):
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_profile_url = serializers.SerializerMethodField(read_only=True)
    attachments = serializers.SerializerMethodField(read_only=True)
    attachment_urls = serializers.SerializerMethodField(read_only=True)
    file_urls = serializers.SerializerMethodField(read_only=True)
    approved_by_name = serializers.SerializerMethodField(read_only=True)
    action_by_name = serializers.SerializerMethodField(read_only=True)
    action_at = serializers.SerializerMethodField(read_only=True)
    can_update = serializers.SerializerMethodField(read_only=True)
    can_cancel = serializers.SerializerMethodField(read_only=True)
    can_approve = serializers.SerializerMethodField(read_only=True)
    can_reject = serializers.SerializerMethodField(read_only=True)
    can_revoke = serializers.SerializerMethodField(read_only=True)
    can_verify_document = serializers.SerializerMethodField(read_only=True)
    can_reject_document = serializers.SerializerMethodField(read_only=True)
    can_reopen_document = serializers.SerializerMethodField(read_only=True)
    can_upload_document = serializers.SerializerMethodField(read_only=True)
    current_document_version_number = serializers.SerializerMethodField(read_only=True)
    document_versions = serializers.SerializerMethodField(read_only=True)
    request_status = serializers.SerializerMethodField(read_only=True)
    status_label = serializers.SerializerMethodField(read_only=True)
    work_mode = serializers.SerializerMethodField(read_only=True)
    mode_label = serializers.SerializerMethodField(read_only=True)
    scope_label = serializers.SerializerMethodField(read_only=True)
    note = serializers.SerializerMethodField(read_only=True)
    comment = serializers.SerializerMethodField(read_only=True)
    action_note = serializers.SerializerMethodField(read_only=True)
    document_status_label = serializers.SerializerMethodField(read_only=True)
    current_document_version = serializers.SerializerMethodField(read_only=True)
    current_document_files = serializers.SerializerMethodField(read_only=True)
    queue_type = serializers.SerializerMethodField(read_only=True)

    work_type = serializers.CharField(source="mode", read_only=True)

    class Meta:
        model = WorkModeRequest
        fields = "__all__"
        extra_kwargs = {
            "employee_id": {"required": False},
            "files": {"read_only": True},
        }

    def _request(self):
        return self.context.get("request") if hasattr(self, "context") else None

    def _request_actor_employee(self):
        request = self._request()
        try:
            return request.user.employee_get if request else None
        except Exception:
            return None

    def _flags(self, obj):
        request = self._request()
        if not request:
            return {}
        try:
            return build_permission_flags(request, obj)
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to build permission flags for work mode request %s", getattr(obj, "id", None))
            return {
                "can_update": False,
                "can_cancel": False,
                "can_upload_document": False,
                "can_approve": False,
                "can_reject": False,
                "can_revoke": False,
                "can_verify_document": False,
                "can_reject_document": False,
                "can_reopen_document": False,
            }

    def to_internal_value(self, data):
        try:
            raw = data.dict() if hasattr(data, "dict") else dict(data)
            raw.pop("duty_destination_detail", None)
            _mode, new_data = coerce_work_type_payload(raw)
            data = new_data
        except Exception:
            pass
        return super().to_internal_value(data)

    def to_representation(self, instance):
        data = super().to_representation(instance)
        if not (data.get("action_reason") or "").strip():
            fallback = (data.get("document_remark") or "").strip()
            if fallback:
                data["action_reason"] = fallback
        # Stable aliases for web/mobile clients during contract cleanup.
        data.setdefault("request_status", data.get("status"))
        data.setdefault("work_mode", data.get("mode"))
        data.setdefault("work_type", data.get("mode"))
        if not (data.get("note") or "").strip():
            data["note"] = data.get("reason") or data.get("description") or ""
        if not (data.get("comment") or "").strip():
            data["comment"] = data.get("action_reason") or data.get("document_remark") or ""
        if not (data.get("action_note") or "").strip():
            data["action_note"] = data.get("action_reason") or data.get("comment") or ""
        data.pop("duty_destination_detail", None)
        return data

    def validate(self, attrs):
        attrs = super().validate(attrs)

        for field in ("reason", "duty_destination_location"):
            if field in attrs and attrs.get(field) is not None:
                attrs[field] = str(attrs.get(field)).strip()

        reason_in = attrs.get("reason")
        if self.instance is None:
            if reason_in is None or str(reason_in).strip() == "":
                raise serializers.ValidationError({"reason": "Reason / Notes is required."})
        else:
            if "reason" in attrs and str(reason_in or "").strip() == "":
                raise serializers.ValidationError({"reason": "Reason / Notes is required."})

        request = self._request()
        actor = self._request_actor_employee()
        employee = attrs.get("employee_id") or getattr(self.instance, "employee_id", None)
        mode = attrs.get("mode") or getattr(self.instance, "mode", None)
        scope = attrs.get("scope") or getattr(self.instance, "scope", None)
        start_date = attrs.get("start_date") or getattr(self.instance, "start_date", None)
        end_date = attrs.get("end_date") or getattr(self.instance, "end_date", None)
        destination = attrs.get("duty_destination_location")
        if destination is None and self.instance is not None:
            destination = getattr(self.instance, "duty_destination_location", None)

        if self.instance is None:
            if request is None:
                raise serializers.ValidationError({"employee_id": "Request context is required."})
            if actor is None:
                raise serializers.ValidationError({"employee_id": "An employee profile is required to create this request."})
            if employee is not None and employee != actor:
                raise serializers.ValidationError({"employee_id": "Requests can only be created for yourself."})
            attrs["employee_id"] = actor

        if mode == AttendanceWorkMode.ON_DUTY and not str(destination or "").strip():
            raise serializers.ValidationError({"duty_destination_location": "Destination location is required for ON DUTY requests."})

        if self.instance is None and mode == AttendanceWorkMode.ON_DUTY:
            request_files = getattr(request, "FILES", None) if request is not None else None
            uploaded = []
            if request_files is not None:
                uploaded = request_files.getlist("files") or request_files.getlist("files[]") or []
            if not uploaded:
                raise serializers.ValidationError({"files": "At least one file is required for ON DUTY requests."})

        if employee and mode and scope and start_date and end_date:
            validate_work_type_request(
                employee=employee,
                mode=mode,
                scope=scope,
                start_date=start_date,
                end_date=end_date,
                instance_id=getattr(self.instance, "id", None),
            )

        effective_doc_status = None
        if self.instance is not None:
            resolver = getattr(self.instance, "effective_document_status", None)
            effective_doc_status = resolver() if callable(resolver) else None
        if mode == AttendanceWorkMode.ON_DUTY and effective_doc_status == WorkModeRequestDocumentStatus.VERIFIED:
            immutable = {"reason", "start_date", "end_date", "scope", "mode", "duty_destination_location"}
            changed = [field for field in immutable if field in attrs]
            if changed:
                raise serializers.ValidationError({"document_status": "Verified On Duty documents are locked. Reopen verification first."})

        return attrs

    def _employee_display_name(self, employee):
        if not employee:
            return None
        first = getattr(employee, "employee_first_name", None) or ""
        last = getattr(employee, "employee_last_name", None) or ""
        full = f"{first} {last}".strip()
        if full:
            return full
        try:
            user = getattr(employee, "employee_user_id", None)
            return getattr(user, "username", None)
        except Exception:
            return None

    def get_request_status(self, obj):
        return getattr(obj, "status", None)

    def get_status_label(self, obj):
        try:
            return obj.get_status_display()
        except Exception:
            return getattr(obj, "status", None)

    def get_work_mode(self, obj):
        return getattr(obj, "mode", None)

    def get_mode_label(self, obj):
        try:
            return obj.get_mode_display()
        except Exception:
            return getattr(obj, "mode", None)

    def get_scope_label(self, obj):
        try:
            return obj.get_scope_display()
        except Exception:
            return getattr(obj, "scope", None)

    def get_note(self, obj):
        return getattr(obj, "reason", None) or getattr(obj, "description", None)

    def get_comment(self, obj):
        return getattr(obj, "action_reason", None) or getattr(obj, "document_remark", None)

    def get_action_note(self, obj):
        return getattr(obj, "action_reason", None) or getattr(obj, "document_remark", None)

    def _document_status_label_for_mode(self, obj, raw_status):
        raw_status = (raw_status or "").strip()
        if getattr(obj, "mode", None) in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH}:
            return "Supporting Attachment Uploaded" if raw_status and raw_status != WorkModeRequestDocumentStatus.NOT_UPLOADED else "Not Uploaded"
        if not raw_status:
            return None
        mapping = {
            WorkModeRequestDocumentStatus.NOT_UPLOADED: "Not Uploaded",
            WorkModeRequestDocumentStatus.SUBMITTED: "Submitted",
            WorkModeRequestDocumentStatus.PENDING_VERIFICATION: "Pending Verification",
            WorkModeRequestDocumentStatus.VERIFIED: "Verified",
            WorkModeRequestDocumentStatus.REJECTED: "Rejected",
        }
        return mapping.get(raw_status, raw_status)

    def _current_document_obj(self, obj):
        current = getattr(obj, "current_document_version", None)
        if current is not None:
            return current
        resolver = getattr(obj, "resolve_current_document_version", None)
        if callable(resolver):
            return resolver()
        return None

    def get_document_status_label(self, obj):
        try:
            resolver = getattr(obj, "effective_document_status", None)
            raw_status = resolver() if callable(resolver) else getattr(obj, "document_status", None)
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to resolve document status label for work mode request %s", getattr(obj, "id", None))
            raw_status = None
        label = self._document_status_label_for_mode(obj, raw_status)
        if label:
            return label
        try:
            return obj.get_document_status_display()
        except Exception:
            return raw_status

    def get_current_document_version(self, obj):
        current = self._current_document_obj(obj)
        if current is None:
            return None
        files = []
        try:
            resolver = getattr(obj, "current_document_files", None)
            files = resolver() if callable(resolver) else []
            files = files or []
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to resolve current document version payload for work mode request %s", getattr(obj, "id", None))
            files = []
        except Exception:
            files = []
        return {
            "id": getattr(current, "id", None),
            "version_number": getattr(current, "version_number", None),
            "status": getattr(current, "status", None),
            "status_label": self._document_status_label_for_mode(obj, getattr(current, "status", None)) or getattr(current, "get_status_display", lambda: getattr(current, "status", None))(),
            "is_current": True,
            "submitted_at": getattr(current, "submitted_at", None),
            "reviewed_at": getattr(current, "reviewed_at", None),
            "review_remark": getattr(current, "review_remark", None),
            "submitted_by_name": self._employee_display_name(getattr(current, "submitted_by", None)),
            "reviewed_by_name": self._employee_display_name(getattr(current, "reviewed_by", None)),
            "files": self._serialize_file_links(obj, files),
        }

    def get_current_document_files(self, obj):
        try:
            resolver = getattr(obj, "current_document_files", None)
            files = resolver() if callable(resolver) else []
            return self._serialize_file_links(obj, files or [])
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to serialize current document files for work mode request %s", getattr(obj, "id", None))
            return []
        except Exception:
            return []

    def _serialize_file_links(self, obj, files):
        out = []
        seen = set()
        for f in files or []:
            fid = getattr(f, "id", None)
            if fid in seen:
                continue
            seen.add(fid)
            request = self._request()
            metadata = build_work_mode_attachment_metadata(request, obj, f)
            metadata["id"] = fid
            out.append(metadata)
        return out

    def get_attachments(self, obj):
        try:
            resolver = getattr(obj, "current_document_files", None)
            files = resolver() if callable(resolver) else []
            files = files or []
            return self._serialize_file_links(obj, files)
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to serialize attachments for work mode request %s", getattr(obj, "id", None))
            return []
        except Exception:
            return []

    def get_attachment_urls(self, obj):
        return [item.get("url") for item in self.get_attachments(obj) if item.get("url")]

    def get_file_urls(self, obj):
        return self.get_attachment_urls(obj)

    def get_action_by_name(self, obj):
        return getattr(obj, "action_actor_display", None)

    def get_action_at(self, obj):
        return getattr(obj, "action_effective_at", None)

    def get_employee_profile_url(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(getattr(obj, "employee_id", None), request=request)

    def get_approved_by_name(self, obj):
        return getattr(obj, "approved_actor_display", None)

    def get_can_update(self, obj):
        return bool(self._flags(obj).get("can_update"))

    def get_can_cancel(self, obj):
        return bool(self._flags(obj).get("can_cancel"))

    def get_can_approve(self, obj):
        return bool(self._flags(obj).get("can_approve"))

    def get_can_reject(self, obj):
        return bool(self._flags(obj).get("can_reject"))

    def get_can_revoke(self, obj):
        return bool(self._flags(obj).get("can_revoke"))

    def get_can_verify_document(self, obj):
        if getattr(obj, "mode", None) in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH}:
            return False
        return bool(self._flags(obj).get("can_verify_document"))

    def get_can_reject_document(self, obj):
        if getattr(obj, "mode", None) in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH}:
            return False
        return bool(self._flags(obj).get("can_reject_document"))

    def get_can_reopen_document(self, obj):
        if getattr(obj, "mode", None) in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH}:
            return False
        return bool(self._flags(obj).get("can_reopen_document"))

    def get_can_upload_document(self, obj):
        allowed = bool(self._flags(obj).get("can_upload_document"))
        if getattr(obj, "mode", None) in {AttendanceWorkMode.WFA, AttendanceWorkMode.WFH}:
            return allowed and getattr(obj, "status", None) == WorkModeRequestStatus.WAITING_FOR_APPROVAL
        return allowed

    def get_current_document_version_number(self, obj):
        current = self._current_document_obj(obj)
        return getattr(current, "version_number", None) if current else None

    def get_document_versions(self, obj):
        out = []
        try:
            versions_rel = getattr(obj, "document_versions", None)
            if versions_rel is None:
                versions = []
            else:
                versions = versions_rel.all().select_related("submitted_by", "reviewed_by").prefetch_related("file_links__attendance_request_file")[:10]
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to resolve historical document versions for work mode request %s", getattr(obj, "id", None))
            versions = []
        except Exception:
            versions = []
        for version in versions:
            files = [link.attendance_request_file for link in version.file_links.all() if getattr(link, "attendance_request_file", None)]
            out.append({
                "id": version.id,
                "version_number": version.version_number,
                "is_current": version.is_current,
                "status": version.status,
                "status_label": self._document_status_label_for_mode(obj, getattr(version, "status", None)) or getattr(version, "get_status_display", lambda: version.status)(),
                "review_remark": version.review_remark,
                "submitted_at": version.submitted_at,
                "reviewed_at": version.reviewed_at,
                "file_count": version.file_links.count(),
                "submitted_by_name": self._employee_display_name(getattr(version, "submitted_by", None)),
                "reviewed_by_name": self._employee_display_name(getattr(version, "reviewed_by", None)),
                "files": self._serialize_file_links(obj, files),
            })
        return out

    def get_queue_type(self, obj):
        try:
            from attendance.services.work_type_request_rules import classify_work_mode_request_queue

            return classify_work_mode_request_queue(obj)
        except WorkModeRequestConsistencyError:
            logger.exception("Failed to classify work mode request queue for request %s", getattr(obj, "id", None))
            return None
        except Exception:
            return None


class MailTemplateSerializer(serializers.ModelSerializer):
    class Meta:
        model = HorillaMailTemplate
        fields = "__all__"


class UserAttendanceListSerializer(serializers.ModelSerializer):
    class Meta:
        model = Attendance
        fields = [
            "id",
            "attendance_date",
            "attendance_clock_in",
            "attendance_clock_out",
            "attendance_worked_hour",
        ]


class UserAttendanceDetailedSerializer(serializers.ModelSerializer):
    class Meta:
        model = Attendance
        fields = "__all__"

class AttendancePunchingHistorySerializer(serializers.ModelSerializer):
    punch_date = serializers.SerializerMethodField()
    punch_time = serializers.SerializerMethodField()
    source = serializers.SerializerMethodField()
    device_info = serializers.SerializerMethodField()
    photo_url = serializers.SerializerMethodField()
    latitude = serializers.SerializerMethodField()
    longitude = serializers.SerializerMethodField()
    location_display = serializers.SerializerMethodField()
    google_maps_url = serializers.SerializerMethodField()
    reason = serializers.SerializerMethodField()
    raw_timestamp = serializers.SerializerMethodField()

    class Meta:
        model = AttendancePunchingHistory
        fields = [
            "id",
            "punch_date",
            "punch_time",
            "source",
            "device_info",
            "photo_url",
            "latitude",
            "longitude",
            "location_display",
            "google_maps_url",
            "accepted_to_attendance",
            "decision_status",
            "decision_source",
            "work_mode",
            "reason",
            "raw_timestamp",
        ]

    def _can_view_audit_fields(self):
        request = self.context.get("request")
        user = getattr(request, "user", None)
        if not user:
            return False
        try:
            if getattr(user, "is_superuser", False):
                return True
            return bool(user.has_perm("attendance.change_attendance"))
        except Exception:
            return False

    def to_representation(self, instance):
        data = super().to_representation(instance)
        if not self._can_view_audit_fields():
            data.pop("decision_source", None)
            data.pop("work_mode", None)
        return data

    def _localized_timestamp(self, obj):
        try:
            return dj_timezone.localtime(obj.punch_timestamp)
        except Exception:
            return obj.punch_timestamp

    def _location_value(self, obj, *keys):
        location = getattr(obj, "location", None)
        if not isinstance(location, dict):
            return None
        for key in keys:
            if key in location and location.get(key) is not None:
                return location.get(key)
        return None

    def get_punch_date(self, obj):
        ts = self._localized_timestamp(obj)
        try:
            return ts.strftime("%Y-%m-%d")
        except Exception:
            return None

    def get_punch_time(self, obj):
        ts = self._localized_timestamp(obj)
        try:
            return ts.strftime("%H:%M:%S")
        except Exception:
            return None

    def get_source(self, obj):
        return getattr(obj, "get_source_display", lambda: None)() or "-"

    def get_device_info(self, obj):
        return (getattr(obj, "device_info", None) or "").strip() or "-"

    def get_photo_url(self, obj):
        try:
            url = obj.photo.url
        except Exception:
            return None
        request = self.context.get("request")
        if request is None:
            return url
        try:
            return request.build_absolute_uri(url)
        except Exception:
            return url

    def get_latitude(self, obj):
        return self._location_value(obj, "lat", "latitude")

    def get_longitude(self, obj):
        return self._location_value(obj, "lng", "longitude")

    def get_location_display(self, obj):
        return getattr(obj, "location_display", None) or "-"

    def get_google_maps_url(self, obj):
        return getattr(obj, "google_maps_url", None)

    def get_reason(self, obj):
        return (getattr(obj, "reason", None) or "").strip() or "-"

    def get_raw_timestamp(self, obj):
        ts = self._localized_timestamp(obj)
        try:
            return ts.isoformat()
        except Exception:
            return None

