from django.utils import timezone as dj_timezone
from rest_framework import serializers

from attendance.models import *
from base.models import HorillaMailTemplate

from attendance.services.work_type_request_rules import (
    coerce_work_type_payload,
    validate_work_type_request,
)


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
    # Attachments uploaded via AttendanceRequestComment.files
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

    def get_attachment_urls(self, obj):
        """Return list of attachment URLs for an attendance correction request.
        Files are stored via AttendanceRequestComment.files (ManyToMany -> AttendanceRequestFile).
        """
        try:
            from attendance.models import AttendanceRequestComment
            urls = []
            seen = set()
            qs = AttendanceRequestComment.objects.filter(request_id=obj).prefetch_related('files')
            for c in qs:
                for f in c.files.all():
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
        try:
            employee_profile = obj.employee_id.employee_profile
            return employee_profile.url
        except:
            return None


class AttendanceRequestSerializer(serializers.ModelSerializer):
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    shift_name = serializers.CharField(source="shift_id.employee_shift", read_only=True)
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_profile_url = serializers.SerializerMethodField(read_only=True)

    # Attachments uploaded via AttendanceRequestComment.files
    attachment_urls = serializers.SerializerMethodField(read_only=True)
    # Alias for UI parity with Work Type Requests
    file_urls = serializers.SerializerMethodField(read_only=True)

    # Status label for mobile/web UI (WAITING / APPROVED / REJECTED / CANCEL)
    status = serializers.SerializerMethodField(read_only=True)
    request_status = serializers.SerializerMethodField(read_only=True)
    action_by_name = serializers.SerializerMethodField(read_only=True)
    action_type = serializers.SerializerMethodField(read_only=True)
    action_at = serializers.SerializerMethodField(read_only=True)
    approved_at = serializers.SerializerMethodField(read_only=True)
    rejected_at = serializers.SerializerMethodField(read_only=True)
    canceled_at = serializers.SerializerMethodField(read_only=True)

    class Meta:
        model = Attendance
        exclude = [
            "attendance_overtime",
            "attendance_overtime_approve",
            "attendance_validated",
            "approved_overtime_second",
            "is_validate_request",
            "is_validate_request_approved",
            "request_type",
            "created_at",
        ]

    def create(self, validated_data):
        # Extract relevant data from validated_data
        employee_id = validated_data.get("employee_id")
        attendance_date = validated_data.get("attendance_date")
        # Check if attendance exists for the employee and date
        attendances = Attendance.objects.filter(
            employee_id=employee_id, attendance_date=attendance_date
        )
        data = {
            "employee_id": validated_data.get("employee_id"),
            "attendance_date": validated_data.get("attendance_date"),
            "attendance_clock_in_date": validated_data.get("attendance_clock_in_date"),
            "attendance_clock_in": validated_data.get("attendance_clock_in"),
            "attendance_clock_out": validated_data.get("attendance_clock_out"),
            "attendance_clock_out_date": validated_data.get("attendance_clock_out_date"),
            "shift_id": validated_data.get("shift_id"),
            "work_type_id": validated_data.get("work_type_id"),
            "attendance_worked_hour": validated_data.get("attendance_worked_hour"),
            "minimum_hour": validated_data.get("minimum_hour"),
        }
        if attendances.exists():
            data["employee_id"] = employee_id.id
            data["attendance_date"] = str(attendance_date)
            data["attendance_clock_in_date"] = self.data["attendance_clock_in_date"]
            data["attendance_clock_in"] = self.data["attendance_clock_in"]
            data["attendance_clock_out"] = (
                None if data["attendance_clock_out"] == "None" else data["attendance_clock_out"]
            )
            data["attendance_clock_out_date"] = (
                None if data["attendance_clock_out_date"] == "None" else data["attendance_clock_out_date"]
            )
            data["work_type_id"] = self.data["work_type_id"]
            data["shift_id"] = self.data["shift_id"]
            attendance = attendances.first()
            for key, value in data.items():
                data[key] = str(value)
            attendance.requested_data = json.dumps(data)
            attendance.is_validate_request = True
            if attendance.request_type != "create_request":
                attendance.request_type = "update_request"
            attendance.request_description = self.data["request_description"]
            attendance.save()
            return attendance

        new_instance = Attendance(**data)
        new_instance.is_validate_request = True
        new_instance.attendance_validated = False
        new_instance.request_description = self.data["request_description"]
        new_instance.request_type = "create_request"
        new_instance.save()
        return new_instance

    def update(self, instance, validated_data):
        if "employee_id" in validated_data:
            validated_data.pop("employee_id")
        return super().update(instance, validated_data)

    def get_attachment_urls(self, obj):
        """Return list of attachment URLs for an attendance correction request.
        Files are stored via AttendanceRequestComment.files (ManyToMany -> AttendanceRequestFile).
        """
        try:
            from attendance.models import AttendanceRequestComment

            urls = []
            seen = set()
            qs = AttendanceRequestComment.objects.filter(request_id=obj).prefetch_related("files")
            for c in qs:
                for f in c.files.all():
                    try:
                        u = getattr(getattr(f, "file", None), "url", None)
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
        try:
            employee_profile = obj.employee_id.employee_profile
            return employee_profile.url
        except Exception:
            return None

    def _compute_status(self, obj):
        """Stable status label for mobile/web UI."""
        try:
            rt = getattr(obj, "request_type", None)
            if rt == "cancel_request":
                return "CANCEL"
            if rt == "reject_request":
                return "REJECTED"
            if getattr(obj, "is_validate_request", False):
                return "WAITING"
            if getattr(obj, "is_validate_request_approved", False) or getattr(obj, "attendance_validated", False):
                return "APPROVED"
        except Exception:
            pass
        return None

    def get_status(self, obj):
        return self._compute_status(obj)

    def get_request_status(self, obj):
        # Alias used by some mobile builds
        return self._compute_status(obj)

    def get_action_by_name(self, obj):
        actor = getattr(obj, "action_by", None)
        if not actor:
            return None
        try:
            first = getattr(actor, "employee_first_name", "") or ""
            last = getattr(actor, "employee_last_name", "") or ""
            name = (first + " " + last).strip()
            return name or str(actor)
        except Exception:
            return None

    def _get_action_type(self, obj):
        value = getattr(obj, "action_type", None)
        if value:
            return value
        status = self._compute_status(obj)
        if status == "APPROVED":
            return "APPROVED"
        if status == "REJECTED":
            return "REJECTED"
        if status == "CANCEL":
            return "CANCELED"
        return None

    def get_action_type(self, obj):
        return self._get_action_type(obj)

    def _get_action_at(self, obj):
        return getattr(obj, "action_at", None)

    def get_action_at(self, obj):
        return self._get_action_at(obj)

    def get_approved_at(self, obj):
        return self._get_action_at(obj) if self._get_action_type(obj) == "APPROVED" else None

    def get_rejected_at(self, obj):
        return self._get_action_at(obj) if self._get_action_type(obj) == "REJECTED" else None

    def get_canceled_at(self, obj):
        return self._get_action_at(obj) if self._get_action_type(obj) == "CANCELED" else None


class AttendanceOverTimeSerializer(serializers.ModelSerializer):
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    employee_profile_url = serializers.SerializerMethodField(read_only=True)
    # Attachments uploaded via AttendanceRequestComment.files
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
        """Return list of attachment URLs for an attendance correction request.
        Files are stored via AttendanceRequestComment.files (ManyToMany -> AttendanceRequestFile).
        """
        try:
            from attendance.models import AttendanceRequestComment
            urls = []
            seen = set()
            qs = AttendanceRequestComment.objects.filter(request_id=obj).prefetch_related('files')
            for c in qs:
                for f in c.files.all():
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
        try:
            employee_profile = obj.employee_id.employee_profile
            return employee_profile.url
        except:
            return None


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
    attachment_urls = serializers.SerializerMethodField(read_only=True)
    file_urls = serializers.SerializerMethodField(read_only=True)
    approved_by_name = serializers.SerializerMethodField(read_only=True)
    action_by_name = serializers.SerializerMethodField(read_only=True)
    action_at = serializers.SerializerMethodField(read_only=True)

    # UI/UX alias (read-only). Input alias is handled in to_internal_value().
    work_type = serializers.CharField(source="mode", read_only=True)

    def to_internal_value(self, data):
        # Allow clients to send `work_type` instead of legacy `mode`.
        # NOTE: For multipart requests, DRF passes a QueryDict; calling dict(QueryDict)
        # turns values into lists (e.g. {"mode": ["wfa"]}) and breaks ChoiceField.
        # Use `.dict()` to get single values.
        try:
            raw = data.dict() if hasattr(data, "dict") else dict(data)
            _mode, new_data = coerce_work_type_payload(raw)
            data = new_data
        except Exception:
            pass
        return super().to_internal_value(data)

    def to_representation(self, instance):
        data = super().to_representation(instance)
        # Mobile builds read action_reason for action notes. Older rows and
        # some document-action flows only populated document_remark, so expose a
        # stable fallback in the serialized payload.
        if not (data.get("action_reason") or "").strip():
            fallback = (data.get("document_remark") or "").strip()
            if fallback:
                data["action_reason"] = fallback
        return data

    def validate(self, attrs):
        attrs = super().validate(attrs)

        # Reason/Notes is required on create, and must not be cleared on update.
        # (Model field is blank=True for backward compatibility, but UX requires it.)
        reason_in = attrs.get("reason")
        if self.instance is None:
            # Creating
            if reason_in is None or str(reason_in).strip() == "":
                raise serializers.ValidationError({"reason": "Reason / Notes is required."})
        else:
            # Updating via serializer (some endpoints may use serializer directly)
            if "reason" in attrs and str(reason_in or "").strip() == "":
                raise serializers.ValidationError({"reason": "Reason / Notes is required."})

        employee = attrs.get("employee_id") or getattr(self.instance, "employee_id", None)
        mode = attrs.get("mode") or getattr(self.instance, "mode", None)
        scope = attrs.get("scope") or getattr(self.instance, "scope", None)
        start_date = attrs.get("start_date") or getattr(self.instance, "start_date", None)
        end_date = attrs.get("end_date") or getattr(self.instance, "end_date", None)

        if employee and mode and scope and start_date and end_date:
            validate_work_type_request(
                employee=employee,
                mode=mode,
                scope=scope,
                start_date=start_date,
                end_date=end_date,
                instance_id=getattr(self.instance, "id", None),
            )

        # If rejected, reason_code must exist (spec)
        status_val = attrs.get("status") or getattr(self.instance, "status", None)
        reason_code = attrs.get("reason_code") or getattr(self.instance, "reason_code", None)
        if attrs.get("employee_id") is not None and self.instance is None:
            request = self.context.get("request")
            try:
                actor = request.user.employee_get if request else None
            except Exception:
                actor = None
            if actor and attrs.get("employee_id") != actor:
                raise serializers.ValidationError({"employee_id": "Requests can only be created for yourself."})

        doc_status = attrs.get("document_status") or getattr(self.instance, "document_status", None)
        if mode == AttendanceWorkMode.ON_DUTY and doc_status == "verified" and getattr(self.instance, "document_status", None) == "verified":
            immutable = {"reason", "start_date", "end_date", "scope", "mode", "duty_destination_location", "duty_destination_detail"}
            changed = [field for field in immutable if field in attrs]
            if changed:
                raise serializers.ValidationError({"document_status": "Verified On Duty documents are locked. Reopen verification first."})

        return attrs

    class Meta:
        model = WorkModeRequest
        fields = "__all__"

    def get_attachment_urls(self, obj):
        try:
            urls = []
            seen = set()
            for f in obj.files.all():
                u = getattr(getattr(f, "file", None), "url", None)
                if u and u not in seen:
                    seen.add(u)
                    urls.append(u)
            return urls
        except Exception:
            return []

    def get_file_urls(self, obj):
        return self.get_attachment_urls(obj)

    def get_action_by_name(self, obj):
        actor = getattr(obj, "action_by", None)
        if not actor:
            return None
        try:
            return f"{actor.employee_first_name} {actor.employee_last_name}".strip() or str(actor)
        except Exception:
            return None

    def get_action_at(self, obj):
        return getattr(obj, "action_at", None) or getattr(obj, "approved_at", None)

    def get_employee_profile_url(self, obj):
        try:
            employee_profile = obj.employee_id.employee_profile
            return employee_profile.url
        except Exception:
            return None

    def get_approved_by_name(self, obj):
        try:
            if obj.approved_by:
                return f"{obj.approved_by.employee_first_name} {obj.approved_by.employee_last_name}".strip()
        except Exception:
            pass
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

