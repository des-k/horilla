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
            "attendance_clock_out_date": validated_data.get(
                "attendance_clock_out_date"
            ),
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
                None
                if data["attendance_clock_out"] == "None"
                else data["attendance_clock_out"]
            )
            data["attendance_clock_out_date"] = (
                None
                if data["attendance_clock_out_date"] == "None"
                else data["attendance_clock_out_date"]
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
            return attendance.save()
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

    def get_employee_profile_url(self, obj):
        try:
            employee_profile = obj.employee_id.employee_profile
            return employee_profile.url
        except:
            return None


class AttendanceOverTimeSerializer(serializers.ModelSerializer):
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    employee_profile_url = serializers.SerializerMethodField(read_only=True)

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

    class Meta:
        model = AttendanceActivity
        fields = "__all__"


class WorkModeRequestSerializer(serializers.ModelSerializer):
    employee_first_name = serializers.CharField(
        source="employee_id.employee_first_name", read_only=True
    )
    employee_last_name = serializers.CharField(
        source="employee_id.employee_last_name", read_only=True
    )
    badge_id = serializers.CharField(source="employee_id.badge_id", read_only=True)
    employee_profile_url = serializers.SerializerMethodField(read_only=True)
    file_urls = serializers.SerializerMethodField(read_only=True)
    approved_by_name = serializers.SerializerMethodField(read_only=True)

    # UI/UX alias (read-only). Input alias is handled in to_internal_value().
    work_type = serializers.CharField(source="mode", read_only=True)

    def to_internal_value(self, data):
        # Allow clients to send `work_type` instead of legacy `mode`.
        try:
            _mode, new_data = coerce_work_type_payload(dict(data))
            data = new_data
        except Exception:
            pass
        return super().to_internal_value(data)

    def validate(self, attrs):
        attrs = super().validate(attrs)

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
        if status_val == WorkModeRequestStatus.REJECTED and not reason_code:
            raise serializers.ValidationError({"reason_code": "reason_code is required when status is REJECTED"})

        return attrs

    class Meta:
        model = WorkModeRequest
        fields = "__all__"

    def get_employee_profile_url(self, obj):
        try:
            employee_profile = obj.employee_id.employee_profile
            return employee_profile.url
        except Exception:
            return None

    def get_file_urls(self, obj):
        try:
            urls = []
            for f in obj.files.all():
                if getattr(f, "file", None) and getattr(f.file, "url", None):
                    urls.append(f.file.url)
            return urls
        except Exception:
            return []

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
