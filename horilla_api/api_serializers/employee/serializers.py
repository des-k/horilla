from rest_framework import serializers

from base.models import Department, EmployeeType, JobPosition
from employee.models import (
    Actiontype,
    DisciplinaryAction,
    Employee,
    EmployeeBankDetails,
    EmployeeWorkInformation,
    Policy,
)
from horilla_documents.models import Document, DocumentRequest
from attendance.models import EmployeeWfhProfileHistory
from attendance.services.wfh_profile import effective_wfh_radius_for
from geofencing.models import GeoFencing
from facedetection.models import EmployeeFaceDetection
from horilla_api.utils.private_media_urls import (
    build_employee_face_api_url,
    build_employee_face_api_version,
    build_employee_profile_api_url,
    build_employee_profile_api_version,
)

from ...api_methods.employee.methods import get_next_badge_id


class ActiontypeSerializer(serializers.ModelSerializer):
    class Meta:
        model = Actiontype
        fields = ["id", "title", "action_type"]


class EmployeeListSerializer(serializers.ModelSerializer):
    employee_profile = serializers.SerializerMethodField()
    job_position_name = serializers.CharField(
        source="employee_work_info.job_position_id.job_position", read_only=True
    )
    employee_work_info_id = serializers.CharField(
        source="employee_work_info.id", read_only=True
    )
    employee_bank_details_id = serializers.CharField(
        source="employee_bank_details.id", read_only=True
    )

    class Meta:
        model = Employee
        fields = [
            "id",
            "employee_first_name",
            "employee_last_name",
            "email",
            "job_position_name",
            "employee_work_info_id",
            "employee_profile",
            "employee_bank_details_id",
        ]

    def get_employee_profile(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(obj, request=request)


class EmployeeSerializer(serializers.ModelSerializer):
    employee_profile = serializers.ImageField(required=False, allow_null=True)
    employee_profile_version = serializers.SerializerMethodField()
    wfh_profile = serializers.SerializerMethodField()
    department_name = serializers.CharField(
        source="employee_work_info.department_id.department", read_only=True
    )
    department_id = serializers.CharField(
        source="employee_work_info.department_id.id", read_only=True
    )
    job_position_name = serializers.CharField(
        source="employee_work_info.job_position_id.job_position", read_only=True
    )
    job_position_id = serializers.CharField(
        source="employee_work_info.job_position_id.id", read_only=True
    )
    employee_work_info_id = serializers.CharField(
        source="employee_work_info.id", read_only=True
    )
    employee_bank_details_id = serializers.CharField(
        source="employee_bank_details.id", read_only=True
    )

    def get_wfh_profile(self, obj):
        profile = getattr(obj, "wfh_profile", None)
        radius = effective_wfh_radius_for(employee=obj, profile=profile)
        face = EmployeeFaceDetection.objects.filter(employee_id=obj).first()
        history = [
            {
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
            }
            for item in EmployeeWfhProfileHistory.objects.filter(employee=obj).order_by("-acted_at", "-id")[:20]
        ]
        home_latitude = getattr(profile, "home_latitude", None)
        home_longitude = getattr(profile, "home_longitude", None)
        effective_radius = radius
        is_home_configured = bool(
            getattr(profile, "is_home_configured", False)
            and home_latitude is not None
            and home_longitude is not None
        )
        return {
            "home_latitude": home_latitude,
            "home_longitude": home_longitude,
            "google_maps_link": f"https://maps.google.com/?q={home_latitude},{home_longitude}" if home_latitude is not None and home_longitude is not None else None,
            "radius_in_meters": effective_radius,
            "is_home_configured": is_home_configured,
            "requires_home_reconfiguration": bool(getattr(profile, "requires_home_reconfiguration", False)),
            "requires_face_reenrollment": bool(getattr(profile, "requires_face_reenrollment", False)),
            "face_image": build_employee_face_api_url(obj, request=self.context.get("request") if hasattr(self, "context") else None, face=face),
            "face_image_version": build_employee_face_api_version(obj, face=face),
            "history": history,
        }

    def get_employee_profile(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(obj, request=request)

    def get_employee_profile_version(self, obj):
        return build_employee_profile_api_version(obj)

    class Meta:
        model = Employee
        fields = "__all__"

    def to_representation(self, instance):
        data = super().to_representation(instance)
        data["employee_profile"] = self.get_employee_profile(instance)
        data["employee_profile_version"] = self.get_employee_profile_version(instance)
        data["wfh_profile"] = self.get_wfh_profile(instance)
        return data

    def create(self, validated_data):
        validated_data["badge_id"] = get_next_badge_id()
        return super().create(validated_data)


class EmployeeWorkInformationSerializer(serializers.ModelSerializer):
    job_position_name = serializers.CharField(
        source="job_position_id.job_position", read_only=True
    )
    department_name = serializers.CharField(
        source="department_id.department", read_only=True
    )
    shift_name = serializers.CharField(source="shift_id.employee_shift", read_only=True)
    job_role_name = serializers.CharField(source="job_role_id.job_role", read_only=True)
    employee_type_name = serializers.CharField(
        source="employee_type_id.employee_type", read_only=True
    )
    reporting_manager_first_name = serializers.CharField(
        source="reporting_manager_id.employee_first_name", read_only=True
    )
    reporting_manager_last_name = serializers.CharField(
        source="reporting_manager_id.employee_last_name", read_only=True
    )
    work_type_name = serializers.CharField(
        source="work_type_id.work_type", read_only=True
    )
    company_name = serializers.CharField(source="company_id.company", read_only=True)
    tags = serializers.SerializerMethodField()

    def get_tags(self, obj):
        return [
            {"id": tag.id, "title": tag.title, "color": tag.color}
            for tag in obj.tags.all()
        ]

    class Meta:
        model = EmployeeWorkInformation
        fields = "__all__"


class EmployeeBankDetailsSerializer(serializers.ModelSerializer):
    class Meta:
        model = EmployeeBankDetails
        fields = "__all__"


class EmployeeTypeSerializer(serializers.ModelSerializer):
    class Meta:
        model = EmployeeType
        fields = "__all__"


class EmployeeBulkUpdateSerializer(serializers.ModelSerializer):
    class Meta:
        model = Employee
        # fields = [
        #     'employee_last_name',
        #     'address',
        #     'country',
        #     'state',
        #     'city',
        #     'zip',
        #     'dob',
        #     'gender',
        #     'qualification',
        #     'experience',
        #     'marital_status',
        #     'children',
        # ]
        fields = [
            "employee_last_name",
        ]


class DisciplinaryActionSerializer(serializers.ModelSerializer):
    class Meta:
        model = DisciplinaryAction
        fields = "__all__"


class PolicySerializer(serializers.ModelSerializer):
    class Meta:
        model = Policy
        fields = "__all__"


class DocumentRequestSerializer(serializers.ModelSerializer):
    class Meta:
        model = DocumentRequest
        fields = "__all__"


class DocumentSerializer(serializers.ModelSerializer):
    class Meta:
        model = Document
        fields = "__all__"


class EmployeeSelectorSerializer(serializers.ModelSerializer):
    employee_profile = serializers.SerializerMethodField()
    class Meta:
        model = Employee
        fields = [
            "id",
            "employee_first_name",
            "employee_last_name",
            "badge_id",
            "employee_profile",
        ]

    def get_employee_profile(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(obj, request=request)
