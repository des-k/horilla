from rest_framework import serializers

from employee.models import Employee
from horilla_api.utils.private_media_urls import build_employee_profile_api_url


class GetEmployeeSerializer(serializers.ModelSerializer):
    full_name = serializers.SerializerMethodField()
    employee_profile = serializers.SerializerMethodField()

    class Meta:
        model = Employee
        fields = ["id", "full_name", "employee_profile"]

    def get_full_name(self, obj):
        return obj.get_full_name()

    def get_employee_profile(self, obj):
        request = self.context.get("request") if hasattr(self, "context") else None
        return build_employee_profile_api_url(obj, request=request)


class LoginRequestSerializer(serializers.Serializer):
    """Simple request body for the login endpoint."""

    username = serializers.CharField()
    password = serializers.CharField()
