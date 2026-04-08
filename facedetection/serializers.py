from rest_framework import serializers

from horilla_api.utils.private_media_urls import build_employee_face_api_url

from .models import *


class FaceDetectionSerializer(serializers.ModelSerializer):
    class Meta:
        model = FaceDetection
        fields = "__all__"
        read_only_fields = ["start"]

    def to_representation(self, instance):
        data = super().to_representation(instance)
        data["start"] = True
        return data


class EmployeeFaceDetectionSerializer(serializers.ModelSerializer):
    class Meta:
        model = EmployeeFaceDetection
        fields = "__all__"

    def to_representation(self, instance):
        data = super().to_representation(instance)
        request = self.context.get("request") if hasattr(self, "context") else None
        data["image"] = build_employee_face_api_url(
            getattr(instance, "employee_id", None),
            request=request,
            face=instance,
        )
        return data
