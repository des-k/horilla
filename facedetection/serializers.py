from rest_framework import serializers

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
