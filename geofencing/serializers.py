from geopy.geocoders import Nominatim
from rest_framework import serializers

from .models import GeoFencing
from .policy import coerce_geofencing_start, geofencing_is_effectively_enabled


class GeoFencingSetupSerializer(serializers.ModelSerializer):
    class Meta:
        model = GeoFencing
        fields = "__all__"

    def validate_start(self, value):
        return coerce_geofencing_start(value)

    def validate(self, data):
        data["start"] = coerce_geofencing_start(data.get("start"))
        geolocator = Nominatim(user_agent="geo_checker")  # Use a unique user-agent
        start = data.get("start")
        if start:
            try:
                latitude = data.get("latitude")
                longitude = data.get("longitude")
                location = geolocator.reverse((latitude, longitude), exactly_one=True)
                if not location:
                    raise serializers.ValidationError("Invalid Location")
            except Exception as e:
                raise serializers.ValidationError(e)
        return data

    def create(self, validated_data):
        validated_data["start"] = coerce_geofencing_start(validated_data.get("start"))
        return super().create(validated_data)

    def update(self, instance, validated_data):
        validated_data["start"] = coerce_geofencing_start(validated_data.get("start"))
        return super().update(instance, validated_data)

    def to_representation(self, instance):
        representation = super().to_representation(instance)
        representation["start"] = geofencing_is_effectively_enabled(instance=instance)
        return representation


class EmployeeLocationSerializer(serializers.ModelSerializer):
    class Meta:
        model = GeoFencing
        fields = ["latitude", "longitude"]
