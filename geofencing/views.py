from django.contrib import messages
from django.contrib.auth.decorators import login_required, permission_required
from django.http import QueryDict
from django.shortcuts import get_object_or_404, render
from django.utils.decorators import method_decorator
from django.utils.translation import gettext_lazy as _
from geopy.distance import geodesic
from rest_framework import status
from rest_framework.permissions import IsAuthenticated
from rest_framework.response import Response
from rest_framework.views import APIView

from base.models import Company
from geofencing.forms import GeoFencingSetupForm

from .models import GeoFencing
from .serializers import *


class GeoFencingSetupGetPostAPIView(APIView):
    permission_classes = [IsAuthenticated]

    @method_decorator(
        permission_required("geofencing.view_geofencing", raise_exception=True),
        name="dispatch",
    )
    def get(self, request):
        company = request.user.employee_get.get_company()
        location = get_object_or_404(GeoFencing, company_id=company.id)
        serializer = GeoFencingSetupSerializer(location)
        return Response(serializer.data, status=status.HTTP_200_OK)

    @method_decorator(
        permission_required("geofencing.add_geofencing", raise_exception=True),
        name="dispatch",
    )
    def post(self, request):
        data = request.data
        if not request.user.is_superuser:
            if isinstance(data, QueryDict):
                data = data.dict()
            company = request.user.employee_get.get_company()
            if company:
                data["company_id"] = company.id
        serializer = GeoFencingSetupSerializer(data=request.data)
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=status.HTTP_201_CREATED)
        return Response(serializer.errors, status=status.HTTP_400_BAD_REQUEST)


class GeoFencingSetupPutDeleteAPIView(APIView):
    permission_classes = [IsAuthenticated]

    @method_decorator(
        permission_required("geofencing.change_geofencing", raise_exception=True),
        name="dispatch",
    )
    def put(self, request, pk):
        location = get_object_or_404(GeoFencing, pk=pk)
        company = request.user.employee_get.get_company()
        if request.user.is_superuser or company == location.company_id:
            serializer = GeoFencingSetupSerializer(
                location, data=request.data, partial=True
            )
            if serializer.is_valid():
                serializer.save()
                return Response(serializer.data, status=status.HTTP_200_OK)
            return Response(serializer.errors, status=status.HTTP_400_BAD_REQUEST)
        raise serializers.ValidationError("Access Denied..")

    @method_decorator(
        permission_required("geofencing.delete_geofencing", raise_exception=True),
        name="dispatch",
    )
    def delete(self, request, pk):
        location = get_object_or_404(GeoFencing, pk=pk)
        company = request.user.employee_get.get_company()
        if request.user.is_superuser or company == location.company_id:
            location.delete()
            return Response(
                {"message": "GeoFencing location deleted successfully"},
                status=status.HTTP_200_OK,
            )
        raise serializers.ValidationError("Access Denied..")


class GeoFencingEmployeeLocationCheckAPIView(APIView):
    permission_classes = [IsAuthenticated]

    def get_company(self, request):
        try:
            company = request.user.employee_get.get_company()
            return company
        except Exception as e:
            raise serializers.ValidationError(e)

    def get_company_location(self, request):
        company = self.get_company(request)
        try:
            location = GeoFencing.objects.get(company_id=company)
            return location
        except Exception as e:
            raise serializers.ValidationError(e)

    def post(self, request):
        serializer = EmployeeLocationSerializer(data={
            "latitude": request.data.get("latitude"),
            "longitude": request.data.get("longitude"),
        })

        company_location = self.get_company_location(request)
        if company_location.start:
            if serializer.is_valid():
                geofence_center = (
                    company_location.latitude,
                    company_location.longitude,
                )
                employee_location = (
                    request.data.get("latitude"),
                    request.data.get("longitude"),
                )
                distance = geodesic(geofence_center, employee_location).meters
                if distance <= company_location.radius_in_meters:
                    return Response(
                        {"message": "Inside the geofence"}, status=status.HTTP_200_OK
                    )
                return Response(
                    {"message": "Outside the geofence"},
                    status=status.HTTP_400_BAD_REQUEST,
                )
            return Response(serializer.errors, status=status.HTTP_400_BAD_REQUEST)
        raise serializers.ValidationError("Geofencing is not yet started..")


class GeoFencingSetUpPermissionCheck(APIView):
    permission_classes = [IsAuthenticated]

    @method_decorator(
        permission_required("geofencing.view_geofencing", raise_exception=True),
        name="dispatch",
    )
    def get(self, request):
        return Response(status=200)


def get_company(request):
    try:
        selected_company = request.session.get("selected_company")
        if selected_company == "all":
            return None
        company = Company.objects.get(id=selected_company)
        return company
    except Exception as e:
        raise serializers.ValidationError(e)


def get_company_location(request):
    company = get_company(request)
    try:
        location = GeoFencing.objects.get(company_id=company)
        return location
    except Exception as e:
        raise serializers.ValidationError(e)


@login_required
@permission_required("geofencing.add_localbackup")
def geo_location_config(request):
    location_obj = None
    if request.method == "POST":
        try:
            location_obj = get_company_location(request)
            form = GeoFencingSetupForm(request.POST, instance=location_obj)
        except Exception:
            data = request.POST
            if isinstance(data, QueryDict):
                data = data.dict()
            if get_company(request) is None:
                data["company_id"] = None
            else:
                data["company_id"] = get_company(request).id
            form = GeoFencingSetupForm(data=data)

        if form.is_valid():
            saved = form.save()
            location_obj = saved
            messages.success(request, _("Geofencing config saved successfully."))
        else:
            messages.error(request, _("Please correct the errors below."))
    else:
        try:
            location_obj = get_company_location(request)
            form = GeoFencingSetupForm(instance=location_obj)
        except Exception:
            form = GeoFencingSetupForm(initial={"start": False})

    geofencing_enabled = bool(getattr(location_obj, "start", False))
    return render(
        request,
        "geo_config.html",
        {
            "form": form,
            "location_capture_enabled": True,
            "geofencing_enabled": geofencing_enabled,
        },
    )
