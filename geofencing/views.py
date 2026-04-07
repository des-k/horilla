from django.contrib import messages
from django.contrib.auth.decorators import login_required, permission_required
from django.http import QueryDict
from django.shortcuts import get_object_or_404, render
from django.utils import timezone
from django.utils.decorators import method_decorator
from django.utils.translation import gettext_lazy as _
from django.db.models import Model
from geopy.distance import geodesic
from rest_framework import status
from rest_framework.permissions import IsAuthenticated
from rest_framework.response import Response
from rest_framework.views import APIView

from base.models import Company
from employee.models import Employee
from attendance.models import EmployeeWfhProfile, EmployeeWfhProfileHistory
from attendance.services.wfh_profile import apply_wfh_face_reset, apply_wfh_home_reset, sync_wfh_radius_profiles_for_company
from facedetection.models import EmployeeFaceDetection
from geofencing.forms import GeoFencingSetupForm, WfhGeoFencingConfigForm

from .models import GeoFencing
from .policy import GEOFENCING_DISABLED_HELP_TEXT, GEOFENCING_DISABLED_NOTE, geofencing_is_effectively_enabled
from .serializers import *


def _is_model_instance(value):
    return isinstance(value, Model)


def _object_id(value):
    if value is None:
        return None
    pk = getattr(value, "pk", None)
    if pk not in (None, ""):
        return pk
    obj_id = getattr(value, "id", None)
    if obj_id not in (None, ""):
        return obj_id
    return value if isinstance(value, int) else None


def _can_reset_wfh_home(user):
    return bool(
        user
        and (
            getattr(user, "is_superuser", False)
            or user.has_perm("attendance.reset_wfh_home_geofence")
        )
    )


def _can_reset_wfh_face(user):
    return bool(
        user
        and (
            getattr(user, "is_superuser", False)
            or user.has_perm("attendance.reset_wfh_face_detection")
        )
    )


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
            instance = serializer.save()
            return Response(GeoFencingSetupSerializer(instance).data, status=status.HTTP_201_CREATED)
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
                instance = serializer.save()
                return Response(GeoFencingSetupSerializer(instance).data, status=status.HTTP_200_OK)
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
            location = GeoFencing.objects.get(company_id=_object_id(company))
            return location
        except Exception as e:
            raise serializers.ValidationError(e)

    def post(self, request):
        serializer = EmployeeLocationSerializer(data={
            "latitude": request.data.get("latitude"),
            "longitude": request.data.get("longitude"),
        })

        company_location = self.get_company_location(request)
        if serializer.is_valid():
            if geofencing_is_effectively_enabled(company=self.get_company(request), geofencing=company_location):
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
                        {"message": "Location accepted"}, status=status.HTTP_200_OK
                    )
                return Response(
                    {"message": "Outside the geofence"},
                    status=status.HTTP_400_BAD_REQUEST,
                )
            return Response(
                {"message": "Location accepted"},
                status=status.HTTP_200_OK,
            )
        return Response(serializer.errors, status=status.HTTP_400_BAD_REQUEST)


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
    company_id = _object_id(company)
    if company_id is None or (company is not None and not _is_model_instance(company)):
        raise serializers.ValidationError("Company geofencing not available")
    try:
        location = GeoFencing.objects.get(company_id=company_id)
        return location
    except Exception as e:
        raise serializers.ValidationError(e)


@login_required
@permission_required("geofencing.add_localbackup")
def geo_location_config(request):
    location_obj = None
    company = get_company(request)
    company_id = _object_id(company)

    try:
        location_obj = get_company_location(request)
    except Exception:
        location_obj = None

    main_form = None
    wfh_form = None

    if request.method == "POST":
        action = request.POST.get("action")
        if action in {"reset_home", "reset_face"}:
            allowed = _can_reset_wfh_home(request.user) if action == "reset_home" else _can_reset_wfh_face(request.user)
            if not allowed:
                messages.error(request, _("Permission denied."))
            else:
                employee_pk = request.POST.get("employee_id")
                employee = Employee.objects.filter(pk=employee_pk).first()
                if employee is None:
                    messages.error(request, _("Please choose a valid employee."))
                else:
                    actor = getattr(request.user, "employee_get", None)
                    if action == "reset_home":
                        apply_wfh_home_reset(employee=employee, acted_by=actor)
                        messages.success(request, _("WFH home geofence reset."))
                    else:
                        apply_wfh_face_reset(employee=employee, acted_by=actor)
                        messages.success(request, _("WFH face detection reset."))
        elif action == "update_wfh_config":
            bound_instance = location_obj
            if bound_instance is None:
                bound_instance = GeoFencing(
                    company_id=company,
                    latitude=0.0,
                    longitude=0.0,
                    radius_in_meters=0,
                    start=False,
                    wfh_start=True,
                    wfh_radius_in_meters=250,
                )
            wfh_form = WfhGeoFencingConfigForm(request.POST, instance=bound_instance)
            if wfh_form.is_valid():
                cleaned = wfh_form.cleaned_data
                defaults = {
                    "wfh_start": cleaned.get("wfh_start", True),
                    "wfh_radius_in_meters": cleaned.get("wfh_radius_in_meters", 250),
                }
                if location_obj is None:
                    defaults.update(
                        {
                            "start": False,
                            "latitude": 0.0,
                            "longitude": 0.0,
                            "radius_in_meters": 0,
                        }
                    )
                obj, _created = GeoFencing.objects.update_or_create(
                    company_id=company,
                    defaults=defaults,
                )
                sync_wfh_radius_profiles_for_company(company=company, radius=obj.wfh_radius_in_meters)
                location_obj = obj
                wfh_form = WfhGeoFencingConfigForm(instance=obj)
                messages.success(request, _("WFH geofencing settings updated."))
            else:
                messages.error(request, _("Please correct the errors below."))

    if main_form is None:
        if location_obj is not None:
            main_form = GeoFencingSetupForm(instance=location_obj, read_only=True, include_wfh_fields=False, hide_submit=True)
        else:
            main_form = GeoFencingSetupForm(
                initial={"start": False, "company_id": company_id},
                read_only=True,
                include_wfh_fields=False,
                hide_submit=True,
            )
    if wfh_form is None:
        if location_obj is not None:
            wfh_form = WfhGeoFencingConfigForm(instance=location_obj)
        else:
            wfh_form = WfhGeoFencingConfigForm(initial={"wfh_start": True, "wfh_radius_in_meters": 250, "company_id": company_id})

    employees = Employee.objects.filter(employee_work_info__company_id=company_id).order_by("employee_first_name", "employee_last_name") if company_id and _is_model_instance(company) else Employee.objects.none()

    return render(
        request,
        "geo_config.html",
        {
            "form": main_form,
            "wfh_form": wfh_form,
            "employees": employees,
            "location_capture_enabled": True,
            "geofencing_enabled": geofencing_is_effectively_enabled(company=company, geofencing=location_obj),
            "geofencing_policy_note": GEOFENCING_DISABLED_NOTE,
            "geofencing_policy_help": GEOFENCING_DISABLED_HELP_TEXT,
        },
    )
