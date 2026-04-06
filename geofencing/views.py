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
from facedetection.models import EmployeeFaceDetection
from geofencing.forms import GeoFencingSetupForm

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
                    profile, created_profile = EmployeeWfhProfile.objects.get_or_create(
                        employee_id=_object_id(employee),
                        defaults={"home_radius_in_meters": 250},
                    )
                    actor = getattr(request.user, "employee_get", None)
                    if action == "reset_home":
                        EmployeeWfhProfileHistory.objects.create(
                            employee=employee,
                            action_type=EmployeeWfhProfileHistory.ActionType.HOME_RESET,
                            acted_by=actor,
                            old_home_latitude=profile.home_latitude,
                            old_home_longitude=profile.home_longitude,
                            old_radius_in_meters=profile.home_radius_in_meters if profile.home_latitude is not None and profile.home_longitude is not None else None,
                            notes="Admin reset WFH home geofence",
                        )
                        profile.requires_home_reconfiguration = True
                        profile.last_home_reset_at = timezone.now()
                        profile.last_home_reset_by = actor
                        profile.save(update_fields=["requires_home_reconfiguration", "last_home_reset_at", "last_home_reset_by"])
                        messages.success(request, _("WFH home geofence reset."))
                    else:
                        face = EmployeeFaceDetection.objects.filter(employee_id=_object_id(employee)).first()
                        old_face = getattr(face.image, "url", None) if face and getattr(face, "image", None) else None
                        EmployeeWfhProfileHistory.objects.create(
                            employee=employee,
                            action_type=EmployeeWfhProfileHistory.ActionType.FACE_RESET,
                            acted_by=actor,
                            old_face_image=old_face,
                            notes="Admin reset WFH face detection",
                        )
                        profile.requires_face_reenrollment = True
                        profile.last_face_reset_at = timezone.now()
                        profile.last_face_reset_by = actor
                        profile.save(update_fields=["requires_face_reenrollment", "last_face_reset_at", "last_face_reset_by"])
                        messages.success(request, _("WFH face detection reset."))
        else:
            form = GeoFencingSetupForm(request.POST, instance=location_obj, read_only=True)
            if form.is_valid():
                obj = form.save(commit=False)
                obj.company_id = company_id
                if int(getattr(obj, "wfh_radius_in_meters", 0) or 0) <= 0:
                    form.add_error("wfh_radius_in_meters", _("WFH radius must be greater than 0."))
                else:
                    obj.save()
                    messages.success(request, _("WFH geofencing settings updated."))
            else:
                messages.error(request, _("Please correct the errors below."))
    elif location_obj is not None:
        form = GeoFencingSetupForm(instance=location_obj, read_only=True)
    else:
        form = GeoFencingSetupForm(
            initial={"start": False, "wfh_start": True, "wfh_radius_in_meters": 250, "company_id": company_id},
            read_only=True,
        )

    if request.method == "POST" and 'form' not in locals():
        try:
            location_obj = get_company_location(request)
        except Exception:
            location_obj = None
        form = GeoFencingSetupForm(instance=location_obj, read_only=True) if location_obj is not None else GeoFencingSetupForm(initial={"start": False, "wfh_start": True, "wfh_radius_in_meters": 250, "company_id": company_id}, read_only=True)

    employees = Employee.objects.filter(employee_work_info__company_id=company_id).order_by("employee_first_name", "employee_last_name") if company_id and _is_model_instance(company) else Employee.objects.none()

    return render(
        request,
        "geo_config.html",
        {
            "form": form,
            "employees": employees,
            "location_capture_enabled": True,
            "geofencing_enabled": geofencing_is_effectively_enabled(company=company, geofencing=location_obj),
            "geofencing_policy_note": GEOFENCING_DISABLED_NOTE,
            "geofencing_policy_help": GEOFENCING_DISABLED_HELP_TEXT,
        },
    )
