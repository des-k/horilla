from __future__ import annotations

from typing import Any

from django.utils import timezone

from attendance.models import EmployeeWfhProfile, EmployeeWfhProfileHistory
from facedetection.models import EmployeeFaceDetection
from geofencing.models import GeoFencing


DEFAULT_WFH_RADIUS_METERS = 250


def _resolve_object_id(value: Any):
    if value is None:
        return None
    pk = getattr(value, "pk", None)
    if pk not in (None, ""):
        return pk
    obj_id = getattr(value, "id", None)
    if obj_id not in (None, ""):
        return obj_id
    return value if isinstance(value, int) else None


def _resolve_company_pk(employee: Any = None, company: Any = None):
    resolved = _resolve_company(employee=employee, company=company)
    return _resolve_object_id(resolved)


def _resolve_company(employee: Any = None, company: Any = None):
    if company is not None:
        return company
    if employee is None:
        return None
    try:
        resolved = employee.get_company()
        if resolved is not None:
            return resolved
    except Exception:
        pass
    return getattr(getattr(employee, "employee_work_info", None), "company_id", None)


def company_wfh_radius_for(*, employee: Any = None, company: Any = None, default: int = DEFAULT_WFH_RADIUS_METERS) -> int:
    company_pk = _resolve_company_pk(employee=employee, company=company)
    if company_pk is None:
        return default
    config = GeoFencing.objects.filter(company_id_id=company_pk).only("wfh_radius_in_meters").first()
    configured = int(getattr(config, "wfh_radius_in_meters", 0) or 0)
    return configured if configured > 0 else default


def effective_wfh_radius_for(*, employee: Any = None, company: Any = None, profile: Any = None, default: int = DEFAULT_WFH_RADIUS_METERS) -> int:
    company_pk = _resolve_company_pk(employee=employee, company=company)
    if company_pk is not None:
        config = GeoFencing.objects.filter(company_id_id=company_pk).only("wfh_radius_in_meters").first()
        configured = int(getattr(config, "wfh_radius_in_meters", 0) or 0)
        if configured > 0:
            return configured
    profile_radius = int(getattr(profile, "home_radius_in_meters", 0) or 0)
    return profile_radius if profile_radius > 0 else default


def sync_wfh_radius_profiles_for_company(*, company: Any = None, employee: Any = None, radius: Any = None) -> int:
    company_pk = _resolve_company_pk(employee=employee, company=company)
    if company_pk is None:
        return 0
    normalized_radius = int(radius or 0)
    if normalized_radius <= 0:
        normalized_radius = company_wfh_radius_for(company=company_pk)
    return EmployeeWfhProfile.objects.filter(
        employee__employee_work_info__company_id_id=company_pk
    ).exclude(home_radius_in_meters=normalized_radius).update(home_radius_in_meters=normalized_radius)


def apply_wfh_home_reset(*, employee, acted_by=None):
    profile, _ = EmployeeWfhProfile.objects.get_or_create(
        employee=employee,
        defaults={"home_radius_in_meters": effective_wfh_radius_for(employee=employee)},
    )
    effective_radius = effective_wfh_radius_for(employee=employee, profile=profile)
    EmployeeWfhProfileHistory.objects.create(
        employee=employee,
        action_type=EmployeeWfhProfileHistory.ActionType.HOME_RESET,
        acted_by=acted_by,
        old_home_latitude=profile.home_latitude,
        old_home_longitude=profile.home_longitude,
        old_radius_in_meters=profile.home_radius_in_meters if profile.home_latitude is not None and profile.home_longitude is not None else None,
        new_home_latitude=None,
        new_home_longitude=None,
        new_radius_in_meters=effective_radius,
        notes="Admin reset WFH home geofence",
    )
    profile.home_latitude = None
    profile.home_longitude = None
    profile.home_radius_in_meters = effective_radius
    profile.is_home_configured = False
    profile.requires_home_reconfiguration = True
    profile.home_configured_at = None
    profile.home_configured_by = None
    profile.last_home_reset_at = timezone.now()
    profile.last_home_reset_by = acted_by
    profile.save(
        update_fields=[
            "home_latitude",
            "home_longitude",
            "home_radius_in_meters",
            "is_home_configured",
            "requires_home_reconfiguration",
            "home_configured_at",
            "home_configured_by",
            "last_home_reset_at",
            "last_home_reset_by",
        ]
    )
    return profile


def apply_wfh_face_reset(*, employee, acted_by=None):
    profile, _ = EmployeeWfhProfile.objects.get_or_create(
        employee=employee,
        defaults={"home_radius_in_meters": effective_wfh_radius_for(employee=employee)},
    )
    employee_pk = _resolve_object_id(employee)
    face = EmployeeFaceDetection.objects.filter(employee_id_id=employee_pk).first() if employee_pk is not None else None
    old_face = getattr(face.image, "url", None) if face and getattr(face, "image", None) else None
    EmployeeWfhProfileHistory.objects.create(
        employee=employee,
        action_type=EmployeeWfhProfileHistory.ActionType.FACE_RESET,
        acted_by=acted_by,
        old_face_image=old_face,
        new_face_image=None,
        notes="Admin reset WFH face detection",
    )
    if face and getattr(face, "image", None):
        face.image.delete(save=False)
        face.image = None
        face.save(update_fields=["image"])
    profile.requires_face_reenrollment = True
    profile.last_face_reset_at = timezone.now()
    profile.last_face_reset_by = acted_by
    profile.save(update_fields=["requires_face_reenrollment", "last_face_reset_at", "last_face_reset_by"])
    return profile
