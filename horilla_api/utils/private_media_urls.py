from datetime import timezone
from django.urls import reverse

from facedetection.models import EmployeeFaceDetection


def _file_version(file_field):
    if not file_field:
        return None
    name = getattr(file_field, "name", None)
    storage = getattr(file_field, "storage", None)
    if not name or storage is None:
        return None
    try:
        modified = storage.get_modified_time(name)
        if modified is None:
            return None
        if getattr(modified, "tzinfo", None) is not None:
            modified = modified.astimezone(timezone.utc)
        return modified.isoformat().replace("+00:00", "Z")
    except Exception:
        return None


def build_employee_profile_api_version(employee):
    return _file_version(getattr(employee, "employee_profile", None))


def build_employee_face_api_version(employee, face=None):
    face_obj = face
    if face_obj is None:
        employee_id = _object_id(employee)
        if employee_id in (None, ""):
            return None
        try:
            face_obj = EmployeeFaceDetection.objects.filter(employee_id_id=employee_id).only("id", "image").first()
        except Exception:
            face_obj = None
    return _file_version(getattr(face_obj, "image", None))


def _object_id(value):
    if value is None:
        return None
    pk = getattr(value, 'pk', None)
    if pk not in (None, ''):
        return pk
    obj_id = getattr(value, 'id', None)
    if obj_id not in (None, ''):
        return obj_id
    return value if isinstance(value, int) else None


def _maybe_absolute(request, path):
    if not path:
        return None
    try:
        return request.build_absolute_uri(path) if request is not None else path
    except Exception:
        return path


def build_employee_profile_api_url(employee, request=None):
    employee_id = _object_id(employee)
    if employee_id in (None, ''):
        return None
    image = getattr(employee, 'employee_profile', None)
    if not image:
        return None
    return _maybe_absolute(request, reverse('api-employee-profile-image', args=[employee_id]))


def build_employee_face_api_url(employee, request=None, face=None):
    employee_id = _object_id(employee)
    if employee_id in (None, ''):
        return None
    face_obj = face
    if face_obj is None:
        try:
            face_obj = EmployeeFaceDetection.objects.filter(employee_id_id=employee_id).only('id', 'image').first()
        except Exception:
            face_obj = None
    image = getattr(face_obj, 'image', None)
    if not image:
        return None
    return _maybe_absolute(request, reverse('api-employee-face-image', args=[employee_id]))



def _file_name(file_field):
    try:
        import os
        return os.path.basename(getattr(file_field, "name", "") or "file")
    except Exception:
        return "file"


def build_leave_type_icon_api_url(leave_type, request=None):
    leave_type_id = _object_id(leave_type)
    if leave_type_id in (None, ""):
        return None
    icon = getattr(leave_type, "icon", None)
    if not icon:
        return None
    return _maybe_absolute(request, reverse("api-leave-type-icon", args=[leave_type_id]))


def build_leave_request_attachment_meta(leave_request, request=None):
    request_id = _object_id(leave_request)
    attachment = getattr(leave_request, "attachment", None)
    if request_id in (None, "") or not attachment:
        return None
    return {
        "name": _file_name(attachment),
        "view_url": _maybe_absolute(request, reverse("api-leave-request-attachment-view", args=[request_id])),
        "download_url": _maybe_absolute(request, reverse("api-leave-request-attachment-download", args=[request_id])),
    }


def build_leave_allocation_attachment_meta(allocation_request, request=None):
    request_id = _object_id(allocation_request)
    attachment = getattr(allocation_request, "attachment", None)
    if request_id in (None, "") or not attachment:
        return None
    return {
        "name": _file_name(attachment),
        "view_url": _maybe_absolute(request, reverse("api-leave-allocation-request-attachment-view", args=[request_id])),
        "download_url": _maybe_absolute(request, reverse("api-leave-allocation-request-attachment-download", args=[request_id])),
    }


def build_employee_profile_avatar_api_url(employee, request=None):
    employee_id = _object_id(employee)
    if employee_id in (None, ""):
        return None
    image = getattr(employee, "employee_profile", None)
    if not image:
        return None
    return _maybe_absolute(request, reverse("api-employee-profile-avatar", args=[employee_id]))


def build_employee_profile_avatar_api_version(employee):
    return build_employee_profile_api_version(employee)
