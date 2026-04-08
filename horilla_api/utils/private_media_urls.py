from django.urls import reverse

from facedetection.models import EmployeeFaceDetection


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
