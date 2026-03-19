from __future__ import annotations

from typing import Iterable

from attendance.models import Attendance, AttendanceRequestFile
from base.methods import get_subordinate_employee_ids


def user_is_request_owner(user, attendance: Attendance) -> bool:
    try:
        return attendance.employee_id.employee_user_id == user
    except Exception:
        return False


def user_can_manage_request(user, attendance: Attendance) -> bool:
    if user_is_request_owner(user, attendance):
        return True
    try:
        if getattr(user, "is_superuser", False):
            return True
    except Exception:
        pass
    try:
        employee_id = int(getattr(attendance, "employee_id_id", None) or attendance.employee_id.id)
    except Exception:
        return False
    try:
        subordinate_ids = {int(v) for v in (get_subordinate_employee_ids(type("R", (), {"user": user})()) or [])}
    except Exception:
        subordinate_ids = set()
    return employee_id in subordinate_ids


def user_can_approve_request(user, attendance: Attendance) -> bool:
    if user_is_request_owner(user, attendance):
        return False
    try:
        if getattr(user, "is_superuser", False):
            return True
    except Exception:
        pass
    try:
        employee_id = int(getattr(attendance, "employee_id_id", None) or attendance.employee_id.id)
    except Exception:
        return False
    try:
        subordinate_ids = {int(v) for v in (get_subordinate_employee_ids(type("R", (), {"user": user})()) or [])}
    except Exception:
        subordinate_ids = set()
    return employee_id in subordinate_ids


def user_can_view_request(user, attendance: Attendance) -> bool:
    return user_can_manage_request(user, attendance)


def user_can_delete_attachment(user, attendance: Attendance) -> bool:
    if not user_is_request_owner(user, attendance):
        return False
    return bool(getattr(attendance, "is_validate_request", False) and not getattr(attendance, "is_validate_request_approved", False))


def hard_delete_request_attachment(attendance: Attendance, file_obj: AttendanceRequestFile) -> None:
    try:
        attendance.request_attachments.remove(file_obj)
    except Exception:
        pass
    storage = getattr(getattr(file_obj, "file", None), "storage", None)
    file_name = getattr(getattr(file_obj, "file", None), "name", None)
    try:
        file_obj.delete()
    finally:
        if storage and file_name:
            try:
                storage.delete(file_name)
            except Exception:
                pass


def iter_request_attachments(attendance: Attendance) -> Iterable[AttendanceRequestFile]:
    try:
        for f in attendance.request_attachments.all():
            if f:
                yield f
    except Exception:
        return
