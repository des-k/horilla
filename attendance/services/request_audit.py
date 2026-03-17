from __future__ import annotations

from typing import Optional

from attendance.models import AttendanceRequestAuditLog


def log_request_action(
    *,
    attendance=None,
    work_mode_request=None,
    actor=None,
    action_type: str,
    old_status: Optional[str] = None,
    new_status: Optional[str] = None,
    remark: Optional[str] = None,
    metadata: Optional[dict] = None,
):
    if attendance is None and work_mode_request is None:
        return None
    return AttendanceRequestAuditLog.objects.create(
        attendance=attendance,
        work_mode_request=work_mode_request,
        actor=actor,
        action_type=action_type,
        old_status=old_status,
        new_status=new_status,
        remark=(remark or "").strip() or None,
        metadata=metadata or None,
    )
