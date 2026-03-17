from __future__ import annotations

import json
from typing import Optional

from attendance.models import AttendanceRequestAuditLog


def log_request_action(*, attendance=None, work_mode_request=None, actor=None, action_type: str, old_status: Optional[str] = None, new_status: Optional[str] = None, remark: Optional[str] = None, metadata: Optional[dict] = None):
    if attendance is None and work_mode_request is None:
        return None
    note = (remark or "").strip() or None
    if metadata:
        try:
            meta = json.dumps(metadata, default=str, ensure_ascii=False)
        except Exception:
            meta = str(metadata)
        note = f"{note}\nMETA: {meta}" if note else f"META: {meta}"
    return AttendanceRequestAuditLog.objects.create(
        attendance=attendance,
        work_mode_request=work_mode_request,
        actor=actor,
        action_type=action_type,
        old_status=old_status,
        new_status=new_status,
        remark=note,
    )
