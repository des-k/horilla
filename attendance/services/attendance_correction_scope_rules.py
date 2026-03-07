"""attendance_correction_scope_rules.py

Rules for Attendance Correction Request stored on Attendance rows.

Scope:
- IN   : only check-in provided
- OUT  : only check-out provided
- FULL : both check-in and check-out provided

Business rule (user requirement):
- For a given employee + date:
  * A session (IN/OUT) that is WAITING blocks another request overlapping that session.
  * A session (IN/OUT) that is APPROVED also blocks another request overlapping that session.
  * FULL overlaps both sessions.

Implementation:
- WAITING is represented by Attendance.is_validate_request == True.
- APPROVED sessions are persisted inside Attendance.requested_data["__meta"]["approved_scopes"]
  so they survive later requests (Horilla may reset is_validate_request_approved).
- For WAITING requests, we also store "__meta.current_scope" to know which session(s)
  are currently in the waiting request.
- IMPORTANT: When applying requested_data via queryset.update(), you MUST filter out "__meta".
"""

from __future__ import annotations

import json
from typing import Any, Dict, List, Optional, Set, Tuple

from django.core.exceptions import ValidationError


def _is_empty(v: Any) -> bool:
    if v is None:
        return True
    if isinstance(v, str) and v.strip() in ("", "None", "null", "NULL"):
        return True
    return False


def infer_scope_from_values(check_in: Any, check_out: Any) -> str:
    has_in = not _is_empty(check_in)
    has_out = not _is_empty(check_out)
    if has_in and has_out:
        return "FULL"
    if has_in:
        return "IN"
    if has_out:
        return "OUT"
    return ""


def scope_to_sessions(scope: str) -> Set[str]:
    s = (scope or "").upper()
    if s == "IN":
        return {"IN"}
    if s == "OUT":
        return {"OUT"}
    if s == "FULL":
        return {"IN", "OUT"}
    return set()


def sessions_to_scope(sessions: Set[str]) -> str:
    s = set(x.upper() for x in sessions)
    if s == {"IN"}:
        return "IN"
    if s == {"OUT"}:
        return "OUT"
    if s == {"IN", "OUT"}:
        return "FULL"
    return ""


def load_requested_data(requested_data: Optional[str]) -> Dict[str, Any]:
    if not requested_data:
        return {}
    if isinstance(requested_data, dict):
        return requested_data
    try:
        d = json.loads(requested_data)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def load_meta(requested_data: Optional[str]) -> Dict[str, Any]:
    d = load_requested_data(requested_data)
    meta = d.get("__meta")
    return meta if isinstance(meta, dict) else {}


def get_approved_scopes(requested_data: Optional[str]) -> List[str]:
    meta = load_meta(requested_data)
    scopes = meta.get("approved_scopes")
    if not isinstance(scopes, list):
        return []
    out: List[str] = []
    for s in scopes:
        if not s:
            continue
        out.append(str(s).upper())
    # de-dup preserve order
    seen: Set[str] = set()
    dedup: List[str] = []
    for s in out:
        if s in seen:
            continue
        seen.add(s)
        dedup.append(s)
    return dedup


def get_current_scope(requested_data: Optional[str]) -> str:
    data = load_requested_data(requested_data)
    meta = data.get("__meta") if isinstance(data.get("__meta"), dict) else {}
    cur = (meta.get("current_scope") or "").upper()
    if cur:
        return cur
    # fallback infer from stored fields
    return infer_scope_from_values(data.get("attendance_clock_in"), data.get("attendance_clock_out"))


def combine_scopes(a: str, b: str) -> str:
    return sessions_to_scope(scope_to_sessions(a) | scope_to_sessions(b))


def validate_new_request_scope(
    *,
    existing_waiting_scope: str,
    approved_scopes: List[str],
    incoming_scope: str,
) -> None:
    """Raise ValidationError if incoming scope overlaps WAITING or APPROVED sessions."""
    incoming_scope = (incoming_scope or "").upper()
    if not incoming_scope:
        raise ValidationError({"attendance_clock_in": "Provide Check-In and/or Check-Out time"})

    incoming_sessions = scope_to_sessions(incoming_scope)

    waiting_scope = (existing_waiting_scope or "").upper()
    waiting_sessions = scope_to_sessions(waiting_scope) if waiting_scope else set()

    approved_sessions: Set[str] = set()
    for s in approved_scopes:
        approved_sessions |= scope_to_sessions(s)

    # 1) Block overlaps with WAITING scope
    if incoming_sessions & waiting_sessions:
        # tailor message
        if waiting_scope == "FULL":
            msg = "There is already a WAITING FULL request for this date."
        elif waiting_scope == "IN":
            msg = "There is already a WAITING IN request for this date. You can only request OUT."
        elif waiting_scope == "OUT":
            msg = "There is already a WAITING OUT request for this date. You can only request IN."
        else:
            msg = "There is already a WAITING attendance correction request for this date."
        raise ValidationError({"non_field_errors": [msg]})

    # 2) Block overlaps with APPROVED scopes
    if incoming_sessions & approved_sessions:
        if incoming_scope == "FULL":
            if approved_sessions == {"IN", "OUT"}:
                msg = "IN and OUT requests have already been approved for this date."
            elif "IN" in approved_sessions:
                msg = "IN request has already been approved for this date. You can only request OUT."
            else:
                msg = "OUT request has already been approved for this date. You can only request IN."
        elif incoming_scope == "IN":
            msg = "IN request has already been approved for this date."
        else:
            msg = "OUT request has already been approved for this date."
        raise ValidationError({"non_field_errors": [msg]})


def build_requested_data_for_save(
    *,
    new_payload: Dict[str, Any],
    existing_requested_data: Optional[str],
    incoming_scope: str,
    keep_existing_fields: bool,
) -> Dict[str, Any]:
    """Build a requested_data dict with __meta.

    - If keep_existing_fields=True (i.e., there's an existing WAITING request),
      merge non-empty new values into existing values so we can add OUT after IN, etc.
    - If keep_existing_fields=False, we start a fresh payload, but still preserve meta.approved_scopes.
    """
    incoming_scope = (incoming_scope or "").upper()
    existing_data = load_requested_data(existing_requested_data)

    # base dict
    if keep_existing_fields:
        out = {k: v for k, v in existing_data.items() if k != "__meta"}
        # merge: overwrite only if new value is non-empty
        for k, v in (new_payload or {}).items():
            if k == "__meta":
                continue
            if _is_empty(v):
                continue
            out[k] = v

        existing_scope = get_current_scope(existing_requested_data)
        combined_scope = combine_scopes(existing_scope, incoming_scope) if existing_scope else incoming_scope
    else:
        out = {k: v for k, v in (new_payload or {}).items() if k != "__meta"}
        combined_scope = incoming_scope

    meta = load_meta(existing_requested_data)
    meta["approved_scopes"] = get_approved_scopes(existing_requested_data)
    meta["current_scope"] = combined_scope
    out["__meta"] = meta
    return out


def record_approved_scope_on_requested_data(requested_data_str: Optional[str]) -> Optional[str]:
    """On approval: add meta.current_scope to meta.approved_scopes and return new JSON."""
    if not requested_data_str:
        return requested_data_str

    data = load_requested_data(requested_data_str)
    meta = data.get("__meta") if isinstance(data.get("__meta"), dict) else {}

    current_scope = (meta.get("current_scope") or "").upper()
    if not current_scope:
        current_scope = infer_scope_from_values(
            data.get("attendance_clock_in"),
            data.get("attendance_clock_out"),
        )
    if not current_scope:
        return requested_data_str

    approved_scopes = get_approved_scopes(requested_data_str)
    if current_scope == "FULL":
        approved_scopes.extend(["IN", "OUT"])
    else:
        approved_scopes.append(current_scope)

    # de-dup
    seen: Set[str] = set()
    dedup: List[str] = []
    for s in approved_scopes:
        if s in seen:
            continue
        seen.add(s)
        dedup.append(s)

    meta["approved_scopes"] = dedup
    meta["current_scope"] = current_scope
    data["__meta"] = meta

    try:
        return json.dumps(data)
    except Exception:
        return requested_data_str
