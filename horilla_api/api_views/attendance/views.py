from datetime import date, datetime, timedelta, timezone
import json

from django import template
from django.conf import settings
from django.core.mail import EmailMessage
from django.db import transaction
from django.db.models import Case, CharField, F, Value, When
from django.http import QueryDict
from django.shortcuts import get_object_or_404
from django.utils import timezone as dj_timezone
from django.utils.decorators import method_decorator
from rest_framework import status
from rest_framework.pagination import PageNumberPagination
from rest_framework.permissions import IsAuthenticated
from rest_framework.response import Response
from rest_framework.views import APIView
from rest_framework.parsers import MultiPartParser, FormParser, JSONParser

import logging

logger = logging.getLogger(__name__)

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceLateComeEarlyOut,
    EmployeeShiftDay,
    WorkModeRequest,
    AttendanceWorkMode,
    WorkModeRequestScope,
    WorkModeRequestStatus,
    WorkModeRequestRejectReasonCode,
)
from attendance.views.clock_in_out import *
from attendance.views.clock_in_out import clock_out
import attendance.views.clock_in_out as cio  # Access underscore helpers excluded by import *

from attendance.services.work_type_request_rules import (
    effective_work_type,
    punch_allowed,
    auto_reject_wfa_waiting_for_date,
    apply_rejection_to_attendance,
    has_attachments,
)

from attendance.views.dashboard import (
    find_expected_attendances,
    find_late_come,
    find_on_time,
)
from attendance.views.views import *
from base.backends import ConfiguredEmailBackend
from base.methods import generate_pdf, is_reportingmanager, filtersubordinates, get_subordinate_employee_ids
from base.models import HorillaMailTemplate
from employee.filters import EmployeeFilter
from employee.models import EmployeeWorkInformation

from ...api_decorators.base.decorators import (
    manager_permission_required,
    permission_required,
)
from ...api_methods.base.methods import groupby_queryset, permission_based_queryset
from ...api_serializers.attendance.serializers import (
    AttendanceActivitySerializer,
    AttendanceLateComeEarlyOutSerializer,
    AttendanceOverTimeSerializer,
    AttendanceRequestSerializer,
    AttendanceSerializer,
    MailTemplateSerializer,
    UserAttendanceDetailedSerializer,
    UserAttendanceListSerializer,
    WorkModeRequestSerializer,
)


# Create your views here.


def query_dict(data):
    query_dict = QueryDict("", mutable=True)
    for key, value in data.items():
        if isinstance(value, list):
            for item in value:
                query_dict.appendlist(key, item)
        else:
            query_dict.update({key: value})
    return query_dict


def _is_attendance_exempt_manager(employee) -> bool:
    """Return True if employee should be excluded from IN/OUT attendance.

    Custom rule requested: if an employee is a reporting manager of at least one
    other employee, they act as "approver-only" and use an external attendance
    system. They can still approve, but must not punch or be counted as missing.
    """

    try:
        return (
            EmployeeWorkInformation.objects.filter(reporting_manager_id=employee)
            .only("id")
            .exists()
        )
    except Exception:
        return False


# -----------------------------------------------------------------------------
# Mobile single-session helpers# -----------------------------------------------------------------------------
# Work-mode helpers (WFO/WFA/ON_DUTY)
# -----------------------------------------------------------------------------
def _pick_work_mode_request(employee, target_date: date, want: str):
    """Return the *effective* WorkModeRequest for the given date.

    Kept for backward compatibility; core resolution is delegated to
    ``attendance.services.work_type_request_rules``.
    """
    return effective_work_type(employee, target_date, want).request


def _resolve_effective_work_type(employee, target_date: date, want: str):
    """Return tuple (mode, source, request)."""
    eff = effective_work_type(employee, target_date, want)
    return eff.mode, eff.source, eff.request


def _mode_from_request(req) -> str:
    # Compatibility helper
    return req.mode if req else AttendanceWorkMode.WFO


def _is_punch_allowed(mode: str, req, source: str):
    from attendance.services.work_type_request_rules import EffectiveWorkType
    return punch_allowed(EffectiveWorkType(mode=mode, source=source, request=req))

def _requires_proof(mode: str) -> bool:
    return mode in (AttendanceWorkMode.WFA, AttendanceWorkMode.ON_DUTY)

def _parse_location_payload(request) -> dict | None:
    """Parse location payload from request.data (multipart or JSON).
    Accepts:
      - location: dict or JSON string
      - lat/lng/accuracy/provider/captured_at
      - latitude/longitude
    """
    data = getattr(request, "data", {}) or {}
    loc = data.get("location", None)
    if loc:
        if isinstance(loc, str):
            try:
                loc = json.loads(loc)
            except Exception:
                loc = None
        if isinstance(loc, dict):
            return loc

    # Flat keys
    lat = data.get("lat", None) or data.get("latitude", None)
    lng = data.get("lng", None) or data.get("longitude", None)
    if lat is None or lng is None:
        return None

    def _to_float(v):
        try:
            return float(v)
        except Exception:
            return None

    lat_f = _to_float(lat)
    lng_f = _to_float(lng)
    if lat_f is None or lng_f is None:
        return None

    payload = {"lat": lat_f, "lng": lng_f}

    acc = data.get("accuracy", None)
    if acc is not None:
        try:
            payload["accuracy"] = float(acc)
        except Exception:
            payload["accuracy"] = acc

    provider = data.get("provider", None) or data.get("source", None)
    if provider:
        payload["provider"] = str(provider)

    captured_at = data.get("captured_at", None) or data.get("timestamp", None)
    if captured_at:
        payload["captured_at"] = str(captured_at)

    return payload


def _is_admin_with_perm(request, perm_codename: str) -> bool:
    try:
        return bool(request.user and request.user.has_perm(perm_codename))
    except Exception:
        return False


def _is_supervisor_of(request, employee_id: int) -> bool:
    """True if request.user is in the reporting chain above `employee_id`."""
    try:
        sub_ids = get_subordinate_employee_ids(request, nested=True)
        return int(employee_id) in set(map(int, sub_ids or []))
    except Exception:
        return False


def _can_act_on_employee(request, employee_id: int, perm_codename: str, allow_owner: bool = False) -> bool:
    """Admin (has perm) OR supervisor of employee. Optionally allow owner."""
    if _is_admin_with_perm(request, perm_codename):
        return True

    try:
        my_emp = request.user.employee_get
        if allow_owner and my_emp and int(my_emp.id) == int(employee_id):
            return True
    except Exception:
        pass

    return _is_supervisor_of(request, employee_id)


# -----------------------------------------------------------------------------
def _api_now(request) -> datetime:
    """
    Resolve a request datetime.

    Priority:
    1) request.datetime (if injected by a wrapper)
    2) timezone-aware now() if USE_TZ
    3) naive datetime.now()
    """
    dt_attr = getattr(request, "datetime", None)
    if dt_attr:
        return dt_attr
    if getattr(settings, "USE_TZ", False):
        return dj_timezone.localtime(dj_timezone.now())
    return datetime.now()


def _api_today(request, dt_now: datetime) -> date:
    """Resolve a request date if provided, otherwise use dt_now.date()."""
    d_attr = getattr(request, "date", None)
    return d_attr if isinstance(d_attr, date) else dt_now.date()


def _coerce_datetime_like(dt_value: datetime | None, ref_dt: datetime) -> datetime | None:
    """Ensure dt_value has the same timezone-awareness as ref_dt.

    - If USE_TZ=True and dt_value is naive, make it aware using ref_dt.tzinfo (or current timezone).
    - If USE_TZ=True and dt_value is aware, convert to ref_dt's timezone for safe comparison.
    - If USE_TZ=False and dt_value is aware, make it naive.
    """
    if dt_value is None:
        return None

    use_tz = getattr(settings, "USE_TZ", False)

    if use_tz:
        # ref tzinfo: prefer ref_dt, fallback to Django current timezone.
        ref_tz = ref_dt.tzinfo if dj_timezone.is_aware(ref_dt) and ref_dt.tzinfo else dj_timezone.get_current_timezone()

        if dj_timezone.is_naive(dt_value):
            return dj_timezone.make_aware(dt_value, ref_tz)

        # dt_value aware: normalize to ref_tz for consistent comparisons
        try:
            return dj_timezone.localtime(dt_value, ref_tz)
        except Exception:
            return dt_value

    # USE_TZ=False
    if dj_timezone.is_aware(dt_value):
        try:
            return dj_timezone.make_naive(dt_value)
        except Exception:
            return dt_value
    return dt_value


def _normalize_none(value):
    """Normalize common empty string values to Python None."""
    if value is None:
        return None
    if isinstance(value, str) and value.strip() in ("", "None", "null", "NULL"):
        return None
    return value


def _format_minimum_hour(value):
    """Return minimum working hour in HH:MM (string) or None."""
    if value is None:
        return None
    # Already HH:MM / HH:MM:SS string
    if isinstance(value, str):
        s = value.strip()
        if not s or s.lower() in ("none", "null"):
            return None
        # Keep only HH:MM if seconds present
        if len(s) >= 5 and s[2] == ":":
            return s[:5]
        return s
    # datetime.time
    try:
        return value.strftime("%H:%M")
    except Exception:
        pass
    # timedelta (best effort)
    try:
        total_seconds = int(value.total_seconds())
        if total_seconds < 0:
            return None
        h = (total_seconds // 3600) % 24
        m = (total_seconds % 3600) // 60
        return f"{h:02d}:{m:02d}"
    except Exception:
        return str(value)



def _normalize_requested_data(requested_data: dict) -> dict:
    """Normalize JSON-requested_data so it can be used safely in queryset.update()."""
    if not requested_data:
        return requested_data

    for key in (
        "attendance_date",
        "attendance_clock_in_date",
        "attendance_clock_out_date",
        "attendance_clock_in",
        "attendance_clock_out",
        "attendance_worked_hour",
        "minimum_hour",
        "batch_attendance_id",
        "shift_id",
        "work_type_id",
    ):
        if key in requested_data:
            requested_data[key] = _normalize_none(requested_data[key])

    return requested_data


def _api_resolve_attendance_date_and_day(shift, dt_now: datetime):
    """
    Apply Horilla night-shift noon-to-noon rule to resolve attendance_date and day.

    Strategy:
    - Prefer resolving the day via EmployeeShiftSchedule for the employee's shift.
    - Fall back to any EmployeeShiftDay row if no schedule row exists.

    Returns:
        attendance_date, day_obj, minimum_hour, start_time_sec, end_time_sec, now_hhmm, now_sec
    """
    date_today = dt_now.date()
    now_hhmm = dt_now.strftime("%H:%M")
    now_sec = strtime_seconds(now_hhmm)
    mid_day_sec = strtime_seconds("12:00")

    def _resolve_for_date(d: date):
        weekday = d.strftime("%A").lower()

        schedule = None
        try:
            schedule = cio.EmployeeShiftSchedule.objects.filter(
                shift_id=shift, day__day=weekday
            ).select_related("day").first()
        except Exception:
            schedule = None

        if schedule:
            day_obj = schedule.day
            minimum_hour = schedule.minimum_working_hour or "00:00"
            try:
                start_time_sec = strtime_seconds(schedule.start_time.strftime("%H:%M")) if schedule.start_time else 0
                end_time_sec = strtime_seconds(schedule.end_time.strftime("%H:%M")) if schedule.end_time else 0
            except Exception:
                start_time_sec, end_time_sec = 0, 0
            return day_obj, minimum_hour, start_time_sec, end_time_sec

        # Fallback (best-effort)
        day_obj = EmployeeShiftDay.objects.filter(day=weekday).first()
        if not day_obj:
            return None, "00:00", 0, 0
        minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day_obj, shift=shift)
        return day_obj, minimum_hour, start_time_sec, end_time_sec

    attendance_date = date_today
    day, minimum_hour, start_time_sec, end_time_sec = _resolve_for_date(date_today)

    is_night_shift = start_time_sec > end_time_sec and start_time_sec != end_time_sec

    if is_night_shift and mid_day_sec > now_sec:
        date_yesterday = date_today - timedelta(days=1)
        attendance_date = date_yesterday
        day, minimum_hour, start_time_sec, end_time_sec = _resolve_for_date(date_yesterday)

    return attendance_date, day, minimum_hour, start_time_sec, end_time_sec, now_hhmm, now_sec

def _ensure_single_session_activity(attendance: Attendance, prev_attendance_date: date | None = None) -> AttendanceActivity:
    """
    Ensure exactly one AttendanceActivity exists for (employee, attendance_date),
    aligned to the approved Attendance values.

    If attendance_date changed, old-date activities are either moved (if no target exists)
    or deleted (if a target already exists).
    """
    employee = attendance.employee_id
    target_date = attendance.attendance_date

    if prev_attendance_date and prev_attendance_date != target_date:
        old_qs = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=prev_attendance_date)
        if old_qs.exists():
            if not AttendanceActivity.objects.filter(employee_id=employee, attendance_date=target_date).exists():
                old_qs.update(attendance_date=target_date)
            else:
                old_qs.delete()

    qs = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=target_date).order_by("-id")
    activity = qs.first()
    if activity:
        qs.exclude(id=activity.id).delete()
    else:
        activity = AttendanceActivity(employee_id=employee, attendance_date=target_date)

    # Resolve shift day
    day = attendance.attendance_day
    if not day:
        day = EmployeeShiftDay.objects.get(day=target_date.strftime("%A").lower())

    # AttendanceActivity requires a non-null clock_in
    clock_in_date = attendance.attendance_clock_in_date or attendance.attendance_clock_out_date or target_date
    clock_in_time = attendance.attendance_clock_in or attendance.attendance_clock_out or datetime.strptime("00:00", "%H:%M").time()

    activity.shift_day = day
    activity.clock_in_date = clock_in_date
    activity.clock_in = clock_in_time

    if hasattr(activity, "in_datetime"):
        activity.in_datetime = datetime.combine(clock_in_date, clock_in_time)

    # Sync OUT fields
    if attendance.attendance_clock_out and attendance.attendance_clock_out_date:
        if hasattr(activity, "clock_out_date"):
            activity.clock_out_date = attendance.attendance_clock_out_date
        if hasattr(activity, "clock_out"):
            activity.clock_out = attendance.attendance_clock_out
        if hasattr(activity, "out_datetime"):
            activity.out_datetime = datetime.combine(attendance.attendance_clock_out_date, attendance.attendance_clock_out)
    else:
        if hasattr(activity, "clock_out_date"):
            activity.clock_out_date = None
        if hasattr(activity, "clock_out"):
            activity.clock_out = None
        if hasattr(activity, "out_datetime"):
            activity.out_datetime = None

    activity.save()
    return activity


def _rebuild_late_early(attendance: Attendance):
    """
    Recompute late come / early out records after an approval or time edit.
    """
    shift = attendance.shift_id
    if not shift:
        return

    day = EmployeeShiftDay.objects.get(day=attendance.attendance_date.strftime("%A").lower())

    AttendanceLateComeEarlyOut.objects.filter(
        attendance_id=attendance, type__in=["late_come", "early_out"]
    ).delete()

    _, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)

    schedule = None
    if hasattr(cio, "_get_schedule"):
        try:
            schedule = cio._get_schedule(shift, day)
        except Exception:
            schedule = None

    if attendance.attendance_clock_in:
        late_come(
            attendance=attendance,
            start_time=start_time_sec,
            end_time=end_time_sec,
            shift=shift,
            schedule=schedule,
        )

    if attendance.attendance_clock_out:
        early_out(
            attendance=attendance,
            start_time=start_time_sec,
            end_time=end_time_sec,
            shift=shift,
            schedule=schedule,
        )


class ClockInAPIView(APIView):
    """Mobile Clock-In (single-session + hybrid mode).

    Rules:
    - WFO is recorded via biometric device only (mobile forbidden).
    - WFA requires an APPROVED WorkModeRequest that covers IN.
    - ON_DUTY allows punch with PENDING/APPROVED request that covers IN (presence-only).
    - Enforce check-in cutoff when configured.
    - Require photo+location for WFA/ON_DUTY (audit).
    """

    permission_classes = [IsAuthenticated]
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def post(self, request):
        employee, work_info = employee_exists(request)
        if not employee or work_info is None:
            return Response(
                {"error": "Missing work information or employee details."},
                status=status.HTTP_400_BAD_REQUEST,
            )

        if _is_attendance_exempt_manager(employee):
            return Response(
                {
                    "error": "Attendance is disabled for reporting managers (approver-only).",
                    "attendance_enabled": False,
                    "attendance_exempt_reason": "REPORTING_MANAGER",
                },
                status=status.HTTP_403_FORBIDDEN,
            )

        if _is_attendance_exempt_manager(employee):
            return Response(
                {
                    "error": "Attendance is disabled for reporting managers (approver-only).",
                    "attendance_enabled": False,
                    "attendance_exempt_reason": "REPORTING_MANAGER",
                },
                status=status.HTTP_403_FORBIDDEN,
            )

        dt_now = _api_now(request)
        shift = work_info.shift_id
        date_today = _api_today(request, dt_now)

        # Resolve attendance date (night shift aware)
        attendance_date, day, minimum_hour, start_time_sec, end_time_sec, now_hhmm, _ = (
            _api_resolve_attendance_date_and_day(shift, dt_now)
        )

        # Resolve work type for IN (request overrides schedule)
        in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")

        if in_mode == AttendanceWorkMode.WFO:
            return Response(
                {"error": "WFO attendance must be recorded via biometric device."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if not _is_punch_allowed(in_mode, in_req, in_source):
            msg = "Request is required." if not in_req else "Request is not approved yet."
            if in_mode == AttendanceWorkMode.ON_DUTY and in_req:
                msg = "On Duty request is not active."
            if in_mode == AttendanceWorkMode.WFA and in_req and in_req.status != WorkModeRequestStatus.APPROVED:
                msg = "WFA requires an approved request before clock-in."
            return Response({"error": msg}, status=status.HTTP_403_FORBIDDEN)

        # Already clocked-in?
        existing = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        if existing and getattr(existing, "attendance_clock_in", None):
            return Response({"message": "Already clocked-in"}, status=status.HTTP_400_BAD_REQUEST)

        # Cutoff check-in



        # Cutoff check-in


        rules = {}


        try:


            rules = cio.get_shift_rules(


                attendance_date,


                shift,


                day,


                start_time_sec=start_time_sec,


                end_time_sec=end_time_sec,


            )


        except Exception:


            rules = {"cutoff_in_dt": None}



        cutoff_in_dt = rules.get("cutoff_in_dt")
        cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now) if cutoff_in_dt else None

        # Window start/end (FINAL spec)
        check_in_window_start_dt = rules.get("check_in_window_start_dt")
        check_in_window_end_dt = rules.get("check_in_window_end_dt") or cutoff_in_dt

        check_in_window_start_dt = (
            _coerce_datetime_like(check_in_window_start_dt, dt_now)
            if check_in_window_start_dt
            else None
        )
        check_in_window_end_dt = (
            _coerce_datetime_like(check_in_window_end_dt, dt_now)
            if check_in_window_end_dt
            else None
        )

        # Auto reject WFA waiting (IN/FULL uses cutoff_in)
        try:
            auto_reject_wfa_waiting_for_date(
                employee=employee,
                target_date=attendance_date,
                now_dt=dt_now,
                cutoff_in_dt=cutoff_in_dt,
                cutoff_out_dt=None,
            )
            # Re-resolve effective type after possible auto-reject
            in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        except Exception:
            pass

        if check_in_window_start_dt and dt_now < check_in_window_start_dt:
            return Response(
                {
                    "error": "Check-in window has not started yet.",
                    "check_in_window_start": check_in_window_start_dt.strftime("%H:%M"),
                    "check_in_window_end": check_in_window_end_dt.strftime("%H:%M") if check_in_window_end_dt else None,
                },
                status=status.HTTP_400_BAD_REQUEST,
            )

        if check_in_window_end_dt and dt_now > check_in_window_end_dt:
            return Response(
                {
                    "error": "Check-in cut-off has passed.",
                    "last_allowed": check_in_window_end_dt.strftime("%Y-%m-%d %H:%M"),
                    "check_in_window_start": check_in_window_start_dt.strftime("%H:%M") if check_in_window_start_dt else None,
                    "check_in_window_end": check_in_window_end_dt.strftime("%H:%M"),
                },
                status=status.HTTP_400_BAD_REQUEST,
            )

        # Proof
        image = request.FILES.get("image")
        location = _parse_location_payload(request)

        if _requires_proof(in_mode):
            if not image:
                return Response({"error": "Photo is required."}, status=status.HTTP_400_BAD_REQUEST)
            if not location:
                return Response({"error": "Location is required."}, status=status.HTTP_400_BAD_REQUEST)

        # Persist
        clock_in_attendance_and_activity(
            employee=employee,
            date_today=date_today,
            attendance_date=attendance_date,
            day=day,
            now_hhmm=now_hhmm,
            shift=shift,
            minimum_hour=minimum_hour,
            start_time_sec=start_time_sec,
            end_time_sec=end_time_sec,
            in_datetime=dt_now,
            clock_in_image=image,
            clock_in_mode=in_mode,
            clock_in_location=location,
            work_mode_request=in_req,
            is_presensi_only=(in_mode == AttendanceWorkMode.ON_DUTY),
        )

        # Re-resolve OUT side for consistent response
        out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")
        attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()

        return Response(
            {
                "message": "Clocked-In",
                "attendance_date": str(attendance_date),

                # Legacy
                "in_mode": in_mode,
                "out_mode": out_mode,
                "work_mode_request_id": getattr(in_req, "id", None),

                # New work-type fields
                "in_work_type": in_mode,
                "out_work_type": out_mode,
                "in_work_type_source": in_source,
                "out_work_type_source": out_source,
                "in_work_type_request_id": getattr(in_req, "id", None),
                "out_work_type_request_id": getattr(out_req, "id", None),
                "in_work_type_request_status": getattr(in_req, "status", None),
                "out_work_type_request_status": getattr(out_req, "status", None),

                # Option B (per-punch audit status)
                "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
                "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
                "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
                "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
                "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
                "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,

                "minimum_working_hour": _format_minimum_hour(minimum_hour),
                "server_now": dt_now.isoformat(),
                "server_time": dt_now.strftime("%H:%M"),
            },
            status=status.HTTP_200_OK,
        )

class ClockOutAPIView(APIView):
    """Mobile Clock-Out (single-session + hybrid mode).

    Rules:
    - WFO is recorded via biometric device only (mobile forbidden).
    - WFA requires an APPROVED WorkModeRequest that covers OUT.
    - ON_DUTY allows punch with PENDING/APPROVED request that covers OUT (presence-only).
    - OUT-only requests can clock-out ONLY after check-in cutoff has passed.
    - WFA: allow updating clock-out (last punch wins).
    - ON_DUTY: do NOT allow updating clock-out (only once).
    - Require photo+location for WFA/ON_DUTY (audit).
    """

    permission_classes = [IsAuthenticated]
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def post(self, request):
        employee, work_info = employee_exists(request)
        if not employee or work_info is None:
            return Response(
                {"error": "Missing work information or employee details."},
                status=status.HTTP_400_BAD_REQUEST,
            )

        shift = work_info.shift_id
        dt_now = _api_now(request)

        attendance_date, day, minimum_hour, start_time_sec, end_time_sec, _, now_sec = (
            _api_resolve_attendance_date_and_day(shift, dt_now)
        )

        out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")

        if out_mode == AttendanceWorkMode.WFO:
            return Response(
                {"error": "WFO attendance must be recorded via biometric device."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if not _is_punch_allowed(out_mode, out_req, out_source):
            msg = "Request is required." if not out_req else "Request is not approved yet."
            if out_mode == AttendanceWorkMode.ON_DUTY and out_req:
                msg = "On Duty request is not active."
            if out_mode == AttendanceWorkMode.WFA and out_req and out_req.status != WorkModeRequestStatus.APPROVED:
                msg = "WFA requires an approved request before clock-out."
            return Response({"error": msg}, status=status.HTTP_403_FORBIDDEN)

        # Schedule for cutoffs



        # Shift rules (cutoffs)


        rules = {}


        try:


            rules = cio.get_shift_rules(


                attendance_date,


                shift,


                day,


                start_time_sec=start_time_sec,


                end_time_sec=end_time_sec,


            )


        except Exception:


            rules = {"cutoff_in_dt": None, "cutoff_out_dt": None}



        # Window end (FINAL spec): end_time + max_late_checkout_hours (or schedule cutoff-out)
        window_end_dt = rules.get("check_out_window_end_dt") or rules.get("cutoff_out_dt")
        window_end_dt = _coerce_datetime_like(window_end_dt, dt_now) if window_end_dt else None

        # Auto reject WFA waiting (OUT uses cutoff_out; FULL uses cutoff_in)
        try:
            _cutoff_in_tmp = rules.get("cutoff_in_dt")
            _cutoff_in_tmp = _coerce_datetime_like(_cutoff_in_tmp, dt_now) if _cutoff_in_tmp else None
            auto_reject_wfa_waiting_for_date(
                employee=employee,
                target_date=attendance_date,
                now_dt=dt_now,
                cutoff_in_dt=_cutoff_in_tmp,
                cutoff_out_dt=window_end_dt,
            )
            out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")
        except Exception:
            pass

        # Hard block only AFTER window end (audit should still be allowed for early checkout)
        if window_end_dt and dt_now > window_end_dt:
            return Response(
                {
                    "error": "Check-out window has ended. Please submit an attendance request.",
                    "check_out_window_end": window_end_dt.strftime("%H:%M"),
                },
                status=status.HTTP_400_BAD_REQUEST,
            )

        # Proof
        image = request.FILES.get("image")
        location = _parse_location_payload(request)

        if _requires_proof(out_mode):
            if not image:
                return Response({"error": "Photo is required."}, status=status.HTTP_400_BAD_REQUEST)
            if not location:
                return Response({"error": "Location is required."}, status=status.HTTP_400_BAD_REQUEST)

        # Allow updating checkout for:
        # - WFA (last punch wins)
        # - Any mode when the existing OUT punch is REJECTED (early checkout)
        existing_att = Attendance.objects.filter(
            employee_id=employee, attendance_date=attendance_date
        ).first()
        existing_out_rejected = bool(
            existing_att
            and getattr(existing_att, "out_attendance_status", None) == "REJECTED"
        )
        allow_update = (out_mode == AttendanceWorkMode.WFA) or existing_out_rejected

        try:
            attendance, missing_check_in = cio.clock_out_attendance_and_activity(
                employee=employee,
                attendance_date=attendance_date,
                shift=shift,
                minimum_hour=minimum_hour,
                out_datetime=dt_now,
                day=day,
                clock_out_image=image,
                clock_out_mode=out_mode,
                clock_out_location=location,
                work_mode_request=out_req,
                is_presensi_only=(out_mode == AttendanceWorkMode.ON_DUTY),
                allow_update_clock_out=allow_update,
                raise_if_already_clocked_out=(not allow_update),
            )
        except Exception as error:
            logger.exception("clock_out_attendance_and_activity failed")
            return Response({"error": str(error)}, status=status.HTTP_400_BAD_REQUEST)

        # For presence-only (On Duty), or REJECTED OUT punches, skip late/early calculations
        if (
            attendance
            and not getattr(attendance, "is_presensi_only", False)
            and not missing_check_in
            and getattr(attendance, "out_attendance_status", None) != "REJECTED"
        ):
            try:
                attendance.late_come_early_out.filter(type="early_out").delete()
            except Exception:
                AttendanceLateComeEarlyOut.objects.filter(
                    attendance_id=attendance, type="early_out"
                ).delete()

            schedule = None
            if hasattr(cio, "_get_schedule"):
                try:
                    schedule = cio._get_schedule(shift, day)
                except Exception:
                    schedule = None

            is_night_shift = False
            try:
                is_night_shift = attendance.is_night_shift()
            except Exception:
                pass

            date_today = dt_now.date()
            next_date = attendance.attendance_date + timedelta(days=1)

            if is_night_shift:
                if (attendance.attendance_date == date_today) or (
                    strtime_seconds("12:00") >= now_sec and date_today == next_date
                ):
                    early_out(
                        attendance=attendance,
                        start_time=start_time_sec,
                        end_time=end_time_sec,
                        shift=shift,
                        schedule=schedule,
                    )
            else:
                if attendance.attendance_date == date_today:
                    early_out(
                        attendance=attendance,
                        start_time=start_time_sec,
                        end_time=end_time_sec,
                        shift=shift,
                        schedule=schedule,
                    )

        # Mobile UI hints (optional)
        def _sec_to_hhmm(sec_val):
            try:
                s = int(sec_val)
            except Exception:
                return None
            if s < 0:
                return None
            h = (s // 3600) % 24
            m = (s % 3600) // 60
            return f"{h:02d}:{m:02d}"

        planned_check_out_hhmm = _sec_to_hhmm(end_time_sec)
        late_by_hhmm = None
        work_hours_below_minimum = False
        work_hours_shortfall_hhmm = None
        checked_out_early = False

        # Best-effort compute hints from the persisted attendance row
        try:
            if attendance and not getattr(attendance, "is_presensi_only", False) and not missing_check_in:
                clock_in_t = getattr(attendance, "attendance_clock_in", None)
                clock_out_t = getattr(attendance, "attendance_clock_out", None)
                if clock_in_t and clock_out_t:
                    in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
                    out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date
                    in_dt = _coerce_datetime_like(datetime.combine(in_date, clock_in_t), dt_now)
                    out_dt = _coerce_datetime_like(datetime.combine(out_date, clock_out_t), dt_now)

                    worked_seconds = 0
                    if in_dt and out_dt:
                        worked_seconds = max(0, int((out_dt - in_dt).total_seconds()))

                    # Below-minimum + shortfall
                    min_hhmm = _format_minimum_hour(minimum_hour)
                    if min_hhmm:
                        try:
                            min_s = strtime_seconds(min_hhmm)
                            if min_s and int(worked_seconds) < int(min_s):
                                work_hours_below_minimum = True
                                short_s = int(min_s) - int(worked_seconds)
                                work_hours_shortfall_hhmm = f"{short_s // 3600:02d}:{(short_s % 3600) // 60:02d}"
                        except Exception:
                            pass

                    # Late-by (scheduled start + grace)
                    grace_seconds = int((rules or {}).get("grace_seconds") or 0)
                    planned_in_hhmm = _sec_to_hhmm(start_time_sec)
                    if planned_in_hhmm and in_dt:
                        planned_in_time = datetime.strptime(planned_in_hhmm, "%H:%M").time()
                        planned_in_dt = _coerce_datetime_like(datetime.combine(attendance_date, planned_in_time), dt_now)
                        grace_dt = planned_in_dt + timedelta(seconds=grace_seconds)
                        if in_dt > grace_dt:
                            late_s = int((in_dt - grace_dt).total_seconds())
                            if late_s > 0:
                                late_by_hhmm = f"{late_s // 3600:02d}:{(late_s % 3600) // 60:02d}"

                    # Early check-out (scheduled end)
                    is_night_shift = False
                    try:
                        is_night_shift = start_time_sec > end_time_sec and start_time_sec != end_time_sec
                    except Exception:
                        is_night_shift = False

                    if planned_check_out_hhmm and out_dt:
                        planned_out_date = attendance_date + timedelta(days=1) if is_night_shift else attendance_date
                        planned_out_time = datetime.strptime(planned_check_out_hhmm, "%H:%M").time()
                        planned_out_dt = _coerce_datetime_like(datetime.combine(planned_out_date, planned_out_time), dt_now)
                        if planned_out_dt and out_dt < planned_out_dt:
                            checked_out_early = True
        except Exception:
            # Do not fail clock-out response if hint computation fails.
            pass

        # Re-resolve IN side for consistent response
        in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()

        return Response(
            {
                "message": "Clocked-Out",
                "attendance_date": str(attendance_date),

                # Legacy
                "in_mode": in_mode,
                "out_mode": out_mode,
                "work_mode_request_id": getattr(out_req, "id", None),

                # New work-type fields
                "in_work_type": in_mode,
                "out_work_type": out_mode,
                "in_work_type_source": in_source,
                "out_work_type_source": out_source,
                "in_work_type_request_id": getattr(in_req, "id", None),
                "out_work_type_request_id": getattr(out_req, "id", None),
                "in_work_type_request_status": getattr(in_req, "status", None),
                "out_work_type_request_status": getattr(out_req, "status", None),

                # Option B (per-punch audit status)
                "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
                "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
                "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
                "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
                "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
                "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,

                "missing_check_in": bool(missing_check_in),

            # Option B (per punch audit status)
            "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
            "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
            "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
            "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
            "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
            "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,
                "late_by": late_by_hhmm,
                "planned_check_out": planned_check_out_hhmm,
                "work_hours_below_minimum": bool(work_hours_below_minimum),
                "work_hours_shortfall": work_hours_shortfall_hhmm,
                "checked_out_early": bool(checked_out_early),

                "updated": bool(allow_update),
                "minimum_working_hour": _format_minimum_hour(minimum_hour),
                "server_now": dt_now.isoformat(),
                "server_time": dt_now.strftime("%H:%M"),
            },
            status=status.HTTP_200_OK,
        )

class AttendanceView(APIView):
    """
    Handles CRUD operations for attendance records.

    Methods:
        get_queryset(request, type): Returns filtered attendance records.
        get(request, pk=None, type=None): Retrieves a specific record or a list of records.
        post(request): Creates a new attendance record.
        put(request, pk): Updates an existing attendance record.
        delete(request, pk): Deletes an attendance record and adjusts related overtime if needed.
    """

    permission_classes = [IsAuthenticated]
    filterset_class = AttendanceFilters

    def get_queryset(self, request=None, type=None):
        # Handle schema generation for DRF-YASG
        if getattr(self, "swagger_fake_view", False) or request is None:
            return Attendance.objects.none()
        if type == "ot":

            condition = AttendanceValidationCondition.objects.first()
            minot = strtime_seconds("00:30")
            if condition is not None:
                minot = strtime_seconds(condition.minimum_overtime_to_approve)
                queryset = Attendance.objects.filter(
                    overtime_second__gte=minot,
                    attendance_validated=True,
                )

        elif type == "validated":
            queryset = Attendance.objects.filter(attendance_validated=True)
        elif type == "non-validated":
            queryset = Attendance.objects.filter(attendance_validated=False)
        else:
            queryset = Attendance.objects.all()
        user = request.user
        # checking user level permissions
        perm = "attendance.view_attendance"
        queryset = permission_based_queryset(user, perm, queryset, user_obj=True)
        return queryset

    def get(self, request, pk=None, type=None):
        # individual object workflow
        if pk:
            attendance = get_object_or_404(Attendance, pk=pk)
            serializer = AttendanceSerializer(instance=attendance)
            return Response(serializer.data, status=200)
        # permission based querysete
        attendances = self.get_queryset(request, type)
        # filtering queryset
        attendances_filter_queryset = self.filterset_class(
            request.GET, queryset=attendances
        ).qs
        field_name = request.GET.get("groupby_field", None)
        if field_name:
            url = request.build_absolute_uri()
            return groupby_queryset(
                request, url, field_name, attendances_filter_queryset
            )
        # pagination workflow
        paginater = PageNumberPagination()
        page = paginater.paginate_queryset(attendances_filter_queryset, request)
        serializer = AttendanceSerializer(page, many=True)
        return paginater.get_paginated_response(serializer.data)

    @manager_permission_required("attendance.add_attendance")
    def post(self, request):
        serializer = AttendanceSerializer(data=request.data)
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)
        employee_id = request.data.get("employee_id")
        attendance_date = request.data.get("attendance_date", date.today())
        if Attendance.objects.filter(
            employee_id=employee_id, attendance_date=attendance_date
        ).exists():
            return Response(
                {
                    "error": [
                        "Attendance for this employee on the current date already exists."
                    ]
                },
                status=400,
            )
        return Response(serializer.errors, status=400)

    @method_decorator(permission_required("attendance.change_attendance"))
    def put(self, request, pk):
        try:
            attendance = Attendance.objects.get(id=pk)
        except Attendance.DoesNotExist:
            return Response({"detail": "Attendance record not found."}, status=404)

        serializer = AttendanceSerializer(instance=attendance, data=request.data)

        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)

        # Customize error message for unique constraint
        serializer_errors = serializer.errors
        if "non_field_errors" in serializer.errors:
            unique_error_msg = (
                "The fields employee_id, attendance_date must make a unique set."
            )
            if unique_error_msg in serializer.errors["non_field_errors"]:
                serializer_errors = {
                    "non_field_errors": [
                        "The employee already has attendance on this date."
                    ]
                }
        return Response(serializer_errors, status=400)

    @method_decorator(permission_required("attendance.delete_attendance"))
    def delete(self, request, pk):
        attendance = Attendance.objects.get(id=pk)
        month = attendance.attendance_date
        month = month.strftime("%B").lower()
        overtime = attendance.employee_id.employee_overtime.filter(month=month).last()
        if overtime is not None:
            if attendance.attendance_overtime_approve:
                # Subtract overtime of this attendance
                total_overtime = strtime_seconds(overtime.overtime)
                attendance_overtime_seconds = strtime_seconds(
                    attendance.attendance_overtime
                )
                if total_overtime > attendance_overtime_seconds:
                    total_overtime = total_overtime - attendance_overtime_seconds
                else:
                    total_overtime = attendance_overtime_seconds - total_overtime
                overtime.overtime = format_time(total_overtime)
                overtime.save()
            try:
                attendance.delete()
                return Response({"status", "deleted"}, status=200)
            except Exception as error:
                return Response({"error:", f"{error}"}, status=400)
        else:
            try:
                attendance.delete()
                return Response({"status", "deleted"}, status=200)
            except Exception as error:
                return Response({"error:", f"{error}"}, status=400)


class ValidateAttendanceView(APIView):
    """
    Validates an attendance record and sends a notification to the employee.

    Method:
        put(request, pk): Marks the attendance as validated and notifies the employee.
    """

    permission_classes = [IsAuthenticated]

    def put(self, request, pk):
        attendance = Attendance.objects.filter(id=pk).update(attendance_validated=True)
        attendance = Attendance.objects.filter(id=pk).first()
        try:
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Your attendance for the date {attendance.attendance_date} is validated",
                verb_ar=f"تم تحقيق حضورك في تاريخ {attendance.attendance_date}",
                verb_de=f"Deine Anwesenheit für das Datum {attendance.attendance_date} ist bestätigt.",
                verb_es=f"Se valida tu asistencia para la fecha {attendance.attendance_date}.",
                verb_fr=f"Votre présence pour la date {attendance.attendance_date} est validée.",
                redirect="/attendance/view-my-attendance",
                icon="checkmark",
                api_redirect=f"/api/attendance/attendance?employee_id{attendance.employee_id}",
            )
        except:
            pass
        return Response(status=200)


class OvertimeApproveView(APIView):
    """
    Approves overtime for an attendance record and sends a notification to the employee.

    Method:
        put(request, pk): Marks the overtime as approved and notifies the employee.
    """

    permission_classes = [IsAuthenticated]

    def put(self, request, pk):
        try:
            attendance = Attendance.objects.filter(id=pk).update(
                attendance_overtime_approve=True
            )
        except Exception as E:
            return Response({"error": str(E)}, status=400)

        attendance = Attendance.objects.filter(id=pk).first()
        try:
            notify.send(
                request.user.employee_get,
                recipient=attendance.employee_id.employee_user_id,
                verb=f"Your {attendance.attendance_date}'s attendance overtime approved.",
                verb_ar=f"تمت الموافقة على إضافة ساعات العمل الإضافية لتاريخ {attendance.attendance_date}.",
                verb_de=f"Die Überstunden für den {attendance.attendance_date} wurden genehmigt.",
                verb_es=f"Se ha aprobado el tiempo extra de asistencia para el {attendance.attendance_date}.",
                verb_fr=f"Les heures supplémentaires pour la date {attendance.attendance_date} ont été approuvées.",
                redirect="/attendance/attendance-overtime-view",
                icon="checkmark",
                api_redirect="/api/attendance/attendance-hour-account/",
            )
        except:
            pass
        return Response(status=200)


class AttendanceRequestView(APIView):
    """
    Handles requests for creating, updating, and viewing attendance records.

    Methods:
        get(request, pk=None): Retrieves a specific attendance request by `pk` or a filtered list of requests.
        post(request): Creates a new attendance request.
        put(request, pk): Updates an existing attendance request.
    """

    serializer_class = AttendanceRequestSerializer
    permission_classes = [IsAuthenticated]
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def get(self, request, pk=None):
        if pk:
            attendance = Attendance.objects.get(id=pk)
            serializer = AttendanceRequestSerializer(instance=attendance)
            return Response(serializer.data, status=200)

        requests = Attendance.objects.filter(
            is_validate_request=True,
        )
        requests = filtersubordinates(
            request=request,
            perm="attendance.view_attendance",
            queryset=requests,
        )
        requests = requests | Attendance.objects.filter(
            employee_id__employee_user_id=request.user,
            is_validate_request=True,
        )
        request_filtered_queryset = AttendanceFilters(request.GET, requests).qs
        field_name = request.GET.get("groupby_field", None)
        if field_name:
            # groupby workflow
            url = request.build_absolute_uri()
            return groupby_queryset(request, url, field_name, request_filtered_queryset)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(request_filtered_queryset, request)
        serializer = self.serializer_class(page, many=True)
        return pagenation.get_paginated_response(serializer.data)

    def post(self, request):
        from attendance.forms import NewRequestForm

        form = NewRequestForm(data=request.data, files=getattr(request, "FILES", None))
        if form.is_valid():
            work_type = form.cleaned_data.get("work_type_id")

            if not WorkType.objects.filter(pk=getattr(work_type, "pk", None)).exists():
                form.cleaned_data["work_type_id"] = None

            if form.new_instance is not None:
                form.new_instance.save()

            # Attach proof files (e.g., CCTV screenshots) via AttendanceRequestComment
            try:
                from attendance.models import AttendanceRequestFile, AttendanceRequestComment

                attendance_obj = form.new_instance

                # If this was an update_request (attendance already exists), attach to the existing record.
                if attendance_obj is None:
                    try:
                        from attendance.models import Attendance
                        emp = request.data.get("employee_id") if hasattr(request, "data") else None
                        if not emp:
                            try:
                                emp = request.user.employee_get.id
                            except Exception:
                                emp = None
                        att_date = request.data.get("attendance_date") if hasattr(request, "data") else None
                        if not att_date:
                            from datetime import date as _date
                            att_date = _date.today()
                        attendance_obj = Attendance.objects.filter(employee_id=emp, attendance_date=att_date).first()
                    except Exception:
                        attendance_obj = None

                uploaded = []
                if hasattr(request, "FILES"):
                    uploaded = request.FILES.getlist("files") or []
                    if not uploaded:
                        f_single = request.FILES.get("file")
                        if f_single:
                            uploaded = [f_single]

                if attendance_obj and uploaded:
                    try:
                        actor_emp = request.user.employee_get
                    except Exception:
                        actor_emp = getattr(attendance_obj, "employee_id", None)

                    comment_text = (request.data.get("request_description") if hasattr(request, "data") else None) or (request.data.get("reason") if hasattr(request, "data") else None) or None
                    c = AttendanceRequestComment.objects.create(
                        request_id=attendance_obj,
                        employee_id=actor_emp,
                        comment=(str(comment_text)[:255] if comment_text else None),
                    )
                    for up in uploaded:
                        arf = AttendanceRequestFile.objects.create(file=up)
                        c.files.add(arf)
            except Exception:
                pass

            return Response(form.data, status=200)
        employee_id = request.data.get("employee_id")
        attendance_date = request.data.get("attendance_date", date.today())
        if Attendance.objects.filter(
            employee_id=employee_id, attendance_date=attendance_date
        ).exists():
            return Response(
                {error: list(message) for error, message in form.errors.items()},
                status=400,
            )
        return Response(form.errors, status=404)

    def put(self, request, pk):
        from attendance.forms import AttendanceRequestForm

        attendance = Attendance.objects.get(id=pk)
        form = AttendanceRequestForm(
            data=request.data,
            files=getattr(request, "FILES", None),
            instance=attendance,
        )
        if form.is_valid():
            attendance = Attendance.objects.get(id=form.instance.pk)
            instance = form.save()
            instance.employee_id = attendance.employee_id
            instance.id = attendance.id
            work_type = form.cleaned_data.get("work_type_id")

            if not WorkType.objects.filter(pk=getattr(work_type, "pk", None)).exists():
                form.cleaned_data["work_type_id"] = None
            if attendance.request_type != "create_request":
                attendance.requested_data = json.dumps(instance.serialize())
                attendance.request_description = instance.request_description
                # set the user level validation here
                attendance.is_validate_request = True
                attendance.save()
            else:
                instance.is_validate_request_approved = False
                instance.is_validate_request = True
                instance.save()
            # Attach proof files (optional) via AttendanceRequestComment
            try:
                from attendance.models import AttendanceRequestFile, AttendanceRequestComment
                uploaded = []
                if hasattr(request, "FILES"):
                    uploaded = request.FILES.getlist("files") or []
                    if not uploaded:
                        f_single = request.FILES.get("file")
                        if f_single:
                            uploaded = [f_single]
                if uploaded:
                    try:
                        actor_emp = request.user.employee_get
                    except Exception:
                        actor_emp = attendance.employee_id
                    comment_text = (request.data.get("request_description") if hasattr(request, "data") else None) or (request.data.get("reason") if hasattr(request, "data") else None)
                    c = AttendanceRequestComment.objects.create(
                        request_id=attendance,
                        employee_id=actor_emp,
                        comment=(str(comment_text)[:255] if comment_text else None),
                    )
                    for up in uploaded:
                        arf = AttendanceRequestFile.objects.create(file=up)
                        c.files.add(arf)
            except Exception:
                pass

            return Response(form.data, status=200)
        return Response(form.errors, status=404)


class AttendanceRequestApproveView(APIView):
    """
    Approves and updates an attendance request.

    Single-session behavior:
    - Apply requested_data to Attendance
    - Ensure exactly one AttendanceActivity per (employee, attendance_date)
    - Rebuild late/early markers after approval
    """

    permission_classes = [IsAuthenticated]

    @manager_permission_required("attendance.change_attendance")
    @transaction.atomic
    def put(self, request, pk):
        try:
            attendance = Attendance.objects.select_for_update().get(id=pk)

            # Admin (permission) OR supervisor in reporting chain can approve.
            if not _can_act_on_employee(
                request,
                getattr(attendance, "employee_id_id", None) or attendance.employee_id.id,
                "attendance.change_attendance",
                allow_owner=False,
            ):
                return Response(
                    {"error": "You do not have permission to perform this action."},
                    status=status.HTTP_403_FORBIDDEN,
                )

            prev_attendance_date = attendance.attendance_date

            attendance.attendance_validated = True
            attendance.is_validate_request_approved = True
            attendance.is_validate_request = False
            attendance.request_description = None
            attendance.save()

            if attendance.requested_data is not None:
                requested_data = _normalize_requested_data(json.loads(attendance.requested_data))
                Attendance.objects.filter(id=pk).update(**requested_data)
                attendance.refresh_from_db()
                attendance.save()

            _ensure_single_session_activity(attendance, prev_attendance_date=prev_attendance_date)
            _rebuild_late_early(attendance)

            # FINAL spec: approving an attendance request may approve an early-checkout
            # that was previously stored as REJECTED. Flip it back to VALID and clear reason.
            try:
                if (
                    getattr(attendance, "out_attendance_status", None) == "REJECTED"
                    and getattr(attendance, "out_attendance_reject_reason_code", None)
                    in (
                        "EARLY_CHECKOUT_BEFORE_SHIFT_END",
                        "EARLY_CHECKOUT_BEFORE_CUTOFF_IN",
                    )
                ):
                    attendance.out_attendance_status = "VALID"
                    attendance.out_attendance_reject_reason_code = None

                    # Recompute worked hours from max(real_in, shift_start)
                    if (
                        attendance.attendance_clock_in_date
                        and attendance.attendance_clock_in
                        and attendance.attendance_clock_out_date
                        and attendance.attendance_clock_out
                        and getattr(attendance, "is_presensi_only", False) is False
                    ):
                        shift = getattr(attendance, "shift_id", None)
                        day_obj = getattr(attendance, "attendance_day", None)
                        shift_start_dt = None
                        if shift and day_obj:
                            _min_h, start_sec, end_sec = shift_schedule_today(day=day_obj, shift=shift)
                            rules = cio.get_shift_rules(
                                attendance.attendance_date,
                                shift,
                                day_obj,
                                start_time_sec=start_sec,
                                end_time_sec=end_sec,
                            )
                            shift_start_dt = rules.get("shift_start_dt")

                        in_dt = cio._combine_local_datetime(attendance.attendance_clock_in_date, attendance.attendance_clock_in)
                        out_dt = cio._combine_local_datetime(attendance.attendance_clock_out_date, attendance.attendance_clock_out)
                        worked_start_dt = max(in_dt, shift_start_dt) if shift_start_dt else in_dt
                        duration_seconds = int((out_dt - worked_start_dt).total_seconds())
                        if duration_seconds < 0:
                            duration_seconds = 0

                        attendance.attendance_worked_hour = format_time(duration_seconds)
                        attendance.attendance_overtime = overtime_calculation(attendance)
                    attendance.save()
            except Exception:
                pass

        except Exception as E:
            return Response({"error": str(E)}, status=400)
        return Response({"status": "approved"}, status=200)


class AttendanceRequestCancelView(APIView):
    """
    Cancels an attendance request.

    Fix:
    - Preserve request_type before clearing it
    - If it was a create_request, remove attendance + daily activity rows
    """

    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        try:
            attendance = Attendance.objects.select_for_update().get(id=pk)
            if _can_act_on_employee(
                request,
                getattr(attendance, "employee_id_id", None) or attendance.employee_id.id,
                "attendance.change_attendance",
                allow_owner=True,
            ):
                req_type = attendance.request_type
                req_date = attendance.attendance_date
                req_employee = attendance.employee_id

                attendance.is_validate_request_approved = False
                attendance.is_validate_request = False
                attendance.request_description = None
                attendance.requested_data = None
                attendance.request_type = None
                attendance.save()

                if req_type == "create_request":
                    AttendanceActivity.objects.filter(
                        employee_id=req_employee,
                        attendance_date=req_date,
                    ).delete()
                    AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()
                    attendance.delete()
        except Exception as E:
            return Response({"error": str(E)}, status=400)
        return Response({"status": "success"}, status=200)


class AttendanceRequestRejectView(APIView):
    """Reject an attendance request (admin/supervisor action).

    Note: This differs from *cancel* (owner action). Reject clears the pending request.
    """

    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        try:
            attendance = Attendance.objects.select_for_update().get(id=pk)

            employee_id = getattr(attendance, "employee_id_id", None) or attendance.employee_id.id

            # Owner cannot reject (use cancel) unless admin.
            try:
                if (
                    attendance.employee_id.employee_user_id == request.user
                    and not request.user.has_perm("attendance.change_attendance")
                ):
                    return Response(
                        {"error": "Use cancel for your own request."},
                        status=status.HTTP_403_FORBIDDEN,
                    )
            except Exception:
                pass

            if not _can_act_on_employee(
                request,
                employee_id,
                "attendance.change_attendance",
                allow_owner=False,
            ):
                return Response(
                    {"error": "You do not have permission to perform this action."},
                    status=status.HTTP_403_FORBIDDEN,
                )

            # Optional rejection comment (saved as AttendanceRequestComment)
            comment_text = (
                (request.data.get("comment") if hasattr(request, "data") else None)
                or (request.data.get("reason") if hasattr(request, "data") else None)
                or None
            )
            if comment_text:
                try:
                    from attendance.models import AttendanceRequestComment

                    AttendanceRequestComment.objects.create(
                        request_id=attendance,
                        employee_id=request.user.employee_get,
                        comment=str(comment_text)[:255],
                    )
                except Exception:
                    pass

            req_type = attendance.request_type
            req_date = attendance.attendance_date
            req_employee = attendance.employee_id

            attendance.is_validate_request_approved = False
            attendance.is_validate_request = False
            attendance.request_description = None
            attendance.requested_data = None
            attendance.request_type = None
            attendance.save()

            if req_type == "create_request":
                AttendanceActivity.objects.filter(
                    employee_id=req_employee,
                    attendance_date=req_date,
                ).delete()
                AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()
                attendance.delete()

        except Exception as E:
            return Response({"error": str(E)}, status=400)

        return Response({"status": "rejected"}, status=200)


class WorkModeRequestView(APIView):
    """CRUD for WorkModeRequest (WFA / ON_DUTY).

    Notes:
    - Endpoint aliases expose this as work-type-request.
    - DB model stays WorkModeRequest.
    - Status rules (FINAL spec):
        * WFA: WAITING_FOR_APPROVAL
        * ON_DUTY: PENDING if no attachment; WAITING_FOR_APPROVAL if attachment exists
    - Edit (PATCH/PUT) is restricted: only add attachments and/or update note (reason).
    """

    permission_classes = [IsAuthenticated]
    serializer_class = WorkModeRequestSerializer
    parser_classes = [MultiPartParser, FormParser, JSONParser]

    def get(self, request, pk=None):
        if pk:
            obj = get_object_or_404(WorkModeRequest, pk=pk)
            emp_id = getattr(obj, "employee_id_id", None) or obj.employee_id.id
            if not _can_act_on_employee(
                request,
                emp_id,
                "attendance.view_workmoderequest",
                allow_owner=True,
            ) and not _can_act_on_employee(
                request,
                emp_id,
                "attendance.change_workmoderequest",
                allow_owner=True,
            ):
                return Response(
                    {"error": "You do not have permission to view this request."},
                    status=status.HTTP_403_FORBIDDEN,
                )
            return Response(self.serializer_class(obj).data, status=200)

        qs = WorkModeRequest.objects.all()
        qs = filtersubordinates(request, qs, perm="attendance.view_workmoderequest")

        # mine=1 => only my requests
        if request.GET.get("mine") in ("1", "true", "True"):
            try:
                qs = qs.filter(employee_id=request.user.employee_get)
            except Exception:
                qs = qs.none()

        # Filters
        status_q = request.GET.get("status")
        if status_q:
            qs = qs.filter(status=status_q)

        mode_q = request.GET.get("mode") or request.GET.get("work_type")
        if mode_q:
            qs = qs.filter(mode=mode_q)

        scope_q = request.GET.get("scope")
        if scope_q:
            qs = qs.filter(scope=scope_q)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(qs.order_by("-id"), request)
        serializer = self.serializer_class(page, many=True)
        return pagenation.get_paginated_response(serializer.data)

    def _collect_uploaded_files(self, request):
        uploaded = []
        if hasattr(request, "FILES"):
            uploaded = request.FILES.getlist("files") or []
            if not uploaded:
                f_single = request.FILES.get("file")
                if f_single:
                    uploaded = [f_single]
        return uploaded

    def _attach_files(self, obj: WorkModeRequest, uploaded_files):
        try:
            from attendance.models import AttendanceRequestFile

            for up in uploaded_files:
                arf = AttendanceRequestFile.objects.create(file=up)
                obj.files.add(arf)
        except Exception:
            pass

    @transaction.atomic
    def post(self, request):
        data = request.data.copy() if hasattr(request.data, "copy") else dict(request.data)

        # Backward compatible aliases
        if not data.get("mode") and data.get("work_mode"):
            data["mode"] = data.get("work_mode")
        if not data.get("mode") and data.get("work_type"):
            data["mode"] = data.get("work_type")
        if not data.get("reason") and data.get("description"):
            data["reason"] = data.get("description")
        if not data.get("start_date") and data.get("date"):
            data["start_date"] = data.get("date")
        if not data.get("end_date") and data.get("start_date"):
            data["end_date"] = data.get("start_date")

        # Default employee_id to current user
        try:
            my_emp = request.user.employee_get
        except Exception:
            my_emp = None
        if not data.get("employee_id") and my_emp:
            data["employee_id"] = my_emp.id

        # Non-admin cannot create for other employee
        if my_emp and str(data.get("employee_id")) != str(my_emp.id):
            if not request.user.has_perm("attendance.add_workmoderequest"):
                return Response(
                    {"error": "You do not have permission to create requests for other employees."},
                    status=status.HTTP_403_FORBIDDEN,
                )

        # Disallow WFO
        if str(data.get("mode")) == AttendanceWorkMode.WFO:
            return Response(
                {"error": "WFO should not be requested. Use WFA or ON DUTY."},
                status=status.HTTP_400_BAD_REQUEST,
            )

        serializer = self.serializer_class(data=data)
        if not serializer.is_valid():
            return Response(serializer.errors, status=400)

        # Create with provisional status; finalized after file attach
        obj: WorkModeRequest = serializer.save(status=WorkModeRequestStatus.PENDING)

        uploaded = self._collect_uploaded_files(request)
        if uploaded:
            self._attach_files(obj, uploaded)

        # FINAL status rules
        if obj.mode == AttendanceWorkMode.WFA:
            obj.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
        elif obj.mode == AttendanceWorkMode.ON_DUTY:
            obj.status = (
                WorkModeRequestStatus.WAITING_FOR_APPROVAL
                if has_attachments(obj)
                else WorkModeRequestStatus.PENDING
            )
        obj.save(update_fields=["status"])

        return Response(self.serializer_class(obj).data, status=200)

    def patch(self, request, pk):
        return self._patch_or_put(request, pk)

    @transaction.atomic
    def put(self, request, pk):
        # Backward compatibility: treat PUT as PATCH
        return self._patch_or_put(request, pk)

    def _patch_or_put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)

        is_admin = request.user.has_perm("attendance.change_workmoderequest")
        is_owner = False
        try:
            is_owner = obj.employee_id.employee_user_id == request.user
        except Exception:
            is_owner = False

        if not (is_admin or is_owner):
            return Response(
                {"error": "You do not have permission to update this request."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if obj.status not in (
            WorkModeRequestStatus.PENDING,
            WorkModeRequestStatus.WAITING_FOR_APPROVAL,
        ):
            return Response({"error": "Only PENDING/WAITING requests can be updated."}, status=400)

        # Spec: edit only for adding attachment + note; do not allow changing type/scope/dates
        data = request.data.copy() if hasattr(request.data, "copy") else dict(request.data)
        forbidden = {"mode", "work_type", "work_mode", "scope", "start_date", "end_date", "employee_id"}
        if any(k in data for k in forbidden):
            return Response(
                {"error": "You can only add attachments and/or update note. work_type/scope/dates cannot be changed."},
                status=400,
            )

        # Update reason/note
        note = data.get("reason") or data.get("note") or data.get("description")
        if note is not None:
            obj.reason = str(note)
            obj.save(update_fields=["reason"])

        # Attach files
        uploaded = self._collect_uploaded_files(request)
        if uploaded:
            self._attach_files(obj, uploaded)

        # ON_DUTY: if PENDING and now has attachments => WAITING_FOR_APPROVAL
        if obj.mode == AttendanceWorkMode.ON_DUTY and obj.status == WorkModeRequestStatus.PENDING:
            if has_attachments(obj):
                obj.status = WorkModeRequestStatus.WAITING_FOR_APPROVAL
                obj.save(update_fields=["status"])

        return Response(self.serializer_class(obj).data, status=200)


class WorkModeRequestApprovalsView(APIView):
    """List requests for managers/admins.

    Includes:
    - WAITING_FOR_APPROVAL (approvable)
    - ON_DUTY PENDING (not yet approvable, usually waiting for letter upload)
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        # Ensure stale WFA WAITING are auto-rejected for *today* to keep approvals clean.
        now_dt = _api_now(request)
        today = now_dt.date()
        try:
            # auto reject for current user and subordinates (lightweight per employee)
            emp_ids = []
            if request.user.has_perm("attendance.change_workmoderequest"):
                emp_ids = list(WorkModeRequest.objects.filter(
                    mode=AttendanceWorkMode.WFA,
                    status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
                    start_date__lte=today,
                    end_date__gte=today,
                ).values_list("employee_id", flat=True).distinct())
            else:
                emp_ids = get_subordinate_employee_ids(request, nested=True) or []

            from employee.models import Employee
            for eid in emp_ids:
                emp = Employee.objects.filter(id=eid).first()
                if not emp:
                    continue
                shift = None
                try:
                    shift = emp.employee_work_info.shift_id
                except Exception:
                    shift = None
                if not shift:
                    continue
                day = EmployeeShiftDay.objects.filter(day=today.strftime("%A").lower()).first()
                if not day:
                    continue
                try:
                    _min_hour, start_sec, end_sec = shift_schedule_today(day=day, shift=shift)
                except Exception:
                    start_sec, end_sec = 0, 0

                rules = {}
                try:
                    rules = cio.get_shift_rules(today, shift, day, start_time_sec=start_sec, end_time_sec=end_sec)
                except Exception:
                    rules = {"cutoff_in_dt": None, "cutoff_out_dt": None}

                auto_reject_wfa_waiting_for_date(
                    employee=emp,
                    target_date=today,
                    now_dt=now_dt,
                    cutoff_in_dt=rules.get("cutoff_in_dt"),
                    cutoff_out_dt=rules.get("cutoff_out_dt"),
                )
        except Exception:
            pass

        from django.db.models import Q
        qs = WorkModeRequest.objects.filter(
            Q(status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)
            | Q(status=WorkModeRequestStatus.PENDING, mode=AttendanceWorkMode.ON_DUTY)
        )

        if request.user.has_perm("attendance.change_workmoderequest"):
            pass
        else:
            sub_ids = get_subordinate_employee_ids(request, nested=True)
            if not sub_ids:
                qs = qs.none()
            else:
                qs = qs.filter(employee_id__id__in=sub_ids)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(qs.order_by("-id"), request)
        serializer = WorkModeRequestSerializer(page, many=True)
        return pagenation.get_paginated_response(serializer.data)


class WorkModeRequestApproveView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)
        emp_id = getattr(obj, "employee_id_id", None) or obj.employee_id.id

        # Owner cannot approve unless admin
        try:
            if (
                obj.employee_id.employee_user_id == request.user
                and not request.user.has_perm("attendance.change_workmoderequest")
            ):
                return Response(
                    {"error": "You cannot approve your own request."},
                    status=status.HTTP_403_FORBIDDEN,
                )
        except Exception:
            pass

        if not _can_act_on_employee(request, emp_id, "attendance.change_workmoderequest", allow_owner=False):
            return Response(
                {"error": "You do not have permission to perform this action."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if obj.status != WorkModeRequestStatus.WAITING_FOR_APPROVAL:
            return Response({"error": "Request is not waiting for approval."}, status=400)

        obj.status = WorkModeRequestStatus.APPROVED
        obj.reason_code = None
        try:
            obj.approved_by = request.user.employee_get
        except Exception:
            obj.approved_by = None
        obj.approved_at = dj_timezone.now()
        obj.save(update_fields=["status", "reason_code", "approved_by", "approved_at"])
        return Response({"status": "approved"}, status=200)


class WorkModeRequestRejectView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)
        emp_id = getattr(obj, "employee_id_id", None) or obj.employee_id.id

        # Owner cannot reject unless admin
        try:
            if (
                obj.employee_id.employee_user_id == request.user
                and not request.user.has_perm("attendance.change_workmoderequest")
            ):
                return Response(
                    {"error": "Use cancel for your own request."},
                    status=status.HTTP_403_FORBIDDEN,
                )
        except Exception:
            pass

        if not _can_act_on_employee(request, emp_id, "attendance.change_workmoderequest", allow_owner=False):
            return Response(
                {"error": "You do not have permission to perform this action."},
                status=status.HTTP_403_FORBIDDEN,
            )

        is_admin = request.user.has_perm("attendance.change_workmoderequest")
        if obj.status not in (WorkModeRequestStatus.WAITING_FOR_APPROVAL, WorkModeRequestStatus.PENDING):
            return Response({"error": "Request cannot be rejected in this status."}, status=400)
        if obj.status == WorkModeRequestStatus.PENDING and not is_admin:
            return Response({"error": "Pending ON DUTY requests are not in approvals."}, status=400)

        comment_text = (
            (request.data.get("comment") if hasattr(request, "data") else None)
            or (request.data.get("reason") if hasattr(request, "data") else None)
            or None
        )
        if comment_text:
            obj.reason = str(comment_text)

        obj.status = WorkModeRequestStatus.REJECTED
        obj.reason_code = WorkModeRequestRejectReasonCode.MANUAL_REJECT
        try:
            obj.approved_by = request.user.employee_get
        except Exception:
            obj.approved_by = None
        obj.approved_at = dj_timezone.now()
        obj.save(update_fields=["status", "reason_code", "reason", "approved_by", "approved_at"])

        # Option B: mark any attendance that already used this request
        try:
            apply_rejection_to_attendance(obj)
        except Exception:
            pass

        return Response({"status": "rejected"}, status=200)


class WorkModeRequestCancelView(APIView):
    permission_classes = [IsAuthenticated]

    @transaction.atomic
    def put(self, request, pk):
        obj = get_object_or_404(WorkModeRequest.objects.select_for_update(), pk=pk)

        is_admin = request.user.has_perm("attendance.change_workmoderequest")
        is_owner = False
        try:
            is_owner = obj.employee_id.employee_user_id == request.user
        except Exception:
            is_owner = False

        if not (is_admin or is_owner):
            return Response(
                {"error": "You do not have permission to cancel this request."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if obj.status not in (WorkModeRequestStatus.PENDING, WorkModeRequestStatus.WAITING_FOR_APPROVAL):
            return Response({"error": "Only PENDING/WAITING requests can be canceled."}, status=400)

        obj.status = WorkModeRequestStatus.CANCELED
        obj.save(update_fields=["status"])
        return Response({"status": "canceled"}, status=200)



class AttendanceOverTimeView(APIView):
    """
    Manages CRUD operations for attendance overtime records.

    Methods:
        get(request, pk=None): Retrieves a specific overtime record by `pk` or a list of records with filtering and pagination.
        post(request): Creates a new overtime record.
        put(request, pk): Updates an existing overtime record.
        delete(request, pk): Deletes an overtime record.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request, pk=None):
        if pk:
            attendance_ot = get_object_or_404(AttendanceOverTime, pk=pk)
            serializer = AttendanceOverTimeSerializer(attendance_ot)
            return Response(serializer.data, status=200)

        filterset_class = AttendanceOverTimeFilter(request.GET)
        queryset = filterset_class.qs
        self_account = queryset.filter(employee_id__employee_user_id=request.user)
        permission_based_queryset = filtersubordinates(
            request, queryset, "attendance.view_attendanceovertime"
        )
        queryset = permission_based_queryset | self_account
        field_name = request.GET.get("groupby_field", None)
        if field_name:
            # groupby workflow
            url = request.build_absolute_uri()
            return groupby_queryset(request, url, field_name, queryset)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(queryset, request)
        serializer = AttendanceOverTimeSerializer(page, many=True)
        return pagenation.get_paginated_response(serializer.data)

    @manager_permission_required("attendance.add_attendanceovertime")
    def post(self, request):
        serializer = AttendanceOverTimeSerializer(data=request.data)
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)
        return Response(serializer.errors, status=400)

    @manager_permission_required("attendance.change_attendanceovertime")
    def put(self, request, pk):
        attendance_ot = get_object_or_404(AttendanceOverTime, pk=pk)
        serializer = AttendanceOverTimeSerializer(
            instance=attendance_ot, data=request.data
        )
        if serializer.is_valid():
            serializer.save()
            return Response(serializer.data, status=200)
        return Response(serializer.errors, status=400)

    @method_decorator(permission_required("attendance.delete_attendanceovertime"))
    def delete(self, request, pk):
        attendance = get_object_or_404(AttendanceOverTime, pk=pk)
        attendance.delete()

        return Response({"message": "Overtime deleted successfully"}, status=204)


class LateComeEarlyOutView(APIView):
    """
    Handles retrieval and deletion of late come and early out records.

    Methods:
        get(request, pk=None): Retrieves a list of late come and early out records with filtering.
        delete(request, pk=None): Deletes a specific late come or early out record by `pk`.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request, pk=None):
        data = LateComeEarlyOutFilter(request.GET)
        serializer = AttendanceLateComeEarlyOutSerializer(data.qs, many=True)
        return Response(serializer.data, status=200)

    def delete(self, request, pk=None):
        attendance = get_object_or_404(AttendanceLateComeEarlyOut, pk=pk)
        attendance.delete()
        return Response({"message": "Attendance deleted successfully"}, status=204)


class AttendanceActivityView(APIView):
    """
    Retrieves attendance activity records.

    Method:
        get(request, pk=None): Retrieves a list of all attendance activity records.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request, pk=None):
        data = AttendanceActivity.objects.all()
        serializer = AttendanceActivitySerializer(data, many=True)
        return Response(serializer.data, status=200)


class TodayAttendance(APIView):
    """
    Provides the ratio of marked attendances to expected attendances for the current day.

    Method:
        get(request): Calculates and returns the attendance ratio for today.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):

        today = datetime.today()
        week_day = today.strftime("%A").lower()

        on_time = find_on_time(request, today=today, week_day=week_day)
        late_come = find_late_come(start_date=today)
        late_come_obj = len(late_come)

        marked_attendances = late_come_obj + on_time

        expected_attendances = find_expected_attendances(week_day=week_day)
        marked_attendances_ratio = 0
        if expected_attendances != 0:
            marked_attendances_ratio = (
                f"{(marked_attendances / expected_attendances) * 100:.2f}"
            )

        return Response(
            {"marked_attendances_ratio": marked_attendances_ratio}, status=200
        )


class OfflineEmployeesCountView(APIView):
    """
    Retrieves the count of active employees who have not clocked in today.

    Method:
        get(request): Returns the number of active employees who are not yet clocked in.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        is_manager = (
            EmployeeWorkInformation.objects.filter(
                reporting_manager_id=request.user.employee_get
            )
            .only("id")
            .exists()
        )

        if request.user.has_perm("employee.view_enployee") or is_manager:
            count = (
                EmployeeFilter({"not_in_yet": date.today()})
                .qs.exclude(employee_work_info__isnull=True)
                .filter(is_active=True)
                .count()
            )
            return Response({"count": count}, status=200)
        return Response(
            {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
        )


class OfflineEmployeesListView(APIView):
    """
    Lists active employees who have not clocked in today, including their leave status.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        user = request.user
        employee = getattr(user, "employee_get", None)
        today = date.today()

        # Manager access: get employees reporting to current user
        managed_employee_ids = EmployeeWorkInformation.objects.filter(
            reporting_manager_id=employee
        ).values_list("employee_id", flat=True)

        # Superusers or users with view permission see all employees
        if user.has_perm("employee.view_employee"):
            base_queryset = Employee.objects.all()
        elif managed_employee_ids.exists():
            base_queryset = Employee.objects.filter(id__in=managed_employee_ids)
        else:
            return Response(
                {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
            )

        # Apply filtering for offline employees
        filtered_qs = (
            EmployeeFilter({"not_in_yet": today}, queryset=base_queryset)
            .qs.exclude(employee_work_info__isnull=True)
            .filter(is_active=True)
            .select_related("employee_work_info")  # optimize joins
        )

        # Get leave status for the filtered employees
        leave_status = self.get_leave_status(filtered_qs)

        pagenation = PageNumberPagination()
        page = pagenation.paginate_queryset(leave_status, request)
        return pagenation.get_paginated_response(page)

    def get_leave_status(self, queryset):

        today = date.today()
        queryset = queryset.distinct()
        # Annotate each employee with their leave status
        employees_with_leave_status = queryset.annotate(
            leave_status=Case(
                # Define different cases based on leave requests and attendance
                When(
                    leaverequest__start_date__lte=today,
                    leaverequest__end_date__gte=today,
                    leaverequest__status="approved",
                    then=Value("On Leave"),
                ),
                When(
                    leaverequest__start_date__lte=today,
                    leaverequest__end_date__gte=today,
                    leaverequest__status="requested",
                    then=Value("Waiting Approval"),
                ),
                When(
                    leaverequest__start_date__lte=today,
                    leaverequest__end_date__gte=today,
                    then=Value("Canceled / Rejected"),
                ),
                When(
                    employee_attendances__attendance_date=today, then=Value("Working")
                ),
                default=Value("Expected working"),  # Default status
                output_field=CharField(),
            ),
            job_position_id=F("employee_work_info__job_position_id"),
        ).values(
            "employee_first_name",
            "employee_last_name",
            "leave_status",
            "employee_profile",
            "id",
            "job_position_id",
        )

        for employee in employees_with_leave_status:

            if employee["employee_profile"]:
                employee["employee_profile"] = (
                    settings.MEDIA_URL + employee["employee_profile"]
                )
        return employees_with_leave_status



class CheckingStatus(APIView):
    """Mobile-friendly daily attendance status (single-session + hybrid mode)."""

    permission_classes = [IsAuthenticated]

    def get(self, request):
        employee = request.user.employee_get
        dt_now = _api_now(request)
        server_now_iso = dt_now.isoformat()
        server_time_hhmm = dt_now.strftime("%H:%M")

        # Approver-only managers (reporting managers) are excluded from attendance.
        # They can still approve requests, but must not clock-in/out in Horilla.
        if _is_attendance_exempt_manager(employee):
            attendance_date = dt_now.date()
            return Response(
                {
                    "status": True,
                    "attendance_enabled": False,
                    "attendance_exempt_reason": "REPORTING_MANAGER",
                    "message": "Attendance is disabled for reporting managers (approver-only).",

                    "has_attendance": False,
                    "attendance_date": attendance_date.strftime("%Y-%m-%d"),
                    "first_check_in": None,
                    "last_check_out": None,
                    "late_by": None,
                    "planned_check_out": None,
                    "work_hours_below_minimum": False,
                    "work_hours_shortfall": None,
                    "checked_out_early": False,
                    "worked_hours": "00:00",
                    "worked_seconds": 0,
                    "is_working": False,
                    "missing_check_in": False,
                    "check_in_cutoff_has_passed": False,
                    "check_out_cutoff_has_passed": False,
                    "can_clock_in": False,
                    "can_clock_out": False,
                    "can_update_clock_out": False,

                    "can_check_in": False,
                    "can_check_out": False,
                    "check_in_window_start": None,
                    "check_in_window_end": None,
                    "check_out_window_start": None,
                    "check_out_window_end": None,
                    "check_in_block_reason": "ATTENDANCE_DISABLED",
                    "check_out_block_reason": "ATTENDANCE_DISABLED",

                    # Legacy work-mode
                    "in_mode": AttendanceWorkMode.WFO,
                    "out_mode": AttendanceWorkMode.WFO,

                    # Work Type Request (Attendance) fields
                    "in_work_type": AttendanceWorkMode.WFO,
                    "out_work_type": AttendanceWorkMode.WFO,
                    "in_work_type_source": "schedule",
                    "out_work_type_source": "schedule",
                    "in_work_type_request_id": None,
                    "out_work_type_request_id": None,
                    "in_work_type_request_status": None,
                    "out_work_type_request_status": None,

                    # Legacy request keys
                    "in_request_status": None,
                    "out_request_status": None,
                    "in_request_scope": None,
                    "out_request_scope": None,
                    "in_work_mode_request_id": None,
                    "out_work_mode_request_id": None,

                    # Option B (audit fields)
                    "in_attendance_status": None,
                    "out_attendance_status": None,
                    "in_attendance_reject_reason_code": None,
                    "out_attendance_reject_reason_code": None,
                    "in_related_work_type_request_id": None,
                    "out_related_work_type_request_id": None,

                    "shift_start": None,
                    "shift_end": None,
                    "grace_time": 0,
                    "minimum_working_hour": None,
                    "check_in_cutoff_time": None,
                    "check_out_cutoff_time": None,
                    "requires_photo_in": False,
                    "requires_location_in": False,
                    "requires_photo_out": False,
                    "requires_location_out": False,
                    "is_presensi_only": False,
                    "server_now": server_now_iso,
                    "server_time": server_time_hhmm,
                },
                status=status.HTTP_200_OK,
            )

        # Resolve shift
        shift = None
        try:
            shift = employee.employee_work_info.shift_id
        except Exception:
            shift = None

        # If shift missing, return minimal safe response (no mobile punch)
        # Keep response shape stable for mobile UI (include work type & audit fields).
        if not shift:
            attendance_date = dt_now.date()

            try:
                in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
                out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")
            except Exception:
                in_mode, in_source, in_req = (AttendanceWorkMode.WFO, "schedule", None)
                out_mode, out_source, out_req = (AttendanceWorkMode.WFO, "schedule", None)

            return Response(
                {
                    "status": False,
                    "attendance_enabled": True,
                    "attendance_exempt_reason": None,
                    "has_attendance": False,
                    "attendance_date": attendance_date.strftime("%Y-%m-%d"),
                    "first_check_in": None,
                    "last_check_out": None,
                    "late_by": None,
                    "planned_check_out": None,
                    "work_hours_below_minimum": False,
                    "work_hours_shortfall": None,
                    "checked_out_early": False,
                    "worked_hours": "00:00",
                    "worked_seconds": 0,
                    "is_working": False,
                    "missing_check_in": False,
                    "check_in_cutoff_has_passed": False,
                    "check_out_cutoff_has_passed": False,
                    "can_clock_in": False,
                    "can_clock_out": False,
                    "can_update_clock_out": False,

                    "can_check_in": False,
                    "can_check_out": False,
                    "check_in_window_start": None,
                    "check_in_window_end": None,
                    "check_out_window_start": None,
                    "check_out_window_end": None,
                    "check_in_block_reason": "SHIFT_NOT_ASSIGNED",
                    "check_out_block_reason": "SHIFT_NOT_ASSIGNED",

                    # Legacy work-mode
                    "in_mode": in_mode,
                    "out_mode": out_mode,

                    # Work Type Request (Attendance) fields
                    "in_work_type": in_mode,
                    "out_work_type": out_mode,
                    "in_work_type_source": in_source,
                    "out_work_type_source": out_source,
                    "in_work_type_request_id": getattr(in_req, "id", None),
                    "out_work_type_request_id": getattr(out_req, "id", None),
                    "in_work_type_request_status": getattr(in_req, "status", None),
                    "out_work_type_request_status": getattr(out_req, "status", None),

                    # Legacy request keys (still used by some clients)
                    "in_request_status": getattr(in_req, "status", None),
                    "out_request_status": getattr(out_req, "status", None),
                    "in_request_scope": getattr(in_req, "scope", None),
                    "out_request_scope": getattr(out_req, "scope", None),
                    "in_work_mode_request_id": getattr(in_req, "id", None),
                    "out_work_mode_request_id": getattr(out_req, "id", None),

                    # Option B (audit fields)
                    "in_attendance_status": None,
                    "out_attendance_status": None,
                    "in_attendance_reject_reason_code": None,
                    "out_attendance_reject_reason_code": None,
                    "in_related_work_type_request_id": None,
                    "out_related_work_type_request_id": None,

                    "shift_start": None,
                    "shift_end": None,
                    "grace_time": 0,
                    "minimum_working_hour": None,
                    "check_in_cutoff_time": None,
                    "check_out_cutoff_time": None,
                    "requires_photo_in": False,
                    "requires_location_in": False,
                    "requires_photo_out": False,
                    "requires_location_out": False,
                    "is_presensi_only": False,
                    "server_now": server_now_iso,
                    "server_time": server_time_hhmm,
                },
                status=status.HTTP_200_OK,
            )

        # Resolve attendance_date + day (night shift aware)
        (
            attendance_date,
            day,
            min_hour,
            start_time_sec,
            end_time_sec,
            now_hhmm,
            now_sec,
        ) = _api_resolve_attendance_date_and_day(shift, dt_now)

        # Schedule & cutoffs



        rules = {}


        try:


            rules = cio.get_shift_rules(


                attendance_date,


                shift,


                day,


                start_time_sec=start_time_sec,


                end_time_sec=end_time_sec,


            )


        except Exception:


            rules = {


                "schedule": None,


                "grace_seconds": 0,


                "cutoff_in_dt": None,


                "cutoff_out_dt": None,


            }



        schedule = rules.get("schedule")


        grace_seconds = int(rules.get("grace_seconds") or 0)


        cutoff_in_dt = rules.get("cutoff_in_dt")
        cutoff_out_dt = rules.get("cutoff_out_dt")

        # Windows (FINAL spec)
        shift_start_dt = rules.get("shift_start_dt")
        shift_end_dt = rules.get("shift_end_dt")
        check_in_window_start_dt = rules.get("check_in_window_start_dt")
        check_in_window_end_dt = rules.get("check_in_window_end_dt")
        check_out_window_start_dt = rules.get("check_out_window_start_dt")
        check_out_window_end_dt = rules.get("check_out_window_end_dt")

        cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now) if cutoff_in_dt else None
        cutoff_out_dt = _coerce_datetime_like(cutoff_out_dt, dt_now) if cutoff_out_dt else None
        shift_start_dt = _coerce_datetime_like(shift_start_dt, dt_now) if shift_start_dt else None
        shift_end_dt = _coerce_datetime_like(shift_end_dt, dt_now) if shift_end_dt else None
        check_in_window_start_dt = _coerce_datetime_like(check_in_window_start_dt, dt_now) if check_in_window_start_dt else None
        check_in_window_end_dt = _coerce_datetime_like(check_in_window_end_dt, dt_now) if check_in_window_end_dt else None
        check_out_window_start_dt = _coerce_datetime_like(check_out_window_start_dt, dt_now) if check_out_window_start_dt else None
        check_out_window_end_dt = _coerce_datetime_like(check_out_window_end_dt, dt_now) if check_out_window_end_dt else None

        # Ensure window fields are ALWAYS present (even if shift rule helper
        # couldn't compute them). This keeps the mobile UI free from hardcoded
        # window math and supports fresh installs.
        DEFAULT_EARLY_CHECKIN_MIN = 120
        DEFAULT_LATE_CHECKIN_MIN = 120
        DEFAULT_EARLY_CHECKOUT_GRACE_MIN = 0
        DEFAULT_MAX_LATE_CHECKOUT_HOURS = 12

        try:
            if (check_in_window_start_dt is None) and shift_start_dt:
                check_in_window_start_dt = shift_start_dt - timedelta(minutes=DEFAULT_EARLY_CHECKIN_MIN)
            if (check_in_window_end_dt is None) and shift_start_dt:
                check_in_window_end_dt = cutoff_in_dt or (shift_start_dt + timedelta(minutes=DEFAULT_LATE_CHECKIN_MIN))

            if (check_out_window_start_dt is None) and shift_end_dt:
                check_out_window_start_dt = shift_end_dt - timedelta(minutes=DEFAULT_EARLY_CHECKOUT_GRACE_MIN)
            if (check_out_window_end_dt is None) and shift_end_dt:
                check_out_window_end_dt = cutoff_out_dt or (shift_end_dt + timedelta(hours=DEFAULT_MAX_LATE_CHECKOUT_HOURS))
        except Exception:
            pass

        # Legacy cutoff flags (kept for backwards compatibility)
        check_in_cutoff_has_passed = bool(cutoff_in_dt and dt_now > cutoff_in_dt)
        check_out_cutoff_has_passed = bool(cutoff_out_dt and dt_now > cutoff_out_dt)

        # Auto reject WFA waiting requests after cutoff (FINAL spec)
        try:
            auto_reject_wfa_waiting_for_date(
                employee=employee,
                target_date=attendance_date,
                now_dt=dt_now,
                cutoff_in_dt=cutoff_in_dt,
                cutoff_out_dt=cutoff_out_dt,
            )
        except Exception:
            pass

# Resolve effective work type (request overrides schedule; IN/OUT can differ)
        in_mode, in_source, in_req = _resolve_effective_work_type(employee, attendance_date, "in")
        out_mode, out_source, out_req = _resolve_effective_work_type(employee, attendance_date, "out")

        # Attendance row
        attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        clock_in_t = getattr(attendance, "attendance_clock_in", None) if attendance else None
        clock_out_t = getattr(attendance, "attendance_clock_out", None) if attendance else None

        # If this attendance is presence-only (On Duty), force worked hours to 00:00
        is_presensi_only = bool(attendance and getattr(attendance, "is_presensi_only", False))

        out_punch_status = getattr(attendance, "out_attendance_status", None) if attendance else None
        out_rejected = bool(out_punch_status == "REJECTED")

        # Worked hours calculation
        worked_seconds = 0
        is_working = False
        if attendance and not is_presensi_only:
            if clock_in_t:
                in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
                in_dt = _coerce_datetime_like(datetime.combine(in_date, clock_in_t), dt_now)

                # FINAL spec: if checked-in earlier than shift_start, start counting at shift_start.
                worked_start_dt = in_dt
                try:
                    if shift_start_dt and in_dt:
                        worked_start_dt = max(in_dt, shift_start_dt)
                except Exception:
                    worked_start_dt = in_dt

                # If OUT punch exists but was REJECTED, treat as not checked-out yet.
                has_valid_out = bool(clock_out_t and not out_rejected)

                if not has_valid_out:
                    is_working = True
                    try:
                        worked_seconds = max(0, int((dt_now - worked_start_dt).total_seconds()))
                    except Exception:
                        worked_seconds = 0
                else:
                    out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date
                    out_dt = _coerce_datetime_like(datetime.combine(out_date, clock_out_t), dt_now)
                    try:
                        worked_seconds = max(0, int((out_dt - worked_start_dt).total_seconds()))
                    except Exception:
                        worked_seconds = 0
            elif clock_out_t:
                # missing check-in computation uses AttendanceActivity placeholder if available
                activity = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
                if activity and getattr(activity, "clock_in_date", None) and getattr(activity, "clock_in", None) and getattr(activity, "clock_out_date", None) and getattr(activity, "clock_out", None):
                    in_dt = _coerce_datetime_like(datetime.combine(activity.clock_in_date, activity.clock_in), dt_now)
                    out_dt = _coerce_datetime_like(datetime.combine(activity.clock_out_date, activity.clock_out), dt_now)
                    try:
                        worked_start_dt = in_dt
                        if shift_start_dt and in_dt:
                            worked_start_dt = max(in_dt, shift_start_dt)
                        worked_seconds = max(0, int((out_dt - worked_start_dt).total_seconds()))
                    except Exception:
                        worked_seconds = 0
                else:
                    worked_seconds = 0

        worked_minutes = max(0, int(worked_seconds // 60))
        worked_hours = f"{worked_minutes//60:02d}:{worked_minutes%60:02d}"

        # Missing check-in flag (for UI messaging)
        missing_check_in = (
            (not clock_in_t)
            and (
                bool(clock_out_t)
                or (bool(check_in_cutoff_has_passed) and not bool(check_out_cutoff_has_passed))
            )
        )

        # Action permissions
        in_allowed = _is_punch_allowed(in_mode, in_req, in_source)
        out_allowed = _is_punch_allowed(out_mode, out_req, out_source)

        requires_photo_in = _requires_proof(in_mode)
        requires_location_in = _requires_proof(in_mode)
        requires_photo_out = _requires_proof(out_mode)
        requires_location_out = _requires_proof(out_mode)

        # Window selection (FINAL spec)
        in_window_start = check_in_window_start_dt
        in_window_end = check_in_window_end_dt

        out_window_start = cutoff_in_dt if (out_mode == AttendanceWorkMode.ON_DUTY) else check_out_window_start_dt
        out_window_end = check_out_window_end_dt

        def _in_window_ok(start_dt, end_dt) -> bool:
            if start_dt and dt_now < start_dt:
                return False
            if end_dt and dt_now > end_dt:
                return False
            return True

        in_window_ok = _in_window_ok(in_window_start, in_window_end)
        out_window_ok = _in_window_ok(out_window_start, out_window_end)

        # Block reasons for mobile UI (FINAL spec)
        check_in_block_reason = None
        check_out_block_reason = None

        if clock_in_t or clock_out_t:
            check_in_block_reason = "ALREADY_PUNCHED"
        elif not in_allowed:
            check_in_block_reason = "MODE_NOT_ALLOWED"
        elif in_window_start and dt_now < in_window_start:
            check_in_block_reason = "BEFORE_WINDOW_START"
        elif in_window_end and dt_now > in_window_end:
            check_in_block_reason = "AFTER_WINDOW_END"

        # Can check-in? (FINAL spec)
        can_clock_in = (
            (not bool(clock_in_t))
            and (not bool(clock_out_t))
            and in_allowed
            and in_window_ok
        )

        # Can update checkout?
        can_update_clock_out = (
            bool(clock_out_t)
            and out_allowed
            and out_window_ok
            and ((out_mode == AttendanceWorkMode.WFA) or out_rejected)
        )

        # Can check-out? (FINAL spec)
        can_clock_out = False
        if not out_allowed:
            check_out_block_reason = "MODE_NOT_ALLOWED"
        elif out_window_start and dt_now < out_window_start:
            check_out_block_reason = "BEFORE_WINDOW_START"
        elif out_window_end and dt_now > out_window_end:
            check_out_block_reason = "AFTER_WINDOW_END"
        else:
            # within window
            if clock_out_t:
                can_clock_out = can_update_clock_out
                if not can_clock_out:
                    check_out_block_reason = "ALREADY_CHECKED_OUT"
            else:
                # allow clock-out even when check-in is missing (single-session placeholder)
                can_clock_out = True

        # Suggested action (for mobile)
        suggested_action = None
        if can_clock_out:
            suggested_action = "clock_out"
        elif can_clock_in:
            suggested_action = "clock_in"

        # Shift context
        def _sec_to_hhmm(sec_val):
            try:
                s = int(sec_val)
            except Exception:
                return None
            if s < 0:
                return None
            h = (s // 3600) % 24
            m = (s % 3600) // 60
            return f"{h:02d}:{m:02d}"

        # Derived helpers for mobile UI (optional; safe defaults when absent)
        planned_check_out_hhmm = _sec_to_hhmm(end_time_sec)
        late_by_hhmm = None
        work_hours_below_minimum = False
        work_hours_shortfall_hhmm = None
        checked_out_early = False

        if attendance and not is_presensi_only:
            try:
                is_night_shift = start_time_sec > end_time_sec and start_time_sec != end_time_sec
            except Exception:
                is_night_shift = False

            # Late-by is calculated from scheduled start + grace time
            if clock_in_t and start_time_sec:
                try:
                    in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
                    in_dt = _coerce_datetime_like(datetime.combine(in_date, clock_in_t), dt_now)

                    planned_in_hhmm = _sec_to_hhmm(start_time_sec)
                    planned_in_time = datetime.strptime(planned_in_hhmm, "%H:%M").time()
                    planned_in_dt = _coerce_datetime_like(
                        datetime.combine(attendance_date, planned_in_time), dt_now
                    )

                    grace_dt = planned_in_dt + timedelta(seconds=int(grace_seconds or 0))
                    if in_dt and grace_dt and in_dt > grace_dt:
                        late_s = int((in_dt - grace_dt).total_seconds())
                        if late_s > 0:
                            late_by_hhmm = f"{late_s // 3600:02d}:{(late_s % 3600) // 60:02d}"
                except Exception:
                    late_by_hhmm = None

            # Below-minimum and shortfall are only meaningful after clock-out
            min_hhmm = _format_minimum_hour(min_hour)
            if clock_in_t and clock_out_t and min_hhmm:
                try:
                    min_s = strtime_seconds(min_hhmm)
                    if min_s and int(worked_seconds) < int(min_s):
                        work_hours_below_minimum = True
                        short_s = int(min_s) - int(worked_seconds)
                        work_hours_shortfall_hhmm = f"{short_s // 3600:02d}:{(short_s % 3600) // 60:02d}"
                except Exception:
                    pass

            # Early check-out is based on scheduled end time
            if clock_in_t and clock_out_t and planned_check_out_hhmm:
                try:
                    out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date
                    out_dt = _coerce_datetime_like(datetime.combine(out_date, clock_out_t), dt_now)

                    planned_out_date = attendance_date + timedelta(days=1) if is_night_shift else attendance_date
                    planned_out_time = datetime.strptime(planned_check_out_hhmm, "%H:%M").time()
                    planned_out_dt = _coerce_datetime_like(
                        datetime.combine(planned_out_date, planned_out_time), dt_now
                    )

                    if out_dt and planned_out_dt and out_dt < planned_out_dt:
                        checked_out_early = True
                except Exception:
                    checked_out_early = False

        payload = {
            "status": (False if is_presensi_only else bool(is_working)),
            "attendance_enabled": True,
            "attendance_exempt_reason": None,
            "has_attendance": bool(attendance),
            "attendance_date": attendance_date.strftime("%Y-%m-%d"),

            "clock_in_time": clock_in_t.strftime("%H:%M") if clock_in_t else None,
            "clock_out_time": clock_out_t.strftime("%H:%M") if clock_out_t else None,
            "clock_in": clock_in_t.strftime("%I:%M %p") if clock_in_t else None,
            "clock_out": clock_out_t.strftime("%I:%M %p") if clock_out_t else None,

            "first_check_in": clock_in_t.strftime("%I:%M %p") if clock_in_t else None,
            "last_check_out": clock_out_t.strftime("%I:%M %p") if clock_out_t else None,

            "worked_hours": "00:00" if is_presensi_only else worked_hours,
            "worked_seconds": 0 if is_presensi_only else int(worked_seconds),
            "is_working": False if is_presensi_only else bool(is_working),

            "shift_start": _sec_to_hhmm(start_time_sec),
            "shift_end": _sec_to_hhmm(end_time_sec),
            "grace_time": int(grace_seconds),
            "minimum_working_hour": _format_minimum_hour(min_hour),

            "check_in_cutoff_time": cutoff_in_dt.strftime("%H:%M") if cutoff_in_dt else None,
            "check_out_cutoff_time": cutoff_out_dt.strftime("%H:%M") if cutoff_out_dt else None,
            "check_in_cutoff_has_passed": bool(check_in_cutoff_has_passed),
            "check_out_cutoff_has_passed": bool(check_out_cutoff_has_passed),

            "missing_check_in": bool(missing_check_in),

            # Option B (per punch audit status)
            "in_attendance_status": getattr(attendance, "in_attendance_status", None) if attendance else None,
            "out_attendance_status": getattr(attendance, "out_attendance_status", None) if attendance else None,
            "in_attendance_reject_reason_code": getattr(attendance, "in_attendance_reject_reason_code", None) if attendance else None,
            "out_attendance_reject_reason_code": getattr(attendance, "out_attendance_reject_reason_code", None) if attendance else None,
            "in_related_work_type_request_id": getattr(attendance, "in_related_work_type_request_id", None) if attendance else None,
            "out_related_work_type_request_id": getattr(attendance, "out_related_work_type_request_id", None) if attendance else None,

            # Work-mode
            "in_mode": in_mode,
                    "out_mode": out_mode,
                    "in_work_type": in_mode,
                    "out_work_type": out_mode,
                    "in_work_type_source": in_source,
                    "out_work_type_source": out_source,
                    "in_work_type_request_id": getattr(in_req, 'id', None),
                    "out_work_type_request_id": getattr(out_req, 'id', None),
                    "in_work_type_request_status": getattr(in_req, 'status', None),
                    "out_work_type_request_status": getattr(out_req, 'status', None),
            "in_request_status": getattr(in_req, "status", None),
            "out_request_status": getattr(out_req, "status", None),
            "in_request_scope": getattr(in_req, "scope", None),
            "out_request_scope": getattr(out_req, "scope", None),
            "in_work_mode_request_id": getattr(in_req, "id", None),
            "out_work_mode_request_id": getattr(out_req, "id", None),

            # Gating flags
            "can_clock_in": bool(can_clock_in),
            "can_clock_out": bool(can_clock_out),
            "can_update_clock_out": bool(can_update_clock_out),
            # New (FINAL spec) keys
            "can_check_in": bool(can_clock_in),
            "can_check_out": bool(can_clock_out),
            "check_in_window_start": in_window_start.strftime("%H:%M") if in_window_start else None,
            "check_in_window_end": in_window_end.strftime("%H:%M") if in_window_end else None,
            "check_out_window_start": out_window_start.strftime("%H:%M") if out_window_start else None,
            "check_out_window_end": out_window_end.strftime("%H:%M") if out_window_end else None,
            "check_in_block_reason": check_in_block_reason,
            "check_out_block_reason": check_out_block_reason,
            "suggested_action": suggested_action,
            "update_check_out": bool(can_update_clock_out),  # legacy key for existing mobile UI

            # Proof requirements (mobile uses this to show camera/GPS)
            "requires_photo_in": bool(requires_photo_in),
            "requires_location_in": bool(requires_location_in),
            "requires_photo_out": bool(requires_photo_out),
            "requires_location_out": bool(requires_location_out),

            # Presence-only
            "is_presensi_only": bool(is_presensi_only),

            "server_now": server_now_iso,
            "server_time": server_time_hhmm,
        }

        # Optional helper fields used by mobile UI for status notes.
        # Keep these stable for backward compatibility.
        payload.update(
            {
                "late_check_in": bool(late_by_hhmm),
                "late_by": late_by_hhmm,
                "planned_check_out": planned_check_out_hhmm,
                "work_hours_below_minimum": bool(work_hours_below_minimum),
                "work_hours_shortfall": work_hours_shortfall_hhmm,
                "checked_out_early": bool(checked_out_early),
            }
        )

        # Attach proof URLs & locations (audit)
        if attendance:
            try:
                if getattr(attendance, "attendance_clock_in_image", None):
                    payload["clock_in_image"] = attendance.attendance_clock_in_image.url
            except Exception:
                pass
            try:
                if getattr(attendance, "attendance_clock_out_image", None):
                    payload["clock_out_image"] = attendance.attendance_clock_out_image.url
            except Exception:
                pass
            # Location fields may be JSON
            try:
                payload["clock_in_location"] = getattr(attendance, "attendance_clock_in_location", None)
            except Exception:
                pass
            try:
                payload["clock_out_location"] = getattr(attendance, "attendance_clock_out_location", None)
            except Exception:
                pass
        return Response(payload, status=status.HTTP_200_OK)

class MailTemplateView(APIView):
    """
    Retrieves a list of recruitment mail templates.

    Method:
        get(request): Returns all recruitment mail templates.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        instances = HorillaMailTemplate.objects.all()
        serializer = MailTemplateSerializer(instances, many=True)
        return Response(serializer.data, status=200)

class ConvertedMailTemplateConvert(APIView):
    """
    Renders a recruitment mail template with data from a specified employee.

    Method:
        put(request): Renders the mail template body with employee and user data and returns the result.
    """

    permission_classes = [IsAuthenticated]

    def put(self, request):
        template_id = request.data.get("template_id", None)
        employee_id = request.data.get("employee_id", None)
        employee = Employee.objects.filter(id=employee_id).first()
        bdy = HorillaMailTemplate.objects.filter(id=template_id).first()
        template_bdy = template.Template(bdy.body)
        context = template.Context(
            {"instance": employee, "self": request.user.employee_get}
        )
        render_bdy = template_bdy.render(context)
        return Response(render_bdy)
class OfflineEmployeeMailsend(APIView):
    """
    Sends an email with attachments and rendered templates to a specified employee.

    Method:
        post(request): Renders email templates with employee and user data, attaches files, and sends the email.
    """

    permission_classes = [IsAuthenticated]

    def post(self, request):
        employee_id = request.POST.get("employee_id")
        subject = request.POST.get("subject", "")
        bdy = request.POST.get("body", "")
        other_attachments = request.FILES.getlist("other_attachments")
        attachments = [
            (file.name, file.read(), file.content_type) for file in other_attachments
        ]
        email_backend = ConfiguredEmailBackend()
        host = email_backend.dynamic_username
        employee = Employee.objects.get(id=employee_id)
        template_attachment_ids = request.POST.getlist("template_attachments")
        bodys = list(
            HorillaMailTemplate.objects.filter(
                id__in=template_attachment_ids
            ).values_list("body", flat=True)
        )
        for html in bodys:
            # Due to not having a solid template we first need to pass the context
            template_bdy = template.Template(html)
            context = template.Context(
                {"instance": employee, "self": request.user.employee_get}
            )
            render_bdy = template_bdy.render(context)
            attachments.append(
                (
                    "Document",
                    generate_pdf(render_bdy, {}, path=False, title="Document").content,
                    "application/pdf",
                )
            )

        template_bdy = template.Template(bdy)
        context = template.Context(
            {"instance": employee, "self": request.user.employee_get}
        )
        render_bdy = template_bdy.render(context)

        email = EmailMessage(
            subject,
            render_bdy,
            host,
            [employee.employee_work_info.email],
        )
        email.content_subtype = "html"

        email.attachments = attachments
        try:
            email.send()
            if employee.employee_work_info.email:
                return Response(f"Mail sent to {employee.get_full_name()}")
            else:
                return Response(f"Email not set for {employee.get_full_name()}")
        except Exception as e:
            return Response("Something went wrong")


class UserAttendanceView(APIView):
    permission_classes = [IsAuthenticated]
    serializer_class = UserAttendanceDetailedSerializer

    def get(self, request):
        employee_id = request.user.employee_get.id

        attendance_queryset = Attendance.objects.filter(
            employee_id=employee_id
        ).order_by("-id")

        paginator = PageNumberPagination()
        paginator.page_size = 20
        page = paginator.paginate_queryset(attendance_queryset, request)

        serializer = self.serializer_class(page, many=True)
        return paginator.get_paginated_response(serializer.data)


class AttendanceTypeAccessCheck(APIView):
    permission_classes = [IsAuthenticated]

    def get(self, request):
        user = request.user
        employee_id = user.employee_get.id

        if user.has_perm("attendance.view_attendance"):
            return Response(status=200)

        is_manager = (
            EmployeeWorkInformation.objects.filter(reporting_manager_id=employee_id)
            .only("id")
            .exists()
        )

        if is_manager:
            return Response(status=200)

        return Response(
            {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
        )

class UserAttendanceDetailedView(APIView):
    permission_classes = [IsAuthenticated]

    def get(self, request, id):
        attendance = get_object_or_404(Attendance, pk=id)
        if attendance.employee_id == request.user.employee_get:
            serializer = UserAttendanceDetailedSerializer(attendance)
            return Response(serializer.data, status=200)
        return Response(
            {"error": "Permission denied"}, status=status.HTTP_403_FORBIDDEN
        )
