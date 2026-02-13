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
)
from attendance.views.clock_in_out import *
from attendance.views.clock_in_out import clock_out
import attendance.views.clock_in_out as cio  # Access underscore helpers excluded by import *

from attendance.views.dashboard import (
    find_expected_attendances,
    find_late_come,
    find_on_time,
)
from attendance.views.views import *
from base.backends import ConfiguredEmailBackend
from base.methods import generate_pdf, is_reportingmanager
from base.models import HorillaMailTemplate
from employee.filters import EmployeeFilter

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


# -----------------------------------------------------------------------------
# Mobile single-session helpers# -----------------------------------------------------------------------------
# Work-mode helpers (WFO/WFA/ON_DUTY)
# -----------------------------------------------------------------------------
def _pick_work_mode_request(employee, target_date: date, want: str):
    """Pick the most relevant WorkModeRequest for a date.

    want: "in" or "out" (scope filter)
    Priority:
      1) APPROVED
      2) PENDING
      3) others (excluding REJECTED/CANCELED)
      then newest first
    """
    if want not in ("in", "out"):
        raise ValueError("want must be 'in' or 'out'")

    qs = WorkModeRequest.objects.filter(
        employee_id=employee,
        start_date__lte=target_date,
        end_date__gte=target_date,
    ).exclude(
        status__in=[WorkModeRequestStatus.REJECTED, WorkModeRequestStatus.CANCELED]
    )

    if want == "in":
        qs = qs.filter(scope__in=[WorkModeRequestScope.IN, WorkModeRequestScope.FULL])
    else:
        qs = qs.filter(scope__in=[WorkModeRequestScope.OUT, WorkModeRequestScope.FULL])

    qs = qs.annotate(
        _status_rank=Case(
                When(status=WorkModeRequestStatus.APPROVED, then=Value(0)),
                When(status=WorkModeRequestStatus.PENDING, then=Value(1)),
                default=Value(9),
            )
        ).order_by("_status_rank", "-id")

    return qs.first()

def _mode_from_request(req) -> str:
    return req.mode if req else AttendanceWorkMode.WFO

def _is_punch_allowed(mode: str, req) -> bool:
    """Server-side authority: whether mobile punch is allowed for a mode."""
    if mode == AttendanceWorkMode.WFO:
        return False
    if not req:
        return False
    if mode == AttendanceWorkMode.WFA:
        return req.status == WorkModeRequestStatus.APPROVED
    if mode == AttendanceWorkMode.ON_DUTY:
        return req.status in (WorkModeRequestStatus.PENDING, WorkModeRequestStatus.APPROVED)
    return False

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

    Returns:
        attendance_date, day_obj, minimum_hour, start_time_sec, end_time_sec, now_hhmm, now_sec
    """
    date_today = dt_now.date()
    now_hhmm = dt_now.strftime("%H:%M")
    now_sec = strtime_seconds(now_hhmm)
    mid_day_sec = strtime_seconds("12:00")

    attendance_date = date_today
    day = EmployeeShiftDay.objects.get(day=date_today.strftime("%A").lower())
    minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)

    if start_time_sec > end_time_sec:
        # Night shift: assign before-noon punches to the previous day.
        if mid_day_sec > now_sec:
            date_yesterday = date_today - timedelta(days=1)
            attendance_date = date_yesterday
            day = EmployeeShiftDay.objects.get(day=date_yesterday.strftime("%A").lower())
            minimum_hour, start_time_sec, end_time_sec = shift_schedule_today(day=day, shift=shift)

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

        dt_now = _api_now(request)
        shift = work_info.shift_id
        date_today = _api_today(request, dt_now)

        # Resolve attendance date (night shift aware)
        attendance_date, day, minimum_hour, start_time_sec, end_time_sec, now_hhmm, _ = (
            _api_resolve_attendance_date_and_day(shift, dt_now)
        )

        # Resolve mode + request for IN
        in_req = _pick_work_mode_request(employee, attendance_date, "in")
        in_mode = _mode_from_request(in_req)

        if in_mode == AttendanceWorkMode.WFO:
            return Response(
                {"error": "WFO attendance must be recorded via biometric device."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if not _is_punch_allowed(in_mode, in_req):
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

        cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now)
        if cutoff_in_dt and dt_now > cutoff_in_dt:
            return Response(
                {
                    "error": "Check-in cut-off has passed.",
                    "last_allowed": cutoff_in_dt.strftime("%Y-%m-%d %H:%M"),
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

        return Response(
            {
                "message": "Clocked-In",
                "attendance_date": str(attendance_date),
                "in_mode": in_mode,
                "work_mode_request_id": getattr(in_req, "id", None),
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

        out_req = _pick_work_mode_request(employee, attendance_date, "out")
        out_mode = _mode_from_request(out_req)

        if out_mode == AttendanceWorkMode.WFO:
            return Response(
                {"error": "WFO attendance must be recorded via biometric device."},
                status=status.HTTP_403_FORBIDDEN,
            )

        if not _is_punch_allowed(out_mode, out_req):
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



        cutoff_out_dt = rules.get("cutoff_out_dt")


        cutoff_out_dt = _coerce_datetime_like(cutoff_out_dt, dt_now) if cutoff_out_dt else None


        if cutoff_out_dt and dt_now > cutoff_out_dt:


            return Response(


                {"error": "Check-out cut-off has passed. Please submit an attendance request."},


                status=status.HTTP_400_BAD_REQUEST,


            )



        # OUT-only rule: allow only after check-in cutoff has passed


        if out_req and out_req.scope == WorkModeRequestScope.OUT:


            cutoff_in_dt = rules.get("cutoff_in_dt")


            cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now) if cutoff_in_dt else None


            if cutoff_in_dt and dt_now <= cutoff_in_dt:


                return Response(


                    {"error": "Clock-out is available only after check-in cut-off time."},


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

        allow_update = out_mode == AttendanceWorkMode.WFA

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

        # For presence-only (On Duty), skip late/early calculations
        if attendance and not getattr(attendance, "is_presensi_only", False) and not missing_check_in:
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

        return Response(
            {
                "message": "Clocked-Out",
                "attendance_date": str(attendance_date),
                "out_mode": out_mode,
                "work_mode_request_id": getattr(out_req, "id", None),
                "missing_check_in": bool(missing_check_in),
                "updated": bool(allow_update),
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

        form = NewRequestForm(data=request.data)
        if form.is_valid():
            work_type = form.cleaned_data.get("work_type_id")

            if not WorkType.objects.filter(pk=getattr(work_type, "pk", None)).exists():
                form.cleaned_data["work_type_id"] = None

            if form.new_instance is not None:
                form.new_instance.save()

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
        form = AttendanceRequestForm(data=request.data, instance=attendance)
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
            if (
                attendance.employee_id.employee_user_id == request.user
                or is_reportingmanager(request)
                or request.user.has_perm("attendance.change_attendance")
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

        # Resolve shift
        shift = None
        try:
            shift = employee.employee_work_info.shift_id
        except Exception:
            shift = None

        # If shift missing, return minimal safe response (no mobile punch)
        if not shift:
            attendance_date = dt_now.date()
            return Response(
                {
                    "status": False,
                    "has_attendance": False,
                    "attendance_date": attendance_date.strftime("%Y-%m-%d"),
                    "worked_hours": "00:00",
                    "missing_check_in": False,
                    "check_in_cutoff_has_passed": False,
                    "check_out_cutoff_has_passed": False,
                    "can_clock_in": False,
                    "can_clock_out": False,
                    "can_update_clock_out": False,
                    "in_mode": AttendanceWorkMode.WFO,
                    "out_mode": AttendanceWorkMode.WFO,
                    "shift_start": None,
                    "shift_end": None,
                    "grace_time": 0,
                    "check_in_cutoff_time": None,
                    "check_out_cutoff_time": None,
                    "requires_photo_in": False,
                    "requires_location_in": False,
                    "requires_photo_out": False,
                    "requires_location_out": False,
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


        check_in_cutoff_has_passed = False


        check_out_cutoff_has_passed = False

        cutoff_in_dt = _coerce_datetime_like(cutoff_in_dt, dt_now) if cutoff_in_dt else None
        cutoff_out_dt = _coerce_datetime_like(cutoff_out_dt, dt_now) if cutoff_out_dt else None

        if cutoff_in_dt and dt_now > cutoff_in_dt:
            check_in_cutoff_has_passed = True
        if cutoff_out_dt and dt_now > cutoff_out_dt:
            check_out_cutoff_has_passed = True

        # Resolve work-mode requests (IN/OUT can differ)
        in_req = _pick_work_mode_request(employee, attendance_date, "in")
        out_req = _pick_work_mode_request(employee, attendance_date, "out")

        in_mode = _mode_from_request(in_req)
        out_mode = _mode_from_request(out_req)

        # Attendance row
        attendance = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
        clock_in_t = getattr(attendance, "attendance_clock_in", None) if attendance else None
        clock_out_t = getattr(attendance, "attendance_clock_out", None) if attendance else None

        # If this attendance is presence-only (On Duty), force worked hours to 00:00
        is_presensi_only = bool(attendance and getattr(attendance, "is_presensi_only", False))

        # Worked hours calculation
        worked_seconds = 0
        is_working = False
        if attendance and not is_presensi_only:
            if clock_in_t:
                in_date = getattr(attendance, "attendance_clock_in_date", None) or attendance_date
                in_dt = _coerce_datetime_like(datetime.combine(in_date, clock_in_t), dt_now)
                if not clock_out_t:
                    is_working = True
                    try:
                        worked_seconds = max(0, int((dt_now - in_dt).total_seconds()))
                    except Exception:
                        worked_seconds = 0
                else:
                    out_date = getattr(attendance, "attendance_clock_out_date", None) or attendance_date
                    out_dt = _coerce_datetime_like(datetime.combine(out_date, clock_out_t), dt_now)
                    try:
                        worked_seconds = max(0, int((out_dt - in_dt).total_seconds()))
                    except Exception:
                        worked_seconds = 0
            elif clock_out_t:
                # missing check-in computation uses AttendanceActivity placeholder if available
                activity = AttendanceActivity.objects.filter(employee_id=employee, attendance_date=attendance_date).first()
                if activity and getattr(activity, "clock_in_date", None) and getattr(activity, "clock_in", None) and getattr(activity, "clock_out_date", None) and getattr(activity, "clock_out", None):
                    in_dt = _coerce_datetime_like(datetime.combine(activity.clock_in_date, activity.clock_in), dt_now)
                    out_dt = _coerce_datetime_like(datetime.combine(activity.clock_out_date, activity.clock_out), dt_now)
                    try:
                        worked_seconds = max(0, int((out_dt - in_dt).total_seconds()))
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
        in_allowed = _is_punch_allowed(in_mode, in_req)
        out_allowed = _is_punch_allowed(out_mode, out_req)

        requires_photo_in = _requires_proof(in_mode)
        requires_location_in = _requires_proof(in_mode)
        requires_photo_out = _requires_proof(out_mode)
        requires_location_out = _requires_proof(out_mode)

        # Can clock-in?
        can_clock_in = (
            (not bool(clock_in_t))
            and (not bool(clock_out_t))
            and (not bool(check_in_cutoff_has_passed))
            and in_allowed
        )

        # Can update checkout?
        can_update_clock_out = (
            bool(clock_out_t)
            and (not bool(check_out_cutoff_has_passed))
            and (out_mode == AttendanceWorkMode.WFA)
            and out_allowed
        )

        # Can clock-out?
        can_clock_out = False
        if not check_out_cutoff_has_passed and out_allowed:
            if clock_out_t:
                can_clock_out = can_update_clock_out  # update only (WFA)
            else:
                # OUT-only must wait until check-in cutoff passes
                if out_req and out_req.scope == WorkModeRequestScope.OUT and not check_in_cutoff_has_passed:
                    can_clock_out = False
                else:
                    # either checked-in already or "missing check-in" after cutoff
                    can_clock_out = bool(clock_in_t) or bool(missing_check_in)

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

        payload = {
            "status": bool(attendance),
            "has_attendance": bool(attendance),
            "attendance_date": attendance_date.strftime("%Y-%m-%d"),

            "clock_in_time": clock_in_t.strftime("%H:%M") if clock_in_t else None,
            "clock_out_time": clock_out_t.strftime("%H:%M") if clock_out_t else None,
            "clock_in": clock_in_t.strftime("%I:%M %p") if clock_in_t else None,
            "clock_out": clock_out_t.strftime("%I:%M %p") if clock_out_t else None,

            "worked_hours": "00:00" if is_presensi_only else worked_hours,
            "worked_seconds": 0 if is_presensi_only else int(worked_seconds),
            "is_working": False if is_presensi_only else bool(is_working),

            "shift_start": _sec_to_hhmm(start_time_sec),
            "shift_end": _sec_to_hhmm(end_time_sec),
            "grace_time": int(grace_seconds),

            "check_in_cutoff_time": cutoff_in_dt.strftime("%H:%M") if cutoff_in_dt else None,
            "check_out_cutoff_time": cutoff_out_dt.strftime("%H:%M") if cutoff_out_dt else None,
            "check_in_cutoff_has_passed": bool(check_in_cutoff_has_passed),
            "check_out_cutoff_has_passed": bool(check_out_cutoff_has_passed),

            "missing_check_in": bool(missing_check_in),

            # Work-mode
            "in_mode": in_mode,
            "out_mode": out_mode,
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
