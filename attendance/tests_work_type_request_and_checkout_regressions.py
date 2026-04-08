from __future__ import annotations

from datetime import date, datetime, time
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from django.http import HttpResponse
from django.test import RequestFactory, SimpleTestCase
from django.utils import timezone
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import AttendanceWorkMode, WorkModeRequestScope
from attendance.views.work_type_requests import work_type_request_view
from horilla_api.api_views.attendance.views import CheckingStatus, WorkModeRequestView
from horilla_api.tests import _AuthUser, _FirstSequence


class _QS:
    def __init__(self, items=None, filter_calls=None):
        self.items = list(items or [])
        self.filter_calls = list(filter_calls or [])

    def all(self):
        return _QS(self.items, self.filter_calls)

    def filter(self, *args, **kwargs):
        return _QS(self.items, self.filter_calls + [kwargs])

    def exclude(self, *args, **kwargs):
        return _QS(self.items, self.filter_calls)

    def order_by(self, *args, **kwargs):
        return list(self.items)

    def distinct(self):
        return _QS(self.items, self.filter_calls)

    def none(self):
        return _QS([], self.filter_calls)

    def __or__(self, other):
        return _QS(self.items + getattr(other, 'items', []), self.filter_calls + getattr(other, 'filter_calls', []))


class _Page:
    def __init__(self, object_list):
        self.object_list = object_list


class WorkTypeRequestListRegressionTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.employee = SimpleNamespace(id=7, employee_first_name='Api', employee_last_name='User')
        self.user = _AuthUser(self.employee)

    def test_api_work_type_request_mine_list_no_longer_uses_undefined_ordered(self):
        request = self.factory.get('/api/attendance/work-type-request/?mine=1')
        force_authenticate(request, user=self.user)
        rows = [SimpleNamespace(id=2), SimpleNamespace(id=1)]
        with patch('horilla_api.api_views.attendance.views.WorkModeRequest.objects', _QS(rows)), \
             patch('horilla_api.api_views.attendance.views.filtersubordinates', return_value=_QS([])), \
             patch.object(WorkModeRequestView, 'serializer_class') as serializer_cls:
            serializer_cls.return_value.data = [{'id': 2}, {'id': 1}]
            response = WorkModeRequestView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data['count'], 2)




class CheckingStatusCheckoutWindowRegressionTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.dt_now = timezone.make_aware(datetime(2026, 3, 20, 12, 30))
        self.attendance_date = date(2026, 3, 20)
        self.day = SimpleNamespace(id=1)
        self.company = SimpleNamespace(id=10, company='Parity Co')
        self.employee = SimpleNamespace(
            employee_first_name='Parity',
            employee_last_name='User',
            email='parity-user@example.com',
            phone='9999999999',
            employee_work_info=SimpleNamespace(shift_id='SHIFT-A'),
        )
        self.employee.get_company = lambda: self.company
        self.user = _AuthUser(self.employee)
        self.shift_rules = {
            'schedule': object(),
            'grace_seconds': 0,
            'clock_in_type': 'after',
            'cutoff_in_dt': self.dt_now.replace(hour=10, minute=0),
            'cutoff_out_dt': self.dt_now.replace(hour=22, minute=0),
            'shift_start_dt': self.dt_now.replace(hour=8, minute=0),
            'shift_end_dt': self.dt_now.replace(hour=17, minute=0),
            'check_in_window_start_dt': self.dt_now.replace(hour=6, minute=0),
            'check_in_window_end_dt': self.dt_now.replace(hour=10, minute=0),
            'check_out_window_start_dt': self.dt_now.replace(hour=12, minute=0),
            'check_out_window_end_dt': self.dt_now.replace(hour=22, minute=0),
        }
        self.access = SimpleNamespace(
            allowed=True,
            message=None,
            reason_code=None,
            blocked_roles=(),
            is_reporting_manager=False,
            is_admin=False,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )

    def _status_request(self):
        request = self.factory.get('/api/attendance/checking-status/')
        force_authenticate(request, user=self.user)
        return request

    def _status_patches(self, *, modes, allowed=None, attendance=None):
        if allowed is None:
            allowed = [True, True]
        return [
            patch('horilla_api.api_views.attendance.views._api_now', return_value=self.dt_now),
            patch('horilla_api.api_views.attendance.views.evaluate_attendance_access', return_value=self.access),
            patch(
                'horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day',
                return_value=(self.attendance_date, self.day, '08:00', 8 * 3600, 17 * 3600, '08:05', 8 * 3600 + 5 * 60),
            ),
            patch('horilla_api.api_views.attendance.views.cio.get_shift_rules', return_value=self.shift_rules),
            patch('horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date'),
            patch('horilla_api.api_views.attendance.views._resolve_punch_work_type', side_effect=modes),
            patch('horilla_api.api_views.attendance.views._is_punch_allowed', side_effect=allowed),
            patch('horilla_api.api_views.attendance.views.Attendance.objects.filter', return_value=_FirstSequence(attendance)),
            patch('horilla_api.api_views.attendance.views.AttendanceActivity.objects.filter', return_value=_FirstSequence(None)),
            patch('horilla_api.api_views.attendance.views._build_mobile_header_note_context', return_value={'header_note_effective_duration_seconds': None}),
        ]

    def test_checking_status_allows_clock_out_once_checkout_window_opens_even_before_shift_end(self):
        attendance = SimpleNamespace(
            attendance_clock_in=time(8, 0),
            attendance_clock_out=None,
            attendance_clock_in_date=self.attendance_date,
            attendance_clock_out_date=None,
            in_attendance_status='VALID',
            out_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_reject_reason_code=None,
            in_related_work_type_request_id=None,
            out_related_work_type_request_id=None,
            reconciliation_source='mobile',
            attendance_worked_hour='04:30',
        )
        request = self._status_request()
        patches = self._status_patches(
            modes=[(AttendanceWorkMode.WFA, 'request', object()), (AttendanceWorkMode.WFA, 'request', object())],
            allowed=[True, True],
            attendance=attendance,
        )
        for m in patches:
            m.start()
        try:
            response = CheckingStatus.as_view()(request)
        finally:
            for m in reversed(patches):
                m.stop()
        self.assertEqual(response.status_code, 200)
        self.assertTrue(response.data['can_clock_out'])
        self.assertIsNone(response.data['check_out_block_reason'])


    def test_api_work_type_request_mine_list_applies_month_overlap_filter(self):
        request = self.factory.get('/api/attendance/work-type-request/?mine=1&month=2026-04')
        force_authenticate(request, user=self.user)
        rows = [SimpleNamespace(id=2), SimpleNamespace(id=1)]
        own_qs = _QS(rows)
        with patch('horilla_api.api_views.attendance.views.WorkModeRequest.objects', _QS(rows)),              patch('horilla_api.api_views.attendance.views.filtersubordinates', return_value=_QS([])),              patch.object(WorkModeRequestView, 'serializer_class') as serializer_cls:
            serializer_cls.return_value.data = [{'id': 2}, {'id': 1}]
            with patch.object(self.user, 'employee_get', self.employee, create=True):
                response = WorkModeRequestView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        # union path uses a fresh own_qs internally, so assert against rendered source regression too
        source = Path('horilla_api/api_views/attendance/views.py').read_text()
        self.assertIn('month_range = _parse_filter_month_range(request.GET.get("month") or request.GET.get("date"))', source)
        self.assertIn('qs = qs.filter(start_date__lte=month_end, end_date__gte=month_start)', source)


class WorkTypeRequestMyMonthWebRegressionTests(SimpleTestCase):
    def test_web_view_source_contains_my_month_filter_and_context(self):
        source = Path('attendance/views/work_type_requests.py').read_text()
        self.assertIn('request.GET.get("my_month")', source)
        self.assertIn('my_qs = my_qs.filter(start_date__lte=my_month_end, end_date__gte=my_month_start)', source)
        self.assertIn('"my_month": my_month', source)

    def test_nav_template_contains_month_filter(self):
        source = Path('attendance/templates/attendance/work_type_requests/nav.html').read_text()
        self.assertIn('name="my_month"', source)
        self.assertIn('value="{{ my_month }}"', source)

    def test_approval_history_template_preserves_my_month_filter(self):
        source = Path('attendance/templates/attendance/work_type_requests/table_approval_history.html').read_text()
        self.assertIn('name="my_month" value="{{ my_month }}"', source)
        self.assertIn('oh-history-filter-control', source)
