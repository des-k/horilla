from datetime import date, datetime
from types import SimpleNamespace
from contextlib import ExitStack
from unittest.mock import MagicMock, patch

from django.core.exceptions import ValidationError
from django.test import SimpleTestCase
from django.utils import timezone
from rest_framework.response import Response
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import AttendanceWorkMode, WorkModeRequestScope
from attendance.services.work_type_request_actions import WorkModeRequestActionError, WorkModeRequestActions
from attendance.services.work_type_request_rules import validate_work_type_request
from horilla_api.api_views.attendance.views import AttendanceRequestView


class _FakeQuerySet:
    def filter(self, *args, **kwargs):
        return self

    def exclude(self, *args, **kwargs):
        return self

    def exists(self):
        return False


class WorkModeRequestCreateWindowRuleTests(SimpleTestCase):
    databases = {"default"}
    def setUp(self):
        self.employee = SimpleNamespace(
            employee_work_info=SimpleNamespace(shift_id=SimpleNamespace(id=7))
        )
        self.target_date = date(2026, 3, 26)
        self.day_obj = SimpleNamespace(day='thursday')

    def _patch_common(self, *, now_dt, rules):
        stack = ExitStack()
        stack.enter_context(
            patch.multiple(
                'attendance.services.work_type_request_rules',
                scheduled_attendance_mode=MagicMock(return_value=AttendanceWorkMode.WFO),
                shift_schedule_today=MagicMock(return_value=(480, 9 * 3600, 18 * 3600)),
                timezone=SimpleNamespace(
                    localdate=MagicMock(return_value=self.target_date),
                    now=MagicMock(return_value=now_dt),
                    localtime=timezone.localtime,
                    is_aware=timezone.is_aware,
                    make_aware=timezone.make_aware,
                    get_current_timezone=timezone.get_current_timezone,
                ),
                WorkModeRequest=SimpleNamespace(objects=SimpleNamespace(filter=MagicMock(return_value=_FakeQuerySet()))),
                EmployeeShiftDay=SimpleNamespace(objects=SimpleNamespace(filter=MagicMock(return_value=SimpleNamespace(first=MagicMock(return_value=self.day_obj))))),
            )
        )
        stack.enter_context(patch('attendance.views.clock_in_out.get_shift_rules', return_value=rules))
        return stack

    def test_in_scope_allowed_while_checkin_window_still_open(self):
        now_dt = timezone.make_aware(datetime(2026, 3, 26, 8, 30))
        rules = {
            'check_in_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 10, 0)),
            'check_out_window_start_dt': timezone.make_aware(datetime(2026, 3, 26, 17, 0)),
            'check_out_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 20, 0)),
        }
        with self._patch_common(now_dt=now_dt, rules=rules):
            validate_work_type_request(
                employee=self.employee,
                mode=AttendanceWorkMode.WFA,
                scope=WorkModeRequestScope.IN,
                start_date=self.target_date,
                end_date=self.target_date,
            )

    def test_full_scope_rejected_after_checkin_window_passes(self):
        now_dt = timezone.make_aware(datetime(2026, 3, 26, 18, 0))
        rules = {
            'check_in_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 10, 0)),
            'check_out_window_start_dt': timezone.make_aware(datetime(2026, 3, 26, 17, 0)),
            'check_out_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 20, 0)),
        }
        with self._patch_common(now_dt=now_dt, rules=rules):
            with self.assertRaisesMessage(ValidationError, 'Only OUT scope may be requested'):
                validate_work_type_request(
                    employee=self.employee,
                    mode=AttendanceWorkMode.ON_DUTY,
                    scope=WorkModeRequestScope.FULL,
                    start_date=self.target_date,
                    end_date=self.target_date,
                )

    def test_out_scope_allowed_before_checkout_window_starts(self):
        now_dt = timezone.make_aware(datetime(2026, 3, 26, 10, 55))
        rules = {
            'check_in_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 10, 0)),
            'check_out_window_start_dt': timezone.make_aware(datetime(2026, 3, 26, 17, 0)),
            'check_out_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 20, 0)),
        }
        with self._patch_common(now_dt=now_dt, rules=rules):
            validate_work_type_request(
                employee=self.employee,
                mode=AttendanceWorkMode.WFA,
                scope=WorkModeRequestScope.OUT,
                start_date=self.target_date,
                end_date=self.target_date,
            )

    def test_out_scope_allowed_when_only_checkout_window_remains_open(self):
        now_dt = timezone.make_aware(datetime(2026, 3, 26, 18, 0))
        rules = {
            'check_in_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 10, 0)),
            'check_out_window_start_dt': timezone.make_aware(datetime(2026, 3, 26, 17, 0)),
            'check_out_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 20, 0)),
        }
        with self._patch_common(now_dt=now_dt, rules=rules):
            validate_work_type_request(
                employee=self.employee,
                mode=AttendanceWorkMode.ON_DUTY,
                scope=WorkModeRequestScope.OUT,
                start_date=self.target_date,
                end_date=self.target_date,
            )

    def test_request_rejected_after_checkout_window_ends(self):
        now_dt = timezone.make_aware(datetime(2026, 3, 26, 21, 0))
        rules = {
            'check_in_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 10, 0)),
            'check_out_window_start_dt': timezone.make_aware(datetime(2026, 3, 26, 17, 0)),
            'check_out_window_end_dt': timezone.make_aware(datetime(2026, 3, 26, 20, 0)),
        }
        with self._patch_common(now_dt=now_dt, rules=rules):
            with self.assertRaisesMessage(ValidationError, 'Check-out window has ended'):
                validate_work_type_request(
                    employee=self.employee,
                    mode=AttendanceWorkMode.ON_DUTY,
                    scope=WorkModeRequestScope.OUT,
                    start_date=self.target_date,
                    end_date=self.target_date,
                )


class WorkModeRequestOnDutyAttachmentRequirementTests(SimpleTestCase):
    databases = {"default"}
    def test_on_duty_create_requires_attachment(self):
        actor = SimpleNamespace(id=10)
        with patch('attendance.services.work_type_request_actions.validate_work_type_request'), \
             patch('attendance.services.work_type_request_actions.WorkModeRequest.objects.create') as create_req:
            with self.assertRaisesMessage(WorkModeRequestActionError, 'At least one file is required for ON DUTY requests.'):
                WorkModeRequestActions.create_request(
                    actor=actor,
                    mode=AttendanceWorkMode.ON_DUTY,
                    scope=WorkModeRequestScope.FULL,
                    start_date=date(2026, 3, 26),
                    end_date=date(2026, 3, 26),
                    reason='Client visit',
                    duty_destination_location='Client HQ',
                    uploaded_files=[],
                )
        create_req.assert_not_called()


class AttendanceRequestSelfBindingRegressionTests(SimpleTestCase):
    databases = {"default"}
    def setUp(self):
        self.factory = APIRequestFactory()
        self.view = AttendanceRequestView.as_view()
        self.user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=33))

    def test_create_request_injects_actor_employee_id_when_client_omits_it(self):
        captured = {}

        def build_form(*args, **kwargs):
            captured['data'] = kwargs.get('data') if 'data' in kwargs else (args[0] if args else None)
            form = MagicMock()
            form.is_valid.return_value = False
            form.errors = {'attendance_date': ['required']}
            return form

        request = self.factory.post('/api/attendance/attendance-request/', {'attendance_date': '2026-03-26'}, format='json')
        force_authenticate(request, user=self.user)

        with patch('attendance.forms.NewRequestForm', side_effect=build_form):
            response = self.view(request)

        self.assertEqual(response.status_code, 400)
        self.assertEqual(captured['data']['employee_id'], 33)
