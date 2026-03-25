from datetime import date, time, timedelta
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase, override_settings
from rest_framework.test import APITestCase, APIRequestFactory, force_authenticate

from attendance.filters import AttendanceActivityFilter
from attendance.models import Attendance, AttendanceActivity, AttendanceChannel, AttendancePunchDirection, AttendancePunchSource, AttendancePunchingHistory, AttendanceWorkMode
from attendance.services.activity_sync import sync_single_session_activity
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from attendance.services.reconciliation import recompute_attendance
from leave.models import AvailableLeave, LeaveRequest, LeaveType
from horilla_api.api_views.attendance import views as api_views


def _identity_filter(_data, queryset=None, **_kwargs):
    return SimpleNamespace(qs=queryset)


class _FakeActivityQuerySet(list):
    model = AttendanceActivity

    def select_related(self, *args, **kwargs):
        return self

    def all(self):
        return self

    def filter(self, **kwargs):
        items = list(self)
        employee = kwargs.get("employee_id")
        if employee is not None:
            items = [item for item in items if getattr(item, "employee_id", None) == employee]
        employee_ids = kwargs.get("employee_id_id__in")
        if employee_ids is not None:
            employee_ids = set(employee_ids)
            items = [item for item in items if getattr(getattr(item, "employee_id", None), "id", None) in employee_ids]
        return _FakeActivityQuerySet(items)

    def order_by(self, *args, **kwargs):
        items = list(self)
        for key in reversed(args):
            reverse = key.startswith("-")
            attr = key[1:] if reverse else key
            items.sort(key=lambda item: getattr(item, attr), reverse=reverse)
        return _FakeActivityQuerySet(items)


class AttendanceActivityApiAndPermissionsTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.manager = SimpleNamespace(id=1)
        self.owner = SimpleNamespace(id=2)
        self.subordinate = SimpleNamespace(id=3)
        self.outsider = SimpleNamespace(id=4)
        self.owner_user = SimpleNamespace(is_authenticated=True, employee_get=self.owner, has_perm=lambda perm: False)
        self.manager_user = SimpleNamespace(is_authenticated=True, employee_get=self.manager, has_perm=lambda perm: False)
        self.admin_user = SimpleNamespace(is_authenticated=True, employee_get=self.manager, has_perm=lambda perm: True)
        self.activities = _FakeActivityQuerySet([
            SimpleNamespace(id=11, employee_id=self.owner, attendance_date=date(2026, 3, 14)),
            SimpleNamespace(id=12, employee_id=self.subordinate, attendance_date=date(2026, 3, 14)),
            SimpleNamespace(id=13, employee_id=self.outsider, attendance_date=date(2026, 3, 15)),
        ])

    def _dummy_serializer(self, obj, many=False):
        if many:
            return SimpleNamespace(data=[{"id": item.id, "employee_id": item.employee_id.id, "attendance_date": item.attendance_date.isoformat()} for item in obj])
        return SimpleNamespace(data={"id": obj.id, "employee_id": obj.employee_id.id, "attendance_date": obj.attendance_date.isoformat()})

    def test_activity_list_blocks_cross_employee_access_for_regular_employee(self):
        request = self.factory.get("/api/attendance/attendance-activity/")
        force_authenticate(request, user=self.owner_user)
        scoped_employees = SimpleNamespace(values_list=lambda *args, **kwargs: [self.owner.id])
        with patch.object(api_views.AttendanceActivity, "objects", self.activities), \
             patch.object(api_views, "get_attendance_subject_employees", return_value=(scoped_employees, False, False, self.owner.id)), \
             patch.object(api_views, "AttendanceActivitySerializer", side_effect=self._dummy_serializer), \
             patch.object(api_views, "AttendanceActivityFilter", side_effect=_identity_filter):
            response = api_views.AttendanceActivityView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data, [{"id": 11, "employee_id": 2, "attendance_date": "2026-03-14"}])

    def test_activity_list_allows_manager_only_for_subordinates(self):
        request = self.factory.get("/api/attendance/attendance-activity/")
        force_authenticate(request, user=self.manager_user)
        scoped_employees = SimpleNamespace(values_list=lambda *args, **kwargs: [self.subordinate.id])
        with patch.object(api_views.AttendanceActivity, "objects", self.activities), \
             patch.object(api_views, "get_attendance_subject_employees", return_value=(scoped_employees, False, False, self.subordinate.id)), \
             patch.object(api_views, "AttendanceActivitySerializer", side_effect=self._dummy_serializer), \
             patch.object(api_views, "AttendanceActivityFilter", side_effect=_identity_filter):
            response = api_views.AttendanceActivityView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual([item["id"] for item in response.data], [12])

    def test_activity_list_allows_superuser_to_view_all_records(self):
        request = self.factory.get("/api/attendance/attendance-activity/")
        force_authenticate(request, user=self.admin_user)
        scoped_employees = SimpleNamespace(values_list=lambda *args, **kwargs: [self.owner.id, self.subordinate.id, self.outsider.id])
        with patch.object(api_views.AttendanceActivity, "objects", self.activities), \
             patch.object(api_views, "get_attendance_subject_employees", return_value=(scoped_employees, True, True, self.owner.id)), \
             patch.object(api_views, "AttendanceActivitySerializer", side_effect=self._dummy_serializer), \
             patch.object(api_views, "AttendanceActivityFilter", side_effect=_identity_filter):
            response = api_views.AttendanceActivityView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual({item["id"] for item in response.data}, {11, 12, 13})

    def test_activity_filter_support_includes_employee_and_date_range_fields(self):
        self.assertIn("employee_id", AttendanceActivityFilter.Meta.fields)
        self.assertIn("attendance_date_from", AttendanceActivityFilter.Meta.fields)
        self.assertIn("attendance_date_till", AttendanceActivityFilter.Meta.fields)


class AttendanceActivityApiIntegrationTests(AttendanceApiIntegrationMixin, APITestCase):
    endpoint = '/api/attendance/attendance-activity/'

    def _call(self, user, params=None):
        response = self.auth_client(user).get(self.endpoint, params or {}, format='json')
        self._clear_request_context()
        return response

    def _json(self, response):
        return response.json()

    def test_activity_list_blocks_cross_employee_access_for_regular_employee(self):
        owner_user, owner = self.create_employee('Owner')
        _, outsider = self.create_employee('Outsider')
        owner_activity = AttendanceActivity.objects.create(employee_id=owner, attendance_date=date(2026, 3, 14))
        AttendanceActivity.objects.create(employee_id=outsider, attendance_date=date(2026, 3, 14))

        response = self._call(owner_user)
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data], [owner_activity.id])
        self.assertEqual({item['employee_id'] for item in data}, {owner.id})

    def test_activity_list_allows_manager_only_for_subordinates(self):
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)
        _, outsider = self.create_employee('Outsider')
        subordinate_activity = AttendanceActivity.objects.create(
            employee_id=subordinate,
            attendance_date=date(2026, 3, 14),
        )
        AttendanceActivity.objects.create(employee_id=outsider, attendance_date=date(2026, 3, 14))

        response = self._call(manager_user)
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data], [subordinate_activity.id])
        self.assertEqual({item['employee_id'] for item in data}, {subordinate.id})

    def test_activity_list_filters_by_employee_and_date_range(self):
        admin_user, _ = self.create_employee('Admin', is_superuser=True)
        _, owner = self.create_employee('Owner')
        _, other = self.create_employee('Other')
        AttendanceActivity.objects.create(employee_id=owner, attendance_date=date(2026, 3, 14))
        expected = AttendanceActivity.objects.create(employee_id=owner, attendance_date=date(2026, 3, 15))
        AttendanceActivity.objects.create(employee_id=other, attendance_date=date(2026, 3, 15))

        response = self._call(
            admin_user,
            params={
                'employee_id': owner.id,
                'attendance_date_from': '2026-03-15',
                'attendance_date_till': '2026-03-15',
            },
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data], [expected.id])
        self.assertEqual(data[0]['attendance_date'], '2026-03-15')

    def test_activity_sync_after_attendance_request_approve(self):
        owner_user, owner = self.create_employee('Owner')
        self.auth_request(owner_user)
        attendance = Attendance.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 16),
            attendance_clock_in_date=date(2026, 3, 16),
            attendance_clock_in=time(9, 30),
            attendance_clock_in_channel=AttendanceChannel.CORRECTION_REQUEST,
            request_type='update_request',
            is_validate_request=False,
            is_validate_request_approved=True,
        )
        sync_single_session_activity(attendance)
        self._clear_request_context()

        response = self._call(
            owner_user,
            params={
                'employee_id': owner.id,
                'attendance_date_from': '2026-03-16',
                'attendance_date_till': '2026-03-16',
            },
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]['employee_id'], owner.id)
        self.assertEqual(data[0]['clock_in'], '09:30:00')
        self.assertEqual(data[0]['clock_in_channel'], AttendanceChannel.CORRECTION_REQUEST)

    def test_activity_sync_after_attendance_request_revoke(self):
        owner_user, owner = self.create_employee('Owner')
        self.auth_request(owner_user)
        attendance = Attendance.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 17),
            attendance_clock_in_date=date(2026, 3, 17),
            attendance_clock_in=time(8, 5),
            attendance_clock_in_channel=AttendanceChannel.MOBILE,
            attendance_validated=True,
        )
        sync_single_session_activity(attendance)
        self._clear_request_context()

        attendance.request_type = 'update_request'
        attendance.is_validate_request = False
        attendance.is_validate_request_approved = True
        attendance.attendance_clock_in = time(9, 30)
        attendance.attendance_clock_in_channel = AttendanceChannel.CORRECTION_REQUEST
        self.auth_request(owner_user)
        attendance.save(update_fields=[
            'request_type',
            'is_validate_request',
            'is_validate_request_approved',
            'attendance_clock_in',
            'attendance_clock_in_channel',
        ])
        sync_single_session_activity(attendance)
        self._clear_request_context()

        approved_response = self._call(
            owner_user,
            params={
                'employee_id': owner.id,
                'attendance_date_from': '2026-03-17',
                'attendance_date_till': '2026-03-17',
            },
        )
        approved_data = self._json(approved_response)
        self.assertEqual(approved_data[0]['clock_in'], '09:30:00')
        self.assertEqual(approved_data[0]['clock_in_channel'], AttendanceChannel.CORRECTION_REQUEST)

        attendance.request_type = 'revoke_request'
        attendance.attendance_clock_in = time(8, 5)
        attendance.attendance_clock_in_channel = AttendanceChannel.MOBILE
        self.auth_request(owner_user)
        attendance.save(update_fields=[
            'request_type',
            'attendance_clock_in',
            'attendance_clock_in_channel',
        ])
        restored_activity = sync_single_session_activity(attendance)
        self._clear_request_context()

        response = self._call(
            owner_user,
            params={
                'employee_id': owner.id,
                'attendance_date_from': '2026-03-17',
                'attendance_date_till': '2026-03-17',
            },
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]['id'], restored_activity.id)
        self.assertEqual(data[0]['clock_in'], '08:05:00')
        self.assertEqual(data[0]['clock_in_channel'], AttendanceChannel.MOBILE)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=owner, attendance_date=date(2026, 3, 17)).count(), 1)


@override_settings(ALLOWED_HOSTS=["testserver", "localhost", "127.0.0.1"])
class AttendanceActivityApiRepresentationIntegrationTests(AttendanceApiIntegrationMixin, APITestCase):
    endpoint = '/api/attendance/attendance-activity/'

    def setUp(self):
        super().setUp()
        self.target_date = date.today() + timedelta(days=12)
        self.owner_user, self.employee = self.create_employee('ActivityOwner')
        self.admin_user, self.admin_employee = self.create_employee('ActivityAdmin', is_superuser=True)
        self.auth_request(self.owner_user)
        weekday_key = self.target_date.strftime('%A').lower()
        self.shift, self.day_obj, self.schedule = self.create_shift_with_schedule(
            employee=self.employee,
            day_key=weekday_key,
            start_time=time(8, 0),
            end_time=time(17, 0),
            minimum_working_hour='08:00',
            is_night_shift=False,
        )
        self.shift_ctx = self.patch_reconciliation_shift_rules(
            target_date=self.target_date,
            schedule=self.schedule,
            shift_start_dt=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, 8, 0),
            shift_end_dt=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, 17, 0),
            check_in_window_start_dt=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, 6, 0),
            check_in_window_end_dt=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, 23, 0),
            check_out_window_start_dt=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, 6, 0),
            check_out_window_end_dt=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, 23, 0),
            minimum_hour='08:00',
        )
        self.leave_type = LeaveType.objects.create(name='Activity Leave', company_id=self.company)
        AvailableLeave.objects.create(employee_id=self.employee, leave_type_id=self.leave_type, available_days=5, carryforward_days=1)
        AvailableLeave.objects.create(employee_id=self.admin_employee, leave_type_id=self.leave_type, available_days=3, carryforward_days=1)

    def _call(self, user, params=None):
        response = self.auth_client(user).get(self.endpoint, params or {}, format='json')
        self._clear_request_context()
        return response

    def _json(self, response):
        return response.json()

    def _attendance(self):
        return Attendance.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _create_punch(self, *, hour, minute, direction, source, device='Main Gate', work_mode=AttendanceWorkMode.WFO):
        return AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(self.target_date.year, self.target_date.month, self.target_date.day, hour, minute),
            source=source,
            punch_direction=direction,
            raw_employee_identifier='ACTIVITY-1',
            device_info=device,
            work_mode=work_mode,
        )

    def _create_requested_leave(self):
        with patch('leave.signals._reconcile_leave_related_punches', return_value=None):
            return LeaveRequest.objects.create(
                employee_id=self.employee,
                leave_type_id=self.leave_type,
                start_date=self.target_date,
                end_date=self.target_date,
                start_date_breakdown='full_day',
                end_date_breakdown='full_day',
                description='Activity API leave',
                status='requested',
            )

    def _approve_leave(self, leave_request):
        with self.shift_ctx:
            return self.auth_client(self.admin_user).put(f'/api/leave/approve/{leave_request.id}/', {}, format='json')

    def _cancel_leave(self, leave_request):
        with self.shift_ctx:
            return self.auth_client(self.owner_user).put(f'/api/leave/cancel/{leave_request.id}/', {}, format='json')

    def _approve_correction_out(self, attendance, out_time_str='17:45:00'):
        attendance.request_type = 'update_request'
        attendance.is_validate_request = True
        attendance.is_validate_request_approved = False
        attendance.requested_data = {
            'attendance_clock_out': out_time_str,
            '__meta': {'current_scope': 'OUT'},
        }
        attendance.save(update_fields=['request_type', 'is_validate_request', 'is_validate_request_approved', 'requested_data'])
        with self.shift_ctx:
            return self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-approve/{attendance.id}',
                {},
                format='json',
            )

    def _revoke_correction(self, attendance):
        with self.shift_ctx:
            return self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-revoke/{attendance.id}',
                {},
                format='json',
            )

    def test_activity_api_after_leave_cancel_keeps_single_final_row_and_correct_note(self):
        self._create_punch(hour=8, minute=0, direction=AttendancePunchDirection.IN, source=AttendancePunchSource.BIOMETRIC)
        self._create_punch(hour=17, minute=10, direction=AttendancePunchDirection.OUT, source=AttendancePunchSource.MOBILE, device='Mobile App')
        leave_request = self._create_requested_leave()
        self.assertEqual(self._approve_leave(leave_request).status_code, 200)
        self.assertEqual(self._cancel_leave(leave_request).status_code, 200)

        attendance = self._attendance()
        response = self._call(
            self.owner_user,
            params={
                'employee_id': self.employee.id,
                'attendance_date_from': self.target_date.isoformat(),
                'attendance_date_till': self.target_date.isoformat(),
            },
        )
        data = self._json(response)
        self.assertEqual(response.status_code, 200)
        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]['clock_in'], '08:00:00')
        self.assertEqual(data[0]['clock_out'], '17:10:00')
        self.assertEqual(data[0]['clock_in_channel'], AttendanceChannel.BIOMETRIC)
        self.assertEqual(data[0]['clock_out_channel'], AttendanceChannel.MOBILE)
        self.assertEqual(data[0]['reconciliation_source'], attendance.reconciliation_source)
        self.assertEqual(data[0]['reconciliation_note'], attendance.reconciliation_note)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)

    def test_activity_api_after_generated_out_revoke_keeps_single_final_truth_without_duplicate_rows(self):
        self._create_punch(hour=8, minute=0, direction=AttendancePunchDirection.IN, source=AttendancePunchSource.BIOMETRIC)
        self._create_punch(hour=16, minute=50, direction=AttendancePunchDirection.OUT, source=AttendancePunchSource.BIOMETRIC)
        self._create_punch(hour=17, minute=20, direction=AttendancePunchDirection.OUT, source=AttendancePunchSource.MOBILE, device='Mobile App')
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)
        attendance = self._attendance()
        self.assertEqual(self._approve_correction_out(attendance).status_code, 200)
        self.assertEqual(self._revoke_correction(attendance).status_code, 200)
        attendance = self._attendance()

        response = self._call(
            self.owner_user,
            params={
                'employee_id': self.employee.id,
                'attendance_date_from': self.target_date.isoformat(),
                'attendance_date_till': self.target_date.isoformat(),
            },
        )
        data = self._json(response)
        self.assertEqual(response.status_code, 200)
        self.assertEqual(len(data), 1)
        self.assertEqual(data[0]['clock_in'], '08:00:00')
        self.assertEqual(data[0]['clock_out'], '17:20:00')
        self.assertEqual(data[0]['clock_in_channel'], AttendanceChannel.BIOMETRIC)
        self.assertEqual(data[0]['clock_out_channel'], AttendanceChannel.MOBILE)
        self.assertEqual(data[0]['reconciliation_source'], attendance.reconciliation_source)
        self.assertEqual(data[0]['reconciliation_note'], attendance.reconciliation_note)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)

    def test_invalid_transition_after_mixed_source_finalization_keeps_activity_api_unchanged(self):
        self._create_punch(hour=8, minute=0, direction=AttendancePunchDirection.IN, source=AttendancePunchSource.BIOMETRIC)
        self._create_punch(hour=16, minute=50, direction=AttendancePunchDirection.OUT, source=AttendancePunchSource.BIOMETRIC)
        self._create_punch(hour=17, minute=20, direction=AttendancePunchDirection.OUT, source=AttendancePunchSource.MOBILE, device='Mobile App')
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)
        attendance = self._attendance()
        self.assertEqual(self._approve_correction_out(attendance).status_code, 200)
        self.assertEqual(self._revoke_correction(attendance).status_code, 200)

        baseline_response = self._call(
            self.owner_user,
            params={
                'employee_id': self.employee.id,
                'attendance_date_from': self.target_date.isoformat(),
                'attendance_date_till': self.target_date.isoformat(),
            },
        )
        baseline_data = self._json(baseline_response)
        second_revoke = self._revoke_correction(attendance)
        self.assertEqual(second_revoke.status_code, 404)

        response = self._call(
            self.owner_user,
            params={
                'employee_id': self.employee.id,
                'attendance_date_from': self.target_date.isoformat(),
                'attendance_date_till': self.target_date.isoformat(),
            },
        )
        data = self._json(response)
        self.assertEqual(response.status_code, 200)
        self.assertEqual(data, baseline_data)
        self.assertEqual(len(data), 1)
