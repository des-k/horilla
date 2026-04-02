from datetime import date, time

from django.test import override_settings
from rest_framework.test import APITestCase

from attendance.models import (
    Attendance,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestStatus,
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchingHistory,
)
from attendance.services.reconciliation import recompute_attendance
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


@override_settings(ALLOWED_HOSTS=['testserver', 'localhost', '127.0.0.1'])
class AttendanceCorrectionRequestApiTests(AttendanceApiIntegrationMixin, APITestCase):
    target_date = date(2026, 4, 2)

    def setUp(self):
        super().setUp()
        self.manager_user, self.manager_employee = self.create_employee('ApiManager')
        self.owner_user, self.employee = self.create_employee('ApiOwner', manager=self.manager_employee)
        self.other_user, self.other_employee = self.create_employee('ApiOther')
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
            shift_start_dt=self.aware_dt(2026, 4, 2, 8, 0),
            shift_end_dt=self.aware_dt(2026, 4, 2, 17, 0),
            check_in_window_start_dt=self.aware_dt(2026, 4, 2, 6, 0),
            check_in_window_end_dt=self.aware_dt(2026, 4, 2, 12, 0),
            check_out_window_start_dt=self.aware_dt(2026, 4, 2, 12, 0),
            check_out_window_end_dt=self.aware_dt(2026, 4, 2, 23, 0),
            minimum_hour='08:00',
        )

    def _raw_punches(self):
        AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 4, 2, 9, 0),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='BIO-2',
            device_info='Gate A',
        )
        AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 4, 2, 17, 0),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='BIO-2',
            device_info='Gate A',
        )
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

    def test_create_update_approve_revoke_and_history_contract(self):
        self._raw_punches()
        owner_client = self.auth_client(self.owner_user)
        manager_client = self.auth_client(self.manager_user)

        create_payload = {
            'attendance_date': self.target_date.isoformat(),
            'scope': 'FULL',
            'reason': 'Forgot correct times',
            'requested_check_in_date': self.target_date.isoformat(),
            'requested_check_in_time': '08:00',
            'requested_check_out_date': self.target_date.isoformat(),
            'requested_check_out_time': '16:00',
        }
        create_response = owner_client.post('/api/attendance/attendance-request/', create_payload, format='json')
        self.assertEqual(create_response.status_code, 201, create_response.data)
        self.assertEqual(create_response.data['scope'], 'FULL')
        self.assertEqual(create_response.data['status'], AttendanceCorrectionRequestStatus.WAITING)
        self.assertTrue(create_response.data['can_edit'])
        self.assertTrue(create_response.data['can_cancel'])
        self.assertFalse(create_response.data['can_approve'])
        self.assertNotIn('request_type', create_response.data)
        self.assertNotIn('requested_data', create_response.data)
        request_id = create_response.data['id']

        # waiting request can change scope and revalidates against itself only
        update_response = owner_client.put(
            f'/api/attendance/attendance-request/{request_id}',
            {
                'attendance_date': self.target_date.isoformat(),
                'scope': 'IN',
                'reason': 'Only check-in correction is needed',
                'requested_check_in_date': self.target_date.isoformat(),
                'requested_check_in_time': '08:15',
            },
            format='json',
        )
        self.assertEqual(update_response.status_code, 200, update_response.data)
        self.assertEqual(update_response.data['scope'], 'IN')
        self.assertEqual(update_response.data['requested_check_in_time'], '08:15:00')
        self.assertIsNone(update_response.data['requested_check_out_time'])

        # conflict: same active IN/FULL slot cannot be created again
        conflict_response = owner_client.post(
            '/api/attendance/attendance-request/',
            {
                'attendance_date': self.target_date.isoformat(),
                'scope': 'FULL',
                'reason': 'conflict',
                'requested_check_in_date': self.target_date.isoformat(),
                'requested_check_in_time': '08:00',
                'requested_check_out_date': self.target_date.isoformat(),
                'requested_check_out_time': '16:00',
            },
            format='json',
        )
        self.assertEqual(conflict_response.status_code, 400)
        self.assertIn('scope', conflict_response.data)

        approve_response = manager_client.put(
            f'/api/attendance/attendance-request-approve/{request_id}', {}, format='json'
        )
        self.assertEqual(approve_response.status_code, 200, approve_response.data)
        self.assertEqual(approve_response.data['status'], AttendanceCorrectionRequestStatus.APPROVED)
        self.assertTrue(approve_response.data['can_revoke'])
        self.assertEqual(approve_response.data['action_by_name'], self.manager_employee.get_full_name())

        att = Attendance.objects.get(employee_id=self.employee, attendance_date=self.target_date)
        self.assertEqual(att.attendance_clock_in, time(8, 15))
        self.assertEqual(att.attendance_clock_out, time(17, 0))

        owner_update_after_approve = owner_client.put(
            f'/api/attendance/attendance-request/{request_id}',
            {
                'attendance_date': self.target_date.isoformat(),
                'scope': 'IN',
                'reason': 'should fail',
                'requested_check_in_date': self.target_date.isoformat(),
                'requested_check_in_time': '08:20',
            },
            format='json',
        )
        self.assertEqual(owner_update_after_approve.status_code, 403)

        revoke_without_reason = manager_client.put(
            f'/api/attendance/attendance-request-revoke/{request_id}', {}, format='json'
        )
        self.assertEqual(revoke_without_reason.status_code, 400)
        self.assertIn('reason', revoke_without_reason.data)

        revoke_response = manager_client.put(
            f'/api/attendance/attendance-request-revoke/{request_id}', {'reason': 'Invalid evidence'}, format='json'
        )
        self.assertEqual(revoke_response.status_code, 200, revoke_response.data)
        self.assertEqual(revoke_response.data['status'], AttendanceCorrectionRequestStatus.REVOKED)
        att.refresh_from_db()
        self.assertEqual(att.attendance_clock_in, time(9, 0))
        self.assertEqual(att.attendance_clock_out, time(17, 0))

        history_response = manager_client.get(
            '/api/attendance/attendance-request/',
            {'approval_view': 'history', 'month': self.target_date.strftime('%Y-%m'), 'status': 'all'},
            format='json',
        )
        self.assertEqual(history_response.status_code, 200)
        results = history_response.data['results']
        self.assertEqual([item['status'] for item in results], [AttendanceCorrectionRequestStatus.REVOKED])

    def test_cancel_stays_out_of_approval_history_but_remains_in_my_requests(self):
        owner_client = self.auth_client(self.owner_user)
        manager_client = self.auth_client(self.manager_user)
        create_response = owner_client.post(
            '/api/attendance/attendance-request/',
            {
                'attendance_date': self.target_date.isoformat(),
                'scope': 'OUT',
                'reason': 'Need out correction only',
                'requested_check_out_date': self.target_date.isoformat(),
                'requested_check_out_time': '16:40',
            },
            format='json',
        )
        self.assertEqual(create_response.status_code, 201, create_response.data)
        request_id = create_response.data['id']

        cancel_response = owner_client.put(
            f'/api/attendance/attendance-request-cancel/{request_id}', {}, format='json'
        )
        self.assertEqual(cancel_response.status_code, 200, cancel_response.data)
        self.assertEqual(cancel_response.data['status'], AttendanceCorrectionRequestStatus.CANCELED)

        my_response = owner_client.get(
            '/api/attendance/attendance-request/',
            {'mine': '1', 'month': self.target_date.strftime('%Y-%m'), 'status': 'all'},
            format='json',
        )
        self.assertEqual(my_response.status_code, 200)
        my_statuses = [item['status'] for item in my_response.data['results']]
        self.assertIn(AttendanceCorrectionRequestStatus.CANCELED, my_statuses)

        history_response = manager_client.get(
            '/api/attendance/attendance-request/',
            {'approval_view': 'history', 'month': self.target_date.strftime('%Y-%m'), 'status': 'all'},
            format='json',
        )
        self.assertEqual(history_response.status_code, 200)
        history_statuses = [item['status'] for item in history_response.data['results']]
        self.assertNotIn(AttendanceCorrectionRequestStatus.CANCELED, history_statuses)
        self.assertTrue(AttendanceCorrectionRequest.objects.filter(id=request_id, status=AttendanceCorrectionRequestStatus.CANCELED).exists())
