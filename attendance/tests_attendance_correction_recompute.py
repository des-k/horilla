from datetime import date, time

from django.test import TestCase, override_settings

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceChannel,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestStatus,
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchingHistory,
)
from attendance.services.attendance_correction_requests import (
    approve_request,
    create_request,
    revoke_request,
)
from attendance.services.reconciliation import recompute_attendance
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


@override_settings(ALLOWED_HOSTS=['testserver', 'localhost', '127.0.0.1'])
class AttendanceCorrectionRecomputeTests(AttendanceApiIntegrationMixin, TestCase):
    target_date = date(2026, 4, 1)

    def setUp(self):
        super().setUp()
        self.manager_user, self.manager_employee = self.create_employee('Manager')
        self.owner_user, self.employee = self.create_employee('Owner', manager=self.manager_employee)
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
            shift_start_dt=self.aware_dt(2026, 4, 1, 8, 0),
            shift_end_dt=self.aware_dt(2026, 4, 1, 17, 0),
            check_in_window_start_dt=self.aware_dt(2026, 4, 1, 6, 0),
            check_in_window_end_dt=self.aware_dt(2026, 4, 1, 12, 0),
            check_out_window_start_dt=self.aware_dt(2026, 4, 1, 12, 0),
            check_out_window_end_dt=self.aware_dt(2026, 4, 1, 23, 0),
            minimum_hour='08:00',
        )

    def _create_raw_punches(self, in_time_value=time(9, 0), out_time_value=time(17, 0)):
        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 4, 1, in_time_value.hour, in_time_value.minute),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='BIO-1',
            device_info='Gate A',
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 4, 1, out_time_value.hour, out_time_value.minute),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='BIO-1',
            device_info='Gate A',
        )
        return in_punch, out_punch

    def test_approved_full_request_overrides_raw_and_revoke_restores_raw(self):
        in_punch, out_punch = self._create_raw_punches()
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        attendance = Attendance.objects.get(employee_id=self.employee, attendance_date=self.target_date)
        activity = AttendanceActivity.objects.get(employee_id=self.employee, attendance_date=self.target_date)
        self.assertEqual(attendance.attendance_clock_in, time(9, 0))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(activity.clock_in, time(9, 0))
        self.assertEqual(activity.clock_out, time(17, 0))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)

        request_obj = create_request(
            employee=self.employee,
            actor_user=self.owner_user,
            payload={
                'attendance_date': self.target_date.isoformat(),
                'scope': 'FULL',
                'reason': 'Correct biometric mismatch',
                'requested_check_in_date': self.target_date.isoformat(),
                'requested_check_in_time': '08:00',
                'requested_check_out_date': self.target_date.isoformat(),
                'requested_check_out_time': '16:00',
            },
            uploaded_files=[],
        )
        self.assertEqual(request_obj.status, AttendanceCorrectionRequestStatus.WAITING)

        with self.shift_ctx:
            request_obj = approve_request(request_obj=request_obj, actor_user=self.manager_user)

        attendance.refresh_from_db()
        activity.refresh_from_db()
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        request_obj.refresh_from_db()

        self.assertEqual(request_obj.status, AttendanceCorrectionRequestStatus.APPROVED)
        self.assertEqual(attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(attendance.attendance_clock_out, time(16, 0))
        self.assertEqual(activity.clock_in, time(8, 0))
        self.assertEqual(activity.clock_out, time(16, 0))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertIsNone(attendance.attendance_clock_in_punch_id)
        self.assertIsNone(attendance.attendance_clock_out_punch_id)
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)

        with self.shift_ctx:
            request_obj = revoke_request(request_obj=request_obj, actor_user=self.manager_user, reason='Manager revoked')

        attendance.refresh_from_db()
        activity.refresh_from_db()
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        request_obj.refresh_from_db()

        self.assertEqual(request_obj.status, AttendanceCorrectionRequestStatus.REVOKED)
        self.assertEqual(attendance.attendance_clock_in, time(9, 0))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(activity.clock_in, time(9, 0))
        self.assertEqual(activity.clock_out, time(17, 0))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendanceCorrectionRequest.objects.count(), 1)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
