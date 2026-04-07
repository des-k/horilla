from datetime import date, time

from django.test import Client, TestCase, override_settings

from attendance.models import AttendanceCorrectionRequest, AttendanceCorrectionRequestStatus
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


@override_settings(ALLOWED_HOSTS=['testserver', 'localhost', '127.0.0.1'])
class AttendanceCorrectionWebSmokeTests(AttendanceApiIntegrationMixin, TestCase):
    target_date = date(2026, 4, 3)

    def setUp(self):
        super().setUp()
        self.manager_user, self.manager_employee = self.create_employee('WebManager')
        self.owner_user, self.employee = self.create_employee('WebOwner', manager=self.manager_employee)
        self.client = Client()

    def test_request_pages_render_and_owner_can_cancel_waiting_request(self):
        request_obj = AttendanceCorrectionRequest.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            scope='FULL',
            requested_check_in_date=self.target_date,
            requested_check_in_time=time(8, 0),
            requested_check_out_date=self.target_date,
            requested_check_out_time=time(16, 0),
            reason='Web smoke',
            status=AttendanceCorrectionRequestStatus.WAITING,
        )
        self.client.force_login(self.owner_user)

        listing = self.client.get('/attendance/request-attendance-view/')
        self.assertEqual(listing.status_code, 200)
        self.assertContains(listing, 'Attendance Requests')
        self.assertContains(listing, 'Edit Request')
        self.assertNotContains(listing, 'title="View"')

        detail = self.client.get(f'/attendance/validate-attendance-request/{request_obj.id}/', HTTP_HX_REQUEST='true')
        self.assertEqual(detail.status_code, 200)
        self.assertContains(detail, 'Requested Value')

        cancel = self.client.get(f'/attendance/cancel-validate-attendance-request/{request_obj.id}/')
        self.assertEqual(cancel.status_code, 302)
        request_obj.refresh_from_db()
        self.assertEqual(request_obj.status, AttendanceCorrectionRequestStatus.CANCELED)

    def test_manager_approval_history_shows_revoke_for_approved_request_and_revoke_restores_raw(self):
        manager_user, manager_employee = self.create_employee('HistoryManager', permissions=['change_attendance'])
        owner_user, employee = self.create_employee('HistoryOwner', manager=manager_employee)
        target_date = date(2026, 4, 4)
        weekday_key = target_date.strftime('%A').lower()
        _, _, schedule = self.create_shift_with_schedule(
            employee=employee,
            day_key=weekday_key,
            start_time=time(8, 0),
            end_time=time(17, 0),
            minimum_working_hour='08:00',
            is_night_shift=False,
        )
        shift_ctx = self.patch_reconciliation_shift_rules(
            target_date=target_date,
            schedule=schedule,
            shift_start_dt=self.aware_dt(2026, 4, 4, 8, 0),
            shift_end_dt=self.aware_dt(2026, 4, 4, 17, 0),
            check_in_window_start_dt=self.aware_dt(2026, 4, 4, 6, 0),
            check_in_window_end_dt=self.aware_dt(2026, 4, 4, 12, 0),
            check_out_window_start_dt=self.aware_dt(2026, 4, 4, 12, 0),
            check_out_window_end_dt=self.aware_dt(2026, 4, 4, 23, 0),
            minimum_hour='08:00',
        )

        from attendance.models import Attendance, AttendanceActivity, AttendanceChannel, AttendancePunchDirection, AttendancePunchSource, AttendancePunchingHistory
        from attendance.services.attendance_correction_requests import approve_request, create_request
        from attendance.services.reconciliation import recompute_attendance

        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=employee,
            attendance_date=target_date,
            punch_timestamp=self.aware_dt(2026, 4, 4, 9, 0),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='BIO-2',
            device_info='Gate A',
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=employee,
            attendance_date=target_date,
            punch_timestamp=self.aware_dt(2026, 4, 4, 17, 0),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='BIO-2',
            device_info='Gate A',
        )

        with shift_ctx:
            recompute_attendance(employee, target_date)
            request_obj = create_request(
                employee=employee,
                actor_user=owner_user,
                payload={
                    'attendance_date': target_date.isoformat(),
                    'scope': 'FULL',
                    'reason': 'Need correction',
                    'requested_check_in_date': target_date.isoformat(),
                    'requested_check_in_time': '08:00',
                    'requested_check_out_date': target_date.isoformat(),
                    'requested_check_out_time': '16:00',
                },
                uploaded_files=[],
            )
            request_obj = approve_request(request_obj=request_obj, actor_user=manager_user)

        self.client.force_login(manager_user)
        listing = self.client.get('/attendance/request-attendance-view/?tab=approvals&approval_subtab=history')
        self.assertEqual(listing.status_code, 200)
        self.assertContains(listing, 'Revoke Approval')
        self.assertContains(listing, f'/attendance/revoke-validate-attendance-request/{request_obj.id}/')

        with shift_ctx:
            revoke = self.client.get(f'/attendance/revoke-validate-attendance-request/{request_obj.id}/')
        self.assertEqual(revoke.status_code, 302)

        request_obj.refresh_from_db()
        attendance = Attendance.objects.get(employee_id=employee, attendance_date=target_date)
        activity = AttendanceActivity.objects.get(employee_id=employee, attendance_date=target_date)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()

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

