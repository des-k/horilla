from datetime import date, time

from django.test import override_settings

from base.models import WorkType
from rest_framework.test import APITestCase

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceChannel,
    AttendanceCorrectionRequest,
    AttendanceCorrectionRequestStatus,
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchingHistory,
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestDocumentStatus,
    WorkModeRequestDocumentVersion,
    WorkModeRequestScope,
    WorkModeRequestStatus,
)
from attendance.services.reconciliation import (
    NOTE_ON_DUTY_FINAL,
    NOTE_ON_DUTY_NOT_GRANTED,
    NOTE_ON_DUTY_PROVISIONAL,
    SOURCE_NORMAL,
    SOURCE_ON_DUTY,
    SOURCE_PROVISIONAL_ON_DUTY,
    recompute_attendance,
)
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


@override_settings(ALLOWED_HOSTS=['testserver', 'localhost', '127.0.0.1'])
class RequestLifecycleFullChainEndpointTests(AttendanceApiIntegrationMixin, APITestCase):
    target_date = date(2026, 3, 21)

    def setUp(self):
        super().setUp()
        self.owner_user, self.employee = self.create_employee('LifecycleOwner')
        self.admin_user, self.admin_employee = self.create_employee('LifecycleAdmin', is_superuser=True)
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
            shift_start_dt=self.aware_dt(2026, 3, 21, 8, 0),
            shift_end_dt=self.aware_dt(2026, 3, 21, 17, 0),
            check_in_window_start_dt=self.aware_dt(2026, 3, 21, 6, 0),
            check_in_window_end_dt=self.aware_dt(2026, 3, 21, 12, 0),
            check_out_window_start_dt=self.aware_dt(2026, 3, 21, 12, 0),
            check_out_window_end_dt=self.aware_dt(2026, 3, 21, 23, 0),
            minimum_hour='08:00',
        )

    def tearDown(self):
        self._clear_request_context()
        super().tearDown()

    def _create_raw_punches(
        self,
        *,
        work_mode=AttendanceWorkMode.WFO,
        in_time_value=time(8, 0),
        out_time_value=time(17, 0),
        in_source=AttendancePunchSource.BIOMETRIC,
        out_source=AttendancePunchSource.BIOMETRIC,
    ):
        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 21, in_time_value.hour, in_time_value.minute),
            source=in_source,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='ENDPT-1',
            device_info='Gate A',
            work_mode=work_mode,
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 21, out_time_value.hour, out_time_value.minute),
            source=out_source,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='ENDPT-1',
            device_info='Gate A',
            work_mode=work_mode,
        )
        return in_punch, out_punch

    def _attendance(self):
        return Attendance.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _activity(self):
        return AttendanceActivity.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _attendance_activity_snapshot(self):
        attendance = self._attendance()
        activity = self._activity()
        return {
            'attendance': (
                attendance.request_type,
                attendance.attendance_clock_in,
                attendance.attendance_clock_out,
                attendance.attendance_clock_in_channel,
                attendance.attendance_clock_out_channel,
                attendance.attendance_clock_in_punch_id,
                attendance.attendance_clock_out_punch_id,
                attendance.attendance_clock_in_mode,
                attendance.attendance_clock_out_mode,
                attendance.late_minutes,
                attendance.early_out_minutes,
                attendance.reconciliation_source,
                attendance.reconciliation_note,
            ),
            'activity': (
                activity.clock_in,
                activity.clock_out,
                activity.clock_in_channel,
                activity.clock_out_channel,
                activity.clock_in_mode,
                activity.clock_out_mode,
                activity.late_minutes,
                activity.early_out_minutes,
                activity.work_mode_request_id_id,
            ),
            'counts': (
                Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(),
                AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(),
                AttendancePunchingHistory.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(),
            ),
        }

    @staticmethod
    def _punch_snapshot(*punches):
        snapshot = []
        for punch in punches:
            punch.refresh_from_db()
            snapshot.append(
                (
                    punch.id,
                    punch.accepted_to_attendance,
                    punch.reason,
                    punch.decision_status,
                    punch.decision_source,
                    punch.attendance_id_id,
                    punch.related_work_mode_request_id,
                )
            )
        return tuple(snapshot)

    def test_attendance_correction_approve_and_revoke_endpoints_update_final_truth_and_keep_raw_trail(self):
        in_punch, out_punch = self._create_raw_punches()
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        attendance = self._attendance()
        self.assertEqual(attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        request_obj = AttendanceCorrectionRequest.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            scope='FULL',
            requested_check_in_date=self.target_date,
            requested_check_in_time=time(8, 30),
            requested_check_out_date=self.target_date,
            requested_check_out_time=time(17, 30),
            reason='Adjust both punches',
            status=AttendanceCorrectionRequestStatus.WAITING,
        )

        with self.shift_ctx:
            response = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-approve/{request_obj.id}',
                {},
                format='json',
            )
        self.assertEqual(response.status_code, 200)

        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.attendance_clock_in, time(8, 30))
        self.assertEqual(attendance.attendance_clock_out, time(17, 30))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertIsNone(attendance.attendance_clock_in_punch_id)
        self.assertIsNone(attendance.attendance_clock_out_punch_id)
        self.assertEqual(activity.clock_in, time(8, 30))
        self.assertEqual(activity.clock_out, time(17, 30))
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)

        with self.shift_ctx:
            revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-revoke/{request_obj.id}',
                {'reason': 'Manager revoked correction'},
                format='json',
            )
        self.assertEqual(revoke.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertEqual(activity.clock_in, time(8, 0))
        self.assertEqual(activity.clock_out, time(17, 0))
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)

    def test_split_attendance_corrections_use_scheduled_work_mode_for_both_sessions(self):
        wfh = WorkType.objects.create(work_type='WFH')
        wfh.company_id.add(self.company)
        work_info = self.employee.employee_work_info
        work_info.work_type_id = wfh
        work_info.save(update_fields=['work_type_id'])

        request_in = AttendanceCorrectionRequest.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            scope='IN',
            requested_check_in_date=self.target_date,
            requested_check_in_time=time(8, 45),
            reason='Adjusted WFH check in',
            status=AttendanceCorrectionRequestStatus.WAITING,
        )
        request_out = AttendanceCorrectionRequest.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            scope='OUT',
            requested_check_out_date=self.target_date,
            requested_check_out_time=time(17, 15),
            reason='Adjusted WFH check out',
            status=AttendanceCorrectionRequestStatus.WAITING,
        )

        with self.shift_ctx:
            approve_in = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-approve/{request_in.id}',
                {},
                format='json',
            )
        self.assertEqual(approve_in.status_code, 200)

        with self.shift_ctx:
            approve_out = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-approve/{request_out.id}',
                {},
                format='json',
            )
        self.assertEqual(approve_out.status_code, 200)

        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.attendance_clock_in, time(8, 45))
        self.assertEqual(attendance.attendance_clock_out, time(17, 15))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFH)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFH)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.WFH)
        self.assertEqual(activity.clock_out_mode, AttendanceWorkMode.WFH)

    def test_attendance_correction_revoke_twice_is_blocked_or_idempotent_without_data_corruption(self):
        in_punch, out_punch = self._create_raw_punches()
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        request_obj = AttendanceCorrectionRequest.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            scope='FULL',
            requested_check_in_date=self.target_date,
            requested_check_in_time=time(8, 30),
            requested_check_out_date=self.target_date,
            requested_check_out_time=time(17, 30),
            reason='Adjust both punches',
            status=AttendanceCorrectionRequestStatus.WAITING,
        )

        with self.shift_ctx:
            approve = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-approve/{request_obj.id}',
                {},
                format='json',
            )
        self.assertEqual(approve.status_code, 200)

        with self.shift_ctx:
            first_revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-revoke/{request_obj.id}',
                {'reason': 'Manager revoked correction'},
                format='json',
            )
        self.assertEqual(first_revoke.status_code, 200)
        baseline_snapshot = self._attendance_activity_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.shift_ctx:
            second_revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/attendance-request-revoke/{request_obj.id}',
                {},
                format='json',
            )
        self.assertEqual(second_revoke.status_code, 403)
        self.assertEqual(self._attendance_activity_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)
        attendance = self._attendance()
        request_obj.refresh_from_db()
        self.assertEqual(request_obj.status, AttendanceCorrectionRequestStatus.REVOKED)

    def test_work_mode_approve_and_revoke_endpoints_update_modes_without_orphaning_raw_trail(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.WFA,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            reason='Remote work approved by manager',
        )

        with self.shift_ctx:
            approve = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-approve/{request.id}',
                {},
                format='json',
            )
        self.assertEqual(approve.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFA)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFA)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.WFA)
        self.assertEqual(activity.clock_out_mode, AttendanceWorkMode.WFA)
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)

        with self.shift_ctx:
            revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-revoke/{request.id}',
                {'remark': 'Remote day revoked'},
                format='json',
            )
        self.assertEqual(revoke.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFO)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)

    def test_wfh_work_mode_approve_and_revoke_endpoints_update_modes_without_orphaning_raw_trail(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.WFH,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            reason='WFH approved by manager',
        )

        with self.shift_ctx:
            approve = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-approve/{request.id}',
                {},
                format='json',
            )
        self.assertEqual(approve.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFH)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFH)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.WFH)
        self.assertEqual(activity.clock_out_mode, AttendanceWorkMode.WFH)

        with self.shift_ctx:
            revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-revoke/{request.id}',
                {'remark': 'WFH day revoked'},
                format='json',
            )
        self.assertEqual(revoke.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFO)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_out_mode, AttendanceWorkMode.WFO)

    def test_work_mode_reject_after_final_state_is_cleanly_blocked(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.WFA,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            reason='Remote work approved by manager',
        )

        with self.shift_ctx:
            approve = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-approve/{request.id}',
                {},
                format='json',
            )
        self.assertEqual(approve.status_code, 200)

        baseline_snapshot = self._attendance_activity_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.shift_ctx:
            reject = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-reject/{request.id}',
                {'reason': 'too late to reject'},
                format='json',
            )
        self.assertEqual(reject.status_code, 400)
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.APPROVED)
        self.assertEqual(self._attendance_activity_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)

    def test_on_duty_document_verify_and_revoke_endpoints_keep_first_in_last_out_truth(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
            document_status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
            submitted_by=self.employee,
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        attendance = self._attendance()
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(attendance.late_minutes, 20)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.reconciliation_source, SOURCE_PROVISIONAL_ON_DUTY)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_PROVISIONAL)

        with self.shift_ctx:
            verify = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/verify',
                {'reason': 'verified'},
                format='json',
            )
        self.assertEqual(verify.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        request.refresh_from_db()
        self.assertEqual(request.document_status, WorkModeRequestDocumentStatus.VERIFIED)
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(attendance.late_minutes, 0)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(attendance.reconciliation_source, SOURCE_ON_DUTY)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_FINAL)
        self.assertEqual(activity.clock_in, time(8, 20))
        self.assertEqual(activity.clock_out, time(16, 40))
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

        with self.shift_ctx:
            revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/revoke',
                {'remark': 'Trip ended'},
                format='json',
            )
        self.assertEqual(revoke.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(attendance.late_minutes, 20)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFO)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_in, time(8, 20))
        self.assertEqual(activity.clock_out, time(16, 40))
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

    def test_on_duty_document_reject_endpoint_keeps_first_in_last_out_truth_under_normal_rules(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
            document_status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
            submitted_by=self.employee,
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self.shift_ctx:
            reject = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/reject-document',
                {'reason': 'proof rejected'},
                format='json',
            )
        self.assertEqual(reject.status_code, 200)
        attendance = self._attendance()
        activity = self._activity()
        request.refresh_from_db()
        self.assertEqual(request.document_status, WorkModeRequestDocumentStatus.REJECTED)
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(attendance.late_minutes, 20)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_NOT_GRANTED)
        self.assertEqual(activity.clock_in, time(8, 20))
        self.assertEqual(activity.clock_out, time(16, 40))
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)


    def test_work_mode_reopen_after_verified_status_follows_supported_transition_only(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
            document_status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
            submitted_by=self.employee,
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        with self.shift_ctx:
            verify = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/verify',
                {'reason': 'verified'},
                format='json',
            )
        self.assertEqual(verify.status_code, 200)

        with self.shift_ctx:
            reopen = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/reopen-document',
                {'remark': 'review again'},
                format='json',
            )
        self.assertEqual(reopen.status_code, 200)
        request.refresh_from_db()
        self.assertEqual(request.document_status, WorkModeRequestDocumentStatus.PENDING_VERIFICATION)
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(attendance.late_minutes, 20)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.reconciliation_source, SOURCE_PROVISIONAL_ON_DUTY)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_PROVISIONAL)
        self.assertEqual(activity.clock_in, time(8, 20))
        self.assertEqual(activity.clock_out, time(16, 40))
        baseline_snapshot = self._attendance_activity_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.shift_ctx:
            second_reopen = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/reopen-document',
                {'remark': 'still review again'},
                format='json',
            )
        self.assertEqual(second_reopen.status_code, 400)
        request.refresh_from_db()
        self.assertEqual(request.document_status, WorkModeRequestDocumentStatus.PENDING_VERIFICATION)
        self.assertEqual(self._attendance_activity_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)


    def test_invalid_transition_after_mixed_source_finalization_keeps_reconciliation_and_raw_visibility_unchanged(self):
        in_punch, out_punch = self._create_raw_punches(
            work_mode=AttendanceWorkMode.WFO,
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_source=AttendancePunchSource.BIOMETRIC,
            out_source=AttendancePunchSource.MOBILE,
        )
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Mixed-source client visit',
            document_status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
            submitted_by=self.employee,
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        with self.shift_ctx:
            verify = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/verify',
                {'reason': 'verified'},
                format='json',
            )
        self.assertEqual(verify.status_code, 200)
        attendance = self._attendance()
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.MOBILE)

        with self.shift_ctx:
            revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/revoke',
                {'remark': 'trip ended'},
                format='json',
            )
        self.assertEqual(revoke.status_code, 200)
        baseline_snapshot = self._attendance_activity_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.shift_ctx:
            invalid_verify = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/verify',
                {'reason': 'should fail'},
                format='json',
            )
        self.assertEqual(invalid_verify.status_code, 400)
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(self._attendance_activity_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)
        attendance = self._attendance()
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.MOBILE)

    def test_invalid_transition_never_changes_raw_trail_visibility(self):
        in_punch, out_punch = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO, in_time_value=time(8, 20), out_time_value=time(16, 40))
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
            document_status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.PENDING_VERIFICATION,
            submitted_by=self.employee,
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self.shift_ctx:
            recompute_attendance(self.employee, self.target_date)

        with self.shift_ctx:
            verify = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/verify',
                {'reason': 'verified'},
                format='json',
            )
        self.assertEqual(verify.status_code, 200)

        with self.shift_ctx:
            revoke = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/revoke',
                {'remark': 'trip ended'},
                format='json',
            )
        self.assertEqual(revoke.status_code, 200)
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        baseline_snapshot = self._attendance_activity_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.shift_ctx:
            invalid_verify = self.auth_client(self.admin_user).put(
                f'/api/attendance/work-mode-request-action/{request.id}/verify',
                {'reason': 'should fail'},
                format='json',
            )
        self.assertEqual(invalid_verify.status_code, 400)
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(self._attendance_activity_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)

