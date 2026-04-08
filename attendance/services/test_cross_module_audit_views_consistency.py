from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.core.exceptions import ValidationError
from django.test import SimpleTestCase, TestCase

from attendance.models import (
    Attendance,
    AttendanceChannel,
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
from attendance.services import activity_sync
from attendance.services.activity_sync import sync_single_session_activity
from attendance.services.punching_history import capture_request_restore_snapshot, clear_raw_links_for_request_override, restore_raw_state_after_request
from attendance.services.attendance_correction_requests import approve_request, create_request, revoke_request
from attendance.services.reconciliation import (
    NOTE_ON_DUTY_FINAL,
    NOTE_ON_DUTY_NOT_GRANTED,
    NOTE_ON_DUTY_PROVISIONAL,
    NOTE_SUPERSEDED_CHECKOUT,
    SOURCE_NORMAL,
    SOURCE_ON_DUTY,
    SOURCE_PROVISIONAL_ON_DUTY,
    recompute_attendance,
)
from attendance.services.work_type_request_actions import WorkModeRequestActions
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from leave.models import LeaveRequest, LeaveType


class _FakeAttendance(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None


class _FakeActivity(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None


class CrossModuleAuditViewsConsistencyTests(SimpleTestCase):
    def setUp(self):
        self.employee = SimpleNamespace(id=55)
        self.in_punch = SimpleNamespace(id=201, source="biometric", accepted_to_attendance=True)
        self.out_punch = SimpleNamespace(id=202, source="biometric", accepted_to_attendance=True)
        self.attendance = _FakeAttendance(
            employee_id=self.employee,
            attendance_date=date(2026, 3, 14),
            attendance_clock_in_date=date(2026, 3, 14),
            attendance_clock_in=time(8, 0),
            attendance_clock_out_date=date(2026, 3, 14),
            attendance_clock_out=time(17, 0),
            attendance_clock_in_channel="biometric",
            attendance_clock_out_channel="biometric",
            attendance_clock_in_punch_id=self.in_punch.id,
            attendance_clock_out_punch_id=self.out_punch.id,
            attendance_clock_in_image=None,
            attendance_clock_out_image=None,
            attendance_clock_in_mode="wfo",
            attendance_clock_out_mode="wfo",
            attendance_clock_in_location=None,
            attendance_clock_out_location=None,
            work_mode_request_id=None,
            request_restore_snapshot=None,
        )

    def test_attendance_activity_and_punch_history_stay_consistent_after_correction_approve(self):
        self.attendance.attendance_clock_in = time(8, 30)
        self.attendance.attendance_clock_out = time(17, 30)
        self.attendance.attendance_clock_in_channel = "request"
        self.attendance.attendance_clock_out_channel = "request"
        clear_raw_links_for_request_override(self.attendance, include_in=True, include_out=True)

        activity = _FakeActivity()
        with patch.object(activity_sync, "_locked_activity", return_value=activity), \
             patch.object(activity_sync.EmployeeShiftDay.objects, "filter") as day_filter:
            day_filter.return_value.first.return_value = None
            synced = activity_sync.sync_single_session_activity(self.attendance)

        self.assertEqual(synced.clock_in, time(8, 30))
        self.assertEqual(synced.clock_out, time(17, 30))
        self.assertEqual(synced.clock_in_channel, "request")
        self.assertEqual(synced.clock_out_channel, "request")
        self.assertIsNone(self.attendance.attendance_clock_in_punch_id)
        self.assertIsNone(self.attendance.attendance_clock_out_punch_id)
        self.assertTrue(self.in_punch.accepted_to_attendance)
        self.assertTrue(self.out_punch.accepted_to_attendance)

    def test_attendance_activity_and_punch_history_stay_consistent_after_correction_revoke(self):
        capture_request_restore_snapshot(self.attendance, include_in=True, include_out=True)
        self.attendance.attendance_clock_in = time(8, 45)
        self.attendance.attendance_clock_out = time(17, 45)
        self.attendance.attendance_clock_in_channel = "request"
        self.attendance.attendance_clock_out_channel = "request"
        clear_raw_links_for_request_override(self.attendance, include_in=True, include_out=True)

        def _relink(attendance, *, include_in=False, include_out=False):
            if include_in:
                attendance.attendance_clock_in_punch_id = self.in_punch.id
            if include_out:
                attendance.attendance_clock_out_punch_id = self.out_punch.id
            return attendance

        with patch("attendance.services.punching_history.relink_attendance_to_raw_punches", side_effect=_relink):
            restore_raw_state_after_request(self.attendance, include_in=True, include_out=True)

        activity = _FakeActivity()
        with patch.object(activity_sync, "_locked_activity", return_value=activity), \
             patch.object(activity_sync.EmployeeShiftDay.objects, "filter") as day_filter:
            day_filter.return_value.first.return_value = None
            synced = activity_sync.sync_single_session_activity(self.attendance)

        self.assertEqual(self.attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(self.attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(self.attendance.attendance_clock_in_punch_id, self.in_punch.id)
        self.assertEqual(self.attendance.attendance_clock_out_punch_id, self.out_punch.id)
        self.assertEqual(synced.clock_in, time(8, 0))
        self.assertEqual(synced.clock_out, time(17, 0))


class CrossModuleAuditViewsConsistencyDbIntegrationTests(AttendanceApiIntegrationMixin, TestCase):
    target_date = date(2026, 3, 17)

    def setUp(self):
        super().setUp()
        self.user, self.employee = self.create_employee('AuditTrail')
        self.auth_request(self.user)
        weekday_key = self.target_date.strftime('%A').lower()
        self.shift, self.day_obj, self.schedule = self.create_shift_with_schedule(
            employee=self.employee,
            day_key=weekday_key,
            start_time=time(8, 0),
            end_time=time(17, 0),
            minimum_working_hour='08:00',
            is_night_shift=False,
        )
        self.shift_start_dt = self.aware_dt(2026, 3, 17, 8, 0)
        self.shift_end_dt = self.aware_dt(2026, 3, 17, 17, 0)
        self.in_window_start_dt = self.aware_dt(2026, 3, 17, 6, 0)
        self.in_window_end_dt = self.aware_dt(2026, 3, 17, 12, 0)
        self.out_window_start_dt = self.aware_dt(2026, 3, 17, 12, 0)
        self.out_window_end_dt = self.aware_dt(2026, 3, 17, 23, 0)

    def tearDown(self):
        self._clear_request_context()
        super().tearDown()

    def _shift_rule_context(self):
        return self.patch_reconciliation_shift_rules(
            target_date=self.target_date,
            schedule=self.schedule,
            shift_start_dt=self.shift_start_dt,
            shift_end_dt=self.shift_end_dt,
            check_in_window_start_dt=self.in_window_start_dt,
            check_in_window_end_dt=self.in_window_end_dt,
            check_out_window_start_dt=self.out_window_start_dt,
            check_out_window_end_dt=self.out_window_end_dt,
            minimum_hour='08:00',
        )

    def _create_raw_punches(
        self,
        *,
        in_time_value=time(8, 0),
        out_time_value=time(17, 0),
        in_source=AttendancePunchSource.BIOMETRIC,
        out_source=AttendancePunchSource.BIOMETRIC,
        work_mode=None,
    ):
        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 17, in_time_value.hour, in_time_value.minute),
            source=in_source,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='AUD-1',
            device_info='Main Gate',
            work_mode=work_mode,
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 17, out_time_value.hour, out_time_value.minute),
            source=out_source,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='AUD-1',
            device_info='Main Gate',
            work_mode=work_mode,
        )
        return in_punch, out_punch

    def _attendance(self):
        return Attendance.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _activity(self):
        return activity_sync.AttendanceActivity.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _layer_snapshot(self):
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
                activity_sync.AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(),
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

    def _assert_layers(self, *, in_time_value, out_time_value, in_channel, out_channel, in_punch_id, out_punch_id, late_minutes=None, early_minutes=None, in_mode=None, out_mode=None):
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(activity_sync.AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)

        self.assertEqual(attendance.attendance_clock_in, in_time_value)
        self.assertEqual(attendance.attendance_clock_out, out_time_value)
        self.assertEqual(attendance.attendance_clock_in_channel, in_channel)
        self.assertEqual(attendance.attendance_clock_out_channel, out_channel)
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch_id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch_id)
        self.assertEqual(activity.clock_in, in_time_value)
        self.assertEqual(activity.clock_out, out_time_value)
        self.assertEqual(activity.clock_in_channel, in_channel)
        self.assertEqual(activity.clock_out_channel, out_channel)
        if late_minutes is not None:
            self.assertEqual(attendance.late_minutes, late_minutes)
            self.assertEqual(activity.late_minutes, late_minutes)
        if early_minutes is not None:
            self.assertEqual(attendance.early_out_minutes, early_minutes)
            self.assertEqual(activity.early_out_minutes, early_minutes)
        if in_mode is not None:
            self.assertEqual(attendance.attendance_clock_in_mode, in_mode)
            self.assertEqual(activity.clock_in_mode, in_mode)
        if out_mode is not None:
            self.assertEqual(attendance.attendance_clock_out_mode, out_mode)
            self.assertEqual(activity.clock_out_mode, out_mode)
        return attendance, activity

    def test_correction_approve_and_revoke_keep_attendance_activity_and_punch_history_consistent(self):
        in_punch, out_punch = self._create_raw_punches()
        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance = self._attendance()
        request_obj = create_request(
            employee=self.employee,
            actor_user=self.user,
            payload={
                'attendance_date': self.target_date.isoformat(),
                'scope': 'FULL',
                'reason': 'Correct both sessions',
                'requested_check_in_date': self.target_date.isoformat(),
                'requested_check_in_time': '08:30',
                'requested_check_out_date': self.target_date.isoformat(),
                'requested_check_out_time': '17:30',
            },
            uploaded_files=[],
        )

        with self._shift_rule_context():
            approve_request(request_obj=request_obj, actor_user=self.user)

        attendance, _ = self._assert_layers(
            in_time_value=time(8, 30),
            out_time_value=time(17, 30),
            in_channel=AttendanceChannel.CORRECTION_REQUEST,
            out_channel=AttendanceChannel.CORRECTION_REQUEST,
            in_punch_id=None,
            out_punch_id=None,
        )
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)
        self.assertEqual(in_punch.attendance_id_id, attendance.id)
        self.assertEqual(out_punch.attendance_id_id, attendance.id)

        with self._shift_rule_context():
            revoke_request(request_obj=request_obj, actor_user=self.user, reason='Manager revoked correction')

        self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 0),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
        )
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(in_punch.attendance_id_id, self._attendance().id)
        self.assertEqual(out_punch.attendance_id_id, self._attendance().id)

    def test_leave_cancel_recompute_restores_raw_truth_without_losing_raw_audit_trail(self):
        in_punch, out_punch = self._create_raw_punches()
        leave_type = LeaveType.objects.create(name='Annual Leave', company_id=self.company)
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown='full_day',
            end_date_breakdown='full_day',
            description='Full day leave',
            status='approved',
        )

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance = self._attendance()
        activity = self._activity()
        self.assertIsNone(attendance.attendance_clock_in)
        self.assertIsNone(attendance.attendance_clock_out)
        self.assertEqual(attendance.reconciliation_note, 'Approved Full-Day Leave')
        self.assertIsNone(activity.clock_in)
        self.assertIsNone(activity.clock_out)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)

        leave_request.status = 'cancelled'
        leave_request.save(update_fields=['status'])
        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 0),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
        )
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)


    def test_leave_reject_recompute_restores_raw_truth_without_losing_raw_audit_trail(self):
        in_punch, out_punch = self._create_raw_punches()
        leave_type = LeaveType.objects.create(name='Sick Leave', company_id=self.company)
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown='full_day',
            end_date_breakdown='full_day',
            description='Medical leave',
            status='approved',
        )

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance = self._attendance()
        activity = self._activity()
        self.assertIsNone(attendance.attendance_clock_in)
        self.assertIsNone(attendance.attendance_clock_out)
        self.assertEqual(attendance.reconciliation_note, 'Approved Full-Day Leave')
        self.assertIsNone(activity.clock_in)
        self.assertIsNone(activity.clock_out)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)

        leave_request.status = 'rejected'
        leave_request.reject_reason = 'Manager rejected retroactive leave'
        leave_request.save(update_fields=['status', 'reject_reason'])
        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 0),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
        )
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)

    def test_work_mode_request_approve_keeps_final_truth_activity_and_raw_trail_consistent(self):
        in_punch, out_punch = self._create_raw_punches(in_time_value=time(8, 20), out_time_value=time(16, 40), work_mode=AttendanceWorkMode.WFO)
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Business trip',
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.VERIFIED,
            submitted_by=self.employee,
            reviewed_by=self.employee,
            review_remark='Verified',
        )
        request.current_document_version = version
        request.document_status = WorkModeRequestDocumentStatus.VERIFIED
        request.save(update_fields=['current_document_version', 'document_status'])

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance, activity = self._assert_layers(
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
            late_minutes=0,
            early_minutes=0,
            in_mode=AttendanceWorkMode.ON_DUTY,
            out_mode=AttendanceWorkMode.ON_DUTY,
        )
        self.assertEqual(attendance.reconciliation_note, 'On Duty Final')
        self.assertEqual(attendance.reconciliation_source, 'On Duty')
        self.assertEqual(activity.work_mode_request_id_id, request.id)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)



    def test_biometric_in_mobile_out_then_leave_cancel_keeps_activity_and_raw_history_consistent(self):
        in_punch, out_punch = self._create_raw_punches(
            in_source=AttendancePunchSource.BIOMETRIC,
            out_source=AttendancePunchSource.MOBILE,
            out_time_value=time(17, 10),
        )
        leave_type = LeaveType.objects.create(name='Mixed Source Leave', company_id=self.company)
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown='full_day',
            end_date_breakdown='full_day',
            description='Approved mixed-source leave',
            status='approved',
        )

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance = self._attendance()
        activity = self._activity()
        self.assertIsNone(attendance.attendance_clock_in)
        self.assertIsNone(attendance.attendance_clock_out)
        self.assertIsNone(activity.clock_in)
        self.assertIsNone(activity.clock_out)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 2)

        leave_request.status = 'cancelled'
        leave_request.save(update_fields=['status'])
        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance, activity = self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 10),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.MOBILE,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
        )
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertNotEqual(attendance.reconciliation_note, 'Approved Full-Day Leave')
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(in_punch.attendance_id_id, attendance.id)
        self.assertEqual(out_punch.attendance_id_id, attendance.id)

    def test_biometric_in_generated_out_then_revoke_restores_machine_truth_without_hiding_raw_rows(self):
        in_punch, early_out_punch = self._create_raw_punches(
            in_source=AttendancePunchSource.BIOMETRIC,
            out_source=AttendancePunchSource.BIOMETRIC,
            out_time_value=time(16, 50),
        )
        latest_out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 17, 17, 20),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='AUD-1',
            device_info='Mobile App',
            work_mode=AttendanceWorkMode.WFO,
        )

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        baseline_attendance = self._attendance()
        self.assertEqual(baseline_attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(baseline_attendance.attendance_clock_out, time(17, 20))
        self.assertEqual(baseline_attendance.attendance_clock_out_channel, AttendanceChannel.MOBILE)

        request_obj = create_request(
            employee=self.employee,
            actor_user=self.user,
            payload={
                'attendance_date': self.target_date.isoformat(),
                'scope': 'OUT',
                'reason': 'Correct generated checkout',
                'requested_check_out_date': self.target_date.isoformat(),
                'requested_check_out_time': '17:45',
            },
            uploaded_files=[],
        )

        with self._shift_rule_context():
            approve_request(request_obj=request_obj, actor_user=self.user)

        overridden = self._attendance()
        self.assertEqual(overridden.attendance_clock_out, time(17, 45))
        self.assertEqual(overridden.attendance_clock_out_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertIsNone(overridden.attendance_clock_out_punch_id)
        early_out_punch.refresh_from_db()
        latest_out_punch.refresh_from_db()
        self.assertFalse(early_out_punch.accepted_to_attendance)
        self.assertFalse(latest_out_punch.accepted_to_attendance)

        with self._shift_rule_context():
            revoke_request(request_obj=request_obj, actor_user=self.user, reason='Manager revoked correction')

        attendance, activity = self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 20),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.MOBILE,
            in_punch_id=in_punch.id,
            out_punch_id=latest_out_punch.id,
        )
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 3)
        in_punch.refresh_from_db()
        early_out_punch.refresh_from_db()
        latest_out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertFalse(early_out_punch.accepted_to_attendance)
        self.assertEqual(early_out_punch.reason, NOTE_SUPERSEDED_CHECKOUT)
        self.assertTrue(latest_out_punch.accepted_to_attendance)
        self.assertEqual(latest_out_punch.attendance_id_id, attendance.id)
        self.assertEqual(activity.clock_out_channel, AttendanceChannel.MOBILE)

    def test_mixed_out_candidates_after_reversal_keep_only_one_final_accepted_out(self):
        in_punch, first_out_punch = self._create_raw_punches(
            in_source=AttendancePunchSource.BIOMETRIC,
            out_source=AttendancePunchSource.BIOMETRIC,
            out_time_value=time(16, 35),
        )
        middle_out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 17, 17, 5),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='AUD-1',
            device_info='Mobile App',
            work_mode=AttendanceWorkMode.WFO,
        )
        final_out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(2026, 3, 17, 17, 25),
            source=AttendancePunchSource.API,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='AUD-1',
            device_info='API Import',
            work_mode=AttendanceWorkMode.WFO,
        )
        leave_type = LeaveType.objects.create(name='Mixed Reverse Leave', company_id=self.company)
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown='full_day',
            end_date_breakdown='full_day',
            description='Temporary full day leave',
            status='approved',
        )

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        leave_request.status = 'cancelled'
        leave_request.save(update_fields=['status'])
        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        attendance, activity = self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 25),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.API,
            in_punch_id=in_punch.id,
            out_punch_id=final_out_punch.id,
        )
        first_out_punch.refresh_from_db()
        middle_out_punch.refresh_from_db()
        final_out_punch.refresh_from_db()
        self.assertFalse(first_out_punch.accepted_to_attendance)
        self.assertFalse(middle_out_punch.accepted_to_attendance)
        self.assertTrue(final_out_punch.accepted_to_attendance)
        self.assertEqual(first_out_punch.reason, NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(middle_out_punch.reason, NOTE_SUPERSEDED_CHECKOUT)
        self.assertEqual(final_out_punch.attendance_id_id, attendance.id)
        self.assertEqual(activity.clock_out_channel, AttendanceChannel.API)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(activity_sync.AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 4)

    def test_work_mode_reject_and_cancel_keep_raw_truth_consistent_for_waiting_requests(self):
        # Waiting requests do not become active truth, so reject/cancel must leave
        # Attendance, AttendanceActivity, and raw punches unchanged.
        reject_in, reject_out = self._create_raw_punches(work_mode=AttendanceWorkMode.WFO)
        reject_request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.WFA,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            reason='WFH waiting approval',
        )
        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        WorkModeRequestActions.reject_request(reject_request, actor=self.employee, remark='Manager denied')

        self._assert_layers(
            in_time_value=time(8, 0),
            out_time_value=time(17, 0),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=reject_in.id,
            out_punch_id=reject_out.id,
            in_mode=AttendanceWorkMode.WFO,
            out_mode=AttendanceWorkMode.WFO,
        )
        reject_in.refresh_from_db()
        reject_out.refresh_from_db()
        self.assertEqual(
            set(AttendancePunchingHistory.objects.filter(employee_id=self.employee, id__in=[reject_in.id, reject_out.id]).values_list('id', flat=True)),
            {reject_in.id, reject_out.id},
        )
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(activity_sync.AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        reject_request.refresh_from_db()
        self.assertEqual(reject_request.status, WorkModeRequestStatus.REJECTED)

        later_date = date(2026, 3, 18)
        later_weekday_key = later_date.strftime('%A').lower()
        _, _, later_schedule = self.create_shift_with_schedule(
            employee=self.employee,
            day_key=later_weekday_key,
            start_time=time(8, 0),
            end_time=time(17, 0),
            minimum_working_hour='08:00',
            is_night_shift=False,
        )
        cancel_in = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=later_date,
            punch_timestamp=self.aware_dt(2026, 3, 18, 8, 0),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='AUD-1',
            device_info='Main Gate',
            work_mode=AttendanceWorkMode.WFO,
        )
        cancel_out = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=later_date,
            punch_timestamp=self.aware_dt(2026, 3, 18, 17, 0),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='AUD-1',
            device_info='Main Gate',
            work_mode=AttendanceWorkMode.WFO,
        )
        cancel_request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.WFA,
            scope=WorkModeRequestScope.FULL,
            start_date=later_date,
            end_date=later_date,
            status=WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            reason='Owner canceled waiting request',
        )
        shift_ctx = self.patch_reconciliation_shift_rules(
            target_date=later_date,
            schedule=self.schedule,
            shift_start_dt=self.aware_dt(2026, 3, 18, 8, 0),
            shift_end_dt=self.aware_dt(2026, 3, 18, 17, 0),
            check_in_window_start_dt=self.aware_dt(2026, 3, 18, 6, 0),
            check_in_window_end_dt=self.aware_dt(2026, 3, 18, 12, 0),
            check_out_window_start_dt=self.aware_dt(2026, 3, 18, 12, 0),
            check_out_window_end_dt=self.aware_dt(2026, 3, 18, 23, 0),
            minimum_hour='08:00',
        )
        with shift_ctx:
            recompute_attendance(self.employee, later_date)

        WorkModeRequestActions.cancel_request(cancel_request, actor=self.employee, remark='Owner canceled')

        later_attendance = Attendance.objects.get(employee_id=self.employee, attendance_date=later_date)
        later_activity = activity_sync.AttendanceActivity.objects.get(employee_id=self.employee, attendance_date=later_date)
        self.assertEqual(later_attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(later_attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(later_attendance.attendance_clock_in_mode, AttendanceWorkMode.WFO)
        self.assertEqual(later_attendance.attendance_clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(later_attendance.attendance_clock_in_punch_id, cancel_in.id)
        self.assertEqual(later_attendance.attendance_clock_out_punch_id, cancel_out.id)
        self.assertEqual(later_activity.clock_in, time(8, 0))
        self.assertEqual(later_activity.clock_out, time(17, 0))
        cancel_in.refresh_from_db()
        cancel_out.refresh_from_db()
        self.assertTrue(cancel_in.accepted_to_attendance)
        self.assertEqual(
            set(AttendancePunchingHistory.objects.filter(employee_id=self.employee, id__in=[cancel_in.id, cancel_out.id]).values_list("id", flat=True)),
            {cancel_in.id, cancel_out.id},
        )
        cancel_request.refresh_from_db()
        self.assertEqual(cancel_request.status, WorkModeRequestStatus.CANCELED)

    def test_work_mode_document_reject_reopen_and_revoke_keep_audit_views_consistent(self):
        in_punch, out_punch = self._create_raw_punches(in_time_value=time(8, 20), out_time_value=time(16, 40), work_mode=AttendanceWorkMode.WFO)
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.VERIFIED,
            submitted_by=self.employee,
            reviewed_by=self.employee,
            review_remark='Verified',
        )
        request.current_document_version = version
        request.document_status = WorkModeRequestDocumentStatus.VERIFIED
        request.save(update_fields=['current_document_version', 'document_status'])

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        self._assert_layers(
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
            late_minutes=0,
            early_minutes=0,
            in_mode=AttendanceWorkMode.ON_DUTY,
            out_mode=AttendanceWorkMode.ON_DUTY,
        )
        attendance = self._attendance()
        self.assertEqual(attendance.reconciliation_source, SOURCE_ON_DUTY)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_FINAL)

        WorkModeRequestActions.reject_document(request, actor=self.employee, remark='Need clearer proof')
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(activity_sync.AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(activity.clock_in, time(8, 20))
        self.assertEqual(activity.clock_out, time(16, 40))
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(attendance.late_minutes, 20)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_NOT_GRANTED)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee, id__in=[in_punch.id, out_punch.id]).count(), 2)
        request.refresh_from_db()
        self.assertEqual(request.document_status, WorkModeRequestDocumentStatus.REJECTED)

        WorkModeRequestActions.reopen_document(request, actor=self.employee, remark='Please review again')
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(activity_sync.AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(attendance.attendance_clock_in, time(8, 20))
        self.assertEqual(attendance.attendance_clock_out, time(16, 40))
        self.assertEqual(activity.clock_in, time(8, 20))
        self.assertEqual(activity.clock_out, time(16, 40))
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(activity.clock_in_mode, AttendanceWorkMode.ON_DUTY)
        self.assertEqual(attendance.late_minutes, 20)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_PROVISIONAL)
        self.assertEqual(attendance.reconciliation_source, SOURCE_PROVISIONAL_ON_DUTY)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee, id__in=[in_punch.id, out_punch.id]).count(), 2)
        request.refresh_from_db()
        self.assertEqual(request.document_status, WorkModeRequestDocumentStatus.PENDING_VERIFICATION)

        WorkModeRequestActions.verify_document(request, actor=self.employee, remark='Verified again')
        self._assert_layers(
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
            late_minutes=0,
            early_minutes=0,
            in_mode=AttendanceWorkMode.ON_DUTY,
            out_mode=AttendanceWorkMode.ON_DUTY,
        )
        attendance = self._attendance()
        self.assertEqual(attendance.reconciliation_source, SOURCE_ON_DUTY)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_FINAL)

        WorkModeRequestActions.revoke_request(request, actor=self.employee, remark='Trip ended')
        self._assert_layers(
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
            in_mode=AttendanceWorkMode.WFO,
            out_mode=AttendanceWorkMode.WFO,
        )
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)


    def test_repeated_revoke_does_not_duplicate_activity_or_punch_decisions(self):
        in_punch, out_punch = self._create_raw_punches(in_time_value=time(8, 20), out_time_value=time(16, 40), work_mode=AttendanceWorkMode.WFO)
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
            document_status=WorkModeRequestDocumentStatus.VERIFIED,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.VERIFIED,
            submitted_by=self.employee,
            reviewed_by=self.employee,
            review_remark='Verified',
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        WorkModeRequestActions.revoke_request(request, actor=self.employee, remark='Trip ended')
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        baseline_snapshot = self._layer_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.assertRaises(ValidationError):
            WorkModeRequestActions.revoke_request(request, actor=self.employee, remark='Trip ended twice')

        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(self._layer_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)

    def test_invalid_work_mode_transition_keeps_attendance_activity_and_history_unchanged(self):
        in_punch, out_punch = self._create_raw_punches(in_time_value=time(8, 20), out_time_value=time(16, 40), work_mode=AttendanceWorkMode.WFO)
        admin_user, admin_employee = self.create_employee('AuditApprover', is_superuser=True)
        request_ctx = SimpleNamespace(user=admin_user)
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

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        WorkModeRequestActions.verify_document(request, actor=admin_employee, request=request_ctx, remark='Verified once')
        WorkModeRequestActions.revoke_request(request, actor=admin_employee, request=request_ctx, remark='Trip ended')
        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        baseline_snapshot = self._layer_snapshot()
        baseline_punch_snapshot = self._punch_snapshot(in_punch, out_punch)

        with self.assertRaises(ValidationError):
            WorkModeRequestActions.verify_document(request, actor=admin_employee, request=request_ctx, remark='Should not verify revoked request')

        request.refresh_from_db()
        self.assertEqual(request.status, WorkModeRequestStatus.REVOKED)
        self.assertEqual(self._layer_snapshot(), baseline_snapshot)
        self.assertEqual(self._punch_snapshot(in_punch, out_punch), baseline_punch_snapshot)

    def test_on_duty_pending_verification_uses_raw_truth_but_keeps_normal_rules(self):
        in_punch, out_punch = self._create_raw_punches(in_time_value=time(8, 20), out_time_value=time(16, 40), work_mode=AttendanceWorkMode.WFO)
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

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        self._assert_layers(
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
            late_minutes=20,
            early_minutes=0,
            in_mode=AttendanceWorkMode.ON_DUTY,
            out_mode=AttendanceWorkMode.ON_DUTY,
        )
        attendance = self._attendance()
        self.assertEqual(attendance.reconciliation_source, SOURCE_PROVISIONAL_ON_DUTY)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_PROVISIONAL)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

    def test_on_duty_rejected_uses_raw_truth_but_keeps_normal_rules(self):
        in_punch, out_punch = self._create_raw_punches(in_time_value=time(8, 20), out_time_value=time(16, 40), work_mode=AttendanceWorkMode.WFO)
        request = WorkModeRequest.objects.create(
            employee_id=self.employee,
            mode=AttendanceWorkMode.ON_DUTY,
            scope=WorkModeRequestScope.FULL,
            start_date=self.target_date,
            end_date=self.target_date,
            status=WorkModeRequestStatus.APPROVED,
            reason='Client visit',
            document_status=WorkModeRequestDocumentStatus.REJECTED,
        )
        version = WorkModeRequestDocumentVersion.objects.create(
            work_mode_request=request,
            version_number=1,
            is_current=True,
            status=WorkModeRequestDocumentStatus.REJECTED,
            submitted_by=self.employee,
            reviewed_by=self.employee,
            review_remark='Rejected proof',
        )
        request.current_document_version = version
        request.save(update_fields=['current_document_version'])

        with self._shift_rule_context():
            recompute_attendance(self.employee, self.target_date)

        self._assert_layers(
            in_time_value=time(8, 20),
            out_time_value=time(16, 40),
            in_channel=AttendanceChannel.BIOMETRIC,
            out_channel=AttendanceChannel.BIOMETRIC,
            in_punch_id=in_punch.id,
            out_punch_id=out_punch.id,
            late_minutes=20,
            early_minutes=0,
            in_mode=AttendanceWorkMode.ON_DUTY,
            out_mode=AttendanceWorkMode.ON_DUTY,
        )
        attendance = self._attendance()
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(attendance.reconciliation_note, NOTE_ON_DUTY_NOT_GRANTED)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

