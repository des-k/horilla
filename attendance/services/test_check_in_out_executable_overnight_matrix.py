from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase, TestCase

from attendance.models import Attendance, AttendanceChannel, AttendancePunchDirection, AttendancePunchSource, AttendancePunchingHistory
from leave.models import LeaveRequest, LeaveType
from attendance.services import activity_sync, monthly_recap
from attendance.services.activity_sync import sync_single_session_activity
from attendance.services.punching_history import capture_request_restore_snapshot, clear_raw_links_for_request_override, restore_raw_state_after_request
from attendance.services.attendance_correction_requests import approve_request, create_request, revoke_request
from attendance.services.reconciliation import (
    NOTE_APPROVED_ATTENDANCE_REQUEST,
    NOTE_FULL_DAY_LEAVE,
    NOTE_HALF_DAY_FIRST,
    SOURCE_ATTENDANCE_REQUEST,
    SOURCE_LEAVE,
    SOURCE_NORMAL,
    recompute_attendance,
    recompute_attendance_range,
) 
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


class _FakeActivity(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None

    def duration(self):
        if not (self.clock_in_date and self.clock_in and self.clock_out_date and self.clock_out):
            return 0
        from datetime import datetime
        return int((datetime.combine(self.clock_out_date, self.clock_out) - datetime.combine(self.clock_in_date, self.clock_in)).total_seconds())


class _FakeAttendance(SimpleNamespace):
    def save(self, *args, **kwargs):
        return None


class CheckInOutExecutableOvernightMatrixTests(SimpleTestCase):
    databases = {"default"}
    def setUp(self):
        self.employee = SimpleNamespace(id=1)
        self.attendance = _FakeAttendance(
            employee_id=self.employee,
            attendance_date=date(2026, 3, 14),
            attendance_clock_in_date=date(2026, 3, 14),
            attendance_clock_in=time(22, 0),
            attendance_clock_out_date=date(2026, 3, 15),
            attendance_clock_out=time(6, 0),
            attendance_clock_in_channel="biometric",
            attendance_clock_out_channel="biometric",
            attendance_clock_in_image=None,
            attendance_clock_out_image=None,
            attendance_clock_in_mode="wfo",
            attendance_clock_out_mode="wfo",
            attendance_clock_in_location=None,
            attendance_clock_out_location=None,
            work_mode_request_id=None,
            request_restore_snapshot=None,
            attendance_clock_in_punch_id=10,
            attendance_clock_out_punch_id=11,
        )

    def test_overnight_biometric_in_out_finalizes_correct_attendance(self):
        fake_activity = _FakeActivity()
        with patch.object(activity_sync, "_locked_activity", return_value=fake_activity), \
             patch.object(activity_sync.EmployeeShiftDay.objects, "filter") as day_filter:
            day_filter.return_value.first.return_value = None
            activity = activity_sync.sync_single_session_activity(self.attendance)
        self.assertEqual(activity.attendance_date, date(2026, 3, 14))
        self.assertEqual(activity.clock_in_date, date(2026, 3, 14))
        self.assertEqual(activity.clock_out_date, date(2026, 3, 15))
        self.assertEqual(activity.clock_out, time(6, 0))
        self.assertEqual(activity.duration(), 8 * 60 * 60)

    def test_overnight_attendance_request_revoke_restores_raw_truth(self):
        capture_request_restore_snapshot(self.attendance, include_in=True, include_out=True)
        self.attendance.attendance_clock_in = time(23, 0)
        self.attendance.attendance_clock_out = time(7, 0)
        clear_raw_links_for_request_override(self.attendance, include_in=True, include_out=True)

        def _relink(attendance, *, include_in=False, include_out=False):
            if include_in:
                attendance.attendance_clock_in_punch_id = 10
            if include_out:
                attendance.attendance_clock_out_punch_id = 11
            return attendance

        with patch("attendance.services.punching_history.relink_attendance_to_raw_punches", side_effect=_relink):
            restore_raw_state_after_request(self.attendance, include_in=True, include_out=True)

        self.assertEqual(self.attendance.attendance_clock_in, time(22, 0))
        self.assertEqual(self.attendance.attendance_clock_out, time(6, 0))
        self.assertEqual(self.attendance.attendance_clock_out_date, date(2026, 3, 15))
        self.assertEqual(self.attendance.attendance_clock_in_punch_id, 10)
        self.assertEqual(self.attendance.attendance_clock_out_punch_id, 11)

    def test_overnight_recompute_range_expands_previous_and_next_day(self):
        with patch("attendance.services.reconciliation.recompute_attendance") as mocked:
            recompute_attendance_range(self.employee, date(2026, 3, 14), date(2026, 3, 14), expand_for_overnight=True)
        called_dates = [call.args[1] for call in mocked.call_args_list]
        self.assertEqual(called_dates, [date(2026, 3, 13), date(2026, 3, 14), date(2026, 3, 15)])




class CheckInOutExecutableMonthBoundaryOvernightDbIntegrationTests(AttendanceApiIntegrationMixin, TestCase):
    attendance_date = date(2026, 3, 31)

    def setUp(self):
        super().setUp()
        self.user, self.employee = self.create_employee('MonthBoundary')
        weekday_key = self.attendance_date.strftime('%A').lower()
        self.shift, self.day_obj, self.schedule = self.create_shift_with_schedule(
            employee=self.employee,
            day_key=weekday_key,
            start_time=time(22, 0),
            end_time=time(6, 0),
            minimum_working_hour='08:00',
            is_night_shift=True,
        )
        self.shift_start_dt = self.aware_dt(2026, 3, 31, 22, 0)
        self.shift_end_dt = self.aware_dt(2026, 4, 1, 6, 0)
        self.in_window_start_dt = self.aware_dt(2026, 3, 31, 20, 0)
        self.in_window_end_dt = self.aware_dt(2026, 4, 1, 10, 0)
        self.out_window_start_dt = self.aware_dt(2026, 4, 1, 4, 0)
        self.out_window_end_dt = self.aware_dt(2026, 4, 1, 10, 0)

    def _shift_rule_context(self):
        return self.patch_reconciliation_shift_rules(
            target_date=self.attendance_date,
            schedule=self.schedule,
            shift_start_dt=self.shift_start_dt,
            shift_end_dt=self.shift_end_dt,
            check_in_window_start_dt=self.in_window_start_dt,
            check_in_window_end_dt=self.in_window_end_dt,
            check_out_window_start_dt=self.out_window_start_dt,
            check_out_window_end_dt=self.out_window_end_dt,
            minimum_hour='08:00',
        )

    def _recap_rule_context(self):
        return self.patch_monthly_recap_shift_rules(
            target_date=self.attendance_date,
            schedule=self.schedule,
            shift_start_dt=self.shift_start_dt,
            shift_end_dt=self.shift_end_dt,
            check_in_window_start_dt=self.in_window_start_dt,
            check_in_window_end_dt=self.in_window_end_dt,
            check_out_window_start_dt=self.out_window_start_dt,
            check_out_window_end_dt=self.out_window_end_dt,
        )

    def _create_raw_punches(self, *, in_dt, out_dt):
        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.attendance_date,
            punch_timestamp=in_dt,
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='BIO-MONTH',
            device_info='Night Gate',
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.attendance_date,
            punch_timestamp=out_dt,
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='BIO-MONTH',
            device_info='Night Gate',
        )
        return in_punch, out_punch

    def _get_recap_for_month(self, month):
        with patch.object(monthly_recap, 'is_holiday', lambda target_date: False), \
             patch.object(monthly_recap.timezone, 'localdate', lambda: date(2026, 4, 30)), \
             self._recap_rule_context():
            return monthly_recap.get_monthly_attendance_recap(self.employee, month)

    @staticmethod
    def _row_for_date(recap, target_date):
        return next(row for row in recap['rows'] if row.attendance_date == target_date)

    def test_month_boundary_override_then_revoke_recomputes_recap_without_stale_totals(self):
        in_punch, out_punch = self._create_raw_punches(
            in_dt=self.aware_dt(2026, 3, 31, 22, 15),
            out_dt=self.aware_dt(2026, 4, 1, 5, 30),
        )

        with self._shift_rule_context():
            result = recompute_attendance(self.employee, self.attendance_date)

        attendance = result.attendance
        march_before = self._get_recap_for_month('2026-03')
        april_before = self._get_recap_for_month('2026-04')
        row_march_before = self._row_for_date(march_before, self.attendance_date)
        self.assertEqual(row_march_before.check_out, '05:30 D+1')
        self.assertEqual(march_before['summary']['late_minutes'], 15)
        self.assertEqual(march_before['summary']['early_out_minutes'], 30)
        self.assertEqual(april_before['summary']['late_minutes'], 0)
        self.assertEqual(april_before['summary']['early_out_minutes'], 0)

        request_obj = create_request(
            employee=self.employee,
            actor_user=self.user,
            payload={
                'attendance_date': self.attendance_date.isoformat(),
                'scope': 'OUT',
                'reason': 'Extend overnight checkout',
                'requested_check_out_date': '2026-04-01',
                'requested_check_out_time': '06:30',
            },
            uploaded_files=[],
        )

        with self._shift_rule_context():
            approved = approve_request(request_obj=request_obj, actor_user=self.user)

        attendance.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(attendance.reconciliation_source, SOURCE_ATTENDANCE_REQUEST)
        self.assertEqual(attendance.reconciliation_note, NOTE_APPROVED_ATTENDANCE_REQUEST)
        self.assertEqual(attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(attendance.attendance_clock_out, time(6, 30))
        self.assertFalse(out_punch.accepted_to_attendance)

        march_approved = self._get_recap_for_month('2026-03')
        april_approved = self._get_recap_for_month('2026-04')
        row_march_approved = self._row_for_date(march_approved, self.attendance_date)
        self.assertEqual(row_march_approved.check_out, '06:30 D+1')
        self.assertEqual(march_approved['summary']['late_minutes'], 15)
        self.assertEqual(march_approved['summary']['early_out_minutes'], 0)
        self.assertEqual(april_approved['summary']['late_minutes'], 0)
        self.assertEqual(april_approved['summary']['early_out_minutes'], 0)

        with self._shift_rule_context():
            revoked = revoke_request(request_obj=request_obj, actor_user=self.user, reason='Manager revoked overnight correction')

        attendance.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(attendance.reconciliation_note, 'Present')
        self.assertEqual(attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(attendance.attendance_clock_out, time(5, 30))
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.attendance_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(id__in=[in_punch.id, out_punch.id]).count(), 2)

        march_revoked = self._get_recap_for_month('2026-03')
        april_revoked = self._get_recap_for_month('2026-04')
        row_march_revoked = self._row_for_date(march_revoked, self.attendance_date)
        self.assertEqual(row_march_revoked.check_out, '05:30 D+1')
        self.assertEqual(march_revoked['summary']['late_minutes'], 15)
        self.assertEqual(march_revoked['summary']['early_out_minutes'], 30)
        self.assertEqual(april_revoked['summary']['late_minutes'], 0)
        self.assertEqual(april_revoked['summary']['early_out_minutes'], 0)

    def test_month_boundary_leave_cancel_restores_daily_and_monthly_truth_without_duplicate_totals(self):
        in_punch, out_punch = self._create_raw_punches(
            in_dt=self.aware_dt(2026, 3, 31, 22, 15),
            out_dt=self.aware_dt(2026, 4, 1, 5, 30),
        )
        leave_type = LeaveType.objects.create(name='Month Boundary Leave', company_id=self.company)
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.attendance_date,
            end_date=self.attendance_date,
            start_date_breakdown='full_day',
            end_date_breakdown='full_day',
            description='Full day overnight leave',
            status='approved',
        )

        with self._shift_rule_context():
            approved_leave = recompute_attendance(self.employee, self.attendance_date)

        attendance = approved_leave.attendance
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(attendance.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(attendance.reconciliation_note, NOTE_FULL_DAY_LEAVE)
        self.assertIsNone(attendance.attendance_clock_in)
        self.assertIsNone(attendance.attendance_clock_out)
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)

        march_leave = self._get_recap_for_month('2026-03')
        april_leave = self._get_recap_for_month('2026-04')
        row_march_leave = self._row_for_date(march_leave, self.attendance_date)
        self.assertEqual(row_march_leave.note, "On Leave")
        self.assertEqual(row_march_leave.check_in, '-')
        self.assertEqual(row_march_leave.check_out, '-')
        self.assertEqual(march_leave['summary']['late_minutes'], 0)
        self.assertEqual(march_leave['summary']['early_out_minutes'], 0)
        self.assertEqual(april_leave['summary']['late_minutes'], 0)
        self.assertEqual(april_leave['summary']['early_out_minutes'], 0)

        leave_request.status = 'cancelled'
        leave_request.save(update_fields=['status'])

        with self._shift_rule_context():
            restored = recompute_attendance(self.employee, self.attendance_date)

        attendance.refresh_from_db()
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(restored.attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(restored.attendance.reconciliation_note, 'Present')
        self.assertEqual(restored.attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(restored.attendance.attendance_clock_out, time(5, 30))
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.attendance_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(id__in=[in_punch.id, out_punch.id]).count(), 2)

        march_restored = self._get_recap_for_month('2026-03')
        april_restored = self._get_recap_for_month('2026-04')
        row_march_restored = self._row_for_date(march_restored, self.attendance_date)
        self.assertEqual(row_march_restored.check_in, '22:15')
        self.assertEqual(row_march_restored.check_out, '05:30 D+1')
        self.assertEqual(march_restored['summary']['late_minutes'], 15)
        self.assertEqual(march_restored['summary']['early_out_minutes'], 30)
        self.assertEqual(april_restored['summary']['late_minutes'], 0)
        self.assertEqual(april_restored['summary']['early_out_minutes'], 0)

    def test_half_day_leave_on_overnight_boundary_keeps_correct_recap_bucket_if_supported(self):
        leave_type = LeaveType.objects.create(name="Night Half Day", company_id=self.company)
        in_punch, out_punch = self._create_raw_punches(
            in_dt=self.aware_dt(2026, 4, 1, 2, 15),
            out_dt=self.aware_dt(2026, 4, 1, 6, 0),
        )
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.attendance_date,
            end_date=self.attendance_date,
            start_date_breakdown="first_half",
            end_date_breakdown="first_half",
            description="Month boundary half-day leave",
            status="approved",
            requested_days=0.5,
            approved_available_days=0.5,
        )

        with self._shift_rule_context():
            approved = recompute_attendance(self.employee, self.attendance_date)

        approved_attendance = approved.attendance
        self.assertEqual(approved_attendance.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(approved_attendance.reconciliation_note, NOTE_HALF_DAY_FIRST)
        self.assertEqual(approved_attendance.attendance_clock_in_date, date(2026, 4, 1))
        self.assertEqual(approved_attendance.attendance_clock_in, time(2, 15))
        self.assertEqual(approved_attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(approved_attendance.attendance_clock_out, time(6, 0))
        self.assertEqual(approved_attendance.late_minutes, 15)
        self.assertEqual(approved_attendance.early_out_minutes, 0)
        self.assertEqual(approved_attendance.minimum_hour, "04:00")

        march_approved = self._get_recap_for_month("2026-03")
        april_approved = self._get_recap_for_month("2026-04")
        row_march_approved = self._row_for_date(march_approved, self.attendance_date)
        self.assertEqual(row_march_approved.check_in, "02:15 D+1")
        self.assertEqual(row_march_approved.check_out, "06:00 D+1")
        self.assertIn("Approved First-Half Leave", row_march_approved.note)
        self.assertEqual(march_approved["summary"]["late_minutes"], 15)
        self.assertEqual(march_approved["summary"]["early_out_minutes"], 0)
        self.assertEqual(april_approved["summary"]["late_minutes"], 0)
        self.assertEqual(april_approved["summary"]["early_out_minutes"], 0)

        leave_request.status = "cancelled"
        leave_request.save(update_fields=["status"])

        with self._shift_rule_context():
            cancelled = recompute_attendance(self.employee, self.attendance_date)

        cancelled_attendance = cancelled.attendance
        self.assertEqual(cancelled_attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(cancelled_attendance.reconciliation_note, "Present")
        self.assertEqual(cancelled_attendance.attendance_clock_in_date, date(2026, 4, 1))
        self.assertEqual(cancelled_attendance.attendance_clock_in, time(2, 15))
        self.assertEqual(cancelled_attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(cancelled_attendance.attendance_clock_out, time(6, 0))
        self.assertEqual(cancelled_attendance.late_minutes, 255)
        self.assertEqual(cancelled_attendance.early_out_minutes, 0)
        self.assertEqual(cancelled_attendance.minimum_hour, "08:00")

        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.attendance_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(id__in=[in_punch.id, out_punch.id]).count(), 2)

        march_cancelled = self._get_recap_for_month("2026-03")
        april_cancelled = self._get_recap_for_month("2026-04")
        row_march_cancelled = self._row_for_date(march_cancelled, self.attendance_date)
        self.assertEqual(row_march_cancelled.check_in, "02:15 D+1")
        self.assertEqual(row_march_cancelled.check_out, "06:00 D+1")
        self.assertNotIn("Approved First-Half Leave", row_march_cancelled.note or "")
        self.assertEqual(march_cancelled["summary"]["late_minutes"], 255)
        self.assertEqual(march_cancelled["summary"]["early_out_minutes"], 0)
        self.assertEqual(april_cancelled["summary"]["late_minutes"], 0)
        self.assertEqual(april_cancelled["summary"]["early_out_minutes"], 0)


class CheckInOutExecutableOvernightDbIntegrationTests(AttendanceApiIntegrationMixin, TestCase):
    attendance_date = date(2026, 3, 14)

    def setUp(self):
        super().setUp()
        self.user, self.employee = self.create_employee('Overnight')
        weekday_key = self.attendance_date.strftime('%A').lower()
        self.shift, self.day_obj, self.schedule = self.create_shift_with_schedule(
            employee=self.employee,
            day_key=weekday_key,
            start_time=time(22, 0),
            end_time=time(6, 0),
            minimum_working_hour='08:00',
            is_night_shift=True,
        )
        self.shift_start_dt = self.aware_dt(2026, 3, 14, 22, 0)
        self.shift_end_dt = self.aware_dt(2026, 3, 15, 6, 0)
        self.in_window_start_dt = self.aware_dt(2026, 3, 14, 20, 0)
        self.in_window_end_dt = self.aware_dt(2026, 3, 15, 2, 0)
        self.out_window_start_dt = self.aware_dt(2026, 3, 15, 4, 0)
        self.out_window_end_dt = self.aware_dt(2026, 3, 15, 10, 0)

    def _shift_rule_context(self):
        return self.patch_reconciliation_shift_rules(
            target_date=self.attendance_date,
            schedule=self.schedule,
            shift_start_dt=self.shift_start_dt,
            shift_end_dt=self.shift_end_dt,
            check_in_window_start_dt=self.in_window_start_dt,
            check_in_window_end_dt=self.in_window_end_dt,
            check_out_window_start_dt=self.out_window_start_dt,
            check_out_window_end_dt=self.out_window_end_dt,
            minimum_hour='08:00',
        )

    def _recap_rule_context(self):
        return self.patch_monthly_recap_shift_rules(
            target_date=self.attendance_date,
            schedule=self.schedule,
            shift_start_dt=self.shift_start_dt,
            shift_end_dt=self.shift_end_dt,
            check_in_window_start_dt=self.in_window_start_dt,
            check_in_window_end_dt=self.in_window_end_dt,
            check_out_window_start_dt=self.out_window_start_dt,
            check_out_window_end_dt=self.out_window_end_dt,
        )

    def _create_raw_punches(self, *, in_dt, out_dt):
        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.attendance_date,
            punch_timestamp=in_dt,
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier='BIO-OVN',
            device_info='Night Gate',
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.attendance_date,
            punch_timestamp=out_dt,
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier='BIO-OVN',
            device_info='Night Gate',
        )
        return in_punch, out_punch

    def _get_target_recap(self):
        with patch.object(monthly_recap, 'is_holiday', lambda target_date: False), self._recap_rule_context():
            recap = monthly_recap.get_monthly_attendance_recap(self.employee, '2026-03')
        row = next(row for row in recap['rows'] if row.attendance_date == self.attendance_date)
        return recap, row

    def test_overnight_biometric_in_out_finalizes_correct_attendance_and_classification_on_attendance_date(self):
        self._create_raw_punches(
            in_dt=self.aware_dt(2026, 3, 14, 22, 15),
            out_dt=self.aware_dt(2026, 3, 15, 5, 30),
        )

        with self._shift_rule_context():
            result = recompute_attendance(self.employee, self.attendance_date)

        attendance = result.attendance
        activity = result.activity
        self.assertEqual(attendance.attendance_date, self.attendance_date)
        self.assertEqual(attendance.attendance_clock_in_date, self.attendance_date)
        self.assertEqual(attendance.attendance_clock_out_date, date(2026, 3, 15))
        self.assertEqual(attendance.attendance_clock_in, time(22, 15))
        self.assertEqual(attendance.attendance_clock_out, time(5, 30))
        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.late_minutes, 15)
        self.assertEqual(attendance.early_out_minutes, 30)
        self.assertEqual(activity.attendance_date, self.attendance_date)
        self.assertEqual(activity.clock_out_date, date(2026, 3, 15))
        self.assertEqual(activity.late_minutes, 15)
        self.assertEqual(activity.early_out_minutes, 30)

        recap, row = self._get_target_recap()
        self.assertEqual(row.check_in, '22:15')
        self.assertEqual(row.check_out, '05:30 D+1')
        self.assertEqual(row.late_minutes, 15)
        self.assertEqual(row.early_out_minutes, 30)
        self.assertEqual(recap['summary']['late_minutes'], 15)
        self.assertEqual(recap['summary']['early_out_minutes'], 30)

    def test_overnight_monthly_recap_changes_after_correction_approve_and_restores_after_revoke(self):
        in_punch, out_punch = self._create_raw_punches(
            in_dt=self.aware_dt(2026, 3, 14, 22, 15),
            out_dt=self.aware_dt(2026, 3, 15, 5, 30),
        )

        with self._shift_rule_context():
            result = recompute_attendance(self.employee, self.attendance_date)
        attendance = result.attendance

        recap_before, row_before = self._get_target_recap()
        self.assertEqual(row_before.check_out, '05:30 D+1')
        self.assertEqual(recap_before['summary']['early_out_minutes'], 30)

        request_obj = create_request(
            employee=self.employee,
            actor_user=self.user,
            payload={
                'attendance_date': self.attendance_date.isoformat(),
                'scope': 'OUT',
                'reason': 'Extend overnight checkout',
                'requested_check_out_date': '2026-03-15',
                'requested_check_out_time': '06:30',
            },
            uploaded_files=[],
        )

        with self._shift_rule_context():
            approved = approve_request(request_obj=request_obj, actor_user=self.user)

        attendance.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(attendance.attendance_date, self.attendance_date)
        self.assertEqual(attendance.attendance_clock_out_date, date(2026, 3, 15))
        self.assertEqual(attendance.attendance_clock_out, time(6, 30))
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertIsNone(attendance.attendance_clock_out_punch_id)
        self.assertFalse(out_punch.accepted_to_attendance)
        self.assertEqual(AttendancePunchingHistory.objects.filter(id=out_punch.id).count(), 1)

        recap_approved, row_approved = self._get_target_recap()
        self.assertEqual(row_approved.check_out, '06:30 D+1')
        self.assertEqual(recap_approved['summary']['early_out_minutes'], 0)
        self.assertEqual(recap_approved['summary']['late_minutes'], 15)

        with self._shift_rule_context():
            revoked = revoke_request(request_obj=request_obj, actor_user=self.user, reason='Manager revoked overnight correction')


        attendance.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertEqual(attendance.attendance_date, self.attendance_date)
        self.assertEqual(attendance.attendance_clock_out_date, date(2026, 3, 15))
        self.assertEqual(attendance.attendance_clock_out, time(5, 30))
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(out_punch.attendance_id_id, attendance.id)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.attendance_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(id__in=[in_punch.id, out_punch.id]).count(), 2)

        recap_revoked, row_revoked = self._get_target_recap()
        self.assertEqual(row_revoked.check_out, '05:30 D+1')
        self.assertEqual(recap_revoked['summary']['early_out_minutes'], 30)
        self.assertEqual(recap_revoked['summary']['late_minutes'], 15)

    def _helper_half_day_leave_on_overnight_boundary_keeps_correct_recap_bucket_if_supported(self):
        leave_type = LeaveType.objects.create(name='Night Half Day', company_id=self.company)
        in_punch, out_punch = self._create_raw_punches(
            in_dt=self.aware_dt(2026, 4, 1, 2, 15),
            out_dt=self.aware_dt(2026, 4, 1, 6, 0),
        )
        leave_request = LeaveRequest.objects.create(
            employee_id=self.employee,
            leave_type_id=leave_type,
            start_date=self.attendance_date,
            end_date=self.attendance_date,
            start_date_breakdown='first_half',
            end_date_breakdown='first_half',
            description='Month boundary half-day leave',
            status='approved',
            requested_days=0.5,
            approved_available_days=0.5,
        )

        with self._shift_rule_context():
            approved = recompute_attendance(self.employee, self.attendance_date)

        approved_attendance = approved.attendance
        self.assertEqual(approved_attendance.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(approved_attendance.reconciliation_note, NOTE_HALF_DAY_FIRST)
        self.assertEqual(approved_attendance.attendance_clock_in_date, date(2026, 4, 1))
        self.assertEqual(approved_attendance.attendance_clock_in, time(2, 15))
        self.assertEqual(approved_attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(approved_attendance.attendance_clock_out, time(6, 0))
        self.assertEqual(approved_attendance.late_minutes, 15)
        self.assertEqual(approved_attendance.early_out_minutes, 0)
        self.assertEqual(approved_attendance.minimum_hour, '04:00')

        march_approved = self._get_recap_for_month('2026-03')
        april_approved = self._get_recap_for_month('2026-04')
        row_march_approved = self._row_for_date(march_approved, self.attendance_date)
        self.assertEqual(row_march_approved.check_in, '02:15 D+1')
        self.assertEqual(row_march_approved.check_out, '06:00 D+1')
        self.assertIn('Approved First Half Leave', row_march_approved.note)
        self.assertEqual(march_approved['summary']['late_minutes'], 15)
        self.assertEqual(march_approved['summary']['early_out_minutes'], 0)
        self.assertEqual(april_approved['summary']['late_minutes'], 0)
        self.assertEqual(april_approved['summary']['early_out_minutes'], 0)

        leave_request.status = 'cancelled'
        leave_request.save(update_fields=['status'])

        with self._shift_rule_context():
            cancelled = recompute_attendance(self.employee, self.attendance_date)

        cancelled_attendance = cancelled.attendance
        self.assertEqual(cancelled_attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(cancelled_attendance.reconciliation_note, 'Present')
        self.assertEqual(cancelled_attendance.attendance_clock_in_date, date(2026, 4, 1))
        self.assertEqual(cancelled_attendance.attendance_clock_in, time(2, 15))
        self.assertEqual(cancelled_attendance.attendance_clock_out_date, date(2026, 4, 1))
        self.assertEqual(cancelled_attendance.attendance_clock_out, time(6, 0))
        self.assertEqual(cancelled_attendance.late_minutes, 255)
        self.assertEqual(cancelled_attendance.early_out_minutes, 0)
        self.assertEqual(cancelled_attendance.minimum_hour, '08:00')

        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.attendance_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(id__in=[in_punch.id, out_punch.id]).count(), 2)

        march_cancelled = self._get_recap_for_month('2026-03')
        april_cancelled = self._get_recap_for_month('2026-04')
        row_march_cancelled = self._row_for_date(march_cancelled, self.attendance_date)
        self.assertEqual(row_march_cancelled.check_in, '02:15 D+1')
        self.assertEqual(row_march_cancelled.check_out, '06:00 D+1')
        self.assertNotIn('Approved First Half Leave', row_march_cancelled.note or '')
        self.assertEqual(march_cancelled['summary']['late_minutes'], 255)
        self.assertEqual(march_cancelled['summary']['early_out_minutes'], 0)
        self.assertEqual(april_cancelled['summary']['late_minutes'], 0)
        self.assertEqual(april_cancelled['summary']['early_out_minutes'], 0)
