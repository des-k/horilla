from calendar import monthrange
from datetime import date, time, timedelta
from unittest.mock import patch

from django.test import override_settings
from rest_framework.test import APITestCase

from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceChannel,
    AttendancePunchDirection,
    AttendancePunchSource,
    AttendancePunchingHistory,
    AttendanceWorkMode,
)
from attendance.services import monthly_recap
from attendance.services.reconciliation import (
    NOTE_FULL_DAY_LEAVE,
    NOTE_HALF_DAY_FIRST,
    NOTE_HALF_DAY_SECOND,
    SOURCE_LEAVE,
    SOURCE_NORMAL,
)
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from leave.models import AvailableLeave, LeaveRequest, LeaveType


@override_settings(ALLOWED_HOSTS=["testserver", "localhost", "127.0.0.1"])
class LeaveLifecycleFullChainEndpointTests(AttendanceApiIntegrationMixin, APITestCase):
    def setUp(self):
        super().setUp()
        self.target_date = date.today() + timedelta(days=7)
        self.owner_user, self.employee = self.create_employee("LeaveOwner")
        self.admin_user, self.admin_employee = self.create_employee(
            "LeaveAdmin", is_superuser=True
        )
        self.auth_request(self.owner_user)

        weekday_key = self.target_date.strftime("%A").lower()
        self.shift, self.day_obj, self.schedule = self.create_shift_with_schedule(
            employee=self.employee,
            day_key=weekday_key,
            start_time=time(8, 0),
            end_time=time(17, 0),
            minimum_working_hour="08:00",
            is_night_shift=False,
            first_half_latest_check_in_time=time(13, 0),
            second_half_earliest_check_out_time=time(12, 0),
        )
        self.shift_ctx = self.patch_reconciliation_shift_rules(
            target_date=self.target_date,
            schedule=self.schedule,
            shift_start_dt=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, 8, 0
            ),
            shift_end_dt=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, 17, 0
            ),
            check_in_window_start_dt=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, 6, 0
            ),
            check_in_window_end_dt=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, 23, 0
            ),
            check_out_window_start_dt=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, 6, 0
            ),
            check_out_window_end_dt=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, 23, 0
            ),
            minimum_hour="08:00",
        )
        self.leave_type = LeaveType.objects.create(name="Annual Leave", company_id=self.company)
        self.owner_available_leave = AvailableLeave.objects.create(
            employee_id=self.employee,
            leave_type_id=self.leave_type,
            available_days=5,
            carryforward_days=1,
        )
        # The reject API currently resolves the acting employee's leave balance.
        self.admin_available_leave = AvailableLeave.objects.create(
            employee_id=self.admin_employee,
            leave_type_id=self.leave_type,
            available_days=3,
            carryforward_days=1,
        )

    def tearDown(self):
        self._clear_request_context()
        super().tearDown()

    def _create_requested_leave(self, *, status="requested", breakdown="full_day"):
        with patch("leave.signals._reconcile_leave_related_punches", return_value=None):
            return LeaveRequest.objects.create(
                employee_id=self.employee,
                leave_type_id=self.leave_type,
                start_date=self.target_date,
                end_date=self.target_date,
                start_date_breakdown=breakdown,
                end_date_breakdown=breakdown,
                description="Endpoint lifecycle leave",
                status=status,
            )

    def _create_raw_punches(self, *, work_mode=AttendanceWorkMode.WFO, in_time=time(8, 0), out_time=time(17, 0)):
        in_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, in_time.hour, in_time.minute
            ),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
            raw_employee_identifier="LEAVE-ENDPT-1",
            device_info="Gate A",
            work_mode=work_mode,
        )
        out_punch = AttendancePunchingHistory.objects.create(
            employee_id=self.employee,
            attendance_date=self.target_date,
            punch_timestamp=self.aware_dt(
                self.target_date.year, self.target_date.month, self.target_date.day, out_time.hour, out_time.minute
            ),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
            raw_employee_identifier="LEAVE-ENDPT-1",
            device_info="Gate A",
            work_mode=work_mode,
        )
        return in_punch, out_punch

    def _attendance(self):
        return Attendance.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _activity(self):
        return AttendanceActivity.objects.get(employee_id=self.employee, attendance_date=self.target_date)

    def _approve_leave(self, leave_request):
        with self.shift_ctx:
            response = self.auth_client(self.admin_user).put(
                f"/api/leave/approve/{leave_request.id}/",
                {},
                format="json",
            )
        return response

    def _reject_leave(self, leave_request, *, reason="Rejected after review"):
        with self.shift_ctx:
            return self.auth_client(self.admin_user).put(
                f"/api/leave/reject/{leave_request.id}/",
                {"reason": reason},
                format="json",
            )

    def _cancel_leave(self, leave_request):
        with self.shift_ctx:
            return self.auth_client(self.owner_user).put(
                f"/api/leave/cancel/{leave_request.id}/",
                {},
                format="json",
            )

    @staticmethod
    def _month_key(target_date):
        return target_date.strftime("%Y-%m")

    @staticmethod
    def _month_end(target_date):
        return date(target_date.year, target_date.month, monthrange(target_date.year, target_date.month)[1])

    @staticmethod
    def _row_for_date(recap, target_date):
        return next(row for row in recap["rows"] if row.attendance_date == target_date)

    def _get_monthly_recap(self):
        with patch.object(monthly_recap, "is_holiday", lambda target_date: False), \
             patch.object(monthly_recap.timezone, "localdate", lambda: self._month_end(self.target_date)), \
             self.patch_monthly_recap_shift_rules(
                 target_date=self.target_date,
                 schedule=self.schedule,
                 shift_start_dt=self.aware_dt(
                     self.target_date.year, self.target_date.month, self.target_date.day, 8, 0
                 ),
                 shift_end_dt=self.aware_dt(
                     self.target_date.year, self.target_date.month, self.target_date.day, 17, 0
                 ),
                 check_in_window_start_dt=self.aware_dt(
                     self.target_date.year, self.target_date.month, self.target_date.day, 6, 0
                 ),
                 check_in_window_end_dt=self.aware_dt(
                     self.target_date.year, self.target_date.month, self.target_date.day, 23, 0
                 ),
                 check_out_window_start_dt=self.aware_dt(
                     self.target_date.year, self.target_date.month, self.target_date.day, 6, 0
                 ),
                 check_out_window_end_dt=self.aware_dt(
                     self.target_date.year, self.target_date.month, self.target_date.day, 23, 0
                 ),
             ):
            return monthly_recap.get_monthly_attendance_recap(self.employee, self._month_key(self.target_date))

    def _assert_leave_finalized_state(self, in_punch, out_punch):
        attendance = self._attendance()
        activity = self._activity()
        self.assertIsNone(attendance.attendance_clock_in)
        self.assertIsNone(attendance.attendance_clock_out)
        self.assertIsNone(activity.clock_in)
        self.assertIsNone(activity.clock_out)
        self.assertEqual(attendance.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(attendance.reconciliation_note, NOTE_FULL_DAY_LEAVE)
        self.assertEqual(activity.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(activity.reconciliation_note, NOTE_FULL_DAY_LEAVE)
        self.assertEqual(
            Attendance.objects.filter(
                employee_id=self.employee, attendance_date=self.target_date
            ).count(),
            1,
        )
        self.assertEqual(
            AttendanceActivity.objects.filter(
                employee_id=self.employee, attendance_date=self.target_date
            ).count(),
            1,
        )
        self.assertEqual(
            AttendancePunchingHistory.objects.filter(
                employee_id=self.employee
            ).count(),
            2,
        )
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertFalse(in_punch.accepted_to_attendance)
        self.assertFalse(out_punch.accepted_to_attendance)
        return attendance, activity

    def _assert_raw_truth_restored(self, in_punch, out_punch):
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
        self.assertEqual(
            Attendance.objects.filter(
                employee_id=self.employee, attendance_date=self.target_date
            ).count(),
            1,
        )
        self.assertEqual(
            AttendanceActivity.objects.filter(
                employee_id=self.employee, attendance_date=self.target_date
            ).count(),
            1,
        )
        self.assertEqual(
            AttendancePunchingHistory.objects.filter(
                employee_id=self.employee
            ).count(),
            2,
        )
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)
        return attendance, activity

    def test_leave_approve_endpoint_updates_status_and_reconciles_attendance_side_effects(self):
        in_punch, out_punch = self._create_raw_punches()
        leave_request = self._create_requested_leave()

        response = self._approve_leave(leave_request)

        self.assertEqual(response.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "approved")
        self.assertEqual(leave_request.approved_available_days, 1)
        self.assertEqual(leave_request.approved_carryforward_days, 0)
        self._assert_leave_finalized_state(in_punch, out_punch)

    def test_leave_reject_endpoint_updates_status_and_preserves_raw_trail(self):
        in_punch, out_punch = self._create_raw_punches()
        leave_request = self._create_requested_leave()

        approve = self._approve_leave(leave_request)
        self.assertEqual(approve.status_code, 200)
        self._assert_leave_finalized_state(in_punch, out_punch)

        reject = self._reject_leave(leave_request, reason="Rejected for audit trail review")

        self.assertEqual(reject.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "rejected")
        self.assertEqual(leave_request.reject_reason, "Rejected for audit trail review")
        self.assertEqual(leave_request.approved_available_days, 0)
        self.assertEqual(leave_request.approved_carryforward_days, 0)
        self._assert_raw_truth_restored(in_punch, out_punch)

    def test_leave_cancel_endpoint_restores_raw_truth_and_keeps_history(self):
        in_punch, out_punch = self._create_raw_punches()
        leave_request = self._create_requested_leave()

        approve = self._approve_leave(leave_request)
        self.assertEqual(approve.status_code, 200)
        self._assert_leave_finalized_state(in_punch, out_punch)

        cancel = self._cancel_leave(leave_request)

        self.assertEqual(cancel.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "cancelled")
        self._assert_raw_truth_restored(in_punch, out_punch)

    def test_leave_repeated_cancel_or_reject_is_idempotent_or_cleanly_blocked(self):
        in_punch, out_punch = self._create_raw_punches()
        leave_request = self._create_requested_leave()

        approve = self._approve_leave(leave_request)
        self.assertEqual(approve.status_code, 200)

        reject = self._reject_leave(leave_request, reason="First rejection stands")
        self.assertEqual(reject.status_code, 200)
        self._assert_raw_truth_restored(in_punch, out_punch)

        repeated_reject = self._reject_leave(leave_request, reason="Should not apply")
        self.assertEqual(repeated_reject.status_code, 400)

        invalid_cancel = self._cancel_leave(leave_request)
        self.assertEqual(invalid_cancel.status_code, 400)

        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "rejected")
        self.assertEqual(leave_request.reject_reason, "First rejection stands")
        self.assertEqual(
            AttendancePunchingHistory.objects.filter(
                employee_id=self.employee
            ).count(),
            2,
        )
        self._assert_raw_truth_restored(in_punch, out_punch)

    def test_first_half_leave_approve_endpoint_recomputes_attendance_truth_without_losing_raw_trail(self):
        in_punch, out_punch = self._create_raw_punches(in_time=time(13, 5), out_time=time(17, 0))
        leave_request = self._create_requested_leave(breakdown="first_half")

        response = self._approve_leave(leave_request)

        self.assertEqual(response.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "approved")
        self.assertEqual(leave_request.requested_days, 0.5)
        self.assertEqual(leave_request.approved_available_days, 0.5)

        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(attendance.reconciliation_note, NOTE_HALF_DAY_FIRST)
        self.assertEqual(attendance.minimum_hour, "04:00")
        self.assertEqual(attendance.attendance_clock_in, time(13, 5))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertEqual(attendance.late_minutes, 5)
        self.assertEqual(attendance.early_out_minutes, 5)
        self.assertEqual(activity.reconciliation_note, NOTE_HALF_DAY_FIRST)
        self.assertEqual(activity.late_minutes, 5)
        self.assertEqual(activity.early_out_minutes, 5)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

    def test_first_half_leave_cancel_restores_normal_truth_without_duplicate_rows(self):
        in_punch, out_punch = self._create_raw_punches(in_time=time(13, 5), out_time=time(17, 0))
        leave_request = self._create_requested_leave(breakdown="first_half")

        approve = self._approve_leave(leave_request)
        self.assertEqual(approve.status_code, 200)
        approved = self._attendance()
        self.assertEqual(approved.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(approved.late_minutes, 5)
        self.assertEqual(approved.minimum_hour, "04:00")

        cancel = self._cancel_leave(leave_request)

        self.assertEqual(cancel.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "cancelled")
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(attendance.reconciliation_note, "Present")
        self.assertEqual(attendance.minimum_hour, "08:00")
        self.assertEqual(attendance.attendance_clock_in, time(13, 5))
        self.assertEqual(attendance.attendance_clock_out, time(17, 0))
        self.assertEqual(attendance.late_minutes, 305)
        self.assertEqual(attendance.early_out_minutes, 0)
        self.assertEqual(activity.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(activity.late_minutes, 305)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

    def test_second_half_leave_approve_endpoint_updates_early_out_or_session_truth_correctly(self):
        in_punch, out_punch = self._create_raw_punches(in_time=time(8, 0), out_time=time(11, 0))
        leave_request = self._create_requested_leave(breakdown="second_half")

        response = self._approve_leave(leave_request)

        self.assertEqual(response.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "approved")
        self.assertEqual(leave_request.requested_days, 0.5)
        self.assertEqual(leave_request.approved_available_days, 0.5)

        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(attendance.reconciliation_note, NOTE_HALF_DAY_SECOND)
        self.assertEqual(attendance.minimum_hour, "04:00")
        self.assertEqual(attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(attendance.attendance_clock_out, time(11, 0))
        self.assertEqual(attendance.attendance_clock_in_punch_id, in_punch.id)
        self.assertEqual(attendance.attendance_clock_out_punch_id, out_punch.id)
        self.assertEqual(attendance.late_minutes, 0)
        self.assertEqual(attendance.early_out_minutes, 60)
        self.assertEqual(activity.reconciliation_note, NOTE_HALF_DAY_SECOND)
        self.assertEqual(activity.late_minutes, 0)
        self.assertEqual(activity.early_out_minutes, 60)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

    def test_second_half_leave_cancel_restores_raw_truth_and_activity_safely(self):
        in_punch, out_punch = self._create_raw_punches(in_time=time(8, 0), out_time=time(11, 0))
        leave_request = self._create_requested_leave(breakdown="second_half")

        approve = self._approve_leave(leave_request)
        self.assertEqual(approve.status_code, 200)
        approved = self._attendance()
        self.assertEqual(approved.reconciliation_source, SOURCE_LEAVE)
        self.assertEqual(approved.early_out_minutes, 60)
        self.assertEqual(approved.minimum_hour, "04:00")

        cancel = self._cancel_leave(leave_request)

        self.assertEqual(cancel.status_code, 200)
        leave_request.refresh_from_db()
        self.assertEqual(leave_request.status, "cancelled")
        attendance = self._attendance()
        activity = self._activity()
        self.assertEqual(attendance.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(attendance.reconciliation_note, "Present")
        self.assertEqual(attendance.minimum_hour, "08:00")
        self.assertEqual(attendance.attendance_clock_in, time(8, 0))
        self.assertEqual(attendance.attendance_clock_out, time(11, 0))
        self.assertEqual(attendance.late_minutes, 0)
        self.assertEqual(attendance.early_out_minutes, 360)
        self.assertEqual(activity.reconciliation_source, SOURCE_NORMAL)
        self.assertEqual(activity.early_out_minutes, 360)
        self.assertEqual(Attendance.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendanceActivity.objects.filter(employee_id=self.employee, attendance_date=self.target_date).count(), 1)
        self.assertEqual(AttendancePunchingHistory.objects.filter(employee_id=self.employee).count(), 2)
        in_punch.refresh_from_db()
        out_punch.refresh_from_db()
        self.assertTrue(in_punch.accepted_to_attendance)
        self.assertTrue(out_punch.accepted_to_attendance)

    def test_half_day_leave_lifecycle_recomputes_monthly_recap_without_stale_totals(self):
        self._create_raw_punches(in_time=time(13, 5), out_time=time(17, 0))
        leave_request = self._create_requested_leave(breakdown="first_half")

        approve = self._approve_leave(leave_request)
        self.assertEqual(approve.status_code, 200)
        approved_recap = self._get_monthly_recap()
        approved_row = self._row_for_date(approved_recap, self.target_date)
        self.assertEqual(approved_row.check_in, "13:05")
        self.assertEqual(approved_row.check_out, "17:00")
        self.assertEqual(approved_row.late_minutes, 5)
        self.assertIn("Approved First-Half Leave", approved_row.note)
        self.assertEqual(approved_recap["summary"]["late_minutes"], 5)
        self.assertEqual(approved_recap["summary"]["early_out_minutes"], 5)

        cancel = self._cancel_leave(leave_request)
        self.assertEqual(cancel.status_code, 200)
        cancelled_recap = self._get_monthly_recap()
        cancelled_row = self._row_for_date(cancelled_recap, self.target_date)
        self.assertEqual(cancelled_row.check_in, "13:05")
        self.assertEqual(cancelled_row.check_out, "17:00")
        self.assertEqual(cancelled_row.late_minutes, 305)
        self.assertNotIn("Approved First-Half Leave", cancelled_row.note or "")
        self.assertEqual(cancelled_recap["summary"]["late_minutes"], 305)
        self.assertEqual(cancelled_recap["summary"]["early_out_minutes"], 0)

