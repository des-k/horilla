import json
import unittest
from datetime import date, datetime, time
from pathlib import Path
from types import SimpleNamespace

from attendance.services.test_monthly_recap_integration import FakeManager, monthly_recap
from attendance.services.final_session_resolution import (
    APPROVED_REQUEST_CHANNEL,
    resolve_final_session,
    should_accept_raw_session,
)


class PrelaunchIntegrityRuleTests(unittest.TestCase):
    target_date = date(2026, 3, 3)

    def setUp(self):
        self.employee = SimpleNamespace(
            id=101,
            employee_work_info=SimpleNamespace(shift_id="SHIFT-A", work_type_id=None),
        )

        monthly_recap.Attendance.objects = FakeManager([])
        monthly_recap.AttendanceActivity.objects = FakeManager([])
        monthly_recap.WorkModeRequest.objects = FakeManager([])
        monthly_recap.LeaveRequest.objects = FakeManager([])
        monthly_recap.EmployeeShiftDay.objects = FakeManager([])
        monthly_recap.is_holiday = lambda target_date: False
        monthly_recap.scheduled_attendance_mode = (
            lambda employee, target_date: monthly_recap.AttendanceWorkMode.WFO
        )
        import sys
        sys.modules["attendance.views.clock_in_out"].get_shift_rules = self._default_shift_rules
        sys.modules["attendance.views.clock_in_out"]._resolve_grace_time = (
            lambda schedule, shift: SimpleNamespace(allowed_clock_out=False, allowed_time_in_secs=0)
        )

    def _default_shift_rules(self, day, shift, day_obj):
        if day != self.target_date:
            return {"schedule": None, "start_time": None, "end_time": None}
        return {
            "schedule": SimpleNamespace(id=1),
            "start_time": time(8, 0),
            "end_time": time(17, 0),
            "shift_start_dt": datetime(2026, 3, 3, 8, 0),
            "shift_end_dt": datetime(2026, 3, 3, 17, 0),
            "check_in_window_start_dt": datetime(2026, 3, 3, 6, 0),
            "check_in_window_end_dt": datetime(2026, 3, 3, 12, 0),
            "check_out_window_start_dt": datetime(2026, 3, 3, 12, 0),
            "check_out_window_end_dt": datetime(2026, 3, 3, 23, 0),
            "cutoff_in_dt": datetime(2026, 3, 3, 12, 0),
            "grace_seconds": 0,
        }

    def _find_row(self, rows, target_date):
        for row in rows:
            if row.attendance_date == target_date:
                return row
        raise AssertionError(f"Row not found for {target_date}")

    def test_schedule_off_no_schedule_ignores_attendance_and_requests(self):
        import sys
        sys.modules["attendance.views.clock_in_out"].get_shift_rules = (
            lambda day, shift, day_obj: {"schedule": None, "start_time": None, "end_time": None}
        )

        attendance = SimpleNamespace(
            id=1,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 10),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            requested_data=json.dumps({
                "attendance_clock_in_date": "2026-03-03",
                "attendance_clock_in": "08:15",
                "__meta": {"approved_scopes": ["IN"]},
            }),
            is_validate_request_approved=True,
            is_validate_request=False,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )
        work_req = SimpleNamespace(
            id=2,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.APPROVED,
            scope=monthly_recap.WorkModeRequestScope.FULL,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(8, 0),
        )
        monthly_recap.Attendance.objects = FakeManager([attendance])
        monthly_recap.WorkModeRequest.objects = FakeManager([work_req])

        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertTrue(row.is_off)
        self.assertEqual(row.check_in, "-")
        self.assertEqual(row.check_out, "-")
        self.assertEqual(row.note, "Holiday")

    def test_schedule_normal_day_raw_earliest_in_and_latest_out_win(self):
        att = SimpleNamespace(
            id=10,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 10),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            requested_data=None,
            is_validate_request=False,
            is_validate_request_approved=False,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )
        act = SimpleNamespace(
            id=11,
            employee_id=self.employee,
            attendance_date=self.target_date,
            clock_in_date=self.target_date,
            clock_in=time(8, 2),
            in_datetime=datetime(2026, 3, 3, 8, 2),
            clock_out_date=self.target_date,
            clock_out=time(17, 12),
            out_datetime=datetime(2026, 3, 3, 17, 12),
            clock_in_channel="biometric",
            clock_out_channel="mobile",
            work_mode_request_id=None,
        )
        monthly_recap.Attendance.objects = FakeManager([att])
        monthly_recap.AttendanceActivity.objects = FakeManager([act])
        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertEqual(row.check_in, "08:02")
        self.assertEqual(row.check_out, "17:12")

    def test_schedule_normal_day_approved_in_later_than_raw_still_wins(self):
        att = monthly_recap.Attendance()
        att.id = 20
        att.employee_id = self.employee
        att.attendance_date = self.target_date
        att.attendance_clock_in_date = self.target_date
        att.attendance_clock_in = time(8, 15)
        att.attendance_clock_out_date = self.target_date
        att.attendance_clock_out = time(17, 0)
        att.attendance_clock_in_channel = APPROVED_REQUEST_CHANNEL
        att.attendance_clock_out_channel = "biometric"
        att.requested_data = json.dumps({
            "attendance_clock_in_date": "2026-03-03",
            "attendance_clock_in": "08:15",
            "__meta": {"approved_scopes": ["IN"]},
        })
        att.is_validate_request = False
        att.is_validate_request_approved = True
        att.shift_id = "SHIFT-A"
        att.work_type_id = None
        att.attendance_validated = True
        act = monthly_recap.AttendanceActivity()
        act.id = 21
        act.employee_id = self.employee
        act.attendance_date = self.target_date
        act.clock_in_date = self.target_date
        act.clock_in = time(8, 1)
        act.in_datetime = datetime(2026, 3, 3, 8, 1)
        act.clock_out_date = None
        act.clock_out = None
        act.out_datetime = None
        act.clock_in_channel = "biometric"
        act.clock_out_channel = None
        act.work_mode_request_id = None
        monthly_recap.Attendance.objects = FakeManager([att])
        monthly_recap.AttendanceActivity.objects = FakeManager([act])
        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertEqual(row.check_in, "08:15")

    def test_schedule_normal_day_approved_out_earlier_than_raw_still_wins(self):
        att = monthly_recap.Attendance()
        att.id = 30
        att.employee_id = self.employee
        att.attendance_date = self.target_date
        att.attendance_clock_in_date = self.target_date
        att.attendance_clock_in = time(8, 0)
        att.attendance_clock_out_date = self.target_date
        att.attendance_clock_out = time(16, 45)
        att.attendance_clock_in_channel = "biometric"
        att.attendance_clock_out_channel = APPROVED_REQUEST_CHANNEL
        att.requested_data = json.dumps({
            "attendance_clock_out_date": "2026-03-03",
            "attendance_clock_out": "16:45",
            "__meta": {"approved_scopes": ["OUT"]},
        })
        att.is_validate_request = False
        att.is_validate_request_approved = True
        att.shift_id = "SHIFT-A"
        att.work_type_id = None
        att.attendance_validated = True
        act = monthly_recap.AttendanceActivity()
        act.id = 31
        act.employee_id = self.employee
        act.attendance_date = self.target_date
        act.clock_in_date = None
        act.clock_in = None
        act.in_datetime = None
        act.clock_out_date = self.target_date
        act.clock_out = time(17, 10)
        act.out_datetime = datetime(2026, 3, 3, 17, 10)
        act.clock_in_channel = None
        act.clock_out_channel = "mobile"
        act.work_mode_request_id = None
        monthly_recap.Attendance.objects = FakeManager([att])
        monthly_recap.AttendanceActivity.objects = FakeManager([act])
        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertEqual(row.check_out, "16:45")

    def test_checkout_without_checkin_stays_empty_and_audit_note_is_explicit(self):
        att = SimpleNamespace(
            id=40,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=None,
            attendance_clock_in=None,
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 5),
            attendance_clock_in_channel=None,
            attendance_clock_out_channel="mobile",
            requested_data=None,
            is_validate_request=False,
            is_validate_request_approved=False,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )
        monthly_recap.Attendance.objects = FakeManager([att])
        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertEqual(row.check_in, "-")
        self.assertEqual(row.check_out, "17:05")
        self.assertIn("Missing Check-In", row.note)

    def test_resolver_blocks_raw_when_existing_channel_is_approved_request(self):
        self.assertFalse(
            should_accept_raw_session(
                session="IN",
                existing_dt=datetime(2026, 3, 3, 8, 15),
                incoming_dt=datetime(2026, 3, 3, 8, 1),
                existing_channel=APPROVED_REQUEST_CHANNEL,
            )
        )
        self.assertEqual(
            resolve_final_session(
                session="OUT",
                approved_dt=datetime(2026, 3, 3, 16, 45),
                raw_datetimes=[datetime(2026, 3, 3, 17, 10)],
                raw_source="biometric",
            ).final_dt,
            datetime(2026, 3, 3, 16, 45),
        )


    def test_schedule_window_approved_request_outside_window_stays_only_in_note(self):
        att = monthly_recap.Attendance()
        att.id = 50
        att.employee_id = self.employee
        att.attendance_date = self.target_date
        att.attendance_clock_in_date = self.target_date
        att.attendance_clock_in = time(13, 5)
        att.attendance_clock_out_date = self.target_date
        att.attendance_clock_out = time(17, 0)
        att.attendance_clock_in_channel = APPROVED_REQUEST_CHANNEL
        att.attendance_clock_out_channel = "biometric"
        att.requested_data = json.dumps({
            "attendance_clock_in_date": "2026-03-03",
            "attendance_clock_in": "13:05",
            "__meta": {"approved_scopes": ["IN"]},
        })
        att.is_validate_request = False
        att.is_validate_request_approved = True
        att.shift_id = "SHIFT-A"
        att.work_type_id = None
        att.attendance_validated = True
        monthly_recap.Attendance.objects = FakeManager([att])
        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertEqual(row.check_in, "-")
        self.assertEqual(row.check_out, "17:00")
        self.assertIn("Approved but out of time limit (IN): 13:05", row.note)

    def test_schedule_pending_work_mode_linked_punch_is_ignored(self):
        pending_work_req = SimpleNamespace(
            id=61,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.PENDING,
            scope=monthly_recap.WorkModeRequestScope.IN,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(8, 0),
        )
        act = monthly_recap.AttendanceActivity()
        act.id = 62
        act.employee_id = self.employee
        act.attendance_date = self.target_date
        act.clock_in_date = self.target_date
        act.clock_in = time(8, 0)
        act.in_datetime = datetime(2026, 3, 3, 8, 0)
        act.clock_out_date = None
        act.clock_out = None
        act.out_datetime = None
        act.clock_in_channel = "mobile"
        act.clock_out_channel = None
        act.work_mode_request_id = pending_work_req
        monthly_recap.WorkModeRequest.objects = FakeManager([pending_work_req])
        monthly_recap.AttendanceActivity.objects = FakeManager([act])
        row = self._find_row(monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03"), self.target_date)
        self.assertEqual(row.check_in, "-")
        self.assertIn("On Duty IN awaiting document upload: 08:00", row.note)

    def test_source_code_has_no_api_placeholder_clock_in_fallback(self):
        text = Path("horilla_api/api_views/attendance/views.py").read_text()
        self.assertNotIn("attendance.attendance_clock_in or attendance.attendance_clock_out", text)
        self.assertNotIn('datetime.strptime("00:00", "%H:%M").time()', text)


if __name__ == "__main__":
    unittest.main(verbosity=2)
