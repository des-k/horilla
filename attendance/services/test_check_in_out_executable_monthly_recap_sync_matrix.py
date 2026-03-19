from __future__ import annotations

from dataclasses import dataclass
from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.models import AttendanceChannel, AttendanceWorkMode
from attendance.services import monthly_recap


class FakeQuerySet(list):
    def _matches(self, obj, **kwargs):
        for key, expected in kwargs.items():
            if key.endswith("__range"):
                attr = key[:-7]
                value = getattr(obj, attr)
                start, end = expected
                if not (start <= value <= end):
                    return False
            elif key.endswith("__lte"):
                attr = key[:-5]
                if not (getattr(obj, attr) <= expected):
                    return False
            elif key.endswith("__gte"):
                attr = key[:-5]
                if not (getattr(obj, attr) >= expected):
                    return False
            else:
                if getattr(obj, key) != expected:
                    return False
        return True

    def filter(self, **kwargs):
        return FakeQuerySet([obj for obj in self if self._matches(obj, **kwargs)])

    def exclude(self, **kwargs):
        return FakeQuerySet([obj for obj in self if not self._matches(obj, **kwargs)])

    def order_by(self, *fields):
        data = list(self)
        for field in reversed(fields):
            reverse = field.startswith("-")
            attr = field[1:] if reverse else field
            data.sort(key=lambda obj: getattr(obj, attr), reverse=reverse)
        return FakeQuerySet(data)

    def all(self):
        return FakeQuerySet(list(self))


class FakeManager:
    def __init__(self, data):
        self._data = FakeQuerySet(data)

    def filter(self, **kwargs):
        return self._data.filter(**kwargs)

    def all(self):
        return self._data.all()


@dataclass
class FakeGraceTime:
    allowed_clock_out: bool = False
    allowed_time_in_secs: int = 0
    clock_in_type: str = "after"


class MonthlyRecapExecutableSyncMatrixTests(SimpleTestCase):
    target_date = date(2026, 3, 19)

    def setUp(self):
        self.employee = SimpleNamespace(
            id=901,
            employee_work_info=SimpleNamespace(shift_id="SHIFT-RAMADAN", work_type_id=None),
        )
        self.manager_patches = [
            patch.object(monthly_recap.Attendance, "objects", FakeManager([])),
            patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager([])),
            patch.object(monthly_recap.WorkModeRequest, "objects", FakeManager([])),
            patch.object(monthly_recap.LeaveRequest, "objects", FakeManager([])),
            patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([])),
            patch.object(monthly_recap, "is_holiday", lambda target_date: False),
            patch.object(
                monthly_recap,
                "scheduled_attendance_mode",
                lambda employee, target_date: monthly_recap.AttendanceWorkMode.WFO,
            ),
            patch("attendance.views.clock_in_out.get_shift_rules", self._default_shift_rules),
            patch(
                "attendance.views.clock_in_out._resolve_grace_time",
                lambda schedule, shift: FakeGraceTime(False, 1800, "before_after"),
            ),
        ]
        for item in self.manager_patches:
            item.start()
        self.addCleanup(lambda: [item.stop() for item in reversed(self.manager_patches)])

    def _default_shift_rules(self, day, shift, day_obj, **kwargs):
        if day != self.target_date:
            return {"schedule": None, "start_time": None, "end_time": None}
        return {
            "schedule": SimpleNamespace(id=5),
            "start_time": time(8, 0),
            "end_time": time(17, 0),
            "shift_start_dt": datetime(2026, 3, 19, 8, 0),
            "shift_end_dt": datetime(2026, 3, 19, 17, 0),
            "check_in_window_start_dt": datetime(2026, 3, 19, 6, 0),
            "check_in_window_end_dt": datetime(2026, 3, 19, 12, 0),
            "check_out_window_start_dt": datetime(2026, 3, 19, 12, 0),
            "check_out_window_end_dt": datetime(2026, 3, 19, 23, 0),
            "cutoff_in_dt": datetime(2026, 3, 19, 12, 0),
            "grace_seconds": 1800,
            "clock_in_type": "before_after",
        }

    def _find_row(self, rows):
        for row in rows:
            if row.attendance_date == self.target_date:
                return row
        self.fail("No recap row for target date")

    def test_monthly_recap_prefers_correction_request_checkout_from_activity_over_raw_attendance(self):
        attendance = SimpleNamespace(
            id=10,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 0),
            attendance_clock_in_channel=AttendanceChannel.BIOMETRIC,
            attendance_clock_in_mode=AttendanceWorkMode.WFO,
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(16, 0),
            attendance_clock_out_channel=AttendanceChannel.BIOMETRIC,
            attendance_clock_out_mode=AttendanceWorkMode.WFO,
            reconciliation_note="",
            reconciliation_source="",
            late_minutes=0,
            early_out_minutes=60,
            attendance_validated=True,
            is_validate_request_approved=False,
            is_validate_request=False,
            request_type=None,
            shift_id="SHIFT-RAMADAN",
        )
        correction_activity = SimpleNamespace(
            id=99,
            employee_id=self.employee,
            attendance_date=self.target_date,
            clock_in_date=None,
            clock_in=None,
            clock_in_channel=None,
            clock_in_mode=None,
            in_datetime=None,
            clock_out_date=self.target_date,
            clock_out=time(16, 30),
            clock_out_channel=AttendanceChannel.CORRECTION_REQUEST,
            clock_out_mode=AttendanceWorkMode.WFO,
            out_datetime=None,
        )
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        with patch.object(monthly_recap.Attendance, "objects", FakeManager([attendance])), \
             patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager([correction_activity])), \
             patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])):
            rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")

        row = self._find_row(rows)
        self.assertEqual(row.check_in, "08:00")
        self.assertEqual(row.check_out, "16:30")
        self.assertIn("Flex In ±30m", row.shift_information)

    def test_monthly_recap_prefers_approved_request_checkin_from_attendance_over_earliest_raw_activity(self):
        approved_attendance = SimpleNamespace(
            id=11,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 15),
            attendance_clock_in_channel=AttendanceChannel.CORRECTION_REQUEST,
            attendance_clock_in_mode=AttendanceWorkMode.WFA,
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            attendance_clock_out_channel=AttendanceChannel.BIOMETRIC,
            attendance_clock_out_mode=AttendanceWorkMode.WFO,
            reconciliation_note="",
            reconciliation_source="",
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=True,
            is_validate_request=False,
            request_type="update_request",
            requested_data={"attendance_clock_in": "08:15", "__meta": {"current_scope": "IN"}},
            shift_id="SHIFT-RAMADAN",
        )
        earlier_raw_activity = SimpleNamespace(
            id=3,
            employee_id=self.employee,
            attendance_date=self.target_date,
            clock_in_date=self.target_date,
            clock_in=time(8, 0),
            clock_in_channel=AttendanceChannel.BIOMETRIC,
            clock_in_mode=AttendanceWorkMode.WFO,
            in_datetime=None,
            clock_out_date=None,
            clock_out=None,
            clock_out_channel=None,
            clock_out_mode=None,
            out_datetime=None,
        )
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        with patch.object(monthly_recap.Attendance, "objects", FakeManager([approved_attendance])), \
             patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager([earlier_raw_activity])), \
             patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])):
            rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")

        row = self._find_row(rows)
        self.assertEqual(row.check_in, "08:15")
        self.assertEqual(row.check_out, "17:00")
        self.assertEqual(row.work_type, "IN: WFA<br>OUT: WFO")
