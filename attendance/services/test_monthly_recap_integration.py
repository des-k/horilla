from __future__ import annotations

from dataclasses import dataclass
from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase

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
            elif key.endswith("__in"):
                attr = key[:-4]
                if getattr(obj, attr) not in expected:
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


class MonthlyRecapIntegrationTests(SimpleTestCase):
    target_date = date(2026, 3, 3)

    def setUp(self):
        self.employee = SimpleNamespace(
            id=101,
            employee_work_info=SimpleNamespace(shift_id="SHIFT-A", work_type_id=None),
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
            patch(
                "attendance.views.clock_in_out.get_shift_rules",
                self._default_shift_rules,
            ),
            patch(
                "attendance.views.clock_in_out._resolve_grace_time",
                lambda schedule, shift: FakeGraceTime(False, 0),
            ),
        ]
        for item in self.manager_patches:
            item.start()
        self.addCleanup(lambda: [item.stop() for item in reversed(self.manager_patches)])

    def _default_shift_rules(self, day, shift, day_obj, **kwargs):
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
        self.fail(f"No row found for {target_date}")

    def test_full_day_leave_uses_persisted_canonical_attendance_result(self):
        attendance = SimpleNamespace(
            id=11,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 0),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFO,
            attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFO,
            reconciliation_note="Approved Full-Day Leave",
            reconciliation_source="Leave",
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=False,
            is_validate_request=False,
            request_type=None,
            shift_id="SHIFT-A",
        )
        leave_request = SimpleNamespace(
            employee_id=self.employee,
            status="approved",
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown="full_day",
            end_date_breakdown="full_day",
        )
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        with patch.object(monthly_recap.Attendance, "objects", FakeManager([attendance])), \
             patch.object(monthly_recap.LeaveRequest, "objects", FakeManager([leave_request])), \
             patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])):
            rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")

        row = self._find_row(rows, self.target_date)
        self.assertEqual(row.note, "Approved Full-Day Leave")
        self.assertEqual(row.check_in, "08:00")
        self.assertEqual(row.check_out, "17:00")

    def test_existing_attendance_row_does_not_fallback_to_independent_leave_logic(self):
        attendance = SimpleNamespace(
            id=12,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 10),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(16, 45),
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFO,
            attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFO,
            reconciliation_note="",
            reconciliation_source="",
            late_minutes=10,
            early_out_minutes=15,
            attendance_validated=True,
            is_validate_request_approved=False,
            is_validate_request=False,
            request_type=None,
            shift_id="SHIFT-A",
        )
        leave_request = SimpleNamespace(
            employee_id=self.employee,
            status="approved",
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown="full_day",
            end_date_breakdown="full_day",
        )
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        with patch.object(monthly_recap.Attendance, "objects", FakeManager([attendance])), \
             patch.object(monthly_recap.LeaveRequest, "objects", FakeManager([leave_request])), \
             patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])):
            rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")

        row = self._find_row(rows, self.target_date)
        self.assertEqual(row.note, "-")
        self.assertEqual(row.check_in, "08:10")
        self.assertEqual(row.check_out, "16:45")
        self.assertEqual(row.late_minutes, 10)
        self.assertEqual(row.early_out_minutes, 15)

    def test_pending_create_request_still_bypasses_canonical_attendance_row(self):
        pending_request_row = SimpleNamespace(
            id=13,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 5),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFO,
            attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFO,
            reconciliation_note="",
            reconciliation_source="",
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=False,
            is_validate_request_approved=False,
            is_validate_request=True,
            request_type="create_request",
            shift_id="SHIFT-A",
        )
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        with patch.object(monthly_recap.Attendance, "objects", FakeManager([pending_request_row])), \
             patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])):
            rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")

        row = self._find_row(rows, self.target_date)
        self.assertEqual(row.check_in, "-")
        self.assertNotEqual(row.note, "-")
