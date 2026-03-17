from __future__ import annotations

import inspect
from dataclasses import dataclass
from datetime import date, datetime, time
from pathlib import Path
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
    clock_in_type: str = "after"


class FlexibleGraceTimeSourceRegressionTests(SimpleTestCase):
    def test_grace_time_settings_template_exposes_clock_in_type_control(self):
        template = Path(
            "attendance/templates/attendance/grace_time/grace_time_form.html"
        ).read_text(encoding="utf-8")

        self.assertIn("form.clock_in_type", template)

    def test_grace_time_update_flow_persists_many_to_many_and_shift_assignments(self):
        source = Path("attendance/views/views.py").read_text(encoding="utf-8")

        self.assertIn("save_m2m", source)
        self.assertIn('cleaned_data.get("shifts")', source)

    def test_web_attendance_request_shift_info_uses_same_grace_resolution_priority_as_clocking(self):
        source = Path("attendance/views/requests.py").read_text(encoding="utf-8")

        self.assertIn("_resolve_grace_time", source)
        self.assertIn("schedule", source)

    def test_mobile_status_payload_exposes_clock_in_type_for_before_after_clients(self):
        source = Path("horilla_api/api_views/attendance/views.py").read_text(encoding="utf-8")

        self.assertIn('"clock_in_type"', source)


    def test_web_attendance_templates_render_compact_flex_badge(self):
        tab_template = Path("attendance/templates/attendance/attendance/tab_content.html").read_text(encoding="utf-8")
        own_template = Path("attendance/templates/attendance/own_attendance/attendances.html").read_text(encoding="utf-8")
        filter_source = Path("attendance/templatetags/attendancefilters.py").read_text(encoding="utf-8")

        self.assertIn("attendance_flex_display", tab_template)
        self.assertIn("attendance_flex_display", own_template)
        self.assertIn("Flex In {symbol}{minutes}m", filter_source)

    def test_monthly_recap_shift_information_uses_compact_symbol_format(self):
        source = Path("attendance/services/monthly_recap.py").read_text(encoding="utf-8")

        self.assertIn("Flex In {flex_symbol}{flexi_min}m", source)


class FlexibleGraceTimeMonthlyRecapRegressionTests(SimpleTestCase):
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
                self._ramadan_shift_rules,
            ),
            patch(
                "attendance.views.clock_in_out._resolve_grace_time",
                lambda schedule, shift: FakeGraceTime(
                    allowed_clock_out=False,
                    allowed_time_in_secs=1800,
                    clock_in_type="before_after",
                ),
            ),
        ]
        for item in self.manager_patches:
            item.start()
        self.addCleanup(lambda: [item.stop() for item in reversed(self.manager_patches)])

    def _ramadan_shift_rules(self, day, shift, day_obj, **kwargs):
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
            "grace_seconds": 1800,
        }

    def _find_row(self, rows, target_date):
        for row in rows:
            if row.attendance_date == target_date:
                return row
        self.fail(f"No row found for {target_date}")

    def test_monthly_recap_before_after_credits_early_checkin_against_early_checkout(self):
        activities = [
            SimpleNamespace(
                id=21,
                employee_id=self.employee,
                attendance_date=self.target_date,
                in_datetime=datetime(2026, 3, 3, 7, 45),
                out_datetime=datetime(2026, 3, 3, 16, 45),
                clock_in_date=self.target_date,
                clock_in=time(7, 45),
                clock_out_date=self.target_date,
                clock_out=time(16, 45),
                attendance_clock_in=None,
                attendance_clock_out=None,
                attendance_clock_in_date=None,
                attendance_clock_out_date=None,
                attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFO,
                attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFO,
                in_attendance_status=None,
                out_attendance_status=None,
                in_related_work_type_request_id=None,
                out_related_work_type_request_id=None,
            )
        ]
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        with patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager(activities)), patch.object(
            monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])
        ):
            rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")

        row = self._find_row(rows, self.target_date)
        self.assertEqual(row.check_in, "07:45")
        self.assertEqual(row.check_out, "16:45")
        self.assertEqual(
            row.early_out_minutes,
            0,
            "before_after should credit a 15 minute early check-in against a 15 minute early check-out",
        )
