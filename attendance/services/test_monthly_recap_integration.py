import json
import sys
import types
import unittest
from dataclasses import dataclass
from datetime import date, datetime, time, timedelta
from pathlib import Path
from types import SimpleNamespace


# Make repo importable when running this file directly.
REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


# ---------------------------------------------------------------------------
# Minimal dependency stubs so the monthly recap service can be imported and
# tested without the full Django project environment.
# ---------------------------------------------------------------------------

def _install_test_stubs():
    django_mod = types.ModuleType("django")
    conf_mod = types.ModuleType("django.conf")
    conf_mod.settings = SimpleNamespace(USE_TZ=False)

    timezone_mod = types.ModuleType("django.utils.timezone")
    timezone_mod.localdate = lambda: date(2026, 3, 31)
    timezone_mod.is_aware = lambda dt: bool(getattr(dt, "tzinfo", None))
    timezone_mod.localtime = lambda dt: dt
    timezone_mod.get_current_timezone = lambda: None
    timezone_mod.make_aware = lambda dt, tz=None: dt.replace(tzinfo=tz)
    timezone_mod.make_naive = lambda dt, tz=None: dt.replace(tzinfo=None)

    utils_mod = types.ModuleType("django.utils")
    utils_mod.timezone = timezone_mod

    core_mod = types.ModuleType("django.core")
    exc_mod = types.ModuleType("django.core.exceptions")
    exc_mod.ValidationError = Exception

    sys.modules["django"] = django_mod
    sys.modules["django.conf"] = conf_mod
    sys.modules["django.utils"] = utils_mod
    sys.modules["django.utils.timezone"] = timezone_mod
    sys.modules["django.core"] = core_mod
    sys.modules["django.core.exceptions"] = exc_mod

    attendance_models = types.ModuleType("attendance.models")

    class Attendance:
        objects = None

    class AttendanceActivity:
        objects = None

    class AttendanceWorkMode:
        WFO = "wfo"
        WFA = "wfa"
        ON_DUTY = "on_duty"

    class WorkModeRequest:
        objects = None

    class WorkModeRequestScope:
        IN = "in"
        OUT = "out"
        FULL = "full"

    class WorkModeRequestStatus:
        APPROVED = "approved"
        PENDING = "pending"
        WAITING_FOR_APPROVAL = "waiting_for_approval"
        REJECTED = "rejected"
        CANCELED = "canceled"

    attendance_models.Attendance = Attendance
    attendance_models.AttendanceActivity = AttendanceActivity
    attendance_models.AttendanceWorkMode = AttendanceWorkMode
    attendance_models.WorkModeRequest = WorkModeRequest
    attendance_models.WorkModeRequestScope = WorkModeRequestScope
    attendance_models.WorkModeRequestStatus = WorkModeRequestStatus
    sys.modules["attendance.models"] = attendance_models

    work_type_rules = types.ModuleType("attendance.services.work_type_request_rules")
    work_type_rules.scheduled_attendance_mode = lambda employee, target_date: AttendanceWorkMode.WFO
    sys.modules["attendance.services.work_type_request_rules"] = work_type_rules

    base_methods = types.ModuleType("base.methods")
    base_methods.is_holiday = lambda target_date: False
    sys.modules["base.methods"] = base_methods

    base_models = types.ModuleType("base.models")

    class EmployeeShiftDay:
        objects = None

    base_models.EmployeeShiftDay = EmployeeShiftDay
    sys.modules["base.models"] = base_models

    employee_models = types.ModuleType("employee.models")

    class Employee:
        pass

    employee_models.Employee = Employee
    sys.modules["employee.models"] = employee_models

    leave_models = types.ModuleType("leave.models")

    class LeaveRequest:
        objects = None

    leave_models.LeaveRequest = LeaveRequest
    sys.modules["leave.models"] = leave_models

    clock_in_out = types.ModuleType("attendance.views.clock_in_out")
    clock_in_out.get_shift_rules = lambda d, shift, day_obj: {}
    clock_in_out._resolve_grace_time = lambda schedule, shift: None
    sys.modules["attendance.views.clock_in_out"] = clock_in_out


_install_test_stubs()

# Import after stubbing.
sys.modules.pop("attendance.services.monthly_recap", None)
from attendance.services import monthly_recap  # noqa: E402


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


class MonthlyRecapIntegrationTests(unittest.TestCase):
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

        sys.modules["attendance.views.clock_in_out"].get_shift_rules = self._default_shift_rules
        sys.modules["attendance.views.clock_in_out"]._resolve_grace_time = (
            lambda schedule, shift: FakeGraceTime(False, 0)
        )

    def _default_shift_rules(self, day, shift, day_obj):
        if day != self.target_date:
            return {
                "schedule": None,
                "start_time": None,
                "end_time": None,
            }

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

    def test_off_day_no_schedule_ignores_attendance_and_requests(self):
        attendance = SimpleNamespace(
            id=1,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 12),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 5),
            requested_data=json.dumps(
                {
                    "attendance_clock_in_date": "2026-03-03",
                    "attendance_clock_in": "08:12",
                    "__meta": {"current_scope": "IN", "approved_scopes": ["IN"]},
                }
            ),
            is_validate_request=True,
            is_validate_request_approved=True,
            shift_id=None,
            work_type_id=None,
            attendance_validated=True,
        )
        work_req = SimpleNamespace(
            id=10,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.PENDING,
            scope=monthly_recap.WorkModeRequestScope.OUT,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(17, 10),
        )

        monthly_recap.Attendance.objects = FakeManager([attendance])
        monthly_recap.WorkModeRequest.objects = FakeManager([work_req])

        def off_shift_rules(day, shift, day_obj):
            return {"schedule": None, "start_time": None, "end_time": None}

        sys.modules["attendance.views.clock_in_out"].get_shift_rules = off_shift_rules

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertTrue(row.is_off)
        self.assertEqual(row.check_in, "—")
        self.assertEqual(row.check_out, "—")
        self.assertEqual(row.late, "00:00")
        self.assertEqual(row.early_out, "00:00")
        self.assertEqual(row.work_type, "—")
        self.assertEqual(row.note, "Holiday")
        self.assertNotIn("pending", row.note.lower())

    def test_normal_day_approved_attendance_request_in_window_changes_final_time(self):
        attendance = SimpleNamespace(
            id=2,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 12),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 2),
            requested_data=json.dumps(
                {
                    "attendance_clock_in_date": "2026-03-03",
                    "attendance_clock_in": "08:12",
                    "__meta": {"approved_scopes": ["IN"]},
                }
            ),
            is_validate_request=False,
            is_validate_request_approved=True,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )

        monthly_recap.Attendance.objects = FakeManager([attendance])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertFalse(row.is_off)
        self.assertEqual(row.check_in, "08:12")
        self.assertEqual(row.check_out, "17:02")
        self.assertEqual(row.late, "00:12")
        self.assertEqual(row.note, "Late")

    def test_normal_day_pending_requests_only_append_note(self):
        attendance = SimpleNamespace(
            id=3,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 20),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 1),
            requested_data=json.dumps(
                {
                    "attendance_clock_in_date": "2026-03-03",
                    "attendance_clock_in": "08:12",
                    "__meta": {"current_scope": "IN"},
                }
            ),
            is_validate_request=True,
            is_validate_request_approved=False,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )
        work_req = SimpleNamespace(
            id=11,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.PENDING,
            scope=monthly_recap.WorkModeRequestScope.OUT,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(17, 10),
        )

        monthly_recap.Attendance.objects = FakeManager([attendance])
        monthly_recap.WorkModeRequest.objects = FakeManager([work_req])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertEqual(row.check_in, "08:20")
        self.assertEqual(row.check_out, "17:01")
        self.assertEqual(row.work_type, "WFO")
        self.assertIn("Attendance IN pending: 08:12", row.note)
        self.assertIn("On Duty OUT awaiting document upload: 17:10", row.note)

    def test_pending_create_request_does_not_fill_empty_check_in_or_check_out(self):
        pending_create_request = SimpleNamespace(
            id=31,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 12),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 5),
            requested_data=json.dumps(
                {
                    "attendance_clock_in_date": "2026-03-03",
                    "attendance_clock_in": "08:12",
                    "attendance_clock_out_date": "2026-03-03",
                    "attendance_clock_out": "17:05",
                    "__meta": {"current_scope": "FULL"},
                }
            ),
            is_validate_request=True,
            is_validate_request_approved=False,
            request_type="create_request",
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=False,
        )

        monthly_recap.Attendance.objects = FakeManager([pending_create_request])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertEqual(row.check_in, "—")
        self.assertEqual(row.check_out, "—")
        self.assertIn("Attendance IN pending: 08:12", row.note)
        self.assertIn("Attendance OUT pending: 17:05", row.note)

    def test_pending_create_request_without_requested_data_stays_empty_and_keeps_detailed_note(self):
        pending_create_request = SimpleNamespace(
            id=32,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 12),
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            requested_data=None,
            is_validate_request=True,
            is_validate_request_approved=False,
            request_type="create_request",
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=False,
        )

        monthly_recap.Attendance.objects = FakeManager([pending_create_request])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertEqual(row.check_in, "—")
        self.assertEqual(row.check_out, "—")
        self.assertIn("Attendance IN pending: 08:12", row.note)
        self.assertNotIn("Attendance correction pending", row.note)

    def test_pending_create_request_dict_requested_data_keeps_detailed_note(self):
        pending_create_request = SimpleNamespace(
            id=33,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 12),
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            requested_data={
                "attendance_clock_in_date": "2026-03-03",
                "attendance_clock_in": "08:12",
                "__meta": {"current_scope": "IN"},
            },
            is_validate_request=True,
            is_validate_request_approved=False,
            request_type="create_request",
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=False,
        )

        monthly_recap.Attendance.objects = FakeManager([pending_create_request])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertEqual(row.check_in, "—")
        self.assertIn("Attendance IN pending: 08:12", row.note)
        self.assertNotIn("Attendance correction pending", row.note)

    def test_pending_work_mode_linked_punch_is_ignored_for_final_time(self):
        pending_work_req = SimpleNamespace(
            id=41,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.PENDING,
            scope=monthly_recap.WorkModeRequestScope.IN,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(8, 0),
        )
        pending_linked_activity = SimpleNamespace(
            id=42,
            employee_id=self.employee,
            attendance_date=self.target_date,
            clock_in_date=self.target_date,
            clock_in=time(8, 0),
            in_datetime=datetime(2026, 3, 3, 8, 0),
            clock_out_date=None,
            clock_out=None,
            out_datetime=None,
            work_mode_request_id=pending_work_req,
        )

        monthly_recap.WorkModeRequest.objects = FakeManager([pending_work_req])
        monthly_recap.AttendanceActivity.objects = FakeManager([pending_linked_activity])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertEqual(row.check_in, "—")
        self.assertEqual(row.check_out, "—")
        self.assertIn("On Duty IN awaiting document upload: 08:00", row.note)

    def test_approved_request_out_of_window_is_not_applied_and_only_goes_to_note(self):
        attendance = SimpleNamespace(
            id=4,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(13, 5),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            requested_data=json.dumps(
                {
                    "attendance_clock_in_date": "2026-03-03",
                    "attendance_clock_in": "13:05",
                    "__meta": {"approved_scopes": ["IN"]},
                }
            ),
            is_validate_request=False,
            is_validate_request_approved=True,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )

        monthly_recap.Attendance.objects = FakeManager([attendance])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertEqual(row.check_in, "—")
        self.assertEqual(row.check_out, "17:00")
        self.assertIn("Approved but out of time limit (IN): 13:05", row.note)

    def test_pending_wfa_request_is_not_shown_in_note(self):
        wfa_req = SimpleNamespace(
            id=51,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            scope=monthly_recap.WorkModeRequestScope.FULL,
            mode=monthly_recap.AttendanceWorkMode.WFA,
        )

        monthly_recap.WorkModeRequest.objects = FakeManager([wfa_req])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03")
        row = self._find_row(rows, self.target_date)

        self.assertNotIn("WFA", row.note)
        self.assertEqual(row.check_in, "—")
        self.assertEqual(row.check_out, "—")

    def test_indonesian_on_duty_pending_without_attachment_uses_upload_wording_and_shift_times(self):
        on_duty_req = SimpleNamespace(
            id=52,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.PENDING,
            scope=monthly_recap.WorkModeRequestScope.FULL,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            files=SimpleNamespace(exists=lambda: False),
        )

        monthly_recap.WorkModeRequest.objects = FakeManager([on_duty_req])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03", language="id")
        row = self._find_row(rows, self.target_date)

        self.assertIn("Dinas Luar Penuh menunggu upload dokumen: 08:00, 17:00", row.note)

    def test_indonesian_on_duty_waiting_uses_approval_wording(self):
        on_duty_req = SimpleNamespace(
            id=53,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            scope=monthly_recap.WorkModeRequestScope.OUT,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            files=SimpleNamespace(exists=lambda: True),
        )

        monthly_recap.WorkModeRequest.objects = FakeManager([on_duty_req])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03", language="id")
        row = self._find_row(rows, self.target_date)

        self.assertIn("Dinas Luar Akhir menunggu persetujuan: 17:00", row.note)

    def test_indonesian_attendance_note_uses_final_wording(self):
        attendance = SimpleNamespace(
            id=54,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(13, 5),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            requested_data=json.dumps(
                {
                    "attendance_clock_in_date": "2026-03-03",
                    "attendance_clock_in": "13:05",
                    "__meta": {"approved_scopes": ["IN"]},
                }
            ),
            is_validate_request=False,
            is_validate_request_approved=True,
            shift_id="SHIFT-A",
            work_type_id=None,
            attendance_validated=True,
        )

        monthly_recap.Attendance.objects = FakeManager([attendance])

        rows = monthly_recap.get_monthly_attendance_rows(self.employee, "2026-03", language="id")
        row = self._find_row(rows, self.target_date)

        self.assertIn("Absensi Datang disetujui tetapi di luar batas waktu: 13:05", row.note)


if __name__ == "__main__":
    unittest.main(verbosity=2)
