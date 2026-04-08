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
            "schedule": SimpleNamespace(id=1, minimum_working_hour="08:00"),
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

    def _get_recap(self, *, attendances=None, activities=None, requests=None, leaves=None, day_obj=None):
        day_obj = day_obj or SimpleNamespace(day=self.target_date.strftime("%A").lower())
        with patch.object(monthly_recap.Attendance, "objects", FakeManager(attendances or [])), \
             patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager(activities or [])), \
             patch.object(monthly_recap.WorkModeRequest, "objects", FakeManager(requests or [])), \
             patch.object(monthly_recap.LeaveRequest, "objects", FakeManager(leaves or [])), \
             patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([day_obj])):
            recap = monthly_recap.get_monthly_attendance_recap(self.employee, "2026-03")
        return recap, self._find_row(recap["rows"], self.target_date)

    def _raw_activity(
        self,
        *,
        id,
        in_time=None,
        out_time=None,
        in_mode=monthly_recap.AttendanceWorkMode.WFO,
        out_mode=monthly_recap.AttendanceWorkMode.WFO,
        work_mode_request_id=None,
    ):
        return SimpleNamespace(
            id=id,
            employee_id=self.employee,
            attendance_date=self.target_date,
            clock_in_date=self.target_date if in_time else None,
            clock_in=in_time,
            in_datetime=datetime.combine(self.target_date, in_time) if in_time else None,
            clock_out_date=self.target_date if out_time else None,
            clock_out=out_time,
            out_datetime=datetime.combine(self.target_date, out_time) if out_time else None,
            clock_in_channel="mobile" if in_time else None,
            clock_out_channel="mobile" if out_time else None,
            clock_in_mode=in_mode if in_time else None,
            clock_out_mode=out_mode if out_time else None,
            work_mode_request_id=work_mode_request_id,
            in_related_work_type_request_id=getattr(work_mode_request_id, "id", None) if work_mode_request_id else None,
            out_related_work_type_request_id=getattr(work_mode_request_id, "id", None) if work_mode_request_id else None,
        )

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
        self.assertEqual(row.note, "On Leave")
        self.assertEqual(row.check_in, "-")
        self.assertEqual(row.check_out, "-")

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
        self.assertEqual(row.note, "On Leave")
        self.assertEqual(row.check_in, "-")
        self.assertEqual(row.check_out, "-")
        self.assertEqual(row.late_minutes, 0)
        self.assertEqual(row.early_out_minutes, 0)

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


    def test_monthly_recap_ignores_waiting_request_and_prefers_raw_punch(self):
        pending_request_row = SimpleNamespace(
            id=30,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 5),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 5),
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
            requested_data={
                "attendance_clock_in_date": "2026-03-03",
                "attendance_clock_in": "08:05",
                "attendance_clock_out_date": "2026-03-03",
                "attendance_clock_out": "17:05",
                "__meta": {"current_scope": "FULL"},
            },
        )
        raw_activity = self._raw_activity(id=31, in_time=time(8, 1), out_time=time(17, 2))

        recap, row = self._get_recap(attendances=[pending_request_row], activities=[raw_activity])

        self.assertEqual(row.check_in, "08:01")
        self.assertEqual(row.check_out, "17:02")
        self.assertIn("Attendance IN pending: 08:05", row.note)
        self.assertIn("Attendance OUT pending: 17:05", row.note)
        self.assertEqual(recap["summary"]["late_minutes"], 1)
        self.assertEqual(recap["summary"]["early_out_minutes"], 0)

    def test_monthly_recap_uses_approved_request_when_it_is_final_truth(self):
        approved_attendance = SimpleNamespace(
            id=40,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 20),
            attendance_clock_in_channel=monthly_recap.APPROVED_REQUEST_CHANNEL,
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFA,
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(16, 40),
            attendance_clock_out_channel=monthly_recap.APPROVED_REQUEST_CHANNEL,
            attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFA,
            reconciliation_note="",
            reconciliation_source="",
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=True,
            is_validate_request=False,
            request_type="update_request",
            shift_id="SHIFT-A",
            requested_data={
                "attendance_clock_in": "08:20",
                "attendance_clock_out": "16:40",
                "__meta": {"approved_scopes": ["FULL"], "current_scope": "FULL"},
            },
        )
        raw_activity = self._raw_activity(id=41, in_time=time(8, 0), out_time=time(17, 0))

        recap, row = self._get_recap(attendances=[approved_attendance], activities=[raw_activity])

        self.assertEqual(row.check_in, "08:20")
        self.assertEqual(row.check_out, "16:40")
        self.assertEqual(row.work_type, "WFA")
        self.assertEqual(recap["summary"]["late_minutes"], 20)
        self.assertEqual(recap["summary"]["early_out_minutes"], 0)
        self.assertEqual(recap["summary"]["total_minutes"], 20)

    def test_monthly_recap_ignores_non_approved_work_type_request_and_terminal_request_effects(self):
        raw_activity = self._raw_activity(id=50, in_time=time(8, 0), out_time=time(17, 0), in_mode=None, out_mode=None)
        waiting_wfa = SimpleNamespace(
            id=51,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.WAITING_FOR_APPROVAL,
            scope=monthly_recap.WorkModeRequestScope.FULL,
            mode=monthly_recap.AttendanceWorkMode.WFA,
            planned_time=time(8, 0),
        )
        revoked_on_duty = SimpleNamespace(
            id=52,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.REVOKED,
            scope=monthly_recap.WorkModeRequestScope.FULL,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(8, 0),
        )

        recap, row = self._get_recap(activities=[raw_activity], requests=[waiting_wfa, revoked_on_duty])

        self.assertEqual(row.work_type, "WFO")
        self.assertEqual(row.note, "")
        self.assertEqual(recap["summary"], {"late_minutes": 0, "early_out_minutes": 0, "total_minutes": 0})

    def test_monthly_recap_reflects_approved_on_duty_effective_state(self):
        raw_activity = self._raw_activity(id=60, in_time=time(8, 0), out_time=time(17, 0), in_mode=None, out_mode=None)
        approved_on_duty = SimpleNamespace(
            id=61,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.APPROVED,
            scope=monthly_recap.WorkModeRequestScope.FULL,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(8, 0),
        )

        _, row = self._get_recap(activities=[raw_activity], requests=[approved_on_duty])

        self.assertEqual(row.work_type, "On Duty FULL")
        self.assertEqual(row.note, "")

    def test_monthly_recap_displays_linked_approved_in_scope_work_type_before_any_punch(self):
        approved_wfa_in = SimpleNamespace(
            id=90,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.APPROVED,
            scope=monthly_recap.WorkModeRequestScope.IN,
            mode=monthly_recap.AttendanceWorkMode.WFA,
            planned_time=time(10, 34),
        )
        canonical_attendance = SimpleNamespace(
            id=91,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=None,
            attendance_clock_in=None,
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            attendance_clock_in_mode=None,
            attendance_clock_out_mode=None,
            work_type_id=SimpleNamespace(work_type='WFO'),
            reconciliation_source='SOURCE_WFA',
            reconciliation_note='WFA reconciled under normal attendance rules',
            in_related_work_type_request_id=approved_wfa_in.id,
            out_related_work_type_request_id=None,
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=False,
            minimum_hour='07:30',
        )

        _, row = self._get_recap(attendances=[canonical_attendance], requests=[approved_wfa_in])

        self.assertEqual(row.check_in, '-')
        self.assertEqual(row.check_out, '-')
        self.assertEqual(row.work_type, 'IN: WFA<br>OUT: WFO')
        self.assertEqual(row.note, 'WFA reconciled under normal attendance rules')

    def test_monthly_recap_keeps_missing_checkout_penalty_for_verified_on_duty_in_only(self):
        verified_on_duty_in = SimpleNamespace(
            id=62,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.APPROVED,
            scope=monthly_recap.WorkModeRequestScope.IN,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(9, 12),
            document_status=monthly_recap.WorkModeRequestDocumentStatus.VERIFIED,
            effective_document_status=lambda: monthly_recap.WorkModeRequestDocumentStatus.VERIFIED,
        )
        canonical_attendance = SimpleNamespace(
            id=63,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(9, 12),
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            attendance_clock_out_mode=None,
            work_type_id=SimpleNamespace(work_type='WFA'),
            reconciliation_source='SOURCE_ON_DUTY',
            reconciliation_note='ON Duty final',
            in_related_work_type_request_id=verified_on_duty_in.id,
            out_related_work_type_request_id=None,
            late_minutes=72,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=False,
            minimum_hour='08:00',
        )

        _, row = self._get_recap(attendances=[canonical_attendance], requests=[verified_on_duty_in])

        self.assertEqual(row.work_type, 'IN: On Duty<br>OUT: WFO')
        self.assertEqual(row.check_in, '09:12')
        self.assertEqual(row.check_out, '-')
        self.assertEqual(row.late, '00:00')
        self.assertGreater(row.early_out_minutes, 0)


    def test_monthly_recap_does_not_drift_when_raw_history_contains_rejected_request_log(self):
        rejected_request = SimpleNamespace(
            id=70,
            employee_id=self.employee,
            start_date=self.target_date,
            end_date=self.target_date,
            status=monthly_recap.WorkModeRequestStatus.REJECTED,
            scope=monthly_recap.WorkModeRequestScope.IN,
            mode=monthly_recap.AttendanceWorkMode.ON_DUTY,
            planned_time=time(7, 50),
        )
        rejected_linked_raw = self._raw_activity(
            id=71,
            in_time=time(7, 50),
            work_mode_request_id=rejected_request,
        )
        valid_raw = self._raw_activity(id=72, in_time=time(8, 10), out_time=time(17, 0))

        recap, row = self._get_recap(activities=[rejected_linked_raw, valid_raw], requests=[rejected_request])

        self.assertEqual(row.check_in, "08:10")
        self.assertEqual(row.check_out, "17:00")
        self.assertEqual(recap["summary"]["late_minutes"], 10)

    def test_monthly_recap_reflects_first_half_leave_final_state(self):
        leave_request = SimpleNamespace(
            employee_id=self.employee,
            status="approved",
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown="first_half",
            end_date_breakdown="first_half",
        )
        raw_activity = self._raw_activity(id=80, in_time=time(11, 55), out_time=time(17, 0))
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        def half_day_rules(day, shift, day_obj, **kwargs):
            rules = self._default_shift_rules(day, shift, day_obj, **kwargs)
            rules["schedule"] = SimpleNamespace(
                id=2,
                enable_first_half_leave_rule=True,
                first_half_leave_latest_check_in_time=time(11, 50),
                enable_second_half_leave_rule=False,
            )
            return rules

        with patch("attendance.views.clock_in_out.get_shift_rules", half_day_rules):
            recap, row = self._get_recap(activities=[raw_activity], leaves=[leave_request], day_obj=day_obj)

        self.assertEqual(row.check_in, "11:55")
        self.assertEqual(row.check_out, "17:00")
        self.assertEqual(row.late_minutes, 5)
        self.assertIn("Approved First Half Leave", row.note)
        self.assertEqual(recap["summary"]["late_minutes"], 5)
        self.assertEqual(recap["summary"]["early_out_minutes"], 0)

    def test_monthly_recap_reflects_second_half_leave_final_state(self):
        leave_request = SimpleNamespace(
            employee_id=self.employee,
            status="approved",
            start_date=self.target_date,
            end_date=self.target_date,
            start_date_breakdown="second_half",
            end_date_breakdown="second_half",
        )
        raw_activity = self._raw_activity(id=90, in_time=time(8, 0), out_time=time(12, 5))
        day_obj = SimpleNamespace(day=self.target_date.strftime("%A").lower())

        def half_day_rules(day, shift, day_obj, **kwargs):
            rules = self._default_shift_rules(day, shift, day_obj, **kwargs)
            rules["schedule"] = SimpleNamespace(
                id=3,
                minimum_working_hour="08:00",
                enable_first_half_leave_rule=False,
                first_half_leave_latest_check_in_time=None,
                enable_second_half_leave_rule=True,
                start_time=time(8, 0),
                end_time=time(17, 0),
                break_start_time=None,
                break_end_time=None,
            )
            return rules

        with patch("attendance.views.clock_in_out.get_shift_rules", half_day_rules):
            recap, row = self._get_recap(activities=[raw_activity], leaves=[leave_request], day_obj=day_obj)

        self.assertEqual(row.check_in, "08:00")
        self.assertEqual(row.check_out, "12:05")
        self.assertEqual(row.early_out_minutes, 0)
        self.assertIn("Approved Second Half Leave", row.note)
        self.assertEqual(recap["summary"]["late_minutes"], 0)
        self.assertEqual(recap["summary"]["early_out_minutes"], 0)

    def test_monthly_recap_recompute_is_idempotent_for_same_final_state(self):
        approved_attendance = SimpleNamespace(
            id=100,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 15),
            attendance_clock_in_channel=monthly_recap.APPROVED_REQUEST_CHANNEL,
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFA,
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            attendance_clock_out_channel="biometric",
            attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFO,
            reconciliation_note="",
            reconciliation_source="",
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=True,
            is_validate_request=False,
            request_type="update_request",
            shift_id="SHIFT-A",
            requested_data={"attendance_clock_in": "08:15", "__meta": {"approved_scopes": ["IN"], "current_scope": "IN"}},
        )
        raw_activity = self._raw_activity(id=101, in_time=time(8, 0), out_time=time(17, 0))

        recap_one, row_one = self._get_recap(attendances=[approved_attendance], activities=[raw_activity])
        recap_two, row_two = self._get_recap(attendances=[approved_attendance], activities=[raw_activity])

        self.assertEqual(recap_one["summary"], recap_two["summary"])
        self.assertEqual(row_one.check_in, row_two.check_in)
        self.assertEqual(row_one.check_out, row_two.check_out)
        self.assertEqual(row_one.work_type, row_two.work_type)
        self.assertEqual(row_one.note, row_two.note)

    def test_missing_check_in_and_out_uses_half_minimum_for_late_and_early_out(self):
        recap, row = self._get_recap()

        self.assertEqual(row.late, "04:00")
        self.assertEqual(row.early_out, "04:00")
        self.assertEqual(row.late_minutes, 240)
        self.assertEqual(row.early_out_minutes, 240)

    def test_missing_check_out_uses_full_policy_early_out_duration(self):
        activity = self._raw_activity(id=41, in_time=time(8, 0))

        recap, row = self._get_recap(activities=[activity])

        self.assertEqual(row.late, "00:00")
        self.assertEqual(row.early_out, "04:00")
        self.assertEqual(row.early_out_minutes, 240)

    def test_missing_check_in_with_checkout_at_shift_end_has_no_early_out(self):
        activity = self._raw_activity(id=42, out_time=time(17, 0))

        recap, row = self._get_recap(activities=[activity])

        self.assertEqual(row.late, "04:00")
        self.assertEqual(row.early_out, "00:00")

    def test_missing_check_in_with_early_checkout_has_positive_early_out(self):
        activity = self._raw_activity(id=43, out_time=time(15, 0))

        recap, row = self._get_recap(activities=[activity])

        self.assertEqual(row.late, "04:00")
        self.assertEqual(row.early_out, "02:00")

    def test_late_and_early_out_ignore_activity_seconds_for_minute_precision(self):
        activity = self._raw_activity(
            id=45,
            in_time=time(10, 15, 18),
            out_time=time(15, 44, 59),
        )

        recap, row = self._get_recap(activities=[activity])

        self.assertEqual(row.late_minutes, 135)
        self.assertEqual(row.early_out_minutes, 16)
        self.assertEqual(row.late, "02:15")
        self.assertEqual(row.early_out, "00:16")
        self.assertEqual(recap["summary"]["late_minutes"], 135)
        self.assertEqual(recap["summary"]["early_out_minutes"], 16)

    def test_flexible_after_early_out_uses_dynamic_earliest_checkout_and_clamps_negative_values(self):
        activity = self._raw_activity(id=44, in_time=time(9, 0), out_time=time(17, 0))

        def flex_shift_rules(day, shift, day_obj, **kwargs):
            if day != self.target_date:
                return {"schedule": None, "start_time": None, "end_time": None}
            return {
                "schedule": SimpleNamespace(id=1, minimum_working_hour="08:00"),
                "start_time": time(8, 0),
                "end_time": time(17, 0),
                "shift_start_dt": datetime(2026, 3, 3, 8, 0),
                "shift_end_dt": datetime(2026, 3, 3, 17, 0),
                "check_in_window_start_dt": datetime(2026, 3, 3, 8, 0),
                "check_in_window_end_dt": datetime(2026, 3, 3, 12, 0),
                "check_out_window_start_dt": datetime(2026, 3, 3, 12, 0),
                "check_out_window_end_dt": datetime(2026, 3, 3, 23, 0),
                "cutoff_in_dt": datetime(2026, 3, 3, 12, 0),
                "grace_seconds": 3600,
                "clock_in_type": "after",
            }

        with patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager([activity])),              patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([SimpleNamespace(day=self.target_date.strftime("%A").lower())])),              patch("attendance.views.clock_in_out.get_shift_rules", flex_shift_rules),              patch("attendance.views.clock_in_out._resolve_grace_time", lambda schedule, shift: FakeGraceTime(False, 0)):
            recap = monthly_recap.get_monthly_attendance_recap(self.employee, "2026-03")

        row = self._find_row(recap["rows"], self.target_date)
        self.assertEqual(row.early_out, "00:00")
        self.assertEqual(row.early_out_minutes, 0)

        activity2 = self._raw_activity(id=45, in_time=time(9, 0), out_time=time(18, 0))
        with patch.object(monthly_recap.AttendanceActivity, "objects", FakeManager([activity2])),              patch.object(monthly_recap.EmployeeShiftDay, "objects", FakeManager([SimpleNamespace(day=self.target_date.strftime("%A").lower())])),              patch("attendance.views.clock_in_out.get_shift_rules", flex_shift_rules),              patch("attendance.views.clock_in_out._resolve_grace_time", lambda schedule, shift: FakeGraceTime(False, 0)):
            recap2 = monthly_recap.get_monthly_attendance_recap(self.employee, "2026-03")

        row2 = self._find_row(recap2["rows"], self.target_date)
        self.assertEqual(row2.early_out, "00:00")
        self.assertEqual(row2.early_out_minutes, 0)


    def test_monthly_recap_preserves_wfh_label(self):
        attendance = SimpleNamespace(
            id=99,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 0),
            attendance_clock_out_date=self.target_date,
            attendance_clock_out=time(17, 0),
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFH,
            attendance_clock_out_mode=monthly_recap.AttendanceWorkMode.WFH,
            reconciliation_note='WFH reconciled under normal attendance rules',
            reconciliation_source='SOURCE_WFH',
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=False,
            is_validate_request=False,
            request_type=None,
            shift_id='SHIFT-A',
        )
        recap, row = self._get_recap(attendances=[attendance])
        self.assertEqual(row.display_in_mode, monthly_recap.AttendanceWorkMode.WFH)
        self.assertEqual(row.display_out_mode, monthly_recap.AttendanceWorkMode.WFH)
        self.assertIn("WFH", row.work_type)

    def test_incomplete_approved_correction_uses_scheduled_mode_for_missing_session_not_stale_attendance_work_type(self):
        attendance = SimpleNamespace(
            id=111,
            employee_id=self.employee,
            attendance_date=self.target_date,
            attendance_clock_in_date=self.target_date,
            attendance_clock_in=time(8, 0),
            attendance_clock_out_date=None,
            attendance_clock_out=None,
            attendance_clock_in_mode=monthly_recap.AttendanceWorkMode.WFH,
            attendance_clock_out_mode=None,
            reconciliation_note='Approved Attendance Request Override',
            reconciliation_source='Attendance Request Override',
            late_minutes=0,
            early_out_minutes=0,
            attendance_validated=True,
            is_validate_request_approved=False,
            is_validate_request=False,
            request_type=None,
            shift_id='SHIFT-A',
            work_type_id=SimpleNamespace(work_type='WFO'),
        )

        with patch.object(monthly_recap, 'scheduled_attendance_mode', lambda employee, target_date: monthly_recap.AttendanceWorkMode.WFH):
            recap, row = self._get_recap(attendances=[attendance])

        self.assertEqual(row.display_in_mode, monthly_recap.AttendanceWorkMode.WFH)
        self.assertEqual(row.display_out_mode, monthly_recap.AttendanceWorkMode.WFH)
        self.assertNotIn('WFO', row.work_type)
        self.assertIn('WFH', row.work_type)

    def test_monthly_recap_does_not_normalize_legacy_remote_to_wfh(self):
        with patch.object(monthly_recap, 'scheduled_attendance_mode', lambda employee, target_date: monthly_recap.AttendanceWorkMode.WFA):
            recap, row = self._get_recap(attendances=[])
        self.assertNotEqual(getattr(row, 'scheduled_mode', monthly_recap.AttendanceWorkMode.WFA), monthly_recap.AttendanceWorkMode.WFH)
