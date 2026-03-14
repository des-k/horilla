from __future__ import annotations

import inspect
from datetime import date, datetime

from django.utils import timezone
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.core.exceptions import ValidationError
from django.test import SimpleTestCase

from attendance.models import Attendance, EmployeeShiftDay
from attendance.views import clock_in_out
from horilla.models import HorillaModel


class ClockInPunchHistoryBugfixTests(SimpleTestCase):
    def test_api_clock_in_stores_in_mode_and_request_on_raw_punch(self):
        from horilla_api.api_views.attendance.views import ClockInAPIView

        attendance_date = date(2026, 3, 14)
        dt_now = datetime(2026, 3, 14, 8, 5)
        employee = SimpleNamespace(employee_work_info=SimpleNamespace(work_type_id="wfa"))
        work_info = SimpleNamespace(shift_id="SHIFT")
        day = SimpleNamespace(id=1)
        punch_log = SimpleNamespace()
        attendance = SimpleNamespace(reconciliation_source="mobile")
        in_req = SimpleNamespace(id=11)
        out_req = SimpleNamespace(id=22)
        request = SimpleNamespace(FILES={}, data={}, POST={}, user=SimpleNamespace(username="user"))
        update_calls = []

        def _capture_update(*args, **kwargs):
            update_calls.append((args, kwargs))

        manager = MagicMock()
        qs = MagicMock()
        qs.first.side_effect = [None, attendance]
        manager.filter.return_value = qs

        with patch("horilla_api.api_views.attendance.views._api_now", return_value=dt_now), \
             patch("horilla_api.api_views.attendance.views._parse_location_payload", return_value=None), \
             patch("horilla_api.api_views.attendance.views.employee_exists", return_value=(employee, work_info)), \
             patch("horilla_api.api_views.attendance.views.create_mobile_punch_history", return_value=punch_log), \
             patch("horilla_api.api_views.attendance.views.update_punch_history", side_effect=_capture_update), \
             patch("horilla_api.api_views.attendance.views._is_attendance_exempt_manager", return_value=False), \
             patch("horilla_api.api_views.attendance.views._api_today", return_value=attendance_date), \
             patch("horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day", return_value=(attendance_date, day, "08:00", None, None, "08:05", None)), \
             patch("horilla_api.api_views.attendance.views._resolve_effective_work_type", side_effect=[("wfa", "request", in_req), ("wfa", "request", in_req), ("on_duty", "request", out_req)]), \
             patch("horilla_api.api_views.attendance.views._is_punch_allowed", return_value=True), \
             patch("horilla_api.api_views.attendance.views.cio.get_shift_rules", return_value={"cutoff_in_dt": None, "check_in_window_start_dt": None, "check_in_window_end_dt": None}), \
             patch("horilla_api.api_views.attendance.views.auto_reject_wfa_waiting_for_date"), \
             patch("horilla_api.api_views.attendance.views._requires_proof", return_value=False), \
             patch("horilla_api.api_views.attendance.views.clock_in_attendance_and_activity"), \
             patch("horilla_api.api_views.attendance.views.reconcile_attendance_punches"), \
             patch("horilla_api.api_views.attendance.views.Attendance.objects", manager):
            response = ClockInAPIView().post(request)

        self.assertEqual(response.status_code, 200)
        final_update = update_calls[-1][1]
        self.assertEqual(final_update["work_mode"], "wfa")
        self.assertIs(final_update["related_work_mode_request"], in_req)


class ClockOutWindowBugfixTests(SimpleTestCase):
    databases = {"default"}
    def test_invalid_early_checkout_is_rejected_before_any_persistence(self):
        employee = SimpleNamespace(employee_work_info=SimpleNamespace(work_type_id="wfa"))
        shift = SimpleNamespace(id=1)
        day = SimpleNamespace(id=1)
        out_dt = timezone.make_aware(datetime(2026, 3, 14, 15, 0))

        with patch("attendance.views.clock_in_out.shift_schedule_today", return_value=("08:00", None, None)), \
             patch("attendance.views.clock_in_out.get_shift_rules", return_value={"check_out_window_start_dt": timezone.make_aware(datetime(2026, 3, 14, 16, 45)), "shift_start_dt": timezone.make_aware(datetime(2026, 3, 14, 8, 0))}), \
             patch("attendance.views.clock_in_out._locked_attendance") as locked_attendance, \
             patch("attendance.views.clock_in_out._locked_activity") as locked_activity, \
             patch("attendance.views.clock_in_out.assign_raw_punch_to_attendance") as assign_raw:
            with self.assertRaisesMessage(ValidationError, "Check-out window has not started yet."):
                clock_in_out.clock_out_attendance_and_activity(
                    employee=employee,
                    attendance_date=date(2026, 3, 14),
                    shift=shift,
                    minimum_hour="08:00",
                    out_datetime=out_dt,
                    day=day,
                )

        locked_attendance.assert_not_called()
        locked_activity.assert_not_called()
        assign_raw.assert_not_called()

    def test_dead_rejected_out_status_logic_is_removed_from_checkout_flow(self):
        source = inspect.getsource(clock_in_out.clock_out_attendance_and_activity)
        self.assertNotIn('attendance.out_attendance_status = "REJECTED"', source)
        self.assertNotIn('EARLY_CHECKOUT_BEFORE_SHIFT_END', source)
        self.assertNotIn('EARLY_CHECKOUT_BEFORE_CUTOFF_IN', source)


class AttendanceSaveBugfixTests(SimpleTestCase):
    def test_snapshot_only_update_skips_heavy_recalculation(self):
        attendance = Attendance(request_restore_snapshot={"in": {"foo": "bar"}})

        with patch("attendance.models.compress_model_image_field") as compress, \
             patch.object(Attendance, "update_attendance_overtime") as update_ot, \
             patch.object(Attendance, "adjust_minimum_hour") as adjust_minimum, \
             patch.object(Attendance, "handle_overtime_conditions") as handle_conditions, \
             patch.object(HorillaModel, "save", return_value=None) as parent_save:
            attendance.save(update_fields=["request_restore_snapshot"])

        compress.assert_not_called()
        update_ot.assert_not_called()
        adjust_minimum.assert_not_called()
        handle_conditions.assert_not_called()
        parent_save.assert_called_once()
        self.assertEqual(parent_save.call_args.kwargs["update_fields"], ["request_restore_snapshot"])

    def test_real_attendance_field_update_keeps_recalculation_active(self):
        employee_ot = SimpleNamespace(overtime_second=0, overtime="00:00", save=MagicMock())
        overtime_manager = MagicMock()
        overtime_manager.filter.return_value.first.side_effect = [employee_ot, employee_ot]
        employee = SimpleNamespace(employee_overtime=overtime_manager)
        attendance = Attendance(
            attendance_date=date(2026, 3, 14),
            minimum_hour="08:00",
            attendance_worked_hour="08:00",
            attendance_overtime="00:00",
        )
        attendance.employee_id_id = 1
        attendance._state.fields_cache["employee_id"] = employee
        attendance.pk = 99
        attendance.attendance_overtime_approve = False
        attendance.approved_overtime_second = 0

        shift_day = EmployeeShiftDay(day="saturday")
        with patch("attendance.models.compress_model_image_field"),              patch.object(Attendance, "update_attendance_overtime") as update_ot,              patch("attendance.models.EmployeeShiftDay.objects.get", return_value=shift_day),              patch.object(Attendance, "adjust_minimum_hour"),              patch.object(Attendance, "handle_overtime_conditions"),              patch("attendance.models.Attendance.objects.get", return_value=SimpleNamespace(attendance_overtime_approve=False)),              patch.object(Attendance, "update_ot"),              patch.object(HorillaModel, "save", return_value=None) as parent_save:
            attendance.save(update_fields=["attendance_clock_out"])

        update_ot.assert_called_once()
        saved_fields = set(parent_save.call_args.kwargs["update_fields"])
        self.assertIn("attendance_clock_out", saved_fields)
        self.assertIn("attendance_overtime", saved_fields)
        self.assertIn("overtime_second", saved_fields)
        self.assertIn("at_work_second", saved_fields)



class StartupSafetyBugfixTests(SimpleTestCase):
    def test_base_app_ready_skips_seed_query_when_table_is_missing(self):
        from base.apps import BaseConfig
        import base

        config = BaseConfig("base", base)
        with patch.object(BaseConfig, "_table_exists", return_value=False), \
             patch("base.models.EmployeeShiftDay.objects.exists", side_effect=AssertionError("must not query")):
            config.ready()

    def test_base_post_migrate_handler_returns_when_required_tables_are_missing(self):
        from base.signals import ensure_default_company_and_shift

        sender = SimpleNamespace(label="base")
        with patch("base.signals._table_exists", return_value=False):
            self.assertIsNone(ensure_default_company_and_shift(sender=sender, using="default"))

    def test_horilla_automations_ready_skips_startup_when_table_is_missing(self):
        from horilla_automations.apps import HorillaAutomationConfig
        import horilla_automations

        config = HorillaAutomationConfig("horilla_automations", horilla_automations)
        with patch("horilla_automations.apps.sys.argv", ["manage.py", "runserver"]),              patch.object(HorillaAutomationConfig, "_table_exists", return_value=False),              patch("horilla_automations.signals.start_automation", side_effect=AssertionError("must not start")):
            config.ready()
