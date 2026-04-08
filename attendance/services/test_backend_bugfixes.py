from __future__ import annotations

import inspect
from pathlib import Path
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
             patch("horilla_api.api_views.attendance.views.evaluate_attendance_access", return_value=SimpleNamespace(allowed=True, message=None)), \
             patch("horilla_api.api_views.attendance.views._api_today", return_value=attendance_date), \
             patch("horilla_api.api_views.attendance.views._api_resolve_attendance_date_and_day", return_value=(attendance_date, day, "08:00", None, None, "08:05", None)), \
             patch("horilla_api.api_views.attendance.views._resolve_punch_work_type", side_effect=[("wfa", "request", in_req), ("wfa", "request", in_req), ("on_duty", "request", out_req)]), \
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


class CanonicalFlowSourceInspectionTests(SimpleTestCase):
    def test_web_clock_out_does_not_manually_reapply_early_out_after_canonical_checkout(self):
        source = inspect.getsource(clock_in_out.clock_out)
        self.assertNotIn('late_come_early_out.filter(type="early_out")', source)
        self.assertNotIn('schedule = _get_schedule(shift, day)', source)

    def test_api_clock_out_does_not_manually_reapply_early_out_after_canonical_checkout(self):
        from horilla_api.api_views.attendance.views import ClockOutAPIView

        source = inspect.getsource(ClockOutAPIView.post)
        self.assertNotIn('late_come_early_out.filter(type="early_out")', source)
        self.assertNotIn('AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance, type="early_out").delete()', source)

    def test_request_restore_helpers_delegate_to_snapshot_restore_before_canonical_normalization(self):
        from attendance.views.requests import _restore_request_back_to_raw as web_restore
        from horilla_api.api_views.attendance.views import _restore_request_back_to_raw as api_restore

        web_source = inspect.getsource(web_restore)
        api_source = inspect.getsource(api_restore)

        self.assertIn('restore_raw_state_after_request', web_source)
        self.assertIn('restore_raw_state_after_request', api_source)
        self.assertNotIn('clear_request_override_and_recompute', web_source)
        self.assertNotIn('clear_request_override_and_recompute', api_source)

    def test_request_cancel_and_reject_handlers_no_longer_delete_derived_rows_manually(self):
        from attendance.views.requests import cancel_attendance_request, reject_validate_attendance_request
        from horilla_api.api_views.attendance.views import AttendanceRequestCancelView, AttendanceRequestRejectView

        self.assertNotIn('AttendanceActivity.objects.filter(', inspect.getsource(cancel_attendance_request))
        self.assertNotIn('AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()', inspect.getsource(cancel_attendance_request))
        self.assertNotIn('AttendanceActivity.objects.filter(', inspect.getsource(reject_validate_attendance_request))
        self.assertNotIn('AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()', inspect.getsource(reject_validate_attendance_request))
        self.assertNotIn('AttendanceActivity.objects.filter(', inspect.getsource(AttendanceRequestCancelView.put))
        self.assertNotIn('AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()', inspect.getsource(AttendanceRequestCancelView.put))
        self.assertNotIn('AttendanceActivity.objects.filter(', inspect.getsource(AttendanceRequestRejectView.put))
        self.assertNotIn('AttendanceLateComeEarlyOut.objects.filter(attendance_id=attendance).delete()', inspect.getsource(AttendanceRequestRejectView.put))

    def test_raw_clock_flows_do_not_snapshot_minimum_hour_before_canonical_reconcile(self):
        in_source = inspect.getsource(clock_in_out.clock_in_attendance_and_activity)
        out_source = inspect.getsource(clock_in_out.clock_out_attendance_and_activity)

        self.assertNotIn('attendance.minimum_hour = minimum_hour', in_source)
        self.assertNotIn('attendance.minimum_hour = minimum_hour', out_source)
        self.assertNotIn('"minimum_hour": minimum_hour', in_source)
        self.assertNotIn('"minimum_hour": minimum_hour', out_source)

    def test_web_clock_in_does_not_manually_reapply_late_come_before_reconcile(self):
        source = inspect.getsource(clock_in_out.clock_in_attendance_and_activity)
        self.assertNotIn('late_come(', source)
        self.assertNotIn('attendance_created and accept_in', source)

    def test_leave_signal_paths_still_delegate_to_canonical_range_recompute(self):
        from leave import signals as leave_signals

        self.assertIn('recompute_attendance_range', inspect.getsource(leave_signals._reconcile_leave_related_punches))

    def test_work_type_actions_recompute_canonical_range_for_revoke_and_document_transitions(self):
        view_source = Path('attendance/views/work_type_requests.py').read_text()
        action_source = Path('attendance/services/work_type_request_actions.py').read_text()
        self.assertIn('def work_type_request_revoke', view_source)
        self.assertIn('def work_type_request_document_action', view_source)
        self.assertIn('def revoke_request', action_source)
        self.assertIn('def verify_document', action_source)
        self.assertIn('def reject_document', action_source)
        self.assertIn('def reopen_document', action_source)
        self.assertIn('WorkModeRequestActions._recompute(req)', action_source)

        from horilla_api.api_views.attendance.views import WorkModeRequestDocumentActionView
        api_source = inspect.getsource(WorkModeRequestDocumentActionView.put)
        self.assertIn('WorkModeRequestActions.', api_source)
        self.assertNotIn('recompute_attendance_range(', api_source)

    def test_monthly_pdf_export_uses_shared_monthly_recap_service(self):
        source = Path('attendance/views/views.py').read_text()
        self.assertIn('def attendance_employee_month_export_pdf', source)
        self.assertIn('get_monthly_attendance_recap(employee, month, language=lang)', source)


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


class BiometricWorkModeBugfixTests(SimpleTestCase):
    def test_resolve_biometric_work_mode_prefers_approved_request(self):
        from attendance.services.work_type_request_rules import resolve_biometric_work_mode

        employee = SimpleNamespace(id=1, employee_work_info=SimpleNamespace(work_type_id=SimpleNamespace(work_type="WFO")))
        approved_request = SimpleNamespace(mode="wfa")
        manager = MagicMock()
        qs = MagicMock()
        qs.order_by.return_value.first.return_value = approved_request
        manager.filter.return_value = qs

        with patch("attendance.services.work_type_request_rules.WorkModeRequest.objects", manager):
            resolved = resolve_biometric_work_mode(employee, date(2026, 3, 14))

        self.assertEqual(resolved.mode, "wfa")
        self.assertEqual(resolved.source, "approved_request")
        self.assertIs(resolved.request, approved_request)

    def test_resolve_biometric_work_mode_uses_schedule_without_request(self):
        from attendance.services.work_type_request_rules import resolve_biometric_work_mode

        employee = SimpleNamespace(id=1, employee_work_info=SimpleNamespace(work_type_id=SimpleNamespace(work_type="Work From Anywhere")))
        manager = MagicMock()
        qs = MagicMock()
        qs.order_by.return_value.first.return_value = None
        manager.filter.return_value = qs

        with patch("attendance.services.work_type_request_rules.WorkModeRequest.objects", manager):
            resolved = resolve_biometric_work_mode(employee, date(2026, 3, 14))

        self.assertEqual(resolved.mode, "wfa")
        self.assertEqual(resolved.source, "schedule")
        self.assertIsNone(resolved.request)

    def test_resolve_biometric_work_mode_falls_back_to_wfo_only_when_unknown(self):
        from attendance.services.work_type_request_rules import resolve_biometric_work_mode

        employee = SimpleNamespace(id=1, employee_work_info=SimpleNamespace(work_type_id=SimpleNamespace(work_type="Mystery")))
        manager = MagicMock()
        qs = MagicMock()
        qs.order_by.return_value.first.return_value = None
        manager.filter.return_value = qs

        with patch("attendance.services.work_type_request_rules.WorkModeRequest.objects", manager):
            resolved = resolve_biometric_work_mode(employee, date(2026, 3, 14))

        self.assertEqual(resolved.mode, "wfo")
        self.assertEqual(resolved.source, "fallback_wfo")

    def test_clock_in_biometric_resolves_schedule_mode_and_updates_raw_punch(self):
        raw_punch = SimpleNamespace(source="biometric")
        request = SimpleNamespace(raw_punch_history=raw_punch)
        employee = SimpleNamespace()
        update_calls = []
        resolved = SimpleNamespace(mode="wfa", request=None)

        with patch("attendance.views.clock_in_out.resolve_biometric_work_mode", return_value=resolved),              patch("attendance.views.clock_in_out.update_punch_history", side_effect=lambda *args, **kwargs: update_calls.append(kwargs)):
            mode, req = clock_in_out._resolve_biometric_mode_context(request, employee, date(2026, 3, 14))

        self.assertEqual(mode, "wfa")
        self.assertIsNone(req)
        self.assertEqual(update_calls[-1]["attendance_date"], date(2026, 3, 14))
        self.assertEqual(update_calls[-1]["work_mode"], "wfa")
        self.assertIsNone(update_calls[-1]["related_work_mode_request"])

    def test_clock_out_biometric_resolves_approved_request_and_updates_raw_punch(self):
        work_request = SimpleNamespace(id=91, mode="on_duty")
        raw_punch = SimpleNamespace(source="biometric")
        request = SimpleNamespace(raw_punch_history=raw_punch)
        employee = SimpleNamespace()
        update_calls = []
        resolved = SimpleNamespace(mode="on_duty", request=work_request)

        with patch("attendance.views.clock_in_out.resolve_biometric_work_mode", return_value=resolved),              patch("attendance.views.clock_in_out.update_punch_history", side_effect=lambda *args, **kwargs: update_calls.append(kwargs)):
            mode, req = clock_in_out._resolve_biometric_mode_context(request, employee, date(2026, 3, 14))

        self.assertEqual(mode, "on_duty")
        self.assertIs(req, work_request)
        self.assertEqual(update_calls[-1]["work_mode"], "on_duty")
        self.assertIs(update_calls[-1]["related_work_mode_request"], work_request)

    def test_reconciliation_prefers_approved_work_request_mode(self):
        from attendance.services import reconciliation

        mode = reconciliation._resolve_final_work_mode(
            employee="EMP",
            attendance_date=date(2026, 3, 14),
            approved_work_request=SimpleNamespace(mode="wfa"),
            accepted_in_punch=SimpleNamespace(work_mode="on_duty"),
        )

        self.assertEqual(mode, "wfa")

    def test_reconciliation_uses_raw_punch_mode_before_schedule(self):
        from attendance.services import reconciliation

        with patch("attendance.services.work_type_request_rules.resolve_biometric_work_mode", return_value=SimpleNamespace(mode="wfa")):
            mode = reconciliation._resolve_final_work_mode(
                employee="EMP",
                attendance_date=date(2026, 3, 14),
                accepted_in_punch=SimpleNamespace(work_mode="on_duty"),
                accepted_out_punch=SimpleNamespace(work_mode=None),
            )

        self.assertEqual(mode, "on_duty")

    def test_reconciliation_uses_schedule_when_raw_mode_missing(self):
        from attendance.services import reconciliation

        with patch("attendance.services.work_type_request_rules.resolve_biometric_work_mode", return_value=SimpleNamespace(mode="wfa")):
            mode = reconciliation._resolve_final_work_mode(
                employee="EMP",
                attendance_date=date(2026, 3, 14),
                accepted_in_punch=SimpleNamespace(work_mode=None),
                accepted_out_punch=SimpleNamespace(work_mode=None),
            )

        self.assertEqual(mode, "wfa")

    def test_helper_source_uses_biometric_mode_resolver_instead_of_hardcoded_wfo(self):
        source = Path("attendance/views/clock_in_out.py").read_text()
        self.assertIn('_resolve_biometric_mode_context(request, employee, attendance_date)', source)
        self.assertIn('work_mode_request=biometric_request', source)

    def test_clock_in_enriches_biometric_raw_punch_before_access_and_cutoff_returns(self):
        source = Path("attendance/views/clock_in_out.py").read_text()
        segment = source[source.index('def clock_in(request):'):source.index('def clock_out(request):')]
        resolver_pos = segment.index('_resolve_biometric_mode_context(request, employee, attendance_date)')
        access_pos = segment.index('access = evaluate_attendance_access')
        cutoff_pos = segment.index('cutoff_in_dt = _calc_cutoff_in_dt')
        self.assertLess(resolver_pos, access_pos)
        self.assertLess(resolver_pos, cutoff_pos)

    def test_clock_out_enriches_biometric_raw_punch_before_access_and_cutoff_returns(self):
        source = Path("attendance/views/clock_in_out.py").read_text()
        segment = source[source.index('def clock_out(request):'):]
        resolver_pos = segment.index('_resolve_biometric_mode_context(request, employee, attendance_date)')
        access_pos = segment.index('access = evaluate_attendance_access')
        cutoff_pos = segment.index('cutoff_out_dt = _calc_cutoff_out_dt')
        self.assertLess(resolver_pos, access_pos)
        self.assertLess(resolver_pos, cutoff_pos)


class WorkTypeRequestWfaDocumentPolicyTests(SimpleTestCase):
    def _request(self, username='owner'):
        user = SimpleNamespace(username=username)
        return SimpleNamespace(user=user)

    def _req(self, *, status, mode='wfa'):
        employee_user = SimpleNamespace(username='owner')
        employee = SimpleNamespace(employee_user_id=employee_user)
        return SimpleNamespace(status=status, mode=mode, employee_id=employee, employee_id_id=1)

    def test_wfa_can_upload_only_while_waiting_for_approval(self):
        from attendance.models import WorkModeRequestStatus
        from attendance.services.work_type_request_permissions import can_upload_document

        request = self._request()
        self.assertTrue(can_upload_document(request, self._req(status=WorkModeRequestStatus.WAITING_FOR_APPROVAL)))
        self.assertFalse(can_upload_document(request, self._req(status=WorkModeRequestStatus.APPROVED)))
        self.assertFalse(can_upload_document(request, self._req(status=WorkModeRequestStatus.REJECTED)))
        self.assertFalse(can_upload_document(request, self._req(status=WorkModeRequestStatus.REVOKED)))
        self.assertFalse(can_upload_document(request, self._req(status=WorkModeRequestStatus.CANCELED)))

    def test_on_duty_upload_rule_is_not_broken_by_wfa_patch(self):
        from attendance.models import AttendanceWorkMode, WorkModeRequestStatus
        from attendance.services.work_type_request_permissions import can_upload_document

        request = self._request()
        req = self._req(status=WorkModeRequestStatus.APPROVED, mode=AttendanceWorkMode.ON_DUTY)
        req.document_status = 'submitted'
        req.effective_document_status = lambda: 'submitted'
        self.assertTrue(can_upload_document(request, req))

    def test_serializer_for_wfa_never_exposes_document_review_actions(self):
        from attendance.models import WorkModeRequestStatus
        from horilla_api.api_serializers.attendance.serializers import WorkModeRequestSerializer

        request = self._request()
        req = self._req(status=WorkModeRequestStatus.APPROVED)
        serializer = WorkModeRequestSerializer(context={'request': request})
        self.assertFalse(serializer.get_can_verify_document(req))
        self.assertFalse(serializer.get_can_reject_document(req))
        self.assertFalse(serializer.get_can_reopen_document(req))
        self.assertFalse(serializer.get_can_upload_document(req))

    def test_legacy_destructive_helpers_are_removed_from_active_layers(self):
        api_source = Path('horilla_api/api_views/attendance/views.py').read_text()
        web_source = Path('attendance/views/work_type_requests.py').read_text()
        self.assertNotIn('def _attach_files(', api_source)
        self.assertNotIn('obj.files.clear()', api_source)
        self.assertNotIn('def _save_on_duty_uploads(', web_source)
        self.assertNotIn('req.files.clear()', web_source)



class ScheduleMinimumHourHelperTests(SimpleTestCase):
    def test_schedule_minimum_hour_for_date_prefers_shift_schedule(self):
        from attendance.methods.utils import schedule_minimum_hour_for_date

        shift = SimpleNamespace(id=1)
        day = SimpleNamespace()
        with patch('attendance.methods.utils.EmployeeShiftDay.objects.get', return_value=day), \
             patch('attendance.methods.utils.shift_schedule_today', return_value=('07:30', None, None)), \
             patch('attendance.methods.utils.attendance_day_checking', return_value='07:30') as day_check:
            value = schedule_minimum_hour_for_date(date(2026, 4, 2), shift, fallback='09:00')

        self.assertEqual(value, '07:30')
        day_check.assert_called_once_with('2026-04-02', '07:30')

    def test_schedule_minimum_hour_for_date_falls_back_when_schedule_missing(self):
        from attendance.methods.utils import schedule_minimum_hour_for_date

        shift = SimpleNamespace(id=1)
        with patch('attendance.methods.utils.EmployeeShiftDay.objects.get', side_effect=Exception('missing')):
            value = schedule_minimum_hour_for_date(date(2026, 4, 2), shift, fallback='09:00')

        self.assertEqual(value, '09:00')
