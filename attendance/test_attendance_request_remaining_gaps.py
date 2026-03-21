from pathlib import Path

from django.core.exceptions import ValidationError
from django.test import SimpleTestCase

from attendance.services.attendance_correction_scope_rules import (
    build_requested_data_for_save,
    validate_new_request_scope,
)


class AttendanceCorrectionScopeRuleRemainingGapTests(SimpleTestCase):
    def test_merge_waiting_out_into_existing_waiting_in_promotes_scope_to_full_and_keeps_prior_values(self):
        existing = {
            "attendance_clock_in": "08:05:00",
            "__meta": {"current_scope": "IN", "approved_scopes": ["IN"]},
        }

        result = build_requested_data_for_save(
            new_payload={"attendance_clock_out": "17:15:00"},
            existing_requested_data=existing,
            incoming_scope="OUT",
            keep_existing_fields=True,
        )

        self.assertIsInstance(result, dict)
        self.assertEqual(result["attendance_clock_in"], "08:05:00")
        self.assertEqual(result["attendance_clock_out"], "17:15:00")
        self.assertEqual(result["__meta"]["current_scope"], "FULL")
        self.assertEqual(result["__meta"]["approved_scopes"], ["IN"])

    def test_fresh_write_from_legacy_string_payload_keeps_approved_scope_as_native_dict(self):
        existing = (
            '{"attendance_clock_in": "08:05:00", '
            '"__meta": {"current_scope": "IN", "approved_scopes": ["IN"]}}'
        )

        result = build_requested_data_for_save(
            new_payload={"attendance_clock_out": "17:15:00"},
            existing_requested_data=existing,
            incoming_scope="OUT",
            keep_existing_fields=False,
        )

        self.assertIsInstance(result, dict)
        self.assertEqual(result["attendance_clock_out"], "17:15:00")
        self.assertEqual(result["__meta"]["current_scope"], "OUT")
        self.assertEqual(result["__meta"]["approved_scopes"], ["IN"])

    def test_validate_new_request_scope_blocks_full_request_when_waiting_in_already_exists(self):
        with self.assertRaises(ValidationError) as ctx:
            validate_new_request_scope(
                existing_waiting_scope="IN",
                approved_scopes=[],
                incoming_scope="FULL",
            )

        self.assertIn("WAITING IN", str(ctx.exception))
        self.assertIn("only request OUT", str(ctx.exception))

    def test_validate_new_request_scope_blocks_full_request_when_in_already_approved(self):
        with self.assertRaises(ValidationError) as ctx:
            validate_new_request_scope(
                existing_waiting_scope="",
                approved_scopes=["IN"],
                incoming_scope="FULL",
            )

        self.assertIn("already been approved", str(ctx.exception))
        self.assertIn("only request OUT", str(ctx.exception))


class AttendanceRequestTemplateRegressionTests(SimpleTestCase):
    def test_my_request_table_keeps_cancel_button_waiting_only(self):
        source = Path("attendance/templates/attendance/attendance_requests/table_my.html").read_text()

        self.assertIn(
            "{% if r.is_validate_request and not r.is_validate_request_approved %}",
            source,
        )
        self.assertIn("cancel-validate-attendance-request", source)
        self.assertNotIn("approve-validate-attendance-request", source)
        self.assertNotIn("reject-validate-attendance-request", source)

    def test_approvals_table_keeps_waiting_actions_for_manager_side(self):
        source = Path("attendance/templates/attendance/attendance_requests/table_approvals.html").read_text()

        self.assertIn("{% trans \"WAITING\" %}", source)
        self.assertIn("reject-validate-attendance-request", source)
        self.assertIn("approve-validate-attendance-request", source)
        self.assertNotIn("cancel-validate-attendance-request", source)

    def test_attendance_request_view_gates_approval_tab_with_can_approve(self):
        source = Path("attendance/templates/attendance/attendance_requests/view.html").read_text()

        self.assertIn("{% if can_approve %}", source)
        self.assertIn("You do not have approval access for Attendance Requests.", source)


class AttendanceRequestDirectAttachmentIsolationTests(SimpleTestCase):
    def test_iter_request_attachments_stays_on_direct_many_to_many_path_only(self):
        source = Path("attendance/services/attendance_request_access.py").read_text()

        self.assertIn("attendance.request_attachments.all()", source)
        self.assertNotIn("AttendanceRequestComment", source)
        self.assertNotIn("comment.files", source)

    def test_attachment_modal_uses_direct_attachment_iterator_and_not_comment_flow(self):
        source = Path("attendance/views/requests.py").read_text()

        self.assertIn('"HTMX modal: show Attendance Request direct attachments."', source)
        self.assertIn("files = list(iter_request_attachments(attendance))", source)
        self.assertNotIn("create-attendance-request-comment", source)
