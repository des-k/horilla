from __future__ import annotations

import unittest
from pathlib import Path


BASE_DIR = Path(__file__).resolve().parents[1]


def _read(rel_path: str) -> str:
    return (BASE_DIR / rel_path).read_text(encoding='utf-8')


class Phase2ApprovalHistorySourceRegressionTests(unittest.TestCase):
    def test_work_type_document_review_queue_no_longer_keeps_verified_items_active(self):
        source = _read('attendance/services/work_type_request_rules.py')

        self.assertIn('DOCUMENT_REVIEW_DOCUMENT_STATUSES = {', source)
        self.assertIn('WorkModeRequestDocumentStatus.SUBMITTED', source)
        self.assertIn('WorkModeRequestDocumentStatus.PENDING_VERIFICATION', source)
        self.assertIn('WorkModeRequestDocumentStatus.REJECTED', source)
        self.assertNotIn('WorkModeRequestDocumentStatus.VERIFIED,', source)
        self.assertIn('return "document_review"', source)

    def test_attendance_request_api_supports_history_filters_by_request_date(self):
        source = _read('horilla_api/api_views/attendance/views.py')

        self.assertIn('approval_view = (request.GET.get("approval_view") or "").strip().lower()', source)
        self.assertIn('if approval_view == "history":', source)
        self.assertIn('history_month_start, history_month_end, _ = _parse_filter_month_range(', source)
        self.assertIn('attendance_date__range=(history_month_start, history_month_end)', source)
        self.assertIn('employee_id = (request.GET.get("employee_id") or "").strip()', source)
        self.assertIn('_attendance_history_status_filter(requests, request.GET.get("status"))', source)
        self.assertIn('response.data["employee_options"] = _approval_scope_employee_options(request, work_type=False)', source)

    def test_work_type_request_api_supports_history_filters_and_excludes_active_queues(self):
        source = _read('horilla_api/api_views/attendance/views.py')

        self.assertIn('queue = (request.GET.get("queue") or "approval").strip().lower()', source)
        self.assertIn('if queue == "history":', source)
        self.assertIn('history_month_start, history_month_end, _ = _parse_filter_month_range(', source)
        self.assertIn('start_date__lte=history_month_end, end_date__gte=history_month_start', source)
        self.assertIn('if queue_type in {"approval", "document_review"}:', source)
        self.assertIn('return qs.exclude(status=WorkModeRequestStatus.PENDING)', source)
        self.assertIn('response.data["employee_options"] = _approval_scope_employee_options(request, work_type=True)', source)

    def test_web_views_expose_approval_history_and_document_review_active_queue(self):
        attendance_view_source = _read('attendance/views/requests.py')
        work_type_view_source = _read('attendance/views/work_type_requests.py')

        self.assertIn('approval_history', attendance_view_source)
        self.assertIn('approval_subtab', attendance_view_source)
        self.assertIn('history_month', attendance_view_source)
        self.assertIn('history_status_options', attendance_view_source)

        self.assertIn('approval_history', work_type_view_source)
        self.assertIn('approval_subtab', work_type_view_source)
        self.assertIn('work_mode_request_document_review_q', work_type_view_source)
        self.assertIn('classify_work_mode_request_queue', work_type_view_source)
        self.assertIn('filtersubordinatesemployeemodel', attendance_view_source)
        self.assertIn('history_employees = Employee.objects.all()', attendance_view_source)
        self.assertIn('filtersubordinatesemployeemodel', work_type_view_source)
        self.assertIn('history_employees = Employee.objects.all()', work_type_view_source)

    def test_web_templates_render_nested_approval_history_tabs(self):
        attendance_template = _read('attendance/templates/attendance/attendance_requests/view.html')
        attendance_history_template = _read('attendance/templates/attendance/attendance_requests/table_approval_history.html')
        work_type_template = _read('attendance/templates/attendance/work_type_requests/view.html')

        self.assertIn('Approval History', attendance_template)
        self.assertIn('approval_subtab', attendance_template)
        self.assertIn('table_approval_history.html', attendance_template)
        self.assertIn('data-tab-group', attendance_template)
        self.assertIn('show_approval_tab', attendance_template)

        self.assertIn('attendance_date', attendance_history_template)
        self.assertIn('request_description', attendance_history_template)
        self.assertIn('history_attach_counts', attendance_history_template)
        self.assertIn('history_shift_info', attendance_history_template)
        self.assertNotIn('r.action_reason', attendance_history_template)
        self.assertNotIn('r.document_remark', attendance_history_template)
        self.assertNotIn('r.mode', attendance_history_template)
        self.assertNotIn('r.scope', attendance_history_template)

        self.assertIn('Approval History', work_type_template)
        self.assertIn('approval_subtab', work_type_template)
        self.assertIn('table_approval_history.html', work_type_template)
        self.assertIn('data-tab-group', work_type_template)
        self.assertIn('show_approval_tab', work_type_template)


if __name__ == '__main__':
    unittest.main()
