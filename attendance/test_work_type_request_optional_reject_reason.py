from types import SimpleNamespace
from unittest.mock import patch

from django.test import RequestFactory, SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.services.work_type_request_actions import (
    WorkModeRequestActions,
    WorkModeRequestActionError,
)
from attendance.views import work_type_requests
from horilla_api.api_views.attendance import views as api_views


class WorkTypeRejectReasonOptionalParityTests(SimpleTestCase):
    databases = {'default'}

    def setUp(self):
        self.request_factory = RequestFactory()
        self.api_factory = APIRequestFactory()
        self.actor = SimpleNamespace(id=7)
        self.req = SimpleNamespace(id=88)
        self.user = SimpleNamespace(is_authenticated=True, is_active=True, is_superuser=False, employee_get=SimpleNamespace(is_active=True))

    def test_web_main_reject_without_reason_passes_none_remark(self):
        request = self.request_factory.post(
            '/attendance/work-type-request/88/reject',
            {'reason_code': 'MANUAL_REJECT', 'reason': ''},
            HTTP_HX_REQUEST='true',
        )
        request.user = self.user
        request.session = {}

        with patch.object(work_type_requests, '_request_actor_employee', return_value=self.actor), \
             patch.object(work_type_requests, 'get_object_or_404', return_value=self.req), \
             patch.object(work_type_requests, 'render', return_value=SimpleNamespace(content=b'')), \
             patch.object(work_type_requests.messages, 'success', lambda *args, **kwargs: None), \
             patch.object(work_type_requests.WorkModeRequestActions, 'reject_request') as reject_mock:
            response = work_type_requests.work_type_request_reject(request, self.req.id)

        self.assertIn(response.status_code, {200, 204})
        reject_mock.assert_called_once()
        self.assertIsNone(reject_mock.call_args.kwargs['remark'])

    def test_api_main_reject_without_reason_passes_none_remark(self):
        request = self.api_factory.put('/api/attendance/work-mode-request/88/reject', {}, format='json')
        force_authenticate(request, user=self.user)

        class DummySerializer:
            def __init__(self, obj, context=None):
                self.data = {'id': getattr(obj, 'id', None)}

        with patch.object(api_views, 'get_object_or_404', return_value=self.req), \
             patch.object(api_views, '_request_actor_employee', return_value=self.actor), \
             patch.object(api_views.WorkModeRequestRejectView, 'serializer_class', DummySerializer), \
             patch.object(api_views.WorkModeRequestActions, 'reject_request') as reject_mock:
            response = api_views.WorkModeRequestRejectView.as_view()(request, pk=self.req.id)

        self.assertEqual(response.status_code, 200)
        reject_mock.assert_called_once()
        self.assertIsNone(reject_mock.call_args.kwargs['remark'])

    def test_document_reject_requires_reason(self):
        req = SimpleNamespace(
            mode='on_duty',
            document_status='submitted',
            save=lambda *args, **kwargs: None,
        )
        version = SimpleNamespace(
            status='submitted',
            reviewed_by=None,
            reviewed_at=None,
            review_remark=None,
            version_number=1,
            save=lambda *args, **kwargs: None,
        )
        func = getattr(WorkModeRequestActions.reject_document, '__wrapped__', WorkModeRequestActions.reject_document)
        with patch('attendance.services.work_type_request_actions.can_reject_document', return_value=True), \
             patch.object(WorkModeRequestActions, '_current_version', return_value=version), \
             patch.object(WorkModeRequestActions, '_apply_current_version_to_request', lambda *args, **kwargs: None), \
             patch.object(WorkModeRequestActions, '_touch_action', lambda *args, **kwargs: None), \
             patch.object(WorkModeRequestActions, '_audit', lambda *args, **kwargs: None), \
             patch.object(WorkModeRequestActions, '_recompute', lambda *args, **kwargs: None):
            with self.assertRaises(WorkModeRequestActionError):
                func(req, actor=self.actor, request=SimpleNamespace(), remark='')
