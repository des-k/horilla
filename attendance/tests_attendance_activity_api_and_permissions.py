from datetime import date, time
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from rest_framework.test import APITestCase, APIRequestFactory, force_authenticate

from attendance.filters import AttendanceActivityFilter
from attendance.models import Attendance, AttendanceActivity, AttendanceChannel
from attendance.services.activity_sync import sync_single_session_activity
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from horilla_api.api_views.attendance import views as api_views


class _FakeActivityQuerySet(list):
    def select_related(self, *args, **kwargs):
        return self

    def all(self):
        return self

    def filter(self, **kwargs):
        items = list(self)
        employee = kwargs.get("employee_id")
        if employee is not None:
            items = [item for item in items if getattr(item, "employee_id", None) == employee]
        return _FakeActivityQuerySet(items)

    def order_by(self, *args, **kwargs):
        items = list(self)
        for key in reversed(args):
            reverse = key.startswith("-")
            attr = key[1:] if reverse else key
            items.sort(key=lambda item: getattr(item, attr), reverse=reverse)
        return _FakeActivityQuerySet(items)


class AttendanceActivityApiAndPermissionsTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.manager = SimpleNamespace(id=1)
        self.owner = SimpleNamespace(id=2)
        self.subordinate = SimpleNamespace(id=3)
        self.outsider = SimpleNamespace(id=4)
        self.owner_user = SimpleNamespace(is_authenticated=True, employee_get=self.owner, has_perm=lambda perm: False)
        self.manager_user = SimpleNamespace(is_authenticated=True, employee_get=self.manager, has_perm=lambda perm: False)
        self.admin_user = SimpleNamespace(is_authenticated=True, employee_get=self.manager, has_perm=lambda perm: True)
        self.activities = _FakeActivityQuerySet([
            SimpleNamespace(id=11, employee_id=self.owner, attendance_date=date(2026, 3, 14)),
            SimpleNamespace(id=12, employee_id=self.subordinate, attendance_date=date(2026, 3, 14)),
            SimpleNamespace(id=13, employee_id=self.outsider, attendance_date=date(2026, 3, 15)),
        ])

    def _dummy_serializer(self, obj, many=False):
        if many:
            return SimpleNamespace(data=[{"id": item.id, "employee_id": item.employee_id.id, "attendance_date": item.attendance_date.isoformat()} for item in obj])
        return SimpleNamespace(data={"id": obj.id, "employee_id": obj.employee_id.id, "attendance_date": obj.attendance_date.isoformat()})

    def test_activity_list_blocks_cross_employee_access_for_regular_employee(self):
        request = self.factory.get("/api/attendance/attendance-activity/")
        force_authenticate(request, user=self.owner_user)
        with patch.object(api_views.AttendanceActivity, "objects", self.activities), \
             patch.object(api_views, "permission_based_queryset", side_effect=Exception("fallback")), \
             patch.object(api_views, "AttendanceActivitySerializer", side_effect=self._dummy_serializer):
            response = api_views.AttendanceActivityView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data, [{"id": 11, "employee_id": 2, "attendance_date": "2026-03-14"}])

    def test_activity_list_allows_manager_only_for_subordinates(self):
        request = self.factory.get("/api/attendance/attendance-activity/")
        force_authenticate(request, user=self.manager_user)
        scoped = _FakeActivityQuerySet([self.activities[1]])
        with patch.object(api_views.AttendanceActivity, "objects", self.activities), \
             patch.object(api_views, "permission_based_queryset", return_value=scoped), \
             patch.object(api_views, "AttendanceActivitySerializer", side_effect=self._dummy_serializer):
            response = api_views.AttendanceActivityView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual([item["id"] for item in response.data], [12])

    def test_activity_list_allows_superuser_to_view_all_records(self):
        request = self.factory.get("/api/attendance/attendance-activity/")
        force_authenticate(request, user=self.admin_user)
        with patch.object(api_views.AttendanceActivity, "objects", self.activities), \
             patch.object(api_views, "permission_based_queryset", return_value=self.activities), \
             patch.object(api_views, "AttendanceActivitySerializer", side_effect=self._dummy_serializer):
            response = api_views.AttendanceActivityView.as_view()(request)
        self.assertEqual(response.status_code, 200)
        self.assertEqual({item["id"] for item in response.data}, {11, 12, 13})

    def test_activity_filter_support_includes_employee_and_date_range_fields(self):
        self.assertIn("employee_id", AttendanceActivityFilter.Meta.fields)
        self.assertIn("attendance_date_from", AttendanceActivityFilter.Meta.fields)
        self.assertIn("attendance_date_till", AttendanceActivityFilter.Meta.fields)



class AttendanceActivityApiIntegrationTests(AttendanceApiIntegrationMixin, APITestCase):
    def _call(self, user, params=None, pk=None):
        request = self.factory.get('/api/attendance/attendance-activity/', params or {})
        force_authenticate(request, user=user)
        view = api_views.AttendanceActivityView.as_view()
        if pk is not None:
            return view(request, pk=pk)
        return view(request)

    def test_activity_list_blocks_cross_employee_access_for_regular_employee(self):
        owner_user, owner = self.create_employee('Owner')
        _, outsider = self.create_employee('Outsider')
        owner_activity = AttendanceActivity.objects.create(employee_id=owner, attendance_date=date(2026, 3, 14))
        AttendanceActivity.objects.create(employee_id=outsider, attendance_date=date(2026, 3, 14))

        response = self._call(owner_user)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in response.data], [owner_activity.id])
        self.assertEqual({item['employee_id'] for item in response.data}, {owner.id})

    def test_activity_list_allows_manager_only_for_subordinates(self):
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)
        _, outsider = self.create_employee('Outsider')
        subordinate_activity = AttendanceActivity.objects.create(
            employee_id=subordinate,
            attendance_date=date(2026, 3, 14),
        )
        AttendanceActivity.objects.create(employee_id=outsider, attendance_date=date(2026, 3, 14))

        response = self._call(manager_user)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in response.data], [subordinate_activity.id])
        self.assertEqual({item['employee_id'] for item in response.data}, {subordinate.id})

    def test_activity_list_filters_by_employee_and_date_range(self):
        admin_user, _ = self.create_employee('Admin', is_superuser=True)
        _, owner = self.create_employee('Owner')
        _, other = self.create_employee('Other')
        AttendanceActivity.objects.create(employee_id=owner, attendance_date=date(2026, 3, 14))
        expected = AttendanceActivity.objects.create(employee_id=owner, attendance_date=date(2026, 3, 15))
        AttendanceActivity.objects.create(employee_id=other, attendance_date=date(2026, 3, 15))

        response = self._call(
            admin_user,
            params={
                'employee_id': owner.id,
                'attendance_date_from': '2026-03-15',
                'attendance_date_till': '2026-03-15',
            },
        )

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in response.data], [expected.id])
        self.assertEqual(response.data[0]['attendance_date'], '2026-03-15')

    def test_activity_sync_after_attendance_request_approve(self):
        owner_user, owner = self.create_employee('Owner')
        attendance = Attendance.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 16),
            attendance_clock_in_date=date(2026, 3, 16),
            attendance_clock_in=time(9, 30),
            attendance_clock_in_channel=AttendanceChannel.CORRECTION_REQUEST,
            request_type='update_request',
            is_validate_request=False,
            is_validate_request_approved=True,
        )
        activity = sync_single_session_activity(attendance)

        response = self._call(owner_user, pk=activity.id)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data['employee_id'], owner.id)
        self.assertEqual(response.data['clock_in'], '09:30:00')
        self.assertEqual(response.data['clock_in_channel'], AttendanceChannel.CORRECTION_REQUEST)
