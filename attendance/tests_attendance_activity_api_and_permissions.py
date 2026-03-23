from datetime import date
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.filters import AttendanceActivityFilter
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
