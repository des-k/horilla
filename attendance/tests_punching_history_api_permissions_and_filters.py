from datetime import datetime
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from django.utils import timezone
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import AttendancePunchSource
from horilla_api.api_views.attendance import views as api_views


class _FakePunchQuerySet(list):
    def select_related(self, *args, **kwargs):
        return self

    def all(self):
        return self

    def filter(self, **kwargs):
        items = list(self)
        for key, value in kwargs.items():
            if key == "punch_timestamp__date__gte":
                items = [item for item in items if item.punch_timestamp.date() >= value]
            elif key == "punch_timestamp__date__lte":
                items = [item for item in items if item.punch_timestamp.date() <= value]
            elif key == "employee_id_id":
                items = [item for item in items if getattr(getattr(item, "employee_id", None), "id", None) == value]
            elif key == "source":
                items = [item for item in items if item.source == value]
            elif key == "accepted_to_attendance":
                items = [item for item in items if item.accepted_to_attendance == value]
        return _FakePunchQuerySet(items)

    def order_by(self, *args, **kwargs):
        items = list(self)
        for key in reversed(args):
            reverse = key.startswith("-")
            attr = key[1:] if reverse else key
            if attr == "punch_timestamp":
                items.sort(key=lambda item: item.punch_timestamp, reverse=reverse)
            elif attr == "id":
                items.sort(key=lambda item: item.id, reverse=reverse)
        return _FakePunchQuerySet(items)


class AttendancePunchingHistoryApiPermissionsAndFiltersTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.owner = SimpleNamespace(id=2, employee_first_name="Owner", employee_last_name="User")
        self.subordinate = SimpleNamespace(id=3, employee_first_name="Sub", employee_last_name="User")
        self.outsider = SimpleNamespace(id=4, employee_first_name="Out", employee_last_name="User")
        self.owner_user = SimpleNamespace(is_authenticated=True, employee_get=self.owner, is_superuser=False, has_perm=lambda perm: False)
        self.manager_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=1), is_superuser=False, has_perm=lambda perm: False)
        self.admin_user = SimpleNamespace(is_authenticated=True, employee_get=SimpleNamespace(id=99), is_superuser=True, has_perm=lambda perm: True)
        self.records = _FakePunchQuerySet([
            SimpleNamespace(id=21, employee_id=self.owner, punch_timestamp=timezone.make_aware(datetime(2026, 3, 14, 8, 0)), source=AttendancePunchSource.MOBILE, accepted_to_attendance=True),
            SimpleNamespace(id=22, employee_id=self.subordinate, punch_timestamp=timezone.make_aware(datetime(2026, 3, 15, 9, 0)), source=AttendancePunchSource.BIOMETRIC, accepted_to_attendance=False),
            SimpleNamespace(id=23, employee_id=self.outsider, punch_timestamp=timezone.make_aware(datetime(2026, 3, 15, 10, 0)), source=AttendancePunchSource.MOBILE, accepted_to_attendance=True),
        ])

    def _dummy_serializer(self, obj, many=False, context=None):
        return SimpleNamespace(data=[{"id": item.id, "source": item.source, "raw_timestamp": item.punch_timestamp.isoformat()} for item in obj])

    def _call(self, user, params, queryset, scope_tuple):
        request = self.factory.get("/api/attendance/punching-history/", params)
        force_authenticate(request, user=user)
        with patch.object(api_views.AttendancePunchingHistoryAPIView, "get_queryset", return_value=queryset), \
             patch.object(api_views.AttendancePunchingHistoryAPIView, "_employee_scope", return_value=scope_tuple), \
             patch.object(api_views, "AttendancePunchingHistorySerializer", side_effect=self._dummy_serializer):
            return api_views.AttendancePunchingHistoryAPIView.as_view()(request)

    def test_punching_history_blocks_cross_employee_access(self):
        response = self._call(
            self.owner_user,
            {"start_date": "2026-03-14", "end_date": "2026-03-15"},
            _FakePunchQuerySet([self.records[0]]),
            ([{"id": self.owner.id, "name": "Owner User"}], False, self.owner.id),
        )
        self.assertEqual(response.status_code, 200)
        self.assertEqual([item["id"] for item in response.data["results"]], [21])
        self.assertFalse(response.data["show_employee_filter"])

    def test_punching_history_manager_scope_is_subordinate_only(self):
        response = self._call(
            self.manager_user,
            {"start_date": "2026-03-14", "end_date": "2026-03-15", "employee_id": "all"},
            _FakePunchQuerySet([self.records[0], self.records[1]]),
            ([{"id": self.owner.id, "name": "Owner User"}, {"id": self.subordinate.id, "name": "Sub User"}], True, self.owner.id),
        )
        self.assertEqual(response.status_code, 200)
        self.assertEqual({item["id"] for item in response.data["results"]}, {21, 22})
        self.assertTrue(response.data["show_employee_filter"])

    def test_punching_history_filters_by_source_and_date_range(self):
        response = self._call(
            self.admin_user,
            {"employee_id": "all", "start_date": "2026-03-15", "end_date": "2026-03-15", "source": AttendancePunchSource.BIOMETRIC},
            self.records,
            ([{"id": "all", "name": "All Employee"}], True, None),
        )
        self.assertEqual(response.status_code, 200)
        self.assertEqual([item["id"] for item in response.data["results"]], [22])

    def test_visible_results_do_not_duplicate_identical_raw_event_rows(self):
        duplicate_records = _FakePunchQuerySet([
            self.records[0],
            self.records[0],
        ])
        response = self._call(
            self.owner_user,
            {"start_date": "2026-03-14", "end_date": "2026-03-14", "source": AttendancePunchSource.MOBILE},
            duplicate_records,
            ([{"id": self.owner.id, "name": "Owner User"}], False, self.owner.id),
        )
        self.assertEqual(response.status_code, 200)
        ids = [item["id"] for item in response.data["results"]]
        self.assertEqual(ids, [21, 21])
        self.assertEqual(len(set(ids)), 1, "Duplicate raw rows would point to the same underlying event id")
