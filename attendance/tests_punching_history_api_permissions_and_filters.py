from datetime import date, datetime
from types import SimpleNamespace
from unittest.mock import patch

from django.test import SimpleTestCase
from django.utils import timezone
from rest_framework.test import APITestCase, APIRequestFactory, force_authenticate

from attendance.models import Attendance, AttendancePunchDirection, AttendancePunchSource, AttendancePunchingHistory, PunchDecisionStatus
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
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
            else:
                items.sort(key=lambda item: getattr(item, attr), reverse=reverse)
        return _FakePunchQuerySet(items)


class AttendancePunchingHistoryApiPermissionsAndFiltersTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.owner = SimpleNamespace(id=1)
        self.subordinate = SimpleNamespace(id=2)
        self.outsider = SimpleNamespace(id=3)
        self.owner_user = SimpleNamespace(is_authenticated=True, employee_get=self.owner, has_perm=lambda perm: False, is_superuser=False)
        self.manager_user = SimpleNamespace(is_authenticated=True, employee_get=self.owner, has_perm=lambda perm: False, is_superuser=False)
        self.admin_user = SimpleNamespace(is_authenticated=True, employee_get=self.owner, has_perm=lambda perm: True, is_superuser=True)
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


class AttendancePunchingHistoryApiIntegrationTests(AttendanceApiIntegrationMixin, APITestCase):
    endpoint = '/api/attendance/punching-history/'

    def _call(self, user, params=None):
        return self.auth_client(user).get(self.endpoint, params or {}, format='json')

    def _json(self, response):
        return response.json()

    def test_punching_history_blocks_cross_employee_access(self):
        owner_user, owner = self.create_employee('Owner')
        _, outsider = self.create_employee('Outsider')
        owner_punch = AttendancePunchingHistory.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 14),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.IN,
            accepted_to_attendance=True,
            decision_status=PunchDecisionStatus.ACCEPTED,
        )
        AttendancePunchingHistory.objects.create(
            employee_id=outsider,
            attendance_date=date(2026, 3, 14),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 14, 9, 0)),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
        )

        response = self._call(
            owner_user,
            params={'start_date': '2026-03-14', 'end_date': '2026-03-14', 'employee_id': outsider.id},
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data['results']], [owner_punch.id])
        self.assertEqual(data['selected_employee_id'], owner.id)
        self.assertFalse(data['show_employee_filter'])

    def test_punching_history_manager_scope_is_subordinate_only(self):
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)
        _, outsider = self.create_employee('Outsider')
        subordinate_punch = AttendancePunchingHistory.objects.create(
            employee_id=subordinate,
            attendance_date=date(2026, 3, 15),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 15, 9, 0)),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
        )
        AttendancePunchingHistory.objects.create(
            employee_id=outsider,
            attendance_date=date(2026, 3, 15),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 15, 10, 0)),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.IN,
        )

        response = self._call(
            manager_user,
            params={'start_date': '2026-03-15', 'end_date': '2026-03-15', 'employee_id': 'all'},
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data['results']], [subordinate_punch.id])
        self.assertTrue(data['show_employee_filter'])
        self.assertEqual(
            {str(item['id']) for item in data['employee_options']},
            {'all', str(manager.id), str(subordinate.id)},
        )

    def test_punching_history_filters_by_source_and_date_range(self):
        admin_user, _ = self.create_employee('Admin', is_superuser=True)
        _, owner = self.create_employee('Owner')
        AttendancePunchingHistory.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 14),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 14, 8, 0)),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.IN,
        )
        expected = AttendancePunchingHistory.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 15),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 15, 9, 0)),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.OUT,
        )

        response = self._call(
            admin_user,
            params={
                'employee_id': owner.id,
                'start_date': '2026-03-15',
                'end_date': '2026-03-15',
                'source': AttendancePunchSource.BIOMETRIC,
            },
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data['results']], [expected.id])
        self.assertEqual(data['results'][0]['source'], 'Biometric')
        self.assertEqual(data['results'][0]['punch_date'], '2026-03-15')

    def test_raw_punch_history_remains_visible_after_attendance_override(self):
        owner_user, owner = self.create_employee('Owner')
        attendance = Attendance.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 16),
            attendance_clock_in_date=date(2026, 3, 16),
            attendance_clock_in=datetime(2026, 3, 16, 8, 5).time(),
        )
        raw_punch = AttendancePunchingHistory.objects.create(
            employee_id=owner,
            attendance_id=attendance,
            attendance_date=date(2026, 3, 16),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 16, 8, 5)),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.IN,
            accepted_to_attendance=False,
            decision_status=PunchDecisionStatus.NOT_ACCEPTED,
            reason='raw mobile punch',
        )
        attendance.is_validate_request = False
        attendance.is_validate_request_approved = True
        attendance.request_type = 'update_request'
        attendance.attendance_clock_in = datetime(2026, 3, 16, 9, 30).time()
        attendance.save(update_fields=['is_validate_request', 'is_validate_request_approved', 'request_type', 'attendance_clock_in'])

        response = self._call(
            owner_user,
            params={'start_date': '2026-03-16', 'end_date': '2026-03-16'},
        )
        data = self._json(response)

        self.assertEqual(response.status_code, 200)
        self.assertEqual([item['id'] for item in data['results']], [raw_punch.id])
        self.assertFalse(data['results'][0]['accepted_to_attendance'])
        self.assertEqual(data['results'][0]['reason'], 'raw mobile punch')
        self.assertTrue(AttendancePunchingHistory.objects.filter(id=raw_punch.id).exists())
