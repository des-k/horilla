from datetime import datetime

from django.test import override_settings
from django.utils import timezone
from unittest.mock import patch

from rest_framework.test import APITestCase

from attendance.models import Attendance, AttendanceGeneralSetting, AttendancePunchingHistory
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin


@override_settings(ALLOWED_HOSTS=['testserver', 'localhost', '127.0.0.1'])
class AttendanceExemptRolesEndpointTests(AttendanceApiIntegrationMixin, APITestCase):
    clock_in_endpoint = '/api/attendance/clock-in/'
    clock_out_endpoint = '/api/attendance/clock-out/'
    status_endpoint = '/api/attendance/checking-in'

    def _configure_company_setting(self, *, allow_reporting_manager_attendance=False, allow_admin_attendance=False):
        AttendanceGeneralSetting.objects.update_or_create(
            company_id=self.company,
            defaults={
                'allow_reporting_manager_attendance': allow_reporting_manager_attendance,
                'allow_admin_attendance': allow_admin_attendance,
            },
        )

    def _post_clock(self, client, endpoint):
        return client.post(
            endpoint,
            {'latitude': '-6.2', 'longitude': '106.8', 'accuracy': '10'},
            format='multipart',
        )

    def test_reporting_manager_cannot_clock_in_when_exempt_and_no_raw_punch_is_created(self):
        manager_user, manager = self.create_employee('Manager')
        self.create_employee('Subordinate', manager=manager)
        self._configure_company_setting(allow_reporting_manager_attendance=False)
        with patch('horilla_api.api_views.attendance.views._api_now', return_value=timezone.make_aware(datetime(2026, 3, 20, 8, 5))):
            response = self._post_clock(self.auth_client(manager_user), self.clock_in_endpoint)

        self.assertEqual(response.status_code, 403)
        self.assertIn('disabled', response.json()['error'].lower())
        self.assertEqual(AttendancePunchingHistory.objects.count(), 0)
        self.assertEqual(Attendance.objects.count(), 0)

    def test_reporting_manager_cannot_clock_out_when_exempt_and_no_raw_punch_is_created(self):
        manager_user, manager = self.create_employee('Manager')
        self.create_employee('Subordinate', manager=manager)
        self._configure_company_setting(allow_reporting_manager_attendance=False)
        with patch('horilla_api.api_views.attendance.views._api_now', return_value=timezone.make_aware(datetime(2026, 3, 20, 18, 5))):
            response = self._post_clock(self.auth_client(manager_user), self.clock_out_endpoint)

        self.assertEqual(response.status_code, 403)
        self.assertIn('disabled', response.json()['error'].lower())
        self.assertEqual(AttendancePunchingHistory.objects.count(), 0)
        self.assertEqual(Attendance.objects.count(), 0)

    def test_reporting_manager_status_endpoint_returns_attendance_disabled(self):
        manager_user, manager = self.create_employee('Manager')
        self.create_employee('Subordinate', manager=manager)
        self._configure_company_setting(allow_reporting_manager_attendance=False)
        with patch('horilla_api.api_views.attendance.views._api_now', return_value=timezone.make_aware(datetime(2026, 3, 20, 8, 5))):
            response = self.auth_client(manager_user).get(self.status_endpoint, format='json')
        data = response.json()

        self.assertEqual(response.status_code, 200)
        self.assertFalse(data['attendance_enabled'])
        self.assertIn('REPORTING_MANAGER', data['blocked_roles'])
        self.assertTrue(data['role_flags']['is_reporting_manager'])
        self.assertFalse(data['attendance_role_settings']['allow_reporting_manager_attendance'])

    def test_admin_cannot_clock_in_when_exempt_and_no_raw_punch_is_created(self):
        admin_user, _ = self.create_employee('Admin', is_superuser=True)
        self._configure_company_setting(allow_admin_attendance=False)
        with patch('horilla_api.api_views.attendance.views._api_now', return_value=timezone.make_aware(datetime(2026, 3, 20, 8, 5))):
            response = self._post_clock(self.auth_client(admin_user), self.clock_in_endpoint)

        self.assertEqual(response.status_code, 403)
        self.assertIn('disabled', response.json()['error'].lower())
        self.assertEqual(AttendancePunchingHistory.objects.count(), 0)
        self.assertEqual(Attendance.objects.count(), 0)

    def test_admin_cannot_clock_out_when_exempt_and_no_raw_punch_is_created(self):
        admin_user, _ = self.create_employee('Admin', is_superuser=True)
        self._configure_company_setting(allow_admin_attendance=False)
        with patch('horilla_api.api_views.attendance.views._api_now', return_value=timezone.make_aware(datetime(2026, 3, 20, 18, 5))):
            response = self._post_clock(self.auth_client(admin_user), self.clock_out_endpoint)

        self.assertEqual(response.status_code, 403)
        self.assertIn('disabled', response.json()['error'].lower())
        self.assertEqual(AttendancePunchingHistory.objects.count(), 0)
        self.assertEqual(Attendance.objects.count(), 0)

    def test_admin_status_endpoint_returns_attendance_disabled(self):
        admin_user, _ = self.create_employee('Admin', is_superuser=True)
        self._configure_company_setting(allow_admin_attendance=False)
        with patch('horilla_api.api_views.attendance.views._api_now', return_value=timezone.make_aware(datetime(2026, 3, 20, 8, 5))):
            response = self.auth_client(admin_user).get(self.status_endpoint, format='json')
        data = response.json()

        self.assertEqual(response.status_code, 200)
        self.assertFalse(data['attendance_enabled'])
        self.assertIn('ADMIN', data['blocked_roles'])
        self.assertTrue(data['role_flags']['is_admin'])
        self.assertFalse(data['attendance_role_settings']['allow_admin_attendance'])
