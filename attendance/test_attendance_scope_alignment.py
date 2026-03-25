from datetime import date, datetime

from django.contrib.messages import get_messages
from django.test import TestCase
from django.urls import reverse
from django.utils import timezone

from attendance.models import AttendanceActivity, AttendanceGeneralSetting, AttendancePunchDirection, AttendancePunchSource, AttendancePunchingHistory
from attendance.tests_api_integration_base import AttendanceApiIntegrationMixin
from attendance.views import views as attendance_views


class AttendanceScopeAlignmentTests(AttendanceApiIntegrationMixin, TestCase):
    @classmethod
    def setUpTestData(cls):
        super().setUpTestData()
        AttendanceGeneralSetting.objects.update_or_create(
            company_id=cls.company,
            defaults={
                'allow_reporting_manager_attendance': False,
                'allow_admin_attendance': False,
            },
        )

    def _set_settings(self, *, allow_reporting_manager_attendance=False, allow_admin_attendance=False):
        AttendanceGeneralSetting.objects.update_or_create(
            company_id=self.company,
            defaults={
                'allow_reporting_manager_attendance': allow_reporting_manager_attendance,
                'allow_admin_attendance': allow_admin_attendance,
            },
        )

    def _get_ids(self, queryset):
        return list(queryset.values_list('id', flat=True))

    def test_employee_month_view_regular_employee_can_open_self_only(self):
        self._set_settings()
        user, employee = self.create_employee('Owner')

        client = self.client
        client.force_login(user)
        response = client.get(reverse('attendance-employee-month-view'))

        self.assertEqual(response.status_code, 200)
        self.assertEqual(self._get_ids(response.context['employees']), [employee.id])
        self.assertEqual(response.context['selected_employee'].id, employee.id)

    def test_login_post_redirects_employee_to_monthly_view_without_permission_message(self):
        self._set_settings()
        user, employee = self.create_employee('LoginOwner')

        response = self.client.post(
            reverse('login'),
            {'username': user.username, 'password': 'pass1234'},
            follow=True,
        )

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.redirect_chain[-1][0].endswith(reverse('attendance-employee-month-view')), True)
        messages = [message.message for message in get_messages(response.wsgi_request)]
        self.assertIn('Login successful.', messages)
        self.assertFalse(any("You don't have permission" in message or 'You dont have permission' in message for message in messages))
        self.assertEqual(response.context['selected_employee'].id, employee.id)

    def test_month_view_manager_self_excluded_when_reporting_manager_attendance_disabled(self):
        self._set_settings(allow_reporting_manager_attendance=False)
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)

        self.client.force_login(manager_user)
        response = self.client.get(reverse('attendance-employee-month-view'))

        self.assertEqual(response.status_code, 200)
        self.assertEqual(self._get_ids(response.context['employees']), [subordinate.id])
        self.assertEqual(response.context['selected_employee'].id, subordinate.id)

    def test_month_view_manager_self_included_when_reporting_manager_attendance_enabled(self):
        self._set_settings(allow_reporting_manager_attendance=True)
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)

        self.client.force_login(manager_user)
        response = self.client.get(reverse('attendance-employee-month-view'))

        self.assertEqual(response.status_code, 200)
        self.assertEqual(self._get_ids(response.context['employees']), [manager.id, subordinate.id])
        self.assertEqual(response.context['selected_employee'].id, manager.id)

    def test_month_view_admin_self_excluded_when_admin_attendance_disabled(self):
        self._set_settings(allow_admin_attendance=False)
        admin_user, admin = self.create_employee(
            'Admin', permissions=['view_attendance', 'change_attendance']
        )
        _, owner = self.create_employee('Owner')

        self.client.force_login(admin_user)
        response = self.client.get(reverse('attendance-employee-month-view'))

        self.assertEqual(response.status_code, 200)
        self.assertNotIn(admin.id, self._get_ids(response.context['employees']))
        self.assertEqual(response.context['selected_employee'].id, owner.id)

    def test_month_view_admin_self_included_when_admin_attendance_enabled(self):
        self._set_settings(allow_admin_attendance=True)
        admin_user, admin = self.create_employee(
            'Admin', permissions=['view_attendance', 'change_attendance']
        )
        _, owner = self.create_employee('Owner')

        self.client.force_login(admin_user)
        response = self.client.get(reverse('attendance-employee-month-view'))

        self.assertEqual(response.status_code, 200)
        self.assertIn(admin.id, self._get_ids(response.context['employees']))
        self.assertEqual(response.context['selected_employee'].id, admin.id)
        self.assertIn(owner.id, self._get_ids(response.context['employees']))

    def test_attendance_activity_scope_manager_self_disabled_but_subordinate_visible(self):
        self._set_settings(allow_reporting_manager_attendance=False)
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)
        AttendanceActivity.objects.create(employee_id=manager, attendance_date=date(2026, 3, 20))
        AttendanceActivity.objects.create(employee_id=subordinate, attendance_date=date(2026, 3, 20))

        request = self.factory.get(reverse('attendance-activity-view'))
        request.user = manager_user

        employee_options, show_filter, can_view_all, default_employee_id = attendance_views._get_attendance_activity_employee_scope(request)
        queryset = attendance_views._scoped_attendance_activity_queryset(request)

        self.assertEqual(self._get_ids(employee_options), [subordinate.id])
        self.assertFalse(show_filter)
        self.assertFalse(can_view_all)
        self.assertEqual(default_employee_id, subordinate.id)
        self.assertEqual(list(queryset.values_list('employee_id', flat=True).distinct()), [subordinate.id])

    def test_attendance_activity_scope_manager_self_enabled(self):
        self._set_settings(allow_reporting_manager_attendance=True)
        manager_user, manager = self.create_employee('Manager')
        _, subordinate = self.create_employee('Subordinate', manager=manager)
        AttendanceActivity.objects.create(employee_id=manager, attendance_date=date(2026, 3, 20))
        AttendanceActivity.objects.create(employee_id=subordinate, attendance_date=date(2026, 3, 20))

        request = self.factory.get(reverse('attendance-activity-view'))
        request.user = manager_user

        employee_options, show_filter, _, default_employee_id = attendance_views._get_attendance_activity_employee_scope(request)
        queryset = attendance_views._scoped_attendance_activity_queryset(request)

        self.assertEqual(self._get_ids(employee_options), [manager.id, subordinate.id])
        self.assertTrue(show_filter)
        self.assertEqual(default_employee_id, manager.id)
        self.assertEqual(set(queryset.values_list('employee_id', flat=True).distinct()), {manager.id, subordinate.id})

    def test_punching_history_scope_admin_self_disabled_but_others_visible(self):
        self._set_settings(allow_admin_attendance=False)
        admin_user, admin = self.create_employee('Admin', permissions=['view_attendancepunchinghistory', 'change_attendance'])
        _, owner = self.create_employee('Owner')
        AttendancePunchingHistory.objects.create(
            employee_id=admin,
            attendance_date=date(2026, 3, 21),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 21, 8, 0)),
            source=AttendancePunchSource.MOBILE,
            punch_direction=AttendancePunchDirection.IN,
        )
        AttendancePunchingHistory.objects.create(
            employee_id=owner,
            attendance_date=date(2026, 3, 21),
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 21, 9, 0)),
            source=AttendancePunchSource.BIOMETRIC,
            punch_direction=AttendancePunchDirection.IN,
        )

        request = self.factory.get(reverse('attendance-punching-history-view'))
        request.user = admin_user

        employee_options, show_filter, can_view_all, default_employee_id = attendance_views._get_punching_history_employee_scope(request)
        queryset = attendance_views._scoped_punching_history_queryset(request)

        self.assertNotIn(admin.id, self._get_ids(employee_options))
        self.assertIn(owner.id, self._get_ids(employee_options))
        self.assertFalse(show_filter)
        self.assertTrue(can_view_all)
        self.assertEqual(default_employee_id, owner.id)
        self.assertEqual(set(queryset.values_list('employee_id', flat=True).distinct()), {owner.id})

    def test_monthly_recap_api_returns_config_scoped_employee_options_for_mobile(self):
        self._set_settings(allow_admin_attendance=False)
        admin_user, admin = self.create_employee('Admin', permissions=['view_attendance', 'change_attendance'])
        _, owner = self.create_employee('Owner')

        response = self.auth_client(admin_user).get('/api/attendance/attendances-recap/', {}, format='json')
        self._clear_request_context()
        data = response.json()

        self.assertEqual(response.status_code, 200)
        self.assertNotIn(str(admin.id), {str(item['id']) for item in data['employee_options']})
        self.assertIn(str(owner.id), {str(item['id']) for item in data['employee_options']})
        self.assertEqual(data['selected_employee_id'], owner.id)
