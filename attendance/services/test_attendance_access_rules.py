from django.test import SimpleTestCase

from attendance.services.attendance_access import build_attendance_access_decision


class AttendanceAccessDecisionTests(SimpleTestCase):
    def test_default_reporting_manager_is_blocked(self):
        decision = build_attendance_access_decision(
            is_reporting_manager=True,
            is_admin=False,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )
        self.assertFalse(decision.allowed)
        self.assertEqual(decision.reason_code, "REPORTING_MANAGER")
        self.assertEqual(decision.blocked_roles, ("REPORTING_MANAGER",))

    def test_default_admin_is_blocked(self):
        decision = build_attendance_access_decision(
            is_reporting_manager=False,
            is_admin=True,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )
        self.assertFalse(decision.allowed)
        self.assertEqual(decision.reason_code, "ADMIN")
        self.assertEqual(decision.blocked_roles, ("ADMIN",))

    def test_reporting_manager_can_attend_when_enabled(self):
        decision = build_attendance_access_decision(
            is_reporting_manager=True,
            is_admin=False,
            allow_reporting_manager_attendance=True,
            allow_admin_attendance=False,
        )
        self.assertTrue(decision.allowed)
        self.assertEqual(decision.blocked_roles, ())

    def test_admin_can_attend_when_enabled(self):
        decision = build_attendance_access_decision(
            is_reporting_manager=False,
            is_admin=True,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=True,
        )
        self.assertTrue(decision.allowed)
        self.assertEqual(decision.blocked_roles, ())

    def test_dual_role_is_blocked_when_any_applicable_role_setting_is_disabled(self):
        decision = build_attendance_access_decision(
            is_reporting_manager=True,
            is_admin=True,
            allow_reporting_manager_attendance=True,
            allow_admin_attendance=False,
        )
        self.assertFalse(decision.allowed)
        self.assertEqual(decision.reason_code, "ADMIN")
        self.assertEqual(decision.blocked_roles, ("ADMIN",))

    def test_dual_role_with_both_disabled_returns_combined_reason(self):
        decision = build_attendance_access_decision(
            is_reporting_manager=True,
            is_admin=True,
            allow_reporting_manager_attendance=False,
            allow_admin_attendance=False,
        )
        self.assertFalse(decision.allowed)
        self.assertEqual(decision.reason_code, "MULTIPLE_PRIVILEGED_ROLES")
        self.assertEqual(decision.blocked_roles, ("REPORTING_MANAGER", "ADMIN"))
