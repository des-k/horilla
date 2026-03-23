from datetime import datetime
from types import SimpleNamespace
from unittest.mock import patch

from django.db import IntegrityError
from django.test import SimpleTestCase
from django.utils import timezone

from attendance.models import AttendancePunchDirection
from attendance.services import punching_history


class BiometricEventKeyDbIntegrationTests(SimpleTestCase):
    databases = {"default"}
    def setUp(self):
        self.device_one = SimpleNamespace(id="dev-1", name="Gate A", machine_type="zk")
        self.device_two = SimpleNamespace(id="dev-2", name="Gate B", machine_type="zk")
        self.ts = timezone.make_aware(datetime(2026, 3, 14, 8, 0))

    def test_biometric_event_key_unique_constraint_blocks_exact_duplicate(self):
        with patch("attendance.services.punching_history.BiometricEventKey.objects.create", side_effect=[None, IntegrityError()]):
            event_key_1, is_dup_1 = punching_history._register_biometric_event_key(
                device=self.device_one,
                raw_employee_identifier="BIO-1",
                punch_timestamp=self.ts,
                punch_code="0",
            )
            event_key_2, is_dup_2 = punching_history._register_biometric_event_key(
                device=self.device_one,
                raw_employee_identifier="BIO-1",
                punch_timestamp=self.ts,
                punch_code="0",
            )
        self.assertEqual(event_key_1, event_key_2)
        self.assertFalse(is_dup_1)
        self.assertTrue(is_dup_2)

    def test_same_timestamp_different_raw_punch_code_is_distinct_event(self):
        key_in = punching_history.build_biometric_event_key(
            vendor="zk",
            device_id=self.device_one.id,
            raw_employee_identifier="BIO-1",
            punch_timestamp=self.ts,
            raw_punch_code="0",
        )
        key_out = punching_history.build_biometric_event_key(
            vendor="zk",
            device_id=self.device_one.id,
            raw_employee_identifier="BIO-1",
            punch_timestamp=self.ts,
            raw_punch_code="1",
        )
        self.assertNotEqual(key_in, key_out)

    def test_same_employee_same_time_different_device_is_distinct_event(self):
        key_one = punching_history.build_biometric_event_key(
            vendor="zk",
            device_id=self.device_one.id,
            raw_employee_identifier="BIO-1",
            punch_timestamp=self.ts,
            raw_punch_code="0",
        )
        key_two = punching_history.build_biometric_event_key(
            vendor="zk",
            device_id=self.device_two.id,
            raw_employee_identifier="BIO-1",
            punch_timestamp=self.ts,
            raw_punch_code="0",
        )
        self.assertNotEqual(key_one, key_two)

    def test_unmatched_employee_event_does_not_create_invalid_attendance(self):
        fake_instance = SimpleNamespace(id=91, employee_id=None, attendance_id=None, accepted_to_attendance=False)
        with patch("attendance.services.punching_history.BiometricEventKey.objects.create", side_effect=[None, IntegrityError()]), \
             patch("attendance.services.punching_history.AttendancePunchingHistory.objects.create", return_value=fake_instance), \
             patch("attendance.services.punching_history._matching_biometric_duplicate", return_value=fake_instance):
            first = punching_history.create_biometric_punch_history(
                device=self.device_one,
                punch_timestamp=self.ts,
                direction=AttendancePunchDirection.IN,
                employee=None,
                attendance_date=self.ts.date(),
                raw_employee_identifier="UNKNOWN-BADGE",
                punch_code="0",
            )
            second = punching_history.create_biometric_punch_history(
                device=self.device_one,
                punch_timestamp=self.ts,
                direction=AttendancePunchDirection.IN,
                employee=None,
                attendance_date=self.ts.date(),
                raw_employee_identifier="UNKNOWN-BADGE",
                punch_code="0",
            )
        self.assertEqual(first.id, second.id)
        self.assertIsNone(first.employee_id)
        self.assertIsNone(first.attendance_id)
        self.assertFalse(first.accepted_to_attendance)
