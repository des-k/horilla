from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import patch

from django.db import IntegrityError
from django.test import SimpleTestCase

from attendance.services.punching_history import (
    _biometric_replay_window_start,
    build_biometric_event_key,
    create_biometric_punch_history,
)


class _FakeDuplicateQuerySet:
    def __init__(self, candidates):
        self.candidates = candidates

    def filter(self, **kwargs):
        return self

    def order_by(self, *args, **kwargs):
        return self

    def __getitem__(self, item):
        return self.candidates[item]


class BiometricIdempotencyGuardTests(SimpleTestCase):
    databases = {'default'}

    def test_replay_window_starts_two_minutes_before_checkpoint(self):
        result = _biometric_replay_window_start(date(2026, 3, 22), time(9, 30, 0))
        self.assertEqual(result, datetime(2026, 3, 22, 9, 28, 0))

    def test_event_key_uses_raw_identity_without_direction(self):
        punch_at = datetime(2026, 3, 22, 8, 0, 0)
        event_key = build_biometric_event_key(
            vendor='zk',
            device_id=9,
            raw_employee_identifier='EMP-01',
            punch_timestamp=punch_at,
            raw_punch_code='0',
        )
        self.assertIn('zk|9|EMP-01|', event_key)
        self.assertTrue(event_key.endswith('|0'))

    def test_duplicate_biometric_event_returns_existing_raw_punch_even_when_direction_changes(self):
        device = SimpleNamespace(id=9, name='Front Gate', machine_type='zk')
        duplicate = SimpleNamespace(raw_payload={'punch_code': '0'})
        duplicate_qs = _FakeDuplicateQuerySet([duplicate])

        with patch(
            'attendance.services.punching_history.BiometricEventKey.objects.create',
            side_effect=IntegrityError('duplicate event_key'),
        ), patch(
            'attendance.services.punching_history.AttendancePunchingHistory.objects.filter',
            return_value=duplicate_qs,
        ), patch(
            'attendance.services.punching_history.AttendancePunchingHistory.objects.create'
        ) as create_mock:
            result = create_biometric_punch_history(
                device=device,
                employee=SimpleNamespace(id=7),
                punch_timestamp=datetime(2026, 3, 22, 8, 0, 0),
                direction='out',
                raw_employee_identifier='EMP-01',
                punch_code='0',
            )

        self.assertIs(result, duplicate)
        create_mock.assert_not_called()

    def test_new_event_still_creates_new_raw_punch(self):
        device = SimpleNamespace(id=9, name='Front Gate', machine_type='zk')
        duplicate_qs = _FakeDuplicateQuerySet([])
        created = object()

        with patch(
            'attendance.services.punching_history.BiometricEventKey.objects.create',
            return_value=SimpleNamespace(event_key='zk|9|EMP-01|2026-03-22T08:00:00+00:00|0'),
        ), patch(
            'attendance.services.punching_history.AttendancePunchingHistory.objects.filter',
            return_value=duplicate_qs,
        ), patch(
            'attendance.services.punching_history.AttendancePunchingHistory.objects.create',
            return_value=created,
        ) as create_mock:
            result = create_biometric_punch_history(
                device=device,
                employee=SimpleNamespace(id=7),
                punch_timestamp=datetime(2026, 3, 22, 8, 0, 0),
                direction='in',
                raw_employee_identifier='EMP-01',
                punch_code='0',
            )

        self.assertIs(result, created)
        create_mock.assert_called_once()

    def test_source_declares_db_enforced_event_key_model(self):
        source = open('biometric/models.py', 'r', encoding='utf-8').read()
        self.assertIn('class BiometricEventKey(models.Model):', source)
        self.assertIn('event_key = models.CharField(max_length=255, unique=True', source)

    def test_source_uses_event_key_before_creating_punch_history(self):
        source = open('attendance/services/punching_history.py', 'r', encoding='utf-8').read()
        self.assertIn('BiometricEventKey.objects.create', source)
        self.assertIn('raw_payload={**payload, "event_key": event_key}', source)
