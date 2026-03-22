from datetime import date, datetime, time
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

from django.test import SimpleTestCase

from attendance.services.punching_history import (
    _biometric_replay_window_start,
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
    def test_replay_window_starts_two_minutes_before_checkpoint(self):
        result = _biometric_replay_window_start(date(2026, 3, 22), time(9, 30, 0))
        self.assertEqual(result, datetime(2026, 3, 22, 9, 28, 0))

    def test_duplicate_biometric_event_returns_existing_raw_punch(self):
        device = SimpleNamespace(id=9, name='Front Gate')
        duplicate = SimpleNamespace(raw_payload={'punch_code': '0'})
        duplicate_qs = _FakeDuplicateQuerySet([duplicate])

        with patch('attendance.services.punching_history.AttendancePunchingHistory.objects.filter', return_value=duplicate_qs), patch(
            'attendance.services.punching_history.AttendancePunchingHistory.objects.create'
        ) as create_mock:
            result = create_biometric_punch_history(
                device=device,
                employee=SimpleNamespace(id=7),
                punch_timestamp=datetime(2026, 3, 22, 8, 0, 0),
                direction='in',
                punch_code='0',
            )

        self.assertIs(result, duplicate)
        create_mock.assert_not_called()

    def test_different_punch_code_still_creates_new_raw_punch(self):
        device = SimpleNamespace(id=9, name='Front Gate')
        existing = SimpleNamespace(raw_payload={'punch_code': '1'})
        duplicate_qs = _FakeDuplicateQuerySet([existing])
        created = object()

        with patch('attendance.services.punching_history.AttendancePunchingHistory.objects.filter', return_value=duplicate_qs), patch(
            'attendance.services.punching_history.AttendancePunchingHistory.objects.create', return_value=created
        ) as create_mock:
            result = create_biometric_punch_history(
                device=device,
                employee=SimpleNamespace(id=7),
                punch_timestamp=datetime(2026, 3, 22, 8, 0, 0),
                direction='in',
                punch_code='0',
            )

        self.assertIs(result, created)
        create_mock.assert_called_once()
