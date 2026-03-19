from __future__ import annotations

from dataclasses import dataclass, field
from datetime import date, datetime
from types import SimpleNamespace

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.models import AttendancePunchDirection
from attendance.services import reconciliation
from attendance.services.final_session_resolution import (
    APPROVED_REQUEST_CHANNEL,
    resolve_final_session,
)
from attendance.services.punching_history import (
    humanize_biometric_error,
    humanize_mobile_error,
)


@dataclass
class FakePunchLog:
    id: int
    punch_direction: str
    punch_timestamp: datetime
    source: str = "mobile"
    attendance_id: object | None = None
    attendance_date: date | None = None
    accepted_to_attendance: bool | None = None
    reason: str | None = None
    decision_status: str | None = None
    decision_source: str | None = None
    saved_update_fields: list[list[str]] = field(default_factory=list)

    def save(self, update_fields=None):
        self.saved_update_fields.append(list(update_fields or []))


class CheckInOutExecutableSourceMatrixTests(SimpleTestCase):
    def _ctx(self):
        return reconciliation.ShiftContext(
            employee="EMP-1",
            attendance_date=date(2026, 3, 19),
            day=None,
            shift=None,
            schedule=None,
            shift_start_dt=timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
            shift_end_dt=timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
            check_in_window_start_dt=timezone.make_aware(datetime(2026, 3, 19, 6, 0)),
            check_in_window_end_dt=timezone.make_aware(datetime(2026, 3, 19, 12, 0)),
            check_out_window_start_dt=timezone.make_aware(datetime(2026, 3, 19, 12, 0)),
            check_out_window_end_dt=timezone.make_aware(datetime(2026, 3, 19, 23, 0)),
            minimum_hour="08:00",
            grace_seconds=0,
            grace_clock_in_type="after",
        )

    def test_source_matrix_selects_expected_final_punches(self):
        cases = [
            {
                "label": "BIO_BIO",
                "logs": [
                    FakePunchLog(1, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 1)), source="biometric"),
                    FakePunchLog(2, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 17, 1)), source="biometric"),
                ],
                "final_in": 1,
                "final_out": 2,
                "extra_in": [],
                "extra_out": [],
                "invalid_in": [],
                "invalid_out": [],
            },
            {
                "label": "BIO_MULTI_IN",
                "logs": [
                    FakePunchLog(11, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 5)), source="biometric"),
                    FakePunchLog(12, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 1)), source="biometric"),
                    FakePunchLog(13, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 17, 0)), source="biometric"),
                ],
                "final_in": 12,
                "final_out": 13,
                "extra_in": [11],
                "extra_out": [],
                "invalid_in": [],
                "invalid_out": [],
            },
            {
                "label": "BIO_MULTI_OUT",
                "logs": [
                    FakePunchLog(21, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 0)), source="biometric"),
                    FakePunchLog(22, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 16, 45)), source="biometric"),
                    FakePunchLog(23, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 17, 2)), source="biometric"),
                ],
                "final_in": 21,
                "final_out": 23,
                "extra_in": [],
                "extra_out": [22],
                "invalid_in": [],
                "invalid_out": [],
            },
            {
                "label": "MULTI_MIXED_WITH_INVALIDS",
                "logs": [
                    FakePunchLog(31, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 5, 59)), source="biometric"),
                    FakePunchLog(32, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 3)), source="mobile"),
                    FakePunchLog(33, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 1)), source="biometric"),
                    FakePunchLog(34, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 11, 55)), source="mobile"),
                    FakePunchLog(35, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 16, 58)), source="biometric"),
                    FakePunchLog(36, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 17, 3)), source="mobile"),
                ],
                "final_in": 33,
                "final_out": 36,
                "extra_in": [32],
                "extra_out": [35],
                "invalid_in": [31],
                "invalid_out": [34],
            },
        ]

        for case in cases:
            with self.subTest(case=case["label"]):
                raw = reconciliation._pick_raw_sessions(case["logs"], self._ctx())

                self.assertEqual(getattr(raw["final_in"], "id", None), case["final_in"])
                self.assertEqual(getattr(raw["final_out"], "id", None), case["final_out"])
                self.assertEqual([log.id for log in raw["extra_in"]], case["extra_in"])
                self.assertEqual([log.id for log in raw["extra_out"]], case["extra_out"])
                self.assertEqual([log.id for log in raw["invalid_in"]], case["invalid_in"])
                self.assertEqual([log.id for log in raw["invalid_out"]], case["invalid_out"])

    def test_approved_request_override_wins_over_raw_mobile_and_biometric(self):
        resolved_in = resolve_final_session(
            session="IN",
            approved_dt=datetime(2026, 3, 19, 8, 15),
            raw_datetimes=[
                datetime(2026, 3, 19, 8, 1),
                datetime(2026, 3, 19, 8, 3),
            ],
            raw_source="mixed",
        )
        resolved_out = resolve_final_session(
            session="OUT",
            approved_dt=datetime(2026, 3, 19, 16, 40),
            raw_datetimes=[
                datetime(2026, 3, 19, 17, 10),
                datetime(2026, 3, 19, 17, 2),
            ],
            raw_source="mixed",
        )

        self.assertEqual(resolved_in.final_source, APPROVED_REQUEST_CHANNEL)
        self.assertEqual(resolved_out.final_source, APPROVED_REQUEST_CHANNEL)
        self.assertEqual(resolved_in.final_dt, datetime(2026, 3, 19, 8, 15))
        self.assertEqual(resolved_out.final_dt, datetime(2026, 3, 19, 16, 40))
        self.assertEqual(resolved_in.raw_dt, datetime(2026, 3, 19, 8, 1))
        self.assertEqual(resolved_out.raw_dt, datetime(2026, 3, 19, 17, 10))

    def test_duplicate_mobile_and_biometric_attempts_are_humanized_for_audit(self):
        self.assertEqual(
            humanize_mobile_error("Already clocked-in", direction="in"),
            "Rejected: valid Check-In already exists",
        )
        self.assertEqual(
            humanize_mobile_error("Already clocked-out", direction="out"),
            "Rejected: valid Check-Out already exists",
        )
        self.assertEqual(
            humanize_biometric_error("Employee already clocked-in", direction=AttendancePunchDirection.IN),
            "Rejected: valid Check-In already exists",
        )
        self.assertEqual(
            humanize_biometric_error("Employee already clocked-out", direction=AttendancePunchDirection.OUT),
            "Rejected: valid Check-Out already exists",
        )

    def test_apply_punch_decisions_marks_duplicate_and_invalid_rows_for_sync_audit(self):
        attendance = SimpleNamespace(attendance_date=date(2026, 3, 19))
        final_in = FakePunchLog(101, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 1)))
        duplicate_in = FakePunchLog(102, AttendancePunchDirection.IN, timezone.make_aware(datetime(2026, 3, 19, 8, 5)))
        invalid_out = FakePunchLog(103, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 11, 55)))
        latest_out = FakePunchLog(104, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 17, 3)))
        superseded_out = FakePunchLog(105, AttendancePunchDirection.OUT, timezone.make_aware(datetime(2026, 3, 19, 16, 55)))

        decisions = {
            101: (True, reconciliation.NOTE_FINAL_IN),
            102: (False, reconciliation.NOTE_DUPLICATE_CHECKIN),
            103: (False, reconciliation.NOTE_INVALID_OUT_WINDOW),
            104: (True, reconciliation.NOTE_FINAL_OUT),
            105: (False, reconciliation.NOTE_SUPERSEDED_CHECKOUT),
        }

        reconciliation._apply_punch_decisions(
            attendance,
            [final_in, duplicate_in, invalid_out, latest_out, superseded_out],
            decisions,
            reconciliation.SOURCE_NORMAL,
        )

        self.assertTrue(final_in.accepted_to_attendance)
        self.assertEqual(final_in.decision_status, "accepted")
        self.assertFalse(duplicate_in.accepted_to_attendance)
        self.assertEqual(duplicate_in.decision_status, "not_accepted")
        self.assertEqual(duplicate_in.reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertFalse(invalid_out.accepted_to_attendance)
        self.assertEqual(invalid_out.decision_status, "invalid")
        self.assertEqual(invalid_out.reason, reconciliation.NOTE_INVALID_OUT_WINDOW)
        self.assertFalse(superseded_out.accepted_to_attendance)
        self.assertEqual(superseded_out.decision_status, "superseded")
        self.assertEqual(latest_out.decision_status, "accepted")
