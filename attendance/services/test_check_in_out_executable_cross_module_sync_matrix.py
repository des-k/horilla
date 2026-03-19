from __future__ import annotations

from dataclasses import dataclass, field
from datetime import date, datetime
from types import SimpleNamespace

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.models import AttendanceChannel, AttendancePunchDirection, AttendanceWorkMode
from attendance.services import reconciliation


@dataclass
class FakePunchLog:
    id: int
    punch_direction: str
    punch_timestamp: datetime
    source: str = "mobile"
    photo: str | None = None
    location: dict | None = None
    attendance_id: object | None = None
    attendance_date: date | None = None
    accepted_to_attendance: bool | None = None
    reason: str | None = None
    decision_status: str | None = None
    decision_source: str | None = None
    saved_update_fields: list[list[str]] = field(default_factory=list)

    def save(self, update_fields=None):
        self.saved_update_fields.append(list(update_fields or []))


class _FakeRecord(SimpleNamespace):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.saved = False

    def save(self):
        self.saved = True


class CrossModuleSyncExecutableMatrixTests(SimpleTestCase):
    def test_sync_attendance_and_activity_keeps_request_override_in_and_raw_biometric_out_aligned(self):
        final_in_dt = timezone.make_aware(datetime(2026, 3, 19, 8, 15))
        final_out_dt = timezone.make_aware(datetime(2026, 3, 19, 17, 5))
        final_out_punch = FakePunchLog(
            id=44,
            punch_direction=AttendancePunchDirection.OUT,
            punch_timestamp=final_out_dt,
            source="biometric",
            photo=None,
            location={"device": "gate-1"},
        )
        attendance = _FakeRecord(
            attendance_clock_in_channel=AttendanceChannel.CORRECTION_REQUEST,
            attendance_clock_in_mode=AttendanceWorkMode.WFA,
            attendance_clock_in_image="corr-in.png",
            attendance_clock_in_location={"from": "request"},
            attendance_clock_out_channel=None,
            attendance_clock_out_mode=None,
            attendance_clock_out_image=None,
            attendance_clock_out_location=None,
            in_attendance_status=None,
            in_attendance_reject_reason_code=None,
            out_attendance_status=None,
            out_attendance_reject_reason_code=None,
            reconciliation_source=None,
            reconciliation_note=None,
            late_minutes=None,
            early_out_minutes=None,
        )
        activity = _FakeRecord(
            reconciliation_source=None,
            reconciliation_note=None,
            late_minutes=None,
            early_out_minutes=None,
        )
        ctx = SimpleNamespace(
            employee="EMP-REQ-RAW",
            attendance_date=date(2026, 3, 19),
            shift="SHIFT-1",
            day=None,
        )

        reconciliation._sync_attendance_and_activity(
            attendance,
            activity,
            final_in_dt=final_in_dt,
            final_out_dt=final_out_dt,
            final_in_punch=None,
            final_out_punch=final_out_punch,
            source=reconciliation.SOURCE_ATTENDANCE_REQUEST,
            note=reconciliation.NOTE_APPROVED_ATTENDANCE_REQUEST,
            final_in_mode=AttendanceWorkMode.WFA,
            final_out_mode=AttendanceWorkMode.WFO,
            final_in_request=None,
            final_out_request=None,
            ctx=ctx,
            minimum_hour="08:00",
            is_presence_only=False,
            late_minutes=0,
            early_minutes=0,
        )

        self.assertEqual(attendance.attendance_clock_in_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(attendance.attendance_clock_in_mode, AttendanceWorkMode.WFA)
        self.assertEqual(attendance.attendance_clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(attendance.attendance_clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_in_channel, AttendanceChannel.CORRECTION_REQUEST)
        self.assertEqual(activity.clock_out_channel, AttendanceChannel.BIOMETRIC)
        self.assertEqual(activity.clock_out_mode, AttendanceWorkMode.WFO)
        self.assertEqual(activity.clock_out_location, {"device": "gate-1"})
        self.assertTrue(attendance.saved)
        self.assertTrue(activity.saved)

    def test_apply_punch_decisions_keeps_final_and_superseded_raw_punches_audit_consistent(self):
        attendance = SimpleNamespace(attendance_date=date(2026, 3, 19))
        final_in = FakePunchLog(
            id=1,
            punch_direction=AttendancePunchDirection.IN,
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
            source="biometric",
        )
        superseded_in = FakePunchLog(
            id=2,
            punch_direction=AttendancePunchDirection.IN,
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 19, 8, 5)),
            source="mobile",
        )
        final_out = FakePunchLog(
            id=3,
            punch_direction=AttendancePunchDirection.OUT,
            punch_timestamp=timezone.make_aware(datetime(2026, 3, 19, 17, 5)),
            source="biometric",
        )

        decisions = {
            final_in.id: (True, reconciliation.NOTE_FINAL_IN),
            superseded_in.id: (False, reconciliation.NOTE_DUPLICATE_CHECKIN),
            final_out.id: (True, reconciliation.NOTE_FINAL_OUT),
        }

        reconciliation._apply_punch_decisions(
            attendance,
            [final_in, superseded_in, final_out],
            decisions,
            reconciliation.SOURCE_NORMAL,
        )

        self.assertTrue(final_in.accepted_to_attendance)
        self.assertEqual(final_in.decision_status, "accepted")
        self.assertEqual(final_in.reason, reconciliation.NOTE_FINAL_IN)
        self.assertFalse(superseded_in.accepted_to_attendance)
        self.assertEqual(superseded_in.decision_status, "not_accepted")
        self.assertEqual(superseded_in.reason, reconciliation.NOTE_DUPLICATE_CHECKIN)
        self.assertTrue(final_out.accepted_to_attendance)
        self.assertEqual(final_out.decision_status, "accepted")
        self.assertEqual(final_out.reason, reconciliation.NOTE_FINAL_OUT)
