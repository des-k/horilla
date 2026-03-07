import unittest

from attendance.services.monthly_recap_note import NoteInputs, derive_note


class MonthlyRecapNoteTests(unittest.TestCase):
    def test_off_holiday_overrides(self):
        note = derive_note(NoteInputs(is_off=True, off_kind="holiday"))
        self.assertEqual(note, "Holiday")

    def test_off_leave_overrides(self):
        note = derive_note(NoteInputs(is_off=True, off_kind="leave"))
        self.assertEqual(note, "On Leave")

    def test_alpha(self):
        note = derive_note(NoteInputs(is_off=False, has_check_in=False, has_check_out=False))
        self.assertEqual(note, "Alpha")

    def test_late_only(self):
        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=True,
                has_check_out=True,
                late_seconds=60,
                early_out_seconds=0,
            )
        )
        self.assertEqual(note, "Late")

    def test_leave_early_only(self):
        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=True,
                has_check_out=True,
                late_seconds=0,
                early_out_seconds=60,
            )
        )
        self.assertEqual(note, "Leave Early")

    def test_late_and_leave_early(self):
        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=True,
                has_check_out=True,
                late_seconds=60,
                early_out_seconds=60,
            )
        )
        self.assertEqual(note, "Late, Leave Early")

    def test_missing_checkin_counts_as_late(self):
        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=False,
                has_check_out=True,
                late_seconds=0,
                early_out_seconds=0,
            )
        )
        self.assertEqual(note, "Late")

    def test_missing_checkout_counts_as_leave_early(self):
        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=True,
                has_check_out=False,
                late_seconds=0,
                early_out_seconds=0,
            )
        )
        self.assertEqual(note, "Leave Early")

    def test_suffixes(self):
        note = derive_note(
            NoteInputs(
                is_off=False,
                has_check_in=True,
                has_check_out=True,
                late_seconds=60,
                early_out_seconds=0,
                pending_suffixes=["Dinas Luar Awal menunggu persetujuan: 08:00"],
                correction_pending=True,
            )
        )
        self.assertIn("Late", note)
        self.assertIn("Dinas Luar Awal menunggu persetujuan: 08:00", note)
        self.assertIn("Attendance correction pending", note)


if __name__ == "__main__":
    unittest.main(verbosity=2)
