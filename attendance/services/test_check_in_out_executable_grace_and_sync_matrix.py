from __future__ import annotations

from datetime import datetime

from django.test import SimpleTestCase
from django.utils import timezone

from attendance.services import reconciliation


class CheckInOutExecutableGraceAndSyncMatrixTests(SimpleTestCase):
    def test_grace_matrix_after_vs_before_after(self):
        cases = [
            {
                "label": "after_early_in_does_not_offset_early_out",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 7, 45)),
                "final_out": timezone.make_aware(datetime(2026, 3, 19, 16, 45)),
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "grace_seconds": 1800,
                "clock_in_type": "after",
                "apply_grace_to_late": True,
                "expected": (0, 15),
            },
            {
                "label": "after_inside_grace_not_late",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 8, 20)),
                "final_out": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "grace_seconds": 1800,
                "clock_in_type": "after",
                "apply_grace_to_late": True,
                "expected": (0, 0),
            },
            {
                "label": "after_outside_grace_becomes_late",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 8, 35)),
                "final_out": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "grace_seconds": 1800,
                "clock_in_type": "after",
                "apply_grace_to_late": True,
                "expected": (5, 0),
            },
            {
                "label": "before_after_full_offset",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 7, 45)),
                "final_out": timezone.make_aware(datetime(2026, 3, 19, 16, 45)),
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "grace_seconds": 1800,
                "clock_in_type": "before_after",
                "apply_grace_to_late": True,
                "expected": (0, 0),
            },
            {
                "label": "before_after_partial_offset",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 7, 40)),
                "final_out": timezone.make_aware(datetime(2026, 3, 19, 16, 30)),
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "grace_seconds": 1800,
                "clock_in_type": "before_after",
                "apply_grace_to_late": True,
                "expected": (0, 10),
            },
            {
                "label": "first_half_leave_threshold_ignores_after_grace_consumption",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 13, 15)),
                "final_out": None,
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 13, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 17, 0)),
                "grace_seconds": 600,
                "clock_in_type": "after",
                "apply_grace_to_late": False,
                "expected": (15, 0),
            },
            {
                "label": "second_half_leave_threshold_counts_early_out_against_morning_boundary",
                "final_in": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "final_out": timezone.make_aware(datetime(2026, 3, 19, 11, 45)),
                "late_reference": timezone.make_aware(datetime(2026, 3, 19, 8, 0)),
                "early_reference": timezone.make_aware(datetime(2026, 3, 19, 12, 0)),
                "grace_seconds": 0,
                "clock_in_type": "after",
                "apply_grace_to_late": True,
                "expected": (0, 15),
            },
        ]

        for case in cases:
            with self.subTest(case=case["label"]):
                result = reconciliation._calculate_late_early(
                    case["final_in"],
                    case["final_out"],
                    case["late_reference"],
                    case["early_reference"],
                    case["grace_seconds"],
                    case["clock_in_type"],
                    apply_grace_to_late=case["apply_grace_to_late"],
                )
                self.assertEqual(result, case["expected"])
