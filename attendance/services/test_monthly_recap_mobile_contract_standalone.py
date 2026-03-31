from __future__ import annotations

import os
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
API_VIEWS = ROOT / 'horilla_api' / 'api_views' / 'attendance' / 'views.py'


def _candidate_mobile_sources() -> list[Path]:
    env_path = os.environ.get('HORILLA_MOBILE_RECAP_PATH', '').strip()
    candidates: list[Path] = []
    if env_path:
        env_candidate = Path(env_path)
        if env_candidate.is_dir():
            env_candidate = env_candidate / 'attendance_views' / 'attendance_attendance.dart'
        candidates.append(env_candidate)

    relative_file = Path('lib') / 'attendance_views' / 'attendance_attendance.dart'
    relative_mobile_file = Path('mobile') / 'lib' / 'attendance_views' / 'attendance_attendance.dart'

    search_roots = [
        ROOT,
        ROOT.parent,
        ROOT.parent.parent,
        Path.cwd(),
        Path.cwd().parent,
    ]
    for base in search_roots:
        candidates.append(base / relative_file)
        candidates.append(base / relative_mobile_file)

    unique: list[Path] = []
    seen: set[Path] = set()
    for candidate in candidates:
        try:
            normalized = candidate.resolve(strict=False)
        except Exception:
            normalized = candidate
        if normalized in seen:
            continue
        seen.add(normalized)
        unique.append(candidate)
    return unique


def _resolve_mobile_recap() -> Path | None:
    for candidate in _candidate_mobile_sources():
        if candidate.exists():
            return candidate
    return None


class MonthlyRecapMobileContractStandaloneTests(unittest.TestCase):
    def test_api_monthly_recap_rows_publish_decimal_minute_fields(self):
        source = API_VIEWS.read_text()
        self.assertIn('"late_minutes": format_decimal_minutes(getattr(r, "late_minutes", 0) or 0)', source)
        self.assertIn('"early_out_minutes": format_decimal_minutes(getattr(r, "early_out_minutes", 0) or 0)', source)

    def test_mobile_summary_and_rows_use_decimal_minute_strings(self):
        mobile_recap = _resolve_mobile_recap()
        if mobile_recap is None:
            self.skipTest(
                'attendance_attendance.dart not found; set HORILLA_MOBILE_RECAP_PATH or place mobile repo nearby'
            )

        source = mobile_recap.read_text()
        self.assertIn('final String lateMinutes;', source)
        self.assertIn('final String earlyOutMinutes;', source)
        self.assertIn('final String totalMinutes;', source)
        self.assertIn("lateMinutes: _toSafeMinuteText(json['late_minutes'], fallback: '0')", source)
        self.assertIn("earlyOutMinutes: _toSafeMinuteText(json['early_out_minutes'], fallback: '0')", source)
        self.assertIn("totalMinutes: _toSafeMinuteText(json['total_minutes'], fallback: '0')", source)
        self.assertIn("value: _formatPenaltyText(row.lateMinutes, row.late)", source)
        self.assertIn("value: _formatPenaltyText(row.earlyOutMinutes, row.earlyOut)", source)


if __name__ == '__main__':
    unittest.main()
