from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
API_VIEWS = ROOT / 'horilla_api' / 'api_views' / 'attendance' / 'views.py'
MOBILE_RECAP = ROOT.parent / 'lib' / 'attendance_views' / 'attendance_attendance.dart'


class MonthlyRecapMobileContractStandaloneTests(unittest.TestCase):
    def test_api_monthly_recap_rows_publish_decimal_minute_fields(self):
        source = API_VIEWS.read_text()
        self.assertIn('"late_minutes": format_decimal_minutes(getattr(r, "late_minutes", 0) or 0)', source)
        self.assertIn('"early_out_minutes": format_decimal_minutes(getattr(r, "early_out_minutes", 0) or 0)', source)

    def test_mobile_summary_and_rows_use_decimal_minute_strings(self):
        source = MOBILE_RECAP.read_text()
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
