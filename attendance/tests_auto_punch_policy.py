from unittest.mock import patch

from django.test import SimpleTestCase

from attendance.middleware import AttendanceMiddleware


class AutoPunchOutPolicyTests(SimpleTestCase):
    def test_middleware_trigger_function_exits_early(self):
        middleware = AttendanceMiddleware(lambda request: None)

        with patch("attendance.middleware.logger.debug") as debug_logger:
            result = middleware.trigger_function()

        self.assertIsNone(result)
        debug_logger.assert_called_once()
