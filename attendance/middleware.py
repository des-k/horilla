"""
Middleware to automatically trigger employee clock-out based on shift schedules.
"""

import logging
from datetime import datetime, timedelta

from django.utils import timezone
from django.utils.deprecation import MiddlewareMixin

from attendance.methods.utils import Request, strtime_seconds

logger = logging.getLogger(__name__)


class AttendanceMiddleware(MiddlewareMixin):
    """
    Automatic punch-out is disabled by business policy.

    The middleware remains in place to preserve import/runtime wiring, but it exits early
    and never performs automatic clock-out actions.
    """

    def process_request(self, request):
        self.trigger_function()

    def trigger_function(self):
        logger.debug("Automatic punch-out is disabled by business policy.")
        return
