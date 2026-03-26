from types import SimpleNamespace
from unittest.mock import patch

from django.contrib.auth.models import User
from django.test import TestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from attendance.models import Attendance
from horilla_api.api_views.attendance.views import AttendanceRequestView


class AttendanceRequestApiRegressionsTests(TestCase):
    def setUp(self):
        self.factory = APIRequestFactory()
        self.user = User.objects.create(username="req-user")

    @patch("horilla_api.api_views.attendance.views.AttendanceFilters")
    @patch("horilla_api.api_views.attendance.views.filtersubordinates")
    def test_list_does_not_crash_when_combining_approval_and_my_request_querysets(self, mock_filtersubordinates, mock_filters_cls):
        mine = Attendance.objects.none().distinct()
        approvals = Attendance.objects.none()
        mock_filtersubordinates.return_value = approvals
        mock_filters_cls.return_value = SimpleNamespace(qs=Attendance.objects.none())

        with patch.object(Attendance.objects, "filter", side_effect=[mine, mine]):
            request = self.factory.get("/api/attendance/attendance-request/")
            force_authenticate(request, user=self.user)
            response = AttendanceRequestView.as_view()(request)

        self.assertEqual(response.status_code, 200)
