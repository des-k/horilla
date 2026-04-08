from types import SimpleNamespace
from unittest.mock import patch

from django.http import HttpResponse
from django.test import RequestFactory, SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from horilla_api.api_views.employee.views import (
    EmployeeFaceImageAPIView,
    EmployeeProfileImageAPIView,
)
from horilla_api.utils.private_media_urls import (
    build_employee_face_api_url,
    build_employee_profile_api_url,
)


class _AuthUser:
    is_authenticated = True

    def __init__(self, employee, allow_global=False):
        self.employee_get = employee
        self._allow_global = allow_global

    def has_perm(self, perm):
        return self._allow_global and perm == "employee.view_employee"


class PrivateMediaUrlHelperTests(SimpleTestCase):
    def setUp(self):
        self.request = RequestFactory().get("/")

    def test_build_employee_profile_api_url_uses_private_api_path(self):
        employee = SimpleNamespace(id=5, employee_profile=object())
        url = build_employee_profile_api_url(employee)
        self.assertEqual(url, "/api/employee/employees/5/profile-image/")

    def test_build_employee_face_api_url_uses_private_api_path(self):
        employee = SimpleNamespace(id=7)
        face = SimpleNamespace(image=object())
        url = build_employee_face_api_url(employee, face=face)
        self.assertEqual(url, "/api/employee/employees/7/face-image/")


class PrivateMediaEndpointTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()

    def test_profile_image_endpoint_allows_self(self):
        employee = SimpleNamespace(id=3, employee_profile=SimpleNamespace())
        user = _AuthUser(employee)
        request = self.factory.get("/api/employee/employees/3/profile-image/")
        force_authenticate(request, user=user)

        with patch("horilla_api.api_views.employee.views.object_check", return_value=employee), patch(
            "horilla_api.api_views.employee.views.private_file_response",
            return_value=HttpResponse(status=200),
        ) as mock_response:
            response = EmployeeProfileImageAPIView.as_view()(request, pk=3)

        self.assertEqual(response.status_code, 200)
        mock_response.assert_called_once()

    def test_profile_image_endpoint_rejects_out_of_scope_user(self):
        requester = SimpleNamespace(id=1, get_subordinate_employees=lambda: SimpleNamespace(filter=lambda **kwargs: SimpleNamespace(exists=lambda: False)))
        target = SimpleNamespace(id=2, employee_profile=SimpleNamespace())
        user = _AuthUser(requester)
        request = self.factory.get("/api/employee/employees/2/profile-image/")
        force_authenticate(request, user=user)

        with patch("horilla_api.api_views.employee.views.object_check", return_value=target):
            response = EmployeeProfileImageAPIView.as_view()(request, pk=2)

        self.assertEqual(response.status_code, 403)

    def test_face_image_endpoint_allows_self(self):
        employee = SimpleNamespace(id=4)
        face = SimpleNamespace(image=SimpleNamespace())
        user = _AuthUser(employee)
        request = self.factory.get("/api/employee/employees/4/face-image/")
        force_authenticate(request, user=user)

        with patch("horilla_api.api_views.employee.views.object_check", return_value=employee), patch(
            "horilla_api.api_views.employee.views.EmployeeFaceDetection.objects.filter"
        ) as mock_filter, patch(
            "horilla_api.api_views.employee.views.private_file_response",
            return_value=HttpResponse(status=200),
        ) as mock_response:
            mock_filter.return_value.first.return_value = face
            response = EmployeeFaceImageAPIView.as_view()(request, pk=4)

        self.assertEqual(response.status_code, 200)
        mock_response.assert_called_once_with(face.image, as_attachment=False)
