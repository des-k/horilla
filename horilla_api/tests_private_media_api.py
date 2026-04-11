from types import SimpleNamespace
from unittest.mock import patch

from django.http import HttpResponse
from django.test import RequestFactory, SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from horilla_api.api_views.employee.views import (
    EmployeeFaceImageAPIView,
    EmployeeProfileAvatarAPIView,
    EmployeeProfileImageAPIView,
)
from horilla_api.api_views.leave.views import (
    LeaveAllocationRequestAttachmentDownloadAPIView,
    LeaveAllocationRequestAttachmentViewAPIView,
    LeaveRequestAttachmentDownloadAPIView,
    LeaveRequestAttachmentViewAPIView,
    LeaveTypeIconAPIView,
)
from horilla_api.utils.private_media_urls import (
    build_employee_face_api_url,
    build_employee_face_api_version,
    build_employee_profile_api_url,
    build_employee_profile_api_version,
    build_employee_profile_avatar_api_url,
    build_employee_profile_avatar_api_version,
    build_leave_allocation_attachment_meta,
    build_leave_request_attachment_meta,
    build_leave_type_icon_api_url,
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

    def test_build_employee_profile_avatar_api_url_uses_private_api_path(self):
        employee = SimpleNamespace(id=5, employee_profile=object())
        url = build_employee_profile_avatar_api_url(employee)
        self.assertEqual(url, "/api/employee/employees/5/profile-avatar/")

    def test_build_employee_profile_api_version_uses_storage_modified_time(self):
        storage = SimpleNamespace(get_modified_time=lambda name: __import__("datetime").datetime(2026, 4, 10, 9, 30, tzinfo=__import__("datetime").timezone.utc))
        employee = SimpleNamespace(employee_profile=SimpleNamespace(name="employee/profile/avatar.png", storage=storage))
        version = build_employee_profile_api_version(employee)
        self.assertEqual(version, "2026-04-10T09:30:00Z")

    def test_build_employee_face_api_version_uses_storage_modified_time(self):
        storage = SimpleNamespace(get_modified_time=lambda name: __import__("datetime").datetime(2026, 4, 10, 9, 45, tzinfo=__import__("datetime").timezone.utc))
        employee = SimpleNamespace(id=7)
        face = SimpleNamespace(image=SimpleNamespace(name="face/image/face.jpg", storage=storage))
        version = build_employee_face_api_version(employee, face=face)
        self.assertEqual(version, "2026-04-10T09:45:00Z")

    def test_build_employee_profile_avatar_api_version_matches_profile_version(self):
        storage = SimpleNamespace(get_modified_time=lambda name: __import__("datetime").datetime(2026, 4, 10, 9, 30, tzinfo=__import__("datetime").timezone.utc))
        employee = SimpleNamespace(employee_profile=SimpleNamespace(name="employee/profile/avatar.png", storage=storage))
        version = build_employee_profile_avatar_api_version(employee)
        self.assertEqual(version, "2026-04-10T09:30:00Z")

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

    def test_profile_avatar_endpoint_allows_self(self):
        employee = SimpleNamespace(id=3, employee_profile=SimpleNamespace())
        user = _AuthUser(employee)
        request = self.factory.get("/api/employee/employees/3/profile-avatar/")
        force_authenticate(request, user=user)

        avatar_file = SimpleNamespace()
        with patch("horilla_api.api_views.employee.views.object_check", return_value=employee), patch(
            "horilla_api.api_views.employee.views.ensure_employee_profile_avatar",
            return_value="employee/profile/avatar__avatar.jpg",
        ), patch(
            "horilla_api.api_views.employee.views.employee_profile_avatar_file",
            return_value=avatar_file,
        ), patch(
            "horilla_api.api_views.employee.views.private_file_response",
            return_value=HttpResponse(status=200),
        ) as mock_response:
            response = EmployeeProfileAvatarAPIView.as_view()(request, pk=3)

        self.assertEqual(response.status_code, 200)
        mock_response.assert_called_once_with(avatar_file, as_attachment=False)

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


class LeavePrivateMediaHelperTests(SimpleTestCase):
    def test_build_leave_type_icon_api_url_uses_private_api_path(self):
        leave_type = SimpleNamespace(id=9, icon=object())
        url = build_leave_type_icon_api_url(leave_type)
        self.assertEqual(url, "/api/leave/leave-type/9/icon/")

    def test_build_leave_request_attachment_meta_uses_private_api_paths(self):
        leave_request = SimpleNamespace(id=11, attachment=SimpleNamespace(name="leave/request/file.pdf"))
        meta = build_leave_request_attachment_meta(leave_request)
        self.assertEqual(meta["name"], "file.pdf")
        self.assertEqual(meta["view_url"], "/api/leave/request/11/attachment/view/")
        self.assertEqual(meta["download_url"], "/api/leave/request/11/attachment/download/")

    def test_build_leave_allocation_attachment_meta_uses_private_api_paths(self):
        allocation = SimpleNamespace(id=12, attachment=SimpleNamespace(name="leave/allocation/proof.png"))
        meta = build_leave_allocation_attachment_meta(allocation)
        self.assertEqual(meta["name"], "proof.png")
        self.assertEqual(meta["view_url"], "/api/leave/allocation-request/12/attachment/view/")
        self.assertEqual(meta["download_url"], "/api/leave/allocation-request/12/attachment/download/")


class LeavePrivateMediaEndpointTests(SimpleTestCase):
    def setUp(self):
        self.factory = APIRequestFactory()

    def test_leave_type_icon_endpoint_allows_authenticated_user(self):
        request = self.factory.get('/api/leave/leave-type/5/icon/')
        force_authenticate(request, user=_AuthUser(SimpleNamespace(id=1)))
        leave_type = SimpleNamespace(icon=SimpleNamespace())
        with patch('horilla_api.api_views.leave.views.get_object_or_404', return_value=leave_type), patch(
            'horilla_api.api_views.leave.views.private_file_response', return_value=HttpResponse(status=200)
        ) as mock_response:
            response = LeaveTypeIconAPIView.as_view()(request, pk=5)
        self.assertEqual(response.status_code, 200)
        mock_response.assert_called_once_with(leave_type.icon, as_attachment=False)

    def test_leave_request_attachment_view_allows_owner(self):
        employee = SimpleNamespace(id=2)
        leave_request = SimpleNamespace(pk=7, employee_id_id=2, attachment=SimpleNamespace())
        request = self.factory.get('/api/leave/request/7/attachment/view/')
        force_authenticate(request, user=_AuthUser(employee))
        with patch('horilla_api.api_views.leave.views.get_object_or_404', return_value=leave_request), patch(
            'horilla_api.api_views.leave.views.private_file_response', return_value=HttpResponse(status=200)
        ) as mock_response:
            response = LeaveRequestAttachmentViewAPIView.as_view()(request, pk=7)
        self.assertEqual(response.status_code, 200)
        mock_response.assert_called_once_with(leave_request.attachment, as_attachment=False)

    def test_leave_request_attachment_download_rejects_out_of_scope_user(self):
        requester = SimpleNamespace(id=1)
        leave_request = SimpleNamespace(pk=8, employee_id_id=2, attachment=SimpleNamespace())
        request = self.factory.get('/api/leave/request/8/attachment/download/')
        force_authenticate(request, user=_AuthUser(requester))
        with patch('horilla_api.api_views.leave.views.get_object_or_404', return_value=leave_request), patch(
            'horilla_api.api_views.leave.views.filtersubordinates'
        ) as mock_filters, patch('horilla_api.api_views.leave.views.filter_conditional_leave_request') as mock_conditional:
            mock_filters.return_value.exists.return_value = False
            mock_conditional.return_value.filter.return_value.exists.return_value = False
            response = LeaveRequestAttachmentDownloadAPIView.as_view()(request, pk=8)
        self.assertEqual(response.status_code, 403)

    def test_leave_allocation_attachment_view_allows_creator(self):
        employee = SimpleNamespace(id=4)
        allocation = SimpleNamespace(pk=3, employee_id_id=5, created_by_id=4, attachment=SimpleNamespace())
        request = self.factory.get('/api/leave/allocation-request/3/attachment/view/')
        force_authenticate(request, user=_AuthUser(employee))
        with patch('horilla_api.api_views.leave.views.get_object_or_404', return_value=allocation), patch(
            'horilla_api.api_views.leave.views.private_file_response', return_value=HttpResponse(status=200)
        ) as mock_response:
            response = LeaveAllocationRequestAttachmentViewAPIView.as_view()(request, pk=3)
        self.assertEqual(response.status_code, 200)
        mock_response.assert_called_once_with(allocation.attachment, as_attachment=False)

    def test_leave_allocation_attachment_download_rejects_out_of_scope_user(self):
        employee = SimpleNamespace(id=4)
        allocation = SimpleNamespace(pk=3, employee_id_id=5, created_by_id=6, attachment=SimpleNamespace())
        request = self.factory.get('/api/leave/allocation-request/3/attachment/download/')
        force_authenticate(request, user=_AuthUser(employee))
        with patch('horilla_api.api_views.leave.views.get_object_or_404', return_value=allocation), patch(
            'horilla_api.api_views.leave.views.filtersubordinates'
        ) as mock_filters:
            mock_filters.return_value.exists.return_value = False
            response = LeaveAllocationRequestAttachmentDownloadAPIView.as_view()(request, pk=3)
        self.assertEqual(response.status_code, 403)
