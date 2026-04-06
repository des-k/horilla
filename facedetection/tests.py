from unittest.mock import patch

from django.contrib.auth.models import Permission, User
from django.contrib.messages.storage.fallback import FallbackStorage
from django.contrib.sessions.middleware import SessionMiddleware
from django.http import HttpResponse
from django.template import engines
from django.test import RequestFactory, TestCase

from attendance.models import EmployeeWfhProfile
from base.models import Company
from employee.models import Employee, EmployeeWorkInformation
from facedetection.models import FaceDetection
from facedetection.views import face_detection_config


def _fake_render(_request, template_name, context):
    template = engines["django"].get_template(template_name)
    return HttpResponse(template.render(context, _request))


class FaceDetectionConfigTests(TestCase):
    def setUp(self):
        self.factory = RequestFactory()
        self.company = Company.objects.create(company="Face Co")
        self.user = User.objects.create_user(username="face-admin", password="pwd")
        perms = Permission.objects.filter(codename__in=["add_localbackup", "reset_wfh_face_detection"])
        self.user.user_permissions.set(perms)
        self.user.has_perm = lambda perm, obj=None: perm in {"geofencing.add_localbackup", "attendance.reset_wfh_face_detection"}
        self.employee = Employee.objects.create(
            employee_first_name="Face",
            employee_last_name="User",
            email="face-user@example.com",
            phone="1234567890",
        )
        self.user.employee_get = self.employee
        self.employee.employee_work_info.company_id = self.company
        self.employee.employee_work_info.save()
        FaceDetection.objects.create(company_id=self.company, start=True)

        self.target = Employee.objects.create(
            employee_first_name="Target",
            employee_last_name="Employee",
            email="target-face@example.com",
            phone="9999999999",
        )
        self.target.employee_work_info.company_id = self.company
        self.target.employee_work_info.save()

    def _attach_session_and_messages(self, request):
        middleware = SessionMiddleware(lambda req: None)
        middleware.process_request(request)
        request.session.save()
        setattr(request, "_messages", FallbackStorage(request))

    def test_face_config_contains_face_reset_controls(self):
        request = self.factory.get("/facedetection/", HTTP_HX_REQUEST="true")
        request.user = self.user
        self._attach_session_and_messages(request)
        request.session["selected_company"] = self.company.id

        with patch("facedetection.views.render", side_effect=_fake_render):
            response = face_detection_config(request)

        content = response.content.decode()
        self.assertEqual(response.status_code, 200)
        self.assertIn("Reset Face Detection For", content)
        self.assertIn("Apply Face Reset", content)
        self.assertIn('name="action" value="reset_face"', content)

    def test_reset_face_post_sets_reenrollment_flag(self):
        request = self.factory.post("/facedetection/", {"action": "reset_face", "employee_id": str(self.target.id)}, HTTP_HX_REQUEST="true")
        request.user = self.user
        self._attach_session_and_messages(request)
        request.session["selected_company"] = self.company.id

        with patch("facedetection.views.render", side_effect=_fake_render):
            response = face_detection_config(request)

        self.assertEqual(response.status_code, 200)
        profile = EmployeeWfhProfile.objects.get(employee=self.target)
        self.assertTrue(profile.requires_face_reenrollment)
