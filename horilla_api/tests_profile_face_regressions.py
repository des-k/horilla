from io import BytesIO
from unittest.mock import patch

from django.contrib.auth.models import User
from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import TestCase
from PIL import Image
from rest_framework.test import APIRequestFactory

from employee.models import Employee
from horilla_api.api_serializers.employee.serializers import EmployeeSerializer


def _png_file(name='test.png', color=(255, 0, 0)):
    bio = BytesIO()
    img = Image.new('RGB', (2, 2), color=color)
    img.save(bio, format='PNG')
    bio.seek(0)
    return SimpleUploadedFile(name, bio.read(), content_type='image/png')


class EmployeeProfileSerializerRegressionTests(TestCase):
    def setUp(self):
        self.user = User.objects.create_user(username='serializer-user', password='pass')
        self.employee = Employee.objects.create(
            employee_user_id=self.user,
            employee_first_name='Serializer',
            employee_last_name='User',
            email='serializer@example.com',
            phone='1234567890',
            badge_id='SER-1',
        )
        self.factory = APIRequestFactory()

    @patch('horilla_api.api_serializers.employee.serializers.get_next_badge_id', return_value='SER-2')
    def test_employee_serializer_accepts_profile_upload_and_returns_private_api_url(self, _next_badge):
        uploaded = _png_file('avatar.png')
        serializer = EmployeeSerializer(
            self.employee,
            data={'employee_profile': uploaded},
            partial=True,
            context={'request': self.factory.get('/api/employee/employees/1/')},
        )
        self.assertTrue(serializer.is_valid(), serializer.errors)
        saved = serializer.save()
        self.assertTrue(bool(saved.employee_profile))
        self.assertEqual(
            serializer.data['employee_profile'],
            f'http://testserver/api/employee/employees/{self.employee.id}/profile-image/',
        )
