import io
import shutil
import tempfile

from django.contrib.auth.models import User
from django.core.files.uploadedfile import SimpleUploadedFile
from django.test import TestCase, override_settings
from PIL import Image
from rest_framework.test import APIClient

from employee.models import Employee

TMP_MEDIA_ROOT = tempfile.mkdtemp(prefix='horilla_profile_update_')


@override_settings(MEDIA_ROOT=TMP_MEDIA_ROOT)
class EmployeeProfileUpdateApiTests(TestCase):
    @classmethod
    def tearDownClass(cls):
        super().tearDownClass()
        shutil.rmtree(TMP_MEDIA_ROOT, ignore_errors=True)

    def _image_upload(self, color='blue'):
        buf = io.BytesIO()
        Image.new('RGB', (4, 4), color=color).save(buf, format='PNG')
        return SimpleUploadedFile(f'{color}.png', buf.getvalue(), content_type='image/png')

    def setUp(self):
        self.user = User.objects.create_user(username='employee-user', password='pw123456')
        self.employee = Employee.objects.create(
            employee_user_id=self.user,
            employee_first_name='Emp',
            employee_last_name='User',
            email='employee@example.com',
            phone='08123',
        )
        self.client = APIClient()
        self.client.force_authenticate(user=self.user)

    def test_self_put_updates_profile_image_and_returns_new_url(self):
        response = self.client.put(
            f'/api/employee/employees/{self.employee.id}/',
            {'employee_profile': self._image_upload('green')},
            format='multipart',
        )

        self.assertEqual(response.status_code, 200)
        self.employee.refresh_from_db()
        self.assertTrue(bool(self.employee.employee_profile))
        self.assertIn('/media/', response.data.get('employee_profile', ''))
