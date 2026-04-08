from django.contrib.auth.models import Permission, User
from django.test import Client, RequestFactory, TestCase
from django.urls import reverse

from base.models import Company
from employee.models import Employee, EmployeeWorkInformation
from employee.views import _employee_directory_queryset, _check_reporting_manager


class EmployeeDirectoryVisibilityTests(TestCase):
    def setUp(self):
        self.factory = RequestFactory()
        self.company = Company.objects.create(
            company="Test Co",
            address="Addr",
            country="ID",
            state="JKT",
            city="Jakarta",
            zip="12345",
        )

        self.admin_user = User.objects.create_user(username="admin", password="pass")
        self.admin_employee = self._make_employee(self.admin_user, "Admin", "admin@test.local")
        view_perm = Permission.objects.get(codename="view_employee")
        self.admin_user.user_permissions.add(view_perm)

        self.manager_user = User.objects.create_user(username="manager", password="pass")
        self.manager_employee = self._make_employee(self.manager_user, "Manager", "manager@test.local")

        self.sub_manager_user = User.objects.create_user(username="submanager", password="pass")
        self.sub_manager_employee = self._make_employee(
            self.sub_manager_user,
            "SubManager",
            "submanager@test.local",
            reporting_manager=self.manager_employee,
        )

        self.leaf_user = User.objects.create_user(username="leaf", password="pass")
        self.leaf_employee = self._make_employee(
            self.leaf_user,
            "Leaf",
            "leaf@test.local",
            reporting_manager=self.sub_manager_employee,
        )

        self.staff_user = User.objects.create_user(username="staff", password="pass")
        self.staff_employee = self._make_employee(self.staff_user, "Staff", "staff@test.local")

    def _make_employee(self, user, first_name, email, reporting_manager=None):
        employee = Employee.objects.create(
            employee_user_id=user,
            employee_first_name=first_name,
            email=email,
            phone="08123",
        )
        work_info = employee.employee_work_info
        work_info.company_id = self.company
        work_info.reporting_manager_id = reporting_manager
        work_info.save()
        return employee

    def _request_for(self, user):
        request = self.factory.get("/")
        request.user = user
        return request

    def test_staff_directory_queryset_contains_only_self(self):
        request = self._request_for(self.staff_user)
        qs = _employee_directory_queryset(request, Employee.objects.order_by("id"))
        self.assertQuerySetEqual(qs, [self.staff_employee.id], lambda emp: emp.id)

    def test_manager_directory_queryset_contains_self_and_nested_subordinates(self):
        request = self._request_for(self.manager_user)
        qs = _employee_directory_queryset(request, Employee.objects.order_by("id"))
        self.assertSetEqual(
            set(qs.values_list("id", flat=True)),
            {self.manager_employee.id, self.sub_manager_employee.id, self.leaf_employee.id},
        )

    def test_admin_directory_queryset_contains_everyone(self):
        request = self._request_for(self.admin_user)
        qs = _employee_directory_queryset(request, Employee.objects.order_by("id"))
        self.assertSetEqual(
            set(qs.values_list("id", flat=True)),
            {
                self.admin_employee.id,
                self.manager_employee.id,
                self.sub_manager_employee.id,
                self.leaf_employee.id,
                self.staff_employee.id,
            },
        )

    def test_employee_detail_access_follows_same_scope(self):
        staff_request = self._request_for(self.staff_user)
        self.assertTrue(_check_reporting_manager(staff_request, obj_id=self.staff_employee.id))
        self.assertFalse(_check_reporting_manager(staff_request, obj_id=self.manager_employee.id))

        manager_request = self._request_for(self.manager_user)
        self.assertTrue(_check_reporting_manager(manager_request, obj_id=self.manager_employee.id))
        self.assertTrue(_check_reporting_manager(manager_request, obj_id=self.sub_manager_employee.id))
        self.assertTrue(_check_reporting_manager(manager_request, obj_id=self.leaf_employee.id))
        self.assertFalse(_check_reporting_manager(manager_request, obj_id=self.staff_employee.id))

    def test_employee_view_list_matches_role_scope(self):
        client = Client()

        client.force_login(self.staff_user)
        response = client.get(reverse("employee-view-list"), HTTP_HX_REQUEST="true")
        self.assertEqual(response.status_code, 200)
        self.assertEqual(
            [employee.id for employee in response.context["data"].object_list],
            [self.staff_employee.id],
        )

        client.force_login(self.manager_user)
        response = client.get(reverse("employee-view-list"), HTTP_HX_REQUEST="true")
        self.assertEqual(response.status_code, 200)
        self.assertSetEqual(
            {employee.id for employee in response.context["data"].object_list},
            {self.manager_employee.id, self.sub_manager_employee.id, self.leaf_employee.id},
        )

        client.force_login(self.admin_user)
        response = client.get(reverse("employee-view-list"), HTTP_HX_REQUEST="true")
        self.assertEqual(response.status_code, 200)
        self.assertSetEqual(
            {employee.id for employee in response.context["data"].object_list},
            {
                self.admin_employee.id,
                self.manager_employee.id,
                self.sub_manager_employee.id,
                self.leaf_employee.id,
                self.staff_employee.id,
            },
        )
