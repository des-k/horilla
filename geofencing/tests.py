from types import SimpleNamespace
from unittest.mock import patch

from django.contrib.messages.storage.fallback import FallbackStorage
from django.contrib.sessions.middleware import SessionMiddleware
from django.template.loader import render_to_string
from django.test import RequestFactory, SimpleTestCase
from rest_framework.test import APIRequestFactory, force_authenticate

from geofencing.models import GeoFencing
from geofencing.serializers import GeoFencingSetupSerializer
from geofencing.views import GeoFencingEmployeeLocationCheckAPIView, geo_location_config


class _PermissiveUser:
    is_authenticated = True
    is_anonymous = False
    is_superuser = True

    def has_perm(self, _perm):
        return True

    def has_perms(self, _perms):
        return True




def _fake_render(_request, template_name, context):
    bound_context = dict(context)
    bound_context["request"] = _request
    content = render_to_string(template_name, bound_context)
    return SimpleNamespace(status_code=200, content=content.encode(), render=lambda: None)


class GeofencingPolicyTests(SimpleTestCase):
    databases = {'default'}

    def setUp(self):
        self.factory = RequestFactory()
        self.api_factory = APIRequestFactory()
        self.user = _PermissiveUser()
        self.company = SimpleNamespace(id=7, company="Horilla HQ")

    def _attach_session_and_messages(self, request):
        middleware = SessionMiddleware(lambda req: None)
        middleware.process_request(request)
        request.session.save()
        setattr(request, "_messages", FallbackStorage(request))
        return request

    def test_model_save_forces_start_false(self):
        geo = GeoFencing(
            latitude=10.0,
            longitude=76.0,
            radius_in_meters=100,
            start=True,
        )

        with patch.object(GeoFencing, "full_clean") as clean_mock, patch(
            "django.db.models.Model.save", return_value=None
        ) as model_save_mock:
            geo.save()

        self.assertFalse(geo.start)
        clean_mock.assert_called_once()
        model_save_mock.assert_called_once()

    def test_serializer_coerces_start_false_for_input_and_output(self):
        serializer = GeoFencingSetupSerializer(
            data={
                "latitude": 10.1,
                "longitude": 76.2,
                "radius_in_meters": 250,
                "start": True,
            }
        )
        self.assertTrue(serializer.is_valid(), serializer.errors)
        self.assertFalse(serializer.validated_data["start"])

        instance = GeoFencing(
            latitude=10.1,
            longitude=76.2,
            radius_in_meters=250,
            start=True,
        )
        self.assertFalse(GeoFencingSetupSerializer(instance).data["start"])

    def test_web_settings_show_disabled_read_only_state(self):
        request = self.factory.get("/api/geofencing/config/")
        request.user = self.user
        self._attach_session_and_messages(request)
        request.session["selected_company"] = self.company.id

        location = GeoFencing(
            latitude=11.0,
            longitude=75.0,
            radius_in_meters=150,
            start=True,
        )

        with patch("geofencing.views.get_company", return_value=self.company), patch(
            "geofencing.views.get_company_location", return_value=location
        ), patch("geofencing.views.render", side_effect=_fake_render):
            response = geo_location_config(request)

        response.render()
        content = response.content.decode()
        self.assertEqual(response.status_code, 200)
        self.assertIn("Geofencing is currently disabled by business policy.", content)
        self.assertIn("Disabled", content)
        self.assertIn("Geofencing is currently disabled by business policy.", content)
        self.assertIn('id="id_latitude"', content)
        self.assertIn('disabled', content)
        self.assertIn('Apply Home Reset', content)
        self.assertNotIn('Apply Face Reset', content)

    def test_web_settings_post_updates_only_wfh_config(self):
        request = self.factory.post(
            "/api/geofencing/config/",
            {
                "action": "update_wfh_config",
                "wfh_start": "",
                "wfh_radius_in_meters": 999,
            },
        )
        request.user = self.user
        self._attach_session_and_messages(request)
        request.session["selected_company"] = self.company.id

        location = GeoFencing(
            latitude=10.5,
            longitude=76.5,
            radius_in_meters=300,
            start=False,
            wfh_start=True,
            wfh_radius_in_meters=250,
        )
        saved_obj = GeoFencing(
            latitude=10.5,
            longitude=76.5,
            radius_in_meters=300,
            start=False,
            wfh_start=False,
            wfh_radius_in_meters=999,
        )

        with patch("geofencing.views.get_company", return_value=self.company), patch(
            "geofencing.views.get_company_location", return_value=location
        ), patch.object(GeoFencing.objects, "update_or_create", return_value=(saved_obj, False)) as update_mock, patch(
            "geofencing.views.sync_wfh_radius_profiles_for_company"
        ) as sync_mock, patch("geofencing.views.render", side_effect=_fake_render):
            response = geo_location_config(request)

        response.render()
        content = response.content.decode()
        self.assertEqual(response.status_code, 200)
        self.assertNotIn('value="250"', content)
        self.assertIn('value="999"', content)
        update_mock.assert_called_once_with(
            company_id=self.company,
            defaults={
                "wfh_start": False,
                "wfh_radius_in_meters": 999,
            },
        )
        sync_mock.assert_called_once_with(company=self.company, radius=999)

    def test_location_check_accepts_when_policy_disables_geofencing(self):
        request = self.api_factory.post(
            "/api/geofencing/location-check/",
            {"latitude": 50.0, "longitude": 50.0},
            format="json",
        )
        force_authenticate(request, user=self.user)

        location = GeoFencing(
            latitude=10.0,
            longitude=76.0,
            radius_in_meters=100,
            start=True,
        )

        with patch.object(
            GeoFencingEmployeeLocationCheckAPIView,
            "get_company_location",
            return_value=location,
        ), patch.object(
            GeoFencingEmployeeLocationCheckAPIView,
            "get_company",
            return_value=self.company,
        ):
            response = GeoFencingEmployeeLocationCheckAPIView.as_view()(request)

        self.assertEqual(response.status_code, 200)
        self.assertEqual(response.data["message"], "Location accepted")
