from django.test import SimpleTestCase

from attendance.services.check_in_out_test_blueprints import (
    PRIORITY_ASSERTION_BUNDLES,
    SOURCE_BLUEPRINTS,
    build_priority_scenarios,
    iter_scenario_families,
)


class CheckInOutCatalogIntegrityTests(SimpleTestCase):
    def test_scenario_family_ids_are_unique(self):
        families = list(iter_scenario_families())
        self.assertGreater(len(families), 0)
        ids = [case.scenario_id for case in families]
        self.assertEqual(len(ids), len(set(ids)))

    def test_priority_scenarios_cover_mobile_biometric_leave_and_grace(self):
        priority = build_priority_scenarios()
        ids = {case.scenario_id for case in priority}

        self.assertTrue(any("/BIO_BIO/" in case_id for case_id in ids))
        self.assertTrue(any("/MOB_MOB/" in case_id for case_id in ids))
        self.assertTrue(any("/MOB_MULTI_IN_ATTEMPT/" in case_id for case_id in ids))
        self.assertTrue(any("LEAVE_FIRST_HALF_APPROVED" in case_id for case_id in ids))
        self.assertTrue(any("LEAVE_SECOND_HALF_APPROVED" in case_id for case_id in ids))
        self.assertTrue(any(case_id.endswith("/GRACE_BEFORE_AFTER") for case_id in ids))

    def test_every_source_blueprint_has_unique_code(self):
        codes = [case.code for case in SOURCE_BLUEPRINTS]
        self.assertEqual(len(codes), len(set(codes)))

    def test_every_family_maps_to_known_assertion_bundle(self):
        for family in iter_scenario_families():
            with self.subTest(family=family.scenario_id):
                self.assertIn(family.expected_assertion_bundle, PRIORITY_ASSERTION_BUNDLES)
