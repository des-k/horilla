from django.utils.translation import gettext_lazy as _


GEOFENCING_DISABLED_NOTE = _("Geofencing is currently disabled by business policy.")
GEOFENCING_DISABLED_HELP_TEXT = _(
    "This control is locked and attendance punches will not be validated against a geofence."
)


def geofencing_is_effectively_enabled(*args, **kwargs) -> bool:
    """Business-policy source of truth.

    Geofencing remains visible in settings for transparency, but the feature is
    globally disabled for the active attendance flow.
    """
    return False



def coerce_geofencing_start(_value=None) -> bool:
    """Normalize any persisted or incoming toggle to the effective OFF state."""
    return geofencing_is_effectively_enabled()
