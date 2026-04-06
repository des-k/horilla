from django import forms
from django.template.loader import render_to_string
from django.utils.translation import gettext_lazy as _

from base.forms import ModelForm

from .models import GeoFencing
from .policy import GEOFENCING_DISABLED_HELP_TEXT, GEOFENCING_DISABLED_NOTE


class GeoFencingSetupForm(ModelForm):
    verbose_name = _("Geofence Configuration")

    class Meta:
        model = GeoFencing
        fields = "__all__"
        widgets = {"company_id": forms.HiddenInput()}

    def __init__(self, *args, read_only=True, **kwargs):
        self.read_only = read_only
        super().__init__(*args, **kwargs)
        self.fields["start"].help_text = GEOFENCING_DISABLED_NOTE

        if self.read_only:
            editable_when_readonly = {"wfh_start", "wfh_radius_in_meters", "company_id"}
            for name, field in self.fields.items():
                if name not in editable_when_readonly:
                    field.disabled = True
                    field.help_text = field.help_text or GEOFENCING_DISABLED_HELP_TEXT
            if "wfh_start" in self.fields:
                self.fields["wfh_start"].help_text = _("Enable or disable WFH home geofencing.")
            if "wfh_radius_in_meters" in self.fields:
                self.fields["wfh_radius_in_meters"].help_text = _("Global WFH radius in meters. Value must be greater than 0.")

    def as_p(self):
        """Render the form with the geofencing read-only state."""
        context = {
            "form": self,
            "hide_submit": False,
        }
        return render_to_string("geofencing/geofencing_form.html", context)
