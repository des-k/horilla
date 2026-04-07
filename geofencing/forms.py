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

    def __init__(self, *args, read_only=True, include_wfh_fields=True, hide_submit=False, **kwargs):
        self.read_only = read_only
        self.include_wfh_fields = include_wfh_fields
        self.hide_submit = hide_submit
        super().__init__(*args, **kwargs)
        if not self.include_wfh_fields:
            self.fields.pop("wfh_start", None)
            self.fields.pop("wfh_radius_in_meters", None)
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
            "hide_submit": self.hide_submit,
        }
        return render_to_string("geofencing/geofencing_form.html", context)


class WfhGeoFencingConfigForm(ModelForm):
    verbose_name = _("WFH Geofence Configuration")

    class Meta:
        model = GeoFencing
        fields = ["wfh_start", "wfh_radius_in_meters", "company_id"]
        widgets = {"company_id": forms.HiddenInput()}

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        if "wfh_start" in self.fields:
            self.fields["wfh_start"].help_text = _("Enable or disable WFH home geofencing.")
            self.fields["wfh_start"].widget.attrs.update({"class": "oh-switch__checkbox"})
        if "wfh_radius_in_meters" in self.fields:
            self.fields["wfh_radius_in_meters"].help_text = _("Global WFH radius in meters. Value must be greater than 0.")
            self.fields["wfh_radius_in_meters"].widget.attrs.update({"class": "oh-input w-100", "min": 1})

    def clean_wfh_radius_in_meters(self):
        value = int(self.cleaned_data.get("wfh_radius_in_meters") or 0)
        if value <= 0:
            raise forms.ValidationError(_("WFH radius must be greater than 0."))
        return value
