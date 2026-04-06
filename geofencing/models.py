from django.core.exceptions import ValidationError
from django.db import models
from django.db.models import Q
from geopy.geocoders import Nominatim

from .policy import coerce_geofencing_start, geofencing_is_effectively_enabled


class GeoFencing(models.Model):
    latitude = models.FloatField()
    longitude = models.FloatField()
    radius_in_meters = models.IntegerField()
    company_id = models.OneToOneField(
        "base.Company",
        related_name="geo_fencing",
        on_delete=models.CASCADE,
        blank=True,
        null=True,
    )
    start = models.BooleanField(default=False)
    wfh_start = models.BooleanField(default=True)
    wfh_radius_in_meters = models.PositiveIntegerField(default=250)

    @property
    def effective_start(self) -> bool:
        return geofencing_is_effectively_enabled(instance=self)

    def clean(self):
        if self.company_id is None:
            qs = GeoFencing.objects.filter(company_id__isnull=True)
            if self.pk:
                qs = qs.exclude(pk=self.pk)
            if qs.exists():
                raise ValidationError("Only one GeoFencing can have a null company_id.")

        geolocator = Nominatim(
            user_agent="geo_checker_unique"
        )  # Unique user-agent is important
        if self.start:
            try:
                location = geolocator.reverse(
                    (self.latitude, self.longitude), exactly_one=True
                )
                if not location:
                    raise ValidationError("Invalid location coordinates.")
            except Exception as e:
                raise ValidationError(f"Geolocation error: {e}")

        return super().clean()

    def save(self, *args, **kwargs):
        self.start = coerce_geofencing_start(self.start)
        if int(self.wfh_radius_in_meters or 0) <= 0:
            raise ValidationError("WFH radius must be greater than 0.")
        self.full_clean()  # Run clean before save
        super().save(*args, **kwargs)

    class Meta:
        constraints = [
            models.UniqueConstraint(
                fields=["company_id"],
                name="unique_company_id_when_not_null_geofencing",
                condition=~Q(company_id=None),
            )
        ]
