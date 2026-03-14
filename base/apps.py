"""
This module contains the configuration for the 'base' app.
"""

from django.apps import AppConfig
from django.db import connection


class BaseConfig(AppConfig):
    """
    Configuration class for the 'base' app.
    """

    default_auto_field = "django.db.models.BigAutoField"
    name = "base"

    @staticmethod
    def _table_exists(table_name: str) -> bool:
        try:
            return table_name in connection.introspection.table_names()
        except Exception:
            return False

    def ready(self) -> None:
        from base import signals

        super().ready()
        try:
            from base.models import EmployeeShiftDay

            if not self._table_exists(EmployeeShiftDay._meta.db_table):
                return

            if not EmployeeShiftDay.objects.exists():
                days = [
                    ("monday", "Monday"),
                    ("tuesday", "Tuesday"),
                    ("wednesday", "Wednesday"),
                    ("thursday", "Thursday"),
                    ("friday", "Friday"),
                    ("saturday", "Saturday"),
                    ("sunday", "Sunday"),
                ]

                EmployeeShiftDay.objects.bulk_create(
                    [EmployeeShiftDay(day=day[0]) for day in days]
                )
        except Exception:
            pass
