"""
attendance/sidebar.py
"""

from django.urls import reverse
from django.utils.translation import gettext_lazy as _

from base.context_processors import enable_late_come_early_out_tracking
from base.templatetags.basefilters import is_reportingmanager

MENU = _("Attendance")
IMG_SRC = "images/ui/attendances.svg"


SUBMENUS = [
    {
        "menu": _("Attendances"),
        "redirect": reverse("attendance-employee-month-view"),
        "accessibility": "attendance.sidebar.attendances_accessibility",
    },
    {
        "menu": _("Attendance Requests"),
        "redirect": reverse("request-attendance-view"),
    },
    {
        "menu": _("Work Type Requests"),
        "redirect": reverse("attendance-work-type-request-view"),
    },
    {
        "menu": _("Attendance Activities"),
        "redirect": reverse("attendance-activity-view"),
    },
    {
        "menu": _("Punching History"),
        "redirect": reverse("attendance-punching-history-view"),
        "accessibility": "attendance.sidebar.punching_history_accessibility",
    },
    {
        "menu": _("Late Come Early Out"),
        "redirect": reverse("late-come-early-out-view"),
        "accessibility": "attendance.sidebar.tracking_accessibility",
    },
]


def attendances_accessibility(request, submenu, user_perms, *args, **kwargs):
    """
    Check if the user has permission to view attendance or is a reporting manager.
    """
    return request.user.has_perm("attendance.view_attendance") or is_reportingmanager(
        request.user
    )


def tracking_accessibility(request, submenu, user_perms, *args, **kwargs):
    """
    Determine if late come/early out tracking is enabled.
    """
    return enable_late_come_early_out_tracking(None).get("tracking")


def punching_history_accessibility(request, submenu, user_perms, *args, **kwargs):
    """Allow explicit audit permission or self-service employee access."""
    if request.user.is_superuser:
        return True
    if request.user.has_perm("attendance.view_attendancepunchinghistory"):
        return True
    return bool(getattr(request.user, "employee_get", None))
