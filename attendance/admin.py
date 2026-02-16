"""
admin.py

This page is used to register attendance models with admins site.
"""

from django.contrib import admin

from .models import (
    Attendance,
    AttendanceActivity,
    AttendanceLateComeEarlyOut,
    AttendanceOverTime,
    AttendanceRequestComment,
    AttendanceRequestFile,
    AttendanceValidationCondition,
    GraceTime,
    WorkRecords,
    WorkModeRequest,
)

# Register your models here.
admin.site.register(Attendance)
admin.site.register(AttendanceActivity)
admin.site.register(AttendanceOverTime)
admin.site.register(AttendanceLateComeEarlyOut)
admin.site.register(AttendanceValidationCondition)
admin.site.register(GraceTime)
admin.site.register(AttendanceRequestComment)
admin.site.register(AttendanceRequestFile)
admin.site.register(WorkRecords)


@admin.register(WorkModeRequest)
class WorkModeRequestAdmin(admin.ModelAdmin):
    list_display = (
        "id",
        "employee_id",
        "mode",
        "scope",
        "start_date",
        "end_date",
        "status",
        "approved_by",
        "approved_at",
    )
    list_filter = ("mode", "scope", "status")
    search_fields = (
        "employee_id__employee_first_name",
        "employee_id__employee_last_name",
        "employee_id__badge_id",
    )

