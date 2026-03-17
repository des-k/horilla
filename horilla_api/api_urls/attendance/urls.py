"""
horilla_api/urls/attendance/urls.py
"""

from django.urls import path

from horilla_api.api_views.attendance.permission_views import (
    AttendancePermissionCheck,
    AttendanceRequestApprovePermissionCheck,
    WorkModeRequestApprovePermissionCheck,
)
from horilla_api.api_views.attendance.views import *

urlpatterns = [
    path("clock-in/", ClockInAPIView.as_view(), name="api-check-in"),
    path("clock-out/", ClockOutAPIView.as_view(), name="api-check-out"),
    path("attendance/", AttendanceView.as_view(), name="api-attendance-list"),
    path("attendance/<int:pk>", AttendanceView.as_view(), name="api-attendance-detail"),
    path(
        "attendance/list/<str:type>",
        AttendanceView.as_view(),
        name="api-attendance-list",
    ),
    path("attendance-validate/<int:pk>", ValidateAttendanceView.as_view()),
    path(
        "attendance-request/",
        AttendanceRequestView.as_view(),
        name="api-attendance-request-view",
    ),
    path(
        "attendance-request/<int:pk>",
        AttendanceRequestView.as_view(),
        name="api-attendance-request-view",
    ),
    path(
        "attendance-request-approve/<int:pk>",
        AttendanceRequestApproveView.as_view(),
        name="api-",
    ),
    path(
        "attendance-request-cancel/<int:pk>",
        AttendanceRequestCancelView.as_view(),
        name="api-",
    ),
    path(
        "attendance-request-reject/<int:pk>",
        AttendanceRequestRejectView.as_view(),
        name="api-",
    ),
    path(
        "attendance-request-revoke/<int:pk>",
        AttendanceRequestRevokeView.as_view(),
        name="api-",
    ),
    path("overtime-approve/<int:pk>", OvertimeApproveView.as_view(), name="api-"),
    path(
        "attendance-hour-account/<int:pk>/",
        AttendanceOverTimeView.as_view(),
        name="api-",
    ),
    path("attendance-hour-account/", AttendanceOverTimeView.as_view(), name="api-"),
    path("late-come-early-out-view/", LateComeEarlyOutView.as_view(), name="api-"),
    path("attendance-activity/", AttendanceActivityView.as_view(), name="api-"),
    path("punching-history/", AttendancePunchingHistoryAPIView.as_view(), name="api-attendance-punching-history"),
    path("punching-history", AttendancePunchingHistoryAPIView.as_view(), name="api-attendance-punching-history-noslash"),
    path("today-attendance/", TodayAttendance.as_view(), name="api-"),
    path("offline-employees/count/", OfflineEmployeesCountView.as_view(), name="api-"),
    path("offline-employees/list/", OfflineEmployeesListView.as_view(), name="api-"),
    path("permission-check/attendance", AttendancePermissionCheck.as_view(), name="api-permission-check-attendance-noslash"),
    path("permission-check/attendance/", AttendancePermissionCheck.as_view(), name="api-permission-check-attendance"),
    path(
        "permission-check/attendance-request-approve",
        AttendanceRequestApprovePermissionCheck.as_view(),
        name="api-permission-check-attendance-request-approve-noslash",
    ),
    path(
        "permission-check/attendance-request-approve/",
        AttendanceRequestApprovePermissionCheck.as_view(),
        name="api-permission-check-attendance-request-approve",
    ),
    path(
        "permission-check/work-mode-request-approve",
        WorkModeRequestApprovePermissionCheck.as_view(),
        name="api-permission-check-work-mode-request-approve-noslash",
    ),
    path(
        "permission-check/work-mode-request-approve/",
        WorkModeRequestApprovePermissionCheck.as_view(),
        name="api-permission-check-work-mode-request-approve",
    ),

    # Work mode requests (WFA / On Duty)
    path(
        "work-mode-request/",
        WorkModeRequestView.as_view(),
        name="api-work-mode-request",
    ),
    path(
        "work-mode-request",
        WorkModeRequestView.as_view(),
        name="api-work-mode-request-noslash",
    ),
    path(
        "work-mode-request/<int:pk>",
        WorkModeRequestView.as_view(),
        name="api-work-mode-request-detail",
    ),
    path(
        "work-mode-request/<int:pk>/",
        WorkModeRequestView.as_view(),
        name="api-work-mode-request-detail-slash",
    ),
    path(
        "work-mode-request-approvals/",
        WorkModeRequestApprovalsView.as_view(),
        name="api-work-mode-request-approvals",
    ),
    path(
        "work-mode-request-approvals",
        WorkModeRequestApprovalsView.as_view(),
        name="api-work-mode-request-approvals-noslash",
    ),
    path(
        "work-mode-request-approve/<int:pk>",
        WorkModeRequestApproveView.as_view(),
        name="api-work-mode-request-approve",
    ),
    path(
        "work-mode-request-approve/<int:pk>/",
        WorkModeRequestApproveView.as_view(),
        name="api-work-mode-request-approve-slash",
    ),
    path(
        "work-mode-request-reject/<int:pk>",
        WorkModeRequestRejectView.as_view(),
        name="api-work-mode-request-reject",
    ),
    path(
        "work-mode-request-reject/<int:pk>/",
        WorkModeRequestRejectView.as_view(),
        name="api-work-mode-request-reject-slash",
    ),
    path(
        "work-mode-request-cancel/<int:pk>",
        WorkModeRequestCancelView.as_view(),
        name="api-work-mode-request-cancel",
    ),
    path(
        "work-mode-request-cancel/<int:pk>/",
        WorkModeRequestCancelView.as_view(),
        name="api-work-mode-request-cancel-slash",
    ),
    path(
        "work-mode-request-action/<int:pk>/<str:action>",
        WorkModeRequestDocumentActionView.as_view(),
        name="api-work-mode-request-action",
    ),
    path(
        "work-mode-request-action/<int:pk>/<str:action>/",
        WorkModeRequestDocumentActionView.as_view(),
        name="api-work-mode-request-action-slash",
    ),


    # Work type requests (alias for work-mode-request)
    path(
        "permission-check/work-type-request-approve",
        WorkModeRequestApprovePermissionCheck.as_view(),
        name="api-permission-check-work-type-request-approve-noslash",
    ),
    path(
        "permission-check/work-type-request-approve/",
        WorkModeRequestApprovePermissionCheck.as_view(),
        name="api-permission-check-work-type-request-approve",
    ),
    path(
        "work-type-request/",
        WorkModeRequestView.as_view(),
        name="api-work-type-request",
    ),
    path(
        "work-type-request",
        WorkModeRequestView.as_view(),
        name="api-work-type-request-noslash",
    ),
    path(
        "work-type-request/<int:pk>",
        WorkModeRequestView.as_view(),
        name="api-work-type-request-detail",
    ),
    path(
        "work-type-request/<int:pk>/",
        WorkModeRequestView.as_view(),
        name="api-work-type-request-detail-slash",
    ),
    path(
        "work-type-request-approvals/",
        WorkModeRequestApprovalsView.as_view(),
        name="api-work-type-request-approvals",
    ),
    path(
        "work-type-request-approvals",
        WorkModeRequestApprovalsView.as_view(),
        name="api-work-type-request-approvals-noslash",
    ),
    path(
        "work-type-request-approve/<int:pk>",
        WorkModeRequestApproveView.as_view(),
        name="api-work-type-request-approve",
    ),
    path(
        "work-type-request-approve/<int:pk>/",
        WorkModeRequestApproveView.as_view(),
        name="api-work-type-request-approve-slash",
    ),
    path(
        "work-type-request-reject/<int:pk>",
        WorkModeRequestRejectView.as_view(),
        name="api-work-type-request-reject",
    ),
    path(
        "work-type-request-reject/<int:pk>/",
        WorkModeRequestRejectView.as_view(),
        name="api-work-type-request-reject-slash",
    ),
    path(
        "work-type-request-cancel/<int:pk>",
        WorkModeRequestCancelView.as_view(),
        name="api-work-type-request-cancel",
    ),
    path(
        "work-type-request-cancel/<int:pk>/",
        WorkModeRequestCancelView.as_view(),
        name="api-work-type-request-cancel-slash",
    ),
    path(
        "work-type-request-action/<int:pk>/<str:action>",
        WorkModeRequestDocumentActionView.as_view(),
        name="api-work-type-request-action",
    ),
    path(
        "work-type-request-action/<int:pk>/<str:action>/",
        WorkModeRequestDocumentActionView.as_view(),
        name="api-work-type-request-action-slash",
    ),

    path("mobile-attendance-settings/", MobileAttendanceSettingsAPIView.as_view(), name="api-mobile-attendance-settings"),
    path("checking-in", CheckingStatus.as_view()),
    path("offline-employee-mail-send", OfflineEmployeeMailsend.as_view()),
    path("converted-mail-template", ConvertedMailTemplateConvert.as_view()),
    path("mail-templates", MailTemplateView.as_view()),
    path("my-attendance/", UserAttendanceView.as_view()),
    path("attendance-type-check/", AttendanceTypeAccessCheck.as_view()),
    path("my-attendance-detailed/<int:id>/", UserAttendanceDetailedView.as_view()),

    # Attendance → Attendances (Monthly recap)
    # Canonical URL (aligned with web route name `attendances-recap/`)
    path(
        "attendances-recap/",
        AttendanceMonthlyRecapAPIView.as_view(),
        name="api-attendance-monthly-recap",
    ),
    # No-slash variant (some clients omit trailing slash)
    path(
        "attendances-recap",
        AttendanceMonthlyRecapAPIView.as_view(),
        name="api-attendance-monthly-recap-noslash",
    ),
    path(
        "attendances-recap/export-pdf/",
        AttendanceMonthlyRecapExportPDFAPIView.as_view(),
        name="api-attendance-monthly-recap-export-pdf",
    ),
    path(
        "attendances-recap/export-pdf",
        AttendanceMonthlyRecapExportPDFAPIView.as_view(),
        name="api-attendance-monthly-recap-export-pdf-noslash",
    ),
]
