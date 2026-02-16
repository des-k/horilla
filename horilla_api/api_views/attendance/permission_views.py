from rest_framework.permissions import IsAuthenticated
from rest_framework.response import Response
from rest_framework.views import APIView

from ...api_decorators.base.decorators import ManagerPermission


class AttendancePermissionCheck(APIView):
    """Legacy permission check used by mobile/web.

    Returns 200 with can_view=true/false.
    """

    permission_classes = [IsAuthenticated]

    def get(self, request):
        can_view = ManagerPermission().has_permission(request, "attendance.view_attendance")
        return Response({"can_view": bool(can_view)}, status=200)


class AttendanceRequestApprovePermissionCheck(APIView):
    """Permission check for approving/rejecting attendance requests (admin + supervisor)."""

    permission_classes = [IsAuthenticated]

    def get(self, request):
        can_approve = ManagerPermission().has_permission(request, "attendance.change_attendance")
        return Response({"can_approve": bool(can_approve)}, status=200)


class WorkModeRequestApprovePermissionCheck(APIView):
    """Permission check for approving/rejecting work-mode requests (admin + supervisor)."""

    permission_classes = [IsAuthenticated]

    def get(self, request):
        can_approve = ManagerPermission().has_permission(
            request, "attendance.change_workmoderequest"
        )
        return Response({"can_approve": bool(can_approve)}, status=200)
