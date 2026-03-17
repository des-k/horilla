from rest_framework.permissions import IsAuthenticated
from rest_framework.response import Response
from rest_framework.views import APIView

from ...api_decorators.base.decorators import ManagerPermission
from attendance.services.work_type_request_permissions import is_global_work_type_approver, subordinate_employee_ids


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
    """Permission check for approving/rejecting work-type requests (admin + supervisor)."""

    permission_classes = [IsAuthenticated]

    def get(self, request):
        can_approve = False
        try:
            can_approve = bool(
                is_global_work_type_approver(request.user)
                or subordinate_employee_ids(request)
            )
        except Exception:
            can_approve = False
        return Response({"can_approve": can_approve}, status=200)
