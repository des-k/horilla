"""attendance/forms_work_type_request.py

Django (templates) forms for Attendance **Work Type Requests**.

UI terminology: *Work Type* (WFA / ON DUTY)
DB model: attendance.WorkModeRequest (kept for backward compatibility).
"""

from __future__ import annotations

from datetime import date
from typing import Optional

from django import forms
from django.core.exceptions import ValidationError
from django.utils import timezone

from attendance.models import (
    AttendanceWorkMode,
    WorkModeRequest,
    WorkModeRequestRejectReasonCode,
    WorkModeRequestScope,
)
from attendance.services.attachment_validation import validate_uploaded_files
from attendance.services.work_type_request_rules import validate_work_type_request


class MultipleClearableFileInput(forms.ClearableFileInput):
    """ClearableFileInput that supports selecting multiple files."""

    allow_multiple_selected = True


class MultipleFileField(forms.FileField):
    """FileField that can clean a list of uploaded files."""

    def clean(self, data, initial=None):
        if data in (None, "", []):
            cleaned = super().clean(None, initial)
            validate_uploaded_files([])
            return cleaned
        if isinstance(data, (list, tuple)):
            parent_clean = super(MultipleFileField, self).clean
            cleaned = [parent_clean(d, initial) for d in data]
            validate_uploaded_files(cleaned)
            return cleaned
        cleaned = super().clean(data, initial)
        validate_uploaded_files([cleaned])
        return cleaned


class WorkTypeRequestCreateForm(forms.ModelForm):
    """Create Work Type Request (Attendance)."""

    # UI label: Work Type
    mode = forms.ChoiceField(
        label="Work Type",
        choices=(
            (AttendanceWorkMode.WFA, "WFA"),
            (AttendanceWorkMode.ON_DUTY, "ON DUTY"),
        ),
        widget=forms.Select(attrs={"class": "oh-select w-100"}),
    )

    scope = forms.ChoiceField(
        label="Scope",
        choices=WorkModeRequestScope.choices,
        widget=forms.Select(attrs={"class": "oh-select w-100"}),
    )

    start_date = forms.DateField(
        label="Start Date",
        widget=forms.DateInput(attrs={"type": "date", "class": "oh-input w-100"}),
    )

    end_date = forms.DateField(
        label="End Date",
        widget=forms.DateInput(attrs={"type": "date", "class": "oh-input w-100"}),
    )

    reason = forms.CharField(
        label="Reason / Note",
        required=True,
        widget=forms.Textarea(attrs={"class": "oh-input w-100", "rows": 3}),
    )

    duty_destination_location = forms.CharField(
        label="Duty Destination Location",
        required=False,
        widget=forms.TextInput(attrs={"class": "oh-input w-100"}),
    )


    files = MultipleFileField(
        label="Supporting Documents",
        required=False,
        help_text="WFA attachments are optional supporting history only. ON DUTY attachments are required at create and enter document review workflow after approval.",
        widget=MultipleClearableFileInput(attrs={"multiple": True, "class": "oh-input w-100"}),
    )

    def __init__(self, *args, employee=None, **kwargs):
        super().__init__(*args, **kwargs)
        self._employee = employee

        today = timezone.localdate().isoformat()
        try:
            self.fields["start_date"].widget.attrs.setdefault("min", today)
            self.fields["end_date"].widget.attrs.setdefault("min", today)
        except Exception:
            pass

        if self.initial.get("start_date") and not self.initial.get("end_date"):
            self.initial["end_date"] = self.initial.get("start_date")

    class Meta:
        model = WorkModeRequest
        fields = [
            "mode",
            "scope",
            "start_date",
            "end_date",
            "reason",
            "duty_destination_location",
        ]

    def clean(self):
        cleaned = super().clean()

        employee = self._employee
        if employee is None:
            raise ValidationError("Employee is required")

        mode = cleaned.get("mode")
        scope = cleaned.get("scope")
        start_date: Optional[date] = cleaned.get("start_date")
        end_date: Optional[date] = cleaned.get("end_date")

        reason = (cleaned.get("reason") or "").strip()
        if not reason:
            raise ValidationError({"reason": "Reason / Note is required"})
        cleaned["reason"] = reason

        duty_destination_location = (cleaned.get("duty_destination_location") or "").strip()
        cleaned["duty_destination_location"] = duty_destination_location

        if mode == AttendanceWorkMode.ON_DUTY and not duty_destination_location:
            raise ValidationError({"duty_destination_location": "Duty destination location is required for On Duty."})

        uploaded_files = self.files.getlist("files") if hasattr(self.files, "getlist") else []
        if mode == AttendanceWorkMode.ON_DUTY and not uploaded_files:
            raise ValidationError({"files": "At least one file is required for On Duty."})

        if not start_date:
            return cleaned

        if scope in (WorkModeRequestScope.IN, WorkModeRequestScope.OUT):
            cleaned["end_date"] = start_date
            end_date = start_date

        if not end_date:
            cleaned["end_date"] = start_date
            end_date = start_date

        validate_work_type_request(
            employee=employee,
            mode=mode,
            scope=scope,
            start_date=start_date,
            end_date=end_date,
            instance_id=None,
        )

        return cleaned


class WorkTypeRequestUpdateForm(forms.Form):
    """Limited edit: add attachments + update note/destination metadata."""

    reason = forms.CharField(
        label="Reason / Note",
        required=False,
        widget=forms.Textarea(attrs={"class": "oh-input w-100", "rows": 3}),
    )

    duty_destination_location = forms.CharField(
        label="Duty Destination Location",
        required=False,
        widget=forms.TextInput(attrs={"class": "oh-input w-100"}),
    )


    files = MultipleFileField(
        label="Documents",
        required=False,
        help_text="WFA uploads stay as supporting history. ON DUTY uploads create a new reviewable document version and preserve prior history.",
        widget=MultipleClearableFileInput(attrs={"multiple": True, "class": "oh-input w-100"}),
    )

    def __init__(self, *args, request_obj: WorkModeRequest | None = None, **kwargs):
        super().__init__(*args, **kwargs)
        self._request_obj = request_obj
        if request_obj is not None and request_obj.mode == AttendanceWorkMode.WFA:
            self.fields["files"].label = "Supporting Documents"
            self.fields["files"].help_text = (
                "WFA documents are optional supporting history only. Uploading more files creates a new version but does not trigger verify/reject/reopen workflow."
            )
        elif request_obj is not None and request_obj.mode == AttendanceWorkMode.ON_DUTY:
            self.fields["files"].label = "On Duty Documents"
            self.fields["files"].help_text = (
                "Uploading files creates a new On Duty document version. Previous versions remain in history and the current version returns to document review."
            )

    def clean(self):
        cleaned = super().clean()
        cleaned["reason"] = (cleaned.get("reason") or "").strip()
        cleaned["duty_destination_location"] = (cleaned.get("duty_destination_location") or "").strip()

        req = self._request_obj
        if req and req.mode == AttendanceWorkMode.ON_DUTY:
            destination = cleaned.get("duty_destination_location") or (getattr(req, "duty_destination_location", "") or "").strip()
            if not destination:
                raise ValidationError({"duty_destination_location": "Duty destination location is required for On Duty."})
        return cleaned


class WorkTypeRequestRejectForm(forms.Form):
    reason_code = forms.ChoiceField(
        label="Reject Reason Code",
        choices=((WorkModeRequestRejectReasonCode.MANUAL_REJECT, "Manual Reject"),),
        initial=WorkModeRequestRejectReasonCode.MANUAL_REJECT,
        widget=forms.Select(attrs={"class": "oh-select w-100"}),
    )
    reason = forms.CharField(
        label="Reject Note",
        required=False,
        widget=forms.Textarea(attrs={"class": "oh-input w-100", "rows": 3}),
    )
