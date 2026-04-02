# pylint: disable=too-few-public-methods
"""
forms.py

This module contains the form classes used in the application.

Each form represents a specific functionality or data input in the
application. They are responsible for validating
and processing user input data.

Classes:
- YourForm: Represents a form for handling specific data input.

Usage:
from django import forms

class YourForm(forms.Form):
    field_name = forms.CharField()

    def clean_field_name(self):
        # Custom validation logic goes here
        pass
"""

import datetime
import json
import logging
import uuid
from calendar import month_name
from collections import OrderedDict
from typing import Any, Dict

from django import forms
from django.apps import apps
from django.core.exceptions import ValidationError
from django.utils import timezone
from django.db.models.query import QuerySet
from django.forms import DateTimeInput
from django.template.loader import render_to_string
from django.utils.html import format_html
from django.utils.translation import gettext_lazy as _

from attendance.filters import AttendanceFilters
from attendance.models import (
    Attendance,
    AttendanceActivity,
    AttendanceLateComeEarlyOut,
    AttendanceOverTime,
    AttendanceRequestComment,
    AttendanceValidationCondition,
    BatchAttendance,
    GraceTime,
    WorkRecords,
    attendance_date_validate,
    strtime_seconds,
    validate_time_format,
)
from attendance.services.attachment_validation import validate_uploaded_files
from base.forms import ModelForm as BaseModelForm
from base.methods import (
    filtersubordinatesemployeemodel,
    get_working_days,
    is_reportingmanager,
    reload_queryset,
    is_holiday,
    is_company_leave,
)
from base.models import Company, EmployeeShift, EmployeeShiftDay, EmployeeShiftSchedule
from employee.filters import EmployeeFilter
from employee.models import Employee
from horilla import horilla_middlewares
from horilla_widgets.widgets.horilla_multi_select_field import HorillaMultiSelectField
from horilla_widgets.widgets.select_widgets import HorillaMultiSelectWidget

logger = logging.getLogger(__name__)


def _resolve_schedule_minimum_hour(attendance_date, shift, fallback="00:00"):
    from attendance.methods.utils import schedule_minimum_hour_for_date

    return schedule_minimum_hour_for_date(attendance_date, shift, fallback=fallback)


def _fmt_dt_value(value, fmt):
    return value.strftime(fmt) if value is not None else None


class AttendanceUpdateForm(BaseModelForm):
    """
    This model form is used to direct save the validated query dict to attendance model
    from AttendanceUpdateForm. This form can be used to update existing attendance.
    """

    class Meta:
        """
        Meta class to add the additional info
        """

        fields = "__all__"
        exclude = [
            "overtime_second",
            "at_work_second",
            "attendance_day",
            "request_description",
            "approved_overtime_second",
            "request_type",
            "requested_data",
            "is_validate_request",
            "is_validate_request_approved",
            "attendance_overtime",
            "is_active",
            "is_holiday",
        ]
        model = Attendance
        widgets = {
            "attendance_clock_in": DateTimeInput(attrs={"type": "time"}),
            "attendance_clock_out": DateTimeInput(attrs={"type": "time"}),
            "attendance_clock_out_date": DateTimeInput(attrs={"type": "date"}),
            "attendance_date": DateTimeInput(attrs={"type": "date"}),
            "attendance_clock_in_date": DateTimeInput(attrs={"type": "date"}),
        }

    def update_worked_hour_hx_fields(self, field_name):
        """Update the widget attributes for worked hour fields."""
        self.fields[field_name].widget.attrs.update(
            {
                "id": str(uuid.uuid4()),
                "hx-include": "#attendanceUpdateForm",
                "hx-target": "#id_attendance_worked_hour_parent_div",
                "hx-swap": "outerHTML",
                "hx-select": "#id_attendance_worked_hour_parent_div",
                "hx-get": "/attendance/update-worked-hour-field",
                "hx-trigger": "change delay:300ms",  # Delay added here for 500ms
            }
        )

    def __init__(self, *args, **kwargs):
        if instance := kwargs.get("instance"):
            # django forms not showing value inside the date, time html element.
            # so here overriding default forms instance method to set initial value
            condition = AttendanceValidationCondition.objects.first()
            condition = (
                strtime_seconds(condition.minimum_overtime_to_approve)
                if condition and condition.minimum_overtime_to_approve
                else 0
            )
            initial = {}
            if instance.attendance_date is not None:
                initial["attendance_date"] = _fmt_dt_value(instance.attendance_date, "%Y-%m-%d")
            if instance.attendance_clock_in is not None:
                initial["attendance_clock_in"] = _fmt_dt_value(instance.attendance_clock_in, "%H:%M")
            if instance.attendance_clock_in_date is not None:
                initial["attendance_clock_in_date"] = _fmt_dt_value(instance.attendance_clock_in_date, "%Y-%m-%d")
            if instance.attendance_clock_out is not None:
                initial["attendance_clock_out"] = _fmt_dt_value(instance.attendance_clock_out, "%H:%M")
            if instance.attendance_clock_out_date is not None:
                initial["attendance_clock_out_date"] = _fmt_dt_value(instance.attendance_clock_out_date, "%Y-%m-%d")
            kwargs["initial"] = initial
        super().__init__(*args, **kwargs)
        self.window_warnings = []
        self.fields["employee_id"].widget.attrs.update({"id": str(uuid.uuid4())})
        self.fields["shift_id"].widget.attrs.update(
            {
                "id": str(uuid.uuid4()),
                "hx-include": "#attendanceUpdateForm",
                "hx-target": "#attendanceUpdateForm",
                "hx-get": "/attendance/update-fields-based-shift",
            }
        )
        for field in [
            "attendance_clock_in_date",
            "attendance_clock_in",
            "attendance_clock_out_date",
            "attendance_clock_out",
        ]:
            self.update_worked_hour_hx_fields(field)
        self.fields["attendance_date"].widget.attrs.update(
            {
                "onchange": "attendanceDateChange($(this))",
            }
        )
        self.fields["work_type_id"].widget.attrs.update({"id": str(uuid.uuid4())})

        if (
            instance is not None
            and not instance.attendance_overtime_approve
            and (
                strtime_seconds(instance.attendance_overtime) < condition
                or not instance.attendance_validated
            )
        ):
            del self.fields["attendance_overtime_approve"]
        self.fields["batch_attendance_id"].choices = list(
            self.fields["batch_attendance_id"].choices
        ) + [("dynamic_create", "Dynamic create")]
        self.fields["batch_attendance_id"].widget.attrs.update(
            {
                "onchange": "dynamicBatchAttendance($(this))",
            }
        )

    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML table rows with Bootstrap styling.
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        table_html = render_to_string("attendance_form.html", context)
        return table_html


class AttendanceForm(BaseModelForm):
    """
    Model form for Attendance model
    """

    employee_id = HorillaMultiSelectField(
        queryset=Employee.objects.filter(employee_work_info__isnull=False),
        widget=HorillaMultiSelectWidget(
            filter_route_name="employee-widget-filter",
            filter_class=EmployeeFilter,
            filter_instance_contex_name="f",
            filter_template_path="employee_filters.html",
        ),
        label=_("Employees"),
    )

    class Meta:
        """
        Meta class to add the additional info
        """

        model = Attendance
        fields = "__all__"
        exclude = [
            "attendance_overtime_approve",
            "attendance_overtime_calculation",
            "at_work_second",
            "overtime_second",
            "attendance_day",
            "request_description",
            "approved_overtime_second",
            "request_type",
            "requested_data",
            "is_validate_request",
            "is_validate_request_approved",
            "attendance_overtime",
            "is_active",
            "is_holiday",
        ]
        widgets = {
            "attendance_clock_in": DateTimeInput(attrs={"type": "time"}),
            "attendance_clock_out": DateTimeInput(attrs={"type": "time"}),
            "attendance_clock_out_date": DateTimeInput(attrs={"type": "date"}),
            "attendance_date": DateTimeInput(attrs={"type": "date"}),
            "attendance_clock_in_date": DateTimeInput(attrs={"type": "date"}),
        }

    def update_worked_hour_hx_fields(self, field_name):
        """Update the widget attributes for worked hour fields."""
        self.fields[field_name].widget.attrs.update(
            {
                "id": str(uuid.uuid4()),
                "hx-include": "#attendanceCreateForm",
                "hx-target": "#id_attendance_worked_hour_parent_div",
                "hx-swap": "outerHTML",
                "hx-select": "#id_attendance_worked_hour_parent_div",
                "hx-get": "/attendance/update-worked-hour-field",
                "hx-trigger": "change delay:300ms",  # Delay added here for 500ms
            }
        )

    def __init__(self, *args, **kwargs):
        # Get the initial data passed from the view
        view_initial = kwargs.pop("initial", {})

        # Default initial values
        initial = {
            "attendance_clock_out_date": datetime.datetime.today()
            .date()
            .strftime("%Y-%m-%d"),
            "attendance_clock_out": datetime.datetime.today().time().strftime("%H:%M"),
        }

        # If an instance is provided, override the default initial values
        if instance := kwargs.get("instance"):
            if instance.attendance_date is not None:
                initial["attendance_date"] = _fmt_dt_value(instance.attendance_date, "%Y-%m-%d")
            if instance.attendance_clock_in is not None:
                initial["attendance_clock_in"] = _fmt_dt_value(instance.attendance_clock_in, "%H:%M")
            if instance.attendance_clock_in_date is not None:
                initial["attendance_clock_in_date"] = _fmt_dt_value(instance.attendance_clock_in_date, "%Y-%m-%d")
            if instance.attendance_clock_out is not None:
                initial["attendance_clock_out"] = _fmt_dt_value(instance.attendance_clock_out, "%H:%M")
            if instance.attendance_clock_out_date is not None:
                initial["attendance_clock_out_date"] = _fmt_dt_value(instance.attendance_clock_out_date, "%Y-%m-%d")

        # Merge with initial values passed from the view
        initial.update(view_initial)
        kwargs["initial"] = initial

        super().__init__(*args, **kwargs)
        reload_queryset(self.fields)
        self.fields["employee_id"].widget.attrs.update({"id": str(uuid.uuid4())})
        self.fields["shift_id"].widget.attrs.update(
            {
                "id": str(uuid.uuid4()),
                "hx-include": "#attendanceCreateForm",
                "hx-target": "#attendanceCreateForm",
                "hx-get": "/attendance/update-fields-based-shift",
            }
        )

        # Update attributes for worked hour fields
        for field in [
            "attendance_clock_in_date",
            "attendance_clock_in",
            "attendance_clock_out_date",
            "attendance_clock_out",
        ]:
            self.update_worked_hour_hx_fields(field)

        self.fields["attendance_date"].widget.attrs.update(
            {
                "onchange": "attendanceDateChange($(this))",
            }
        )
        self.fields["work_type_id"].widget.attrs.update({"id": str(uuid.uuid4())})
        self.fields["batch_attendance_id"].choices = list(
            self.fields["batch_attendance_id"].choices
        ) + [("dynamic_create", "Dynamic create")]
        self.fields["batch_attendance_id"].widget.attrs.update(
            {
                "onchange": "dynamicBatchAttendance($(this))",
            }
        )

    def save(self, commit=True):
        instance = super().save(commit=False)
        for emp_id in self.data.getlist("employee_id"):
            if int(emp_id) != int(instance.employee_id.id):
                data_copy = self.data.copy()
                data_copy.update({"employee_id": str(emp_id)})
                attendance = AttendanceUpdateForm(data_copy).save(commit=False)
                attendance.save()
        if commit:
            instance.save()
        return instance

    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML table rows with Bootstrap styling.
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        table_html = render_to_string("attendance_form.html", context)
        return table_html

    def clean(self) -> Dict[str, Any]:
        self.window_warnings = []
        super().clean()
        self.instance.employee_id = Employee.objects.filter(
            id=self.data.get("employee_id")
        ).first()

        self.errors.pop("employee_id", None)
        if self.instance.employee_id is None:
            raise ValidationError({"employee_id": _("This field is required")})
        super().clean()
        employee_ids = self.data.getlist("employee_id")
        existing_attendance = Attendance.objects.filter(
            attendance_date=self.data["attendance_date"]
        ).filter(employee_id__id__in=employee_ids)
        if existing_attendance.exists():
            employee_names = [
                attendance.employee_id.__str__() for attendance in existing_attendance
            ]
            raise ValidationError(
                {
                    "employee_id": f"Already attendance exists for {', '.join(employee_names)} employees"
                }
            )

    def clean_employee_id(self):
        """
        Used to validate employee_id field
        """
        employee = self.cleaned_data["employee_id"]
        for emp in employee:
            attendance = Attendance.objects.filter(
                employee_id=emp, attendance_date=self.data["attendance_date"]
            ).first()
            if attendance is not None:
                raise ValidationError(
                    _(
                        ("Attendance for the date already exists for {emp}").format(
                            emp=emp
                        )
                    )
                )
        if employee.first() is None:
            raise ValidationError(_("Employee not chosen"))

        return employee.first()


class AttendanceActivityForm(BaseModelForm):
    """
    Model form for AttendanceActivity model
    """

    class Meta:
        """
        Meta class to add the additional info
        """

        model = AttendanceActivity
        fields = "__all__"
        widgets = {
            "clock_in": DateTimeInput(attrs={"type": "time"}),
            "clock_out": DateTimeInput(attrs={"type": "time"}),
            "clock_in_date": DateTimeInput(attrs={"type": "date"}),
            "clock_out_date": DateTimeInput(attrs={"type": "date"}),
        }

    def __init__(self, *args, **kwargs):
        if instance := kwargs.get("instance"):
            # django forms not showing value inside the date, time html element.
            # so here overriding default forms instance method to set initial value

            initial = {}
            if instance.attendance_date is not None:
                initial["attendance_date"] = _fmt_dt_value(instance.attendance_date, "%Y-%m-%d")
            if instance.clock_in_date is not None:
                initial["clock_in_date"] = _fmt_dt_value(instance.clock_in_date, "%Y-%m-%d")
            if instance.clock_in is not None:
                initial["clock_in"] = _fmt_dt_value(instance.clock_in, "%H:%M")
            if instance.clock_out is not None:
                initial["clock_out"] = _fmt_dt_value(instance.clock_out, "%H:%M")
            if instance.clock_out_date is not None:
                initial["clock_out_date"] = _fmt_dt_value(instance.clock_out_date, "%Y-%m-%d")
            kwargs["initial"] = initial
        super().__init__(*args, **kwargs)


class MonthSelectField(forms.ChoiceField):
    """
    Generate month choices
    """

    def __init__(self, *args, **kwargs):
        choices = [
            (month_name[i].lower(), _(month_name[i].capitalize())) for i in range(1, 13)
        ]
        super().__init__(choices=choices, *args, **kwargs)


class AttendanceOverTimeForm(BaseModelForm):
    """
    Model form for AttendanceOverTime model
    """

    month = MonthSelectField(label=_("Month"))

    class Meta:
        """
        Meta class to add the additional info
        """

        model = AttendanceOverTime
        fields = "__all__"
        exclude = [
            "hour_account_second",
            "overtime_second",
            "month_sequence",
            "hour_pending_second",
            "is_active",
        ]
        labels = {
            "employee_id": _("Employee"),
            "year": _("Year"),
            "worked_hours": _("Worked Hours"),
            "pending_hours": _("Pending Hours"),
            "overtime": _("Overtime"),
        }

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.fields["employee_id"].widget.attrs.update({"id": str(uuid.uuid4())})

    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML table rows with Bootstrap styling.
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        table_html = render_to_string("attendance_form.html", context)
        return table_html


class AttendanceLateComeEarlyOutForm(BaseModelForm):
    """
    Model form for attendance AttendanceLateComeEarlyOut
    """

    class Meta:
        """
        Meta class to add the additional info
        """

        model = AttendanceLateComeEarlyOut
        fields = "__all__"


class AttendanceValidationConditionForm(forms.ModelForm):
    """
    Model form for AttendanceValidationCondition
    """

    validation_at_work = forms.CharField(
        required=True,
        initial="00:00",
        widget=forms.TextInput(
            attrs={"class": "oh-input w-100", "placeholder": "09:00"}
        ),
        label=format_html(
            _(
                "<span title='Do not Auto Validate Attendance if an Employee Works More Than this Amount of Duration'>{}</span>"
            ),
            _("Worked Hours(At Work) Auto Approve Till"),
        ),
    )
    minimum_overtime_to_approve = forms.CharField(
        required=True,
        initial="00:00",
        widget=forms.TextInput(
            attrs={"class": "oh-input w-100", "placeholder": "00:30"}
        ),
        label=_("Minimum Hour to Approve Overtime"),
    )
    overtime_cutoff = forms.CharField(
        required=True,
        initial="00:00",
        widget=forms.TextInput(
            attrs={"class": "oh-input w-100", "placeholder": "02:00"}
        ),
        label=_("Maximum Allowed Overtime Per Day"),
    )
    company_id = forms.ModelMultipleChoiceField(
        label=_("Company"),
        queryset=Company.objects.all(),
        required=False,
        widget=forms.SelectMultiple(attrs={"class": "oh-select oh-select-2 w-100"}),
    )

    class Meta:
        """
        Meta class for additional options
        """

        model = AttendanceValidationCondition
        fields = "__all__"
        exclude = ["is_active"]


class AttendanceRequestForm(BaseModelForm):
    """
    AttendanceRequestForm
    """

    def update_worked_hour_hx_fields(self, field_name):
        """Update the widget attributes for worked hour fields."""
        self.fields[field_name].widget.attrs.update(
            {
                "id": str(uuid.uuid4()),
                "hx-include": "#attendanceRequestForm",
                "hx-target": "#id_attendance_worked_hour_parent_div",
                "hx-swap": "outerHTML",
                "hx-select": "#id_attendance_worked_hour_parent_div",
                "hx-get": "/attendance/update-worked-hour-field",
                "hx-trigger": "change delay:300ms",  # Delay added here for 300ms
            }
        )

    def __init__(self, *args, **kwargs):
        instance = kwargs.get("instance")
        if instance is not None:
            # django forms not showing value inside the date, time html element.
            # so here overriding default forms instance method to set initial value
            initial = {}
            if instance.attendance_date is not None:
                initial["attendance_date"] = _fmt_dt_value(instance.attendance_date, "%Y-%m-%d")
            if getattr(instance, 'attendance_clock_in', None) is not None:
                initial["attendance_clock_in"] = _fmt_dt_value(instance.attendance_clock_in, "%H:%M")
            if getattr(instance, 'attendance_clock_in_date', None) is not None:
                initial["attendance_clock_in_date"] = _fmt_dt_value(instance.attendance_clock_in_date, "%Y-%m-%d")
            if getattr(instance, 'attendance_clock_out', None) is not None:
                initial["attendance_clock_out"] = _fmt_dt_value(instance.attendance_clock_out, "%H:%M")
            if getattr(instance, 'attendance_clock_out_date', None) is not None:
                initial["attendance_clock_out_date"] = _fmt_dt_value(instance.attendance_clock_out_date, "%Y-%m-%d")
            kwargs["initial"] = initial

        super().__init__(*args, **kwargs)

        # Allow per-day request: IN only / OUT only / BOTH
        for f in [
            "attendance_clock_in_date",
            "attendance_clock_in",
            "attendance_clock_out_date",
            "attendance_clock_out",
        ]:
            if f in self.fields:
                self.fields[f].required = False

        # Shift / worked hour / minimum hour should not be chosen/typed by user
        for f in ["shift_id", "attendance_worked_hour", "minimum_hour"]:
            if f in self.fields:
                self.fields[f].required = False
                self.fields[f].widget = forms.HiddenInput()

        if 'minimum_hour' in self.fields:
            self.fields['minimum_hour'].initial = '00:00'
        if 'attendance_worked_hour' in self.fields:
            self.fields['attendance_worked_hour'].initial = '00:00'

        if 'attendance_date' in self.fields:
            self.fields['attendance_date'].widget.attrs.update({
                'onchange': 'attendanceDateChange($(this))',
            })
        if 'work_type_id' in self.fields:
            self.fields['work_type_id'].widget.attrs.update({'id': str(uuid.uuid4())})
        if 'batch_attendance_id' in self.fields:
            # Attendance Correction Request (mobile parity): no batch selection
            self.fields['batch_attendance_id'].required = False
            self.fields['batch_attendance_id'].widget = forms.HiddenInput()

    class Meta:
        """
        Meta class for additional options
        """

        model = Attendance
        fields = [
            "attendance_date",
            "shift_id",
            "work_type_id",
            "attendance_clock_in_date",
            "attendance_clock_in",
            "attendance_clock_out_date",
            "attendance_clock_out",
            "attendance_worked_hour",
            "minimum_hour",
            "request_description",
            "batch_attendance_id",
        ]
        widgets = {
            "attendance_date": DateTimeInput(attrs={"type": "date"}),
            "attendance_clock_in": DateTimeInput(attrs={"type": "time"}),
            "attendance_clock_in_date": DateTimeInput(attrs={"type": "date"}),
            "attendance_clock_out": DateTimeInput(attrs={"type": "time"}),
            "attendance_clock_out_date": DateTimeInput(attrs={"type": "date"}),
        }

    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML table rows with Bootstrap styling.
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        table_html = render_to_string("attendance_form.html", context)
        return table_html


    def clean(self):
        """
        Block attendance requests on:
        - Holiday / company leave
        - Dates that have no shift schedule (no shift assigned OR no start/end on that weekday)

        Applies to BOTH Web and Mobile because both create/update flows use
        AttendanceRequestForm / NewRequestForm in the backend API.
        """
        cleaned_data = super().clean()

        employee = self.cleaned_data.get('employee_id') or getattr(self.instance, 'employee_id', None)
        attendance_date = self.cleaned_data.get('attendance_date')
        if attendance_date is None:
            attendance_date = getattr(self.instance, 'attendance_date', None)

        if not attendance_date:
            return cleaned_data

        # Holiday / company leave
        try:
            if is_holiday(attendance_date) or is_company_leave(attendance_date):
                raise ValidationError({'attendance_date': _("You cannot submit an attendance request on a holiday/off day.")})
        except ValidationError:
            raise
        except Exception:
            raise ValidationError({'attendance_date': _("Unable to validate whether this date is an off day.")})

        # Resolve shift: prefer explicit shift_id from form, fallback to employee work info
        shift = self.cleaned_data.get('shift_id')
        if not shift and employee is not None:
            try:
                shift = getattr(getattr(employee, 'employee_work_info', None), 'shift_id', None)
            except Exception:
                shift = None

        if not shift:
            raise ValidationError({'attendance_date': _("You cannot submit an attendance request because no shift is assigned for this employee.")})

        try:
            day_name = ['monday','tuesday','wednesday','thursday','friday','saturday','sunday'][attendance_date.weekday()]
            day_obj = EmployeeShiftDay.objects.filter(day=day_name).first()
            if not day_obj:
                raise ValidationError({'attendance_date': _("You cannot submit an attendance request because shift day configuration is missing.")})

            sched = EmployeeShiftSchedule.objects.filter(shift_id=shift, day=day_obj).first()
            if (not sched) or (getattr(sched, 'start_time', None) is None) or (getattr(sched, 'end_time', None) is None):
                raise ValidationError({'attendance_date': _("You cannot submit an attendance request because there is no shift schedule for this date.")})
        except ValidationError:
            raise
        except Exception:
            raise ValidationError({'attendance_date': _("Unable to validate shift schedule for this date.")})

        return cleaned_data

    def save(self, commit: bool = ...) -> Any:
        # No need to save the changes to the actual modal instance
        return super().save(False)

class MultipleClearableFileInput(forms.ClearableFileInput):
    """ClearableFileInput that allows selecting multiple files.

    Django's built-in ClearableFileInput raises ValueError when `multiple` is set.
    This subclass enables multiple selection and will return a list from
    value_from_datadict.
    """
    allow_multiple_selected = True


class MultipleFileField(forms.FileField):
    """FileField that accepts multiple uploaded files and returns a list."""

    widget = MultipleClearableFileInput

    def __init__(self, *args, **kwargs):
        # Ensure multiple selection is enabled
        widget = kwargs.get("widget")
        if widget is None:
            kwargs["widget"] = MultipleClearableFileInput(attrs={"multiple": True})
        else:
            # force multiple attribute for provided widget
            widget.attrs = dict(widget.attrs or {})
            widget.attrs["multiple"] = True
            kwargs["widget"] = widget
        super().__init__(*args, **kwargs)

    def clean(self, data, initial=None):
        if not data:
            return []
        if isinstance(data, (list, tuple)):
            cleaned = []
            errors = []
            for item in data:
                try:
                    cleaned.append(super().clean(item, initial))
                except ValidationError as e:
                    errors.extend(e.error_list)
            if errors:
                raise ValidationError(errors)
            validate_uploaded_files(cleaned)
            return cleaned
        cleaned = [super().clean(data, initial)]
        validate_uploaded_files(cleaned)
        return cleaned

class NewRequestForm(AttendanceRequestForm):
    """
    NewRequestForm (Web + API)
    Aligned with Mobile "Attendance Correction Request" create flow:
      - Employee, Date
      - Scope: IN / OUT / BOTH (hidden field set by UI)
      - Check In / Check Out time (same day)
      - Reason / Note (required)
      - Attachment(s) optional (multi file upload via field name "files")
    """

    # UI-only scope (not a model field). Values: IN / OUT / BOTH
    scope = forms.CharField(
        required=False,
        initial="BOTH",
        widget=forms.HiddenInput(),
        label=_("Scope"),
    )

    # Optional attachments (not a model field). API + mobile uses "files".
    files = MultipleFileField(
        required=False,
        label=_("Attachment"),
        help_text=_("Optional. Upload supporting file(s)."),
    )

    def __init__(self, *args, **kwargs):
        # Get the initial data passed from views.py file (employee_id, etc.)
        view_initial = kwargs.get("initial") or {}
        super().__init__(*args, **kwargs)

        # Rebuild field order to match mobile:
        # employee, date, check-in, check-out, reason, files (+ hidden technical fields)
        old = self.fields

        employee_field = forms.ModelChoiceField(
            queryset=Employee.objects.filter(is_active=True),
            label=_("Employee"),
            widget=forms.Select(attrs={"class": "oh-select oh-select-2 w-100"}),
            initial=view_initial.get("employee_id"),
        )

        ordered = {
            "employee_id": employee_field,
            "attendance_date": old.get("attendance_date"),
            "attendance_clock_in": old.get("attendance_clock_in"),
            "attendance_clock_out": old.get("attendance_clock_out"),
            "request_description": old.get("request_description"),
            "files": self.fields.get("files"),
            # Hidden UI-only scope
            "scope": self.fields.get("scope"),
        }

        # Keep any remaining fields (mostly hidden) to preserve backend logic
        for k, v in old.items():
            if k not in ordered and k not in ("employee_id",):
                ordered[k] = v

        # Drop None entries (defensive)
        ordered = {k: v for k, v in ordered.items() if v is not None}

        self.fields = ordered

        # --- Hide fields not used in the mobile create flow ---
        hide_fields = [
            "shift_id",
            "work_type_id",
            "attendance_clock_in_date",
            "attendance_clock_out_date",
            "attendance_worked_hour",
            "minimum_hour",
            "batch_attendance_id",
        ]
        for f in hide_fields:
            if f in self.fields:
                self.fields[f].required = False
                self.fields[f].widget = forms.HiddenInput()

        # Work Type is not selected in mobile create flow; keep backend defaulting.
        if "work_type_id" in self.fields:
            self.fields["work_type_id"].required = False

        # Normalize labels to match mobile
        if "attendance_clock_in" in self.fields:
            self.fields["attendance_clock_in"].label = _("Check In")
        if "attendance_clock_out" in self.fields:
            self.fields["attendance_clock_out"].label = _("Check Out")
        if "request_description" in self.fields:
            self.fields["request_description"].label = _("Reason / Note")
            self.fields["request_description"].required = True

        # Scope hidden field default
        if "scope" in self.fields and not self.initial.get("scope"):
            self.initial["scope"] = "BOTH"


        # Limit attendance_date to yesterday and earlier (mobile parity)
        if "attendance_date" in self.fields:
            try:
                max_date = timezone.localdate() - datetime.timedelta(days=1)
                self.fields["attendance_date"].widget.attrs["max"] = max_date.strftime("%Y-%m-%d")
            except Exception:
                pass
    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML rows (modal).
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        form_html = render_to_string("requests/attendance/request_new_form.html", context)
        return form_html

    @staticmethod
    def _infer_scope(raw_scope, in_time, out_time):
        scope = (raw_scope or "").strip().upper()
        if scope in ("IN", "OUT", "BOTH"):
            return scope
        if in_time and out_time:
            return "BOTH"
        if in_time:
            return "IN"
        if out_time:
            return "OUT"
        return "BOTH"

    @staticmethod
    def _time_in_window(target_time, start_dt, end_dt):
        if target_time is None or start_dt is None or end_dt is None:
            return False

        current_tz = timezone.get_current_timezone()
        windows_are_aware = timezone.is_aware(start_dt) or timezone.is_aware(end_dt)

        def normalize_dt(value):
            if value is None:
                return None
            if windows_are_aware:
                if timezone.is_naive(value):
                    return timezone.make_aware(value, current_tz)
                return timezone.localtime(value, current_tz)
            if timezone.is_aware(value):
                return timezone.make_naive(value, current_tz)
            return value

        candidate = normalize_dt(datetime.datetime.combine(start_dt.date(), target_time))
        start = normalize_dt(start_dt)
        end = normalize_dt(end_dt)

        if candidate is None or start is None or end is None:
            return False

        if end < start:
            end = end + datetime.timedelta(days=1)
        if candidate < start and end.date() > start.date():
            candidate = candidate + datetime.timedelta(days=1)
        return start <= candidate <= end

    def _get_request_windows(self, attendance_date, shift):
        if not attendance_date or not shift:
            return {}
        try:
            from attendance.methods.utils import shift_schedule_today
            from attendance.views.clock_in_out import get_shift_rules

            day_obj = EmployeeShiftDay.objects.filter(day=attendance_date.strftime("%A").lower()).first()
            if not day_obj:
                return {}
            _min_h, start_sec, end_sec = shift_schedule_today(day=day_obj, shift=shift)
            return get_shift_rules(
                attendance_date,
                shift,
                day_obj,
                start_time_sec=start_sec,
                end_time_sec=end_sec,
            ) or {}
        except Exception:
            return {}

    def _validate_window(self, field_name, label, value, start_dt, end_dt):
        if value is None:
            return
        if start_dt is None or end_dt is None:
            kind = "check-in" if field_name == "attendance_clock_in" else "check-out"
            self.window_warnings.append(
                _("%(label)s is outside the configured %(kind)s window and will require manual approval review.")
                % {"label": label, "kind": kind}
            )
            return
        if not self._time_in_window(value, start_dt, end_dt):
            self.window_warnings.append(
                _("%(label)s is outside %(start)s - %(end)s and will require manual approval review.")
                % {"label": label, "start": start_dt.strftime("%H:%M"), "end": end_dt.strftime("%H:%M")}
            )

    def clean(self) -> Dict[str, Any]:
        self.window_warnings = []
        super().clean()

        employee = self.cleaned_data.get("employee_id")
        attendance_date = self.cleaned_data.get("attendance_date")

        # Only allow requests for yesterday and earlier (no today/future)
        if attendance_date:
            try:
                max_date = timezone.localdate() - datetime.timedelta(days=1)
                if attendance_date > max_date:
                    raise ValidationError({"attendance_date": _("You can only request for yesterday and earlier.")})
            except ValidationError:
                raise
            except Exception:
                # fail open on timezone issues
                pass
        if employee and not hasattr(employee, "employee_work_info"):
            raise ValidationError(_("Employee work info not found"))

        # Reason is required (mobile parity)
        reason = (self.cleaned_data.get("request_description") or "").strip()
        if not reason:
            raise ValidationError({"request_description": _("Reason is required")})

        in_time = self.cleaned_data.get("attendance_clock_in")
        out_time = self.cleaned_data.get("attendance_clock_out")
        scope = self._infer_scope(self.data.get("scope") or self.cleaned_data.get("scope"), in_time, out_time)

        # Apply scope rules (mobile parity)
        if scope == "IN":
            out_time = None
            self.cleaned_data["attendance_clock_out"] = None
            self.cleaned_data["attendance_clock_out_date"] = None
        elif scope == "OUT":
            in_time = None
            self.cleaned_data["attendance_clock_in"] = None
            self.cleaned_data["attendance_clock_in_date"] = None
        else:
            scope = "BOTH"

        needs_in = scope in ("IN", "BOTH")
        needs_out = scope in ("OUT", "BOTH")

        if needs_in and not in_time:
            raise ValidationError({"attendance_clock_in": _("Provide Check In time")})
        if needs_out and not out_time:
            raise ValidationError({"attendance_clock_out": _("Provide Check Out time")})

        # Default in/out dates = attendance_date (mobile sends the same day)
        in_date = self.cleaned_data.get("attendance_clock_in_date")
        out_date = self.cleaned_data.get("attendance_clock_out_date")
        if in_time and not in_date:
            self.cleaned_data["attendance_clock_in_date"] = attendance_date
            in_date = attendance_date
        if out_time and not out_date:
            self.cleaned_data["attendance_clock_out_date"] = attendance_date
            out_date = attendance_date

        # Default shift/work type from employee work info
        shift = self.cleaned_data.get("shift_id")
        if not shift and employee and hasattr(employee, "employee_work_info"):
            shift = employee.employee_work_info.shift_id
            self.cleaned_data["shift_id"] = shift

        work_type = self.cleaned_data.get("work_type_id")
        if not work_type and employee and hasattr(employee, "employee_work_info"):
            work_type = employee.employee_work_info.work_type_id
            self.cleaned_data["work_type_id"] = work_type

        rules = self._get_request_windows(attendance_date, shift)
        if needs_in:
            self._validate_window(
                "attendance_clock_in",
                "Check In Time",
                in_time,
                rules.get("check_in_window_start_dt"),
                rules.get("check_in_window_end_dt"),
            )
        if needs_out:
            self._validate_window(
                "attendance_clock_out",
                "Check Out Time",
                out_time,
                rules.get("check_out_window_start_dt"),
                rules.get("check_out_window_end_dt"),
            )

        # Minimum hour must always come from the shift schedule for the selected date.
        minimum_hour = _resolve_schedule_minimum_hour(attendance_date, shift, fallback=self.cleaned_data.get("minimum_hour") or self.data.get("minimum_hour") or "00:00")
        self.cleaned_data["minimum_hour"] = minimum_hour

        worked_hour = self.cleaned_data.get("attendance_worked_hour") or "00:00"
        if not self.data.get("attendance_worked_hour") and in_time and out_time and in_date and out_date:
            try:
                import datetime as _dt
                in_dt = _dt.datetime.combine(in_date, in_time)
                out_dt = _dt.datetime.combine(out_date, out_time)
                if out_dt < in_dt:
                    out_dt = out_dt + _dt.timedelta(days=1)
                mins = int((out_dt - in_dt).total_seconds() // 60)
                h = mins // 60
                m = mins % 60
                worked_hour = f"{h:02d}:{m:02d}"
            except Exception:
                worked_hour = "00:00"
        self.cleaned_data["attendance_worked_hour"] = worked_hour

        # Check if attendance exists for the employee and date
        attendances = Attendance.objects.filter(employee_id=employee, attendance_date=attendance_date)

        # -----------------------------------------------------------------
        # Scope rules (IN / OUT / FULL) to prevent duplicates/overlaps.
        # -----------------------------------------------------------------
        from attendance.services.attendance_correction_scope_rules import (
            infer_scope_from_values,
            get_approved_scopes,
            get_current_scope,
            build_requested_data_for_save,
            validate_new_request_scope,
        )

        incoming_scope = infer_scope_from_values(in_time, out_time)

        approved_scopes = []
        existing_waiting_scope = ""
        keep_existing_fields = False
        existing_attendance = attendances.first() if attendances.exists() else None
        if existing_attendance is not None:
            existing_req = getattr(existing_attendance, "requested_data", None)
            approved_scopes = get_approved_scopes(existing_req)
            if bool(getattr(existing_attendance, "is_validate_request", False)):
                existing_waiting_scope = get_current_scope(existing_req)
                keep_existing_fields = True

        validate_new_request_scope(
            existing_waiting_scope=existing_waiting_scope,
            approved_scopes=approved_scopes,
            incoming_scope=incoming_scope,
        )

        data = {
            "employee_id": employee,
            "attendance_date": attendance_date,
            "attendance_clock_in_date": in_date,
            "attendance_clock_in": in_time,
            "attendance_clock_out": out_time,
            "attendance_clock_out_date": out_date,
            "shift_id": shift,
            "work_type_id": work_type,
            "attendance_worked_hour": worked_hour,
            "minimum_hour": minimum_hour,
        }

        if attendances.exists():
            # update_request: store requested_data on existing record
            data["employee_id"] = employee.id
            data["attendance_date"] = str(attendance_date)
            data["attendance_clock_in_date"] = self.data.get("attendance_clock_in_date") or (str(in_date) if in_date else None)
            data["attendance_clock_in"] = self.data.get("attendance_clock_in") or (in_time.strftime("%H:%M") if in_time else None)
            data["attendance_clock_out"] = None if (self.data.get("attendance_clock_out") in (None, "", "None")) else self.data.get("attendance_clock_out")
            data["attendance_clock_out_date"] = None if (self.data.get("attendance_clock_out_date") in (None, "", "None")) else self.data.get("attendance_clock_out_date")

            attendance = attendances.first()
            # Merge requested_data while keeping previous fields if needed
            meta_wrapped = build_requested_data_for_save(
                new_payload={
                    **data,
                    "work_type_id": self.data.get("work_type_id") or (str(getattr(work_type, "id", "")) if work_type else ""),
                    "shift_id": self.data.get("shift_id") or (str(getattr(shift, "id", "")) if shift else ""),
                    "attendance_worked_hour": self.data.get("attendance_worked_hour") or worked_hour,
                    "minimum_hour": minimum_hour,
                },
                existing_requested_data=getattr(attendance, "requested_data", None),
                incoming_scope=incoming_scope,
                keep_existing_fields=keep_existing_fields,
            )
            attendance.requested_data = meta_wrapped
            attendance.is_validate_request = True
            if attendance.request_type != "create_request":
                attendance.request_type = "update_request"
            attendance.request_description = self.data.get("request_description")
            attendance.save()
            self.new_instance = None
            return self.cleaned_data

        # New create_request row
        meta_wrapped = build_requested_data_for_save(
            new_payload={
                "employee_id": employee.id,
                "attendance_date": str(attendance_date),
                "attendance_clock_in_date": self.data.get("attendance_clock_in_date") or (str(in_date) if in_date else None),
                "attendance_clock_in": self.data.get("attendance_clock_in") or (in_time.strftime("%H:%M") if in_time else None),
                "attendance_clock_out": None if (self.data.get("attendance_clock_out") in (None, "", "None")) else self.data.get("attendance_clock_out"),
                "attendance_clock_out_date": None if (self.data.get("attendance_clock_out_date") in (None, "", "None")) else self.data.get("attendance_clock_out_date"),
                "work_type_id": self.data.get("work_type_id") or (str(getattr(work_type, "id", "")) if work_type else ""),
                "shift_id": self.data.get("shift_id") or (str(getattr(shift, "id", "")) if shift else ""),
                "attendance_worked_hour": self.data.get("attendance_worked_hour") or worked_hour,
                "minimum_hour": minimum_hour,
            },
            existing_requested_data=None,
            incoming_scope=incoming_scope,
            keep_existing_fields=False,
        )

        new_instance = Attendance(**data)
        new_instance.is_validate_request = True
        new_instance.attendance_validated = False
        new_instance.request_description = self.data.get("request_description")
        new_instance.request_type = "create_request"
        new_instance.requested_data = meta_wrapped
        self.new_instance = new_instance
        return self.cleaned_data


excluded_fields = [
    "id",
    "attendance_id__employee_id",
    "in_datetime",
    "out_datetime",
    "requested_data",
    "at_work_second",
    "approved_overtime_second",
    "is_validate_request",
    "is_validate_request_approved",
    "request_description",
    "request_type",
    "month_sequence",
    "objects",
    "horilla_history",
]


class AttendanceExportForm(forms.Form):
    """
    This form allows users to choose which fields of the `Attendance` model
    they want to include in the export excel file as column. The fields are
    presented as a list of checkboxes, and the user can select multiple fields.
    """

    model_fields = Attendance._meta.get_fields()
    field_choices = [
        (field.name, field.verbose_name)
        for field in model_fields
        if hasattr(field, "verbose_name") and field.name not in excluded_fields
    ]

    selected_fields = forms.MultipleChoiceField(
        choices=field_choices,
        widget=forms.CheckboxSelectMultiple,
        initial=[
            "employee_id",
            "shift_id",
            "work_type_id",
            "attendance_date",
            "attendance_clock_in",
            "attendance_clock_in_date",
            "attendance_clock_out",
            "attendance_clock_out_date",
            "attendance_worked_hour",
            "attendance_validated",
        ],
    )


class LateComeEarlyOutExportForm(forms.Form):
    """
    This form allows users to choose fields from both the `AttendanceLateComeEarlyOut`
    model and the related `Attendance` model to include in the export excel file.
    The fields are presented as checkboxes, and users can select multiple fields.
    """

    model_fields = AttendanceLateComeEarlyOut._meta.get_fields()
    field_choices_1 = [
        (field.name, field.verbose_name)
        for field in model_fields
        if hasattr(field, "verbose_name") and field.name not in excluded_fields
    ]
    model_fields_2 = Attendance._meta.get_fields()
    field_choices_2 = [
        ("attendance_id__" + field.name, field.verbose_name)
        for field in model_fields_2
        if hasattr(field, "verbose_name") and field.name not in excluded_fields
    ]
    field_choices = field_choices_1 + field_choices_2
    field_choices = list(OrderedDict.fromkeys(field_choices))
    selected_fields = forms.MultipleChoiceField(
        choices=field_choices,
        widget=forms.CheckboxSelectMultiple,
        initial=[
            "employee_id",
            "type",
            "attendance_id__attendance_date",
            "attendance_id__attendance_clock_in_date",
            "attendance_id__attendance_clock_in",
            "attendance_id__attendance_clock_out_date",
            "attendance_id__attendance_clock_out",
        ],
    )


class AttendanceActivityExportForm(forms.Form):
    """
    This form allows users to choose specific fields from the `AttendanceActivity`
    model to include in the export excel file. The fields are presented as checkboxes,
    enabling users to select multiple fields.
    """

    model_fields = AttendanceActivity._meta.get_fields()
    field_choices = [
        (field.name, field.verbose_name)
        for field in model_fields
        if hasattr(field, "verbose_name") and field.name not in excluded_fields
    ]
    selected_fields = forms.MultipleChoiceField(
        choices=field_choices,
        widget=forms.CheckboxSelectMultiple,
        initial=[
            "employee_id",
            "attendance_date",
            "clock_in_date",
            "clock_in",
            "clock_out_date",
            "clock_out",
        ],
    )


class AttendanceOverTimeExportForm(forms.Form):
    """
    This form allows users to choose specific fields from the `AttendanceOverTime`
    model to include in the export. The fields are presented as checkboxes,
    enabling users to select multiple fields.
    """

    model_fields = AttendanceOverTime._meta.get_fields()
    field_choices = [
        (field.name, field.verbose_name)
        for field in model_fields
        if hasattr(field, "verbose_name") and field.name not in excluded_fields
    ]
    selected_fields = forms.MultipleChoiceField(
        choices=field_choices,
        widget=forms.CheckboxSelectMultiple,
        initial=[
            "employee_id",
            "month",
            "year",
            "worked_hours",
            "pending_hours",
            "overtime",
        ],
    )


class GraceTimeForm(BaseModelForm):
    """
    Form for create or update Grace time
    """

    shifts = forms.ModelMultipleChoiceField(
        queryset=EmployeeShift.objects.all(),
        required=False,
        help_text=_("Allcocate this grace time for Check-In Attendance"),
    )

    class Meta:
        """
        Meta class for additional options
        """

        model = GraceTime
        fields = "__all__"
        widgets = {
            "is_default": forms.HiddenInput(),
            "allowed_time": forms.TextInput(attrs={"placeholder": "00:00:00 Hours"}),
        }

        exclude = ["objects", "allowed_time_in_secs", "is_active"]


class GraceTimeAssignForm(forms.Form):
    """
    Form for create or update Grace time
    """

    shifts = forms.ModelMultipleChoiceField(
        queryset=EmployeeShift.objects.all(),
    )
    verbose_name = _("Assign Shifts")

    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML table rows with Bootstrap styling.
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        form_html = render_to_string("common_form.html", context)
        return form_html

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.fields["shifts"].widget.attrs["class"] = "oh-select w-100 oh-select-2"


class AttendanceRequestCommentForm(BaseModelForm):
    """
    AttendanceRequestComment form
    """

    class Meta:
        """
        Meta class for additional options
        """

        model = AttendanceRequestComment
        fields = ("comment",)


def get_date_list(employee_id, from_date, to_date):
    """
    This method will return a list of company working dates
    """
    working_dates = get_working_days(from_date, to_date)
    working_date_list = working_dates["working_days_on"]
    working_date_list.sort()
    attendance_dates = []
    if len(working_date_list) > 0:
        # filter through approved leave of employee
        if apps.is_installed("leave"):
            from leave.filters import LeaveRequestFilter

            approved_leave_dates_filtered = LeaveRequestFilter(
                data={
                    "from_date": working_date_list[0],
                    "to_date": working_date_list[-1],
                    "status": "approved",
                }
            )
            approved_leave_dates_filtered = approved_leave_dates_filtered.qs.filter(
                employee_id=employee_id
            )
        else:
            approved_leave_dates_filtered = QuerySet().none()
        approved_leave_dates = []
        # Extract the list of approved leave dates
        if len(approved_leave_dates_filtered) > 0:
            for leave in approved_leave_dates_filtered:
                approved_leave_dates += leave.requested_dates()
        attendance_filters = AttendanceFilters(
            data={
                "attendance_date__gte": working_date_list[0],
                "attendance_date__lte": working_date_list[-1],
            }
        )
        existing_attendance = attendance_filters.qs.filter(employee_id=employee_id)
        # Extract the list of attendance dates
        attendance_dates = list(
            existing_attendance.values_list("attendance_date", flat=True)
        )
    # Calculate the dates that need new attendance records
    date_list = [
        date
        for date in working_date_list
        if date not in attendance_dates and date not in approved_leave_dates
    ]
    return date_list


class BulkAttendanceRequestForm(BaseModelForm):
    """
    Bulk attendance request create form
    """

    employee_id = forms.ModelChoiceField(
        queryset=Employee.objects.filter(is_active=True),
        widget=forms.Select(
            attrs={
                            }
        ),
        label=_("Employee"),
    )
    create_bulk = forms.BooleanField(
        required=False,
        initial=True,
        label=_("Create Bulk"),
        widget=forms.CheckboxInput(
            attrs={
                "class": "oh-checkbox",
                "hx-target": "#objectCreateModalTarget",
                "hx-get": "/attendance/request-new-attendance?bulk=False",
            }
        ),
    )
    from_date = forms.DateField(
        required=False,
        label=_("From Date"),
        widget=forms.DateInput(attrs={"type": "date", "class": "form-control"}),
    )
    to_date = forms.DateField(
        required=False,
        label=_("To Date"),
        widget=forms.DateInput(attrs={"type": "date", "class": "form-control"}),
    )
    batch_attendance_id = forms.ModelChoiceField(
        queryset=BatchAttendance.objects.all(),
        required=False,
        label="Batch",
        widget=forms.Select(attrs={"onchange": "dynamicBatchAttendance($(this))"}),
    )

    class Meta:
        """
        Meta class for additional options
        """

        model = Attendance
        fields = (
            "employee_id",
            "create_bulk",
            "from_date",
            "to_date",
            "shift_id",
            "work_type_id",
            "attendance_clock_in",
            "attendance_clock_out",
            "minimum_hour",
            "attendance_worked_hour",
            "request_description",
        )

    def update_worked_hour_hx_fields(self, field_name):
        """Update the widget attributes for worked hour fields."""
        self.fields[field_name].widget.attrs.update(
            {
                "id": str(uuid.uuid4()),
                "hx-include": "#attendanceRequestForm",
                "hx-target": "#id_attendance_worked_hour_parent_div",
                "hx-swap": "outerHTML",
                "hx-select": "#id_attendance_worked_hour_parent_div",
                "hx-get": "/attendance/update-worked-hour-field",
                "hx-trigger": "change delay:300ms",
            }
        )

    def __init__(self, *args, **kwargs):
        request = getattr(horilla_middlewares._thread_locals, "request", None)
        employee = request.user.employee_get
        super().__init__(*args, **kwargs)
        # Attendance Correction Request (mobile parity): no batch selection
        if 'batch_attendance_id' in self.fields:
            self.fields['batch_attendance_id'].required = False
            self.fields['batch_attendance_id'].widget = forms.HiddenInput()

        # Shift / worked hour / minimum hour should not be chosen/typed by user
        for f in ["shift_id", "attendance_worked_hour", "minimum_hour"]:
            if f in self.fields:
                self.fields[f].required = False
                self.fields[f].widget = forms.HiddenInput()
        if 'minimum_hour' in self.fields:
            self.fields['minimum_hour'].initial = '00:00'
        if 'attendance_worked_hour' in self.fields:
            self.fields['attendance_worked_hour'].initial = '00:00'

        if employee and hasattr(employee, "employee_work_info"):
            shift = employee.employee_work_info.shift_id
            self.fields["shift_id"].initial = shift
        if request.user.has_perm("attendance.add_attendance") or is_reportingmanager(
            request
        ):
            employees = filtersubordinatesemployeemodel(
                request, Employee.objects.all(), perm="pms.add_feedback"
            )
            self.fields["employee_id"].queryset = employees | Employee.objects.filter(
                employee_user_id=request.user
            )
        else:
            self.fields["employee_id"].queryset = Employee.objects.filter(
                employee_user_id=request.user
            )
        self.fields["batch_attendance_id"].choices = list(
            self.fields["batch_attendance_id"].choices
        ) + [("dynamic_create", "Dynamic create")]

    def clean(self):
        cleaned_data = self.cleaned_data
        from_date = cleaned_data.get("from_date")
        to_date = cleaned_data.get("to_date")
        attendance_worked_hour = cleaned_data.get("attendance_worked_hour") or "00:00"
        attendance_clock_out = cleaned_data.get("attendance_clock_out")
        employee_id = cleaned_data.get("employee_id")
        shift_id = cleaned_data.get("shift_id") or (
            employee_id.employee_work_info.shift_id
            if employee_id and hasattr(employee_id, "employee_work_info")
            else None
        )
        minimum_hour = _resolve_schedule_minimum_hour(
            from_date,
            shift_id,
            fallback=cleaned_data.get("minimum_hour") or "00:00",
        )
        cleaned_data["minimum_hour"] = minimum_hour
        now = datetime.datetime.now().time()
        today = datetime.datetime.today().date()
        validate_time_format(attendance_worked_hour)
        validate_time_format(minimum_hour)
        attendance_date_validate(from_date)
        attendance_date_validate(to_date)
        date_list = get_date_list(employee_id, from_date, to_date)
        if from_date and to_date and from_date > to_date:
            raise ValidationError({"to_date": _("To date should be after from date")})
        if to_date == today and attendance_clock_out > now:
            raise ValidationError(
                {
                    "attendance_clock_out": (
                        f"Check out time is in the future for the date {to_date}."
                    )
                }
            )
        if employee_id and not hasattr(employee_id, "employee_work_info"):
            raise ValidationError(_("Employee work info not found"))
        if len(date_list) <= 0:
            raise ValidationError(
                _(
                    "There is no valid date to create attendance request between this date range"
                )
            )
        return cleaned_data

    def save(self, commit=True):
        # Access cleaned data
        cleaned_data = self.cleaned_data
        employee_id = cleaned_data.get("employee_id")
        from_date = cleaned_data.get("from_date")
        to_date = cleaned_data.get("to_date")
        shift_id = cleaned_data.get("shift_id") or employee_id.employee_work_info.shift_id
        attendance_clock_in = cleaned_data.get("attendance_clock_in")
        attendance_clock_out = cleaned_data.get("attendance_clock_out")
        request_description = cleaned_data.get("request_description")
        attendance_worked_hour = cleaned_data.get("attendance_worked_hour") or "00:00"
        minimum_hour = cleaned_data.get("minimum_hour") or "00:00"
        work_type_id = employee_id.employee_work_info.work_type_id
        date_list = get_date_list(employee_id, from_date, to_date)
        batch = (
            cleaned_data.get("batch_attendance_id")
            if cleaned_data.get("batch_attendance_id")
            else None
        )
        # Prepare initial data for the form
        initial_data = {
            "employee_id": employee_id,
            "shift_id": shift_id,
            "work_type_id": work_type_id,
            "attendance_clock_in": attendance_clock_in,
            "attendance_clock_out": attendance_clock_out,
            "attendance_worked_hour": attendance_worked_hour,
            "is_validate_request": True,
            "minimum_hour": minimum_hour,
            "request_description": request_description,
        }
        for date in date_list:
            initial_data.update(
                {
                    "attendance_date": date,
                    "attendance_clock_in_date": date,
                    "attendance_clock_out_date": date,
                    "minimum_hour": _resolve_schedule_minimum_hour(date, shift_id, fallback=minimum_hour),
                }
            )
            form = NewRequestForm(data=initial_data)
            if form.is_valid():
                instance = form.save(commit=False)
                instance.is_validate_request = True
                instance.employee_id = employee_id
                instance.request_type = "create_request"
                instance.is_bulk_request = True
                if batch:
                    instance.batch_attendance_id = batch
                instance.save()
            else:
                logger(form.errors)
        instance = super().save(commit=False)
        if commit:
            instance.save()

        return instance


class WorkRecordsForm(BaseModelForm):
    """
    WorkRecordForm
    """

    class Meta:
        """
        Meta class for additional options
        """

        fields = "__all__"
        model = WorkRecords


class BatchAttendanceForm(BaseModelForm):
    """
    BatchAttendanceForm
    """

    verbose_name = _("Create attendance batch")

    class Meta:
        """
        Meta class for additional options
        """

        fields = "__all__"
        model = BatchAttendance
        exclude = ["is_active"]

    def as_p(self, *args, **kwargs):
        """
        Render the form fields as HTML table rows with Bootstrap styling.
        """
        _ = args, kwargs  # Explicitly mark as used for pylint
        context = {"form": self}
        form_html = render_to_string("common_form.html", context)
        return form_html

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        if self.instance.pk:
            self.verbose_name = _("Update attendance batch")
