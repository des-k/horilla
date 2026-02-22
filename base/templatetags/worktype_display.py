from django import template

from base.worktype_display import worktype_label

register = template.Library()


@register.filter(name="worktype_label")
def worktype_label_filter(val):
    return worktype_label(val)
