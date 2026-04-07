from __future__ import annotations

from typing import Iterable, Optional

from django.db.models import Model
from django.urls import reverse
from notifications.signals import notify

from attendance.models import AttendanceWorkMode




def _is_model_instance(value) -> bool:
    return isinstance(value, Model) and getattr(value, 'pk', None) is not None


def _safe_sender(actor, recipient=None):
    if _is_model_instance(actor):
        return actor
    if _is_model_instance(recipient):
        return recipient
    return None


def _safe_recipient(recipient):
    return recipient if _is_model_instance(recipient) else None

def _employee_user(employee):
    return getattr(employee, 'employee_user_id', None)


def _employee_name(employee) -> str:
    if employee is None:
        return 'Employee'
    first = (getattr(employee, 'employee_first_name', '') or '').strip()
    last = (getattr(employee, 'employee_last_name', '') or '').strip()
    full = ' '.join(part for part in (first, last) if part).strip()
    return full or str(employee)


def _notify_domain_event(*, actor, recipient, verb: str, redirect: str, icon: str, payload: dict, translations: Optional[dict] = None):
    recipient = _safe_recipient(recipient)
    sender = _safe_sender(actor, recipient=recipient)
    if recipient is None or sender is None:
        return []
    kwargs = dict(payload)
    kwargs['redirect'] = redirect
    kwargs['icon'] = icon
    for key, value in (translations or {}).items():
        if value:
            kwargs[key] = value
    return notify.send(sender, recipient=recipient, verb=verb, **kwargs)


def _attendance_payload(attendance, *, event: str, status: str, message: str, recipient_role: str, actor_name: Optional[str] = None, reason: Optional[str] = None):
    payload = {
        'category': 'attendance',
        'event': event,
        'entity_type': 'attendance_request',
        'entity_id': attendance.id,
        'status': status,
        'message': message,
        'recipient_role': recipient_role,
        'mobile_route': '/attendance_request',
        'mobile_args': {
            'tab': 'attendance_request',
            'request_id': attendance.id,
            'focus_action': 'open_detail',
        },
        'date': getattr(attendance, 'attendance_date', None).isoformat() if getattr(attendance, 'attendance_date', None) else None,
    }
    if actor_name:
        payload['actor_name'] = actor_name
    if reason:
        payload['reason'] = reason
    return payload


def send_attendance_request_notification(*, actor, recipient, attendance, event: str, recipient_role: str, reason: Optional[str] = None):
    employee_name = _employee_name(getattr(attendance, 'employee_id', None))
    date_label = getattr(attendance, 'attendance_date', None)
    date_label = date_label.isoformat() if hasattr(date_label, 'isoformat') else str(date_label)
    actor_name = _employee_name(getattr(actor, 'employee_get', None) or actor)

    if event == 'attendance_request_created':
        verb = f'{employee_name} attendance update request for {date_label} is created'
        message = f'Pengajuan koreksi attendance {date_label} menunggu persetujuan Anda.'
        translations = {
            'verb_ar': f'تم إنشاء طلب تحديث الحضور لـ {employee_name} في {date_label}',
            'verb_de': f'Die Anfrage zur Aktualisierung der Anwesenheit von {employee_name} für den {date_label} wurde erstellt',
            'verb_es': f'Se ha creado la solicitud de actualización de asistencia para {employee_name} el {date_label}',
            'verb_fr': f'La demande de mise à jour de présence de {employee_name} pour le {date_label} a été créée',
        }
        status = 'requested'
    elif event == 'attendance_request_approved':
        if recipient_role == 'requester':
            verb = f'Your attendance request for {date_label} is validated'
            message = f'Pengajuan koreksi attendance {date_label} disetujui.'
        else:
            verb = f'{employee_name} attendance request for {date_label} is validated'
            message = f'Pengajuan koreksi attendance {date_label} untuk {employee_name} telah disetujui.'
        translations = {
            'verb_ar': f'تم التحقق من طلب الحضور في {date_label}',
            'verb_de': f'Der Anwesenheitsantrag für den {date_label} wurde bestätigt',
            'verb_es': f'Se ha validado la solicitud de asistencia para la fecha {date_label}',
            'verb_fr': f'La demande de présence pour le {date_label} a été validée',
        }
        status = 'approved'
    elif event == 'attendance_request_rejected':
        verb = f'Your attendance request for {date_label} has been rejected'
        message = f'Pengajuan koreksi attendance {date_label} ditolak. Lihat alasannya.'
        translations = {
            'verb_ar': f'تم رفض طلب الحضور في {date_label}',
            'verb_de': f'Der Anwesenheitsantrag für den {date_label} wurde abgelehnt',
            'verb_es': f'Se rechazó la solicitud de asistencia para la fecha {date_label}',
            'verb_fr': f'La demande de présence pour le {date_label} a été rejetée',
        }
        status = 'rejected'
    elif event == 'attendance_request_canceled':
        verb = f'Your attendance request for {date_label} has been canceled'
        message = f'Pengajuan koreksi attendance {date_label} dibatalkan.'
        translations = {
            'verb_ar': f'تم إلغاء طلب الحضور في {date_label}',
            'verb_de': f'Der Anwesenheitsantrag für den {date_label} wurde storniert',
            'verb_es': f'Se canceló la solicitud de asistencia para la fecha {date_label}',
            'verb_fr': f'La demande de présence pour le {date_label} a été annulée',
        }
        status = 'canceled'
    elif event == 'attendance_request_revoked':
        verb = f'Your attendance request for {date_label} has been revoked'
        message = f'Persetujuan koreksi attendance {date_label} direvoke. Lihat alasannya.'
        translations = {
            'verb_ar': f'تم سحب الموافقة على طلب الحضور في {date_label}',
            'verb_de': f'Die Genehmigung des Anwesenheitsantrags für den {date_label} wurde widerrufen',
            'verb_es': f'Se revocó la aprobación de la solicitud de asistencia para la fecha {date_label}',
            'verb_fr': f"L'approbation de la demande de présence pour le {date_label} a été révoquée",
        }
        status = 'revoked'
    else:
        raise ValueError(f'Unsupported attendance event: {event}')

    payload = _attendance_payload(attendance, event=event, status=status, message=message, recipient_role=recipient_role, actor_name=actor_name, reason=reason)
    return _notify_domain_event(
        actor=actor,
        recipient=recipient,
        verb=verb,
        redirect=reverse('request-attendance-view') + f'?id={attendance.id}',
        icon='checkmark-circle-outline',
        payload=payload,
        translations=translations,
    )


def _work_mode_route_args(req):
    return {
        'tab': 'work_mode_request',
        'request_id': req.id,
        'focus_action': 'open_detail',
    }


def _work_mode_label(mode: str) -> str:
    raw = (mode or '').strip().lower()
    if raw == AttendanceWorkMode.WFA:
        return 'WFA'
    if raw == AttendanceWorkMode.ON_DUTY:
        return 'On Duty'
    return (mode or 'Work mode').replace('_', ' ').title()


def _date_or_range(req) -> tuple[Optional[str], Optional[dict]]:
    start = getattr(req, 'start_date', None)
    end = getattr(req, 'end_date', None)
    if start and end:
        if start == end:
            return start.isoformat(), None
        return None, {'start': start.isoformat(), 'end': end.isoformat()}
    if start:
        return start.isoformat(), None
    return None, None


def _work_mode_payload(req, *, event: str, status: str, message: str, recipient_role: str, reason: Optional[str] = None, actor_name: Optional[str] = None):
    date_value, date_range = _date_or_range(req)
    payload = {
        'category': 'work_mode',
        'event': event,
        'entity_type': 'work_mode_request',
        'entity_id': req.id,
        'status': status,
        'message': message,
        'recipient_role': recipient_role,
        'mode': getattr(req, 'mode', None),
        'mobile_route': '/attendance_request',
        'mobile_args': _work_mode_route_args(req),
    }
    if actor_name:
        payload['actor_name'] = actor_name
    if reason:
        payload['reason'] = reason
    if date_value:
        payload['date'] = date_value
    if date_range:
        payload['date_range'] = date_range
    return payload


def _requester_user(req):
    employee = getattr(req, 'employee_id', None)
    return _employee_user(employee)


def _approver_user(req):
    employee = getattr(req, 'employee_id', None)
    work_info = None
    if employee is not None:
        try:
            work_info = employee.employee_work_info
        except Exception:
            work_info = None
    manager = getattr(work_info, 'reporting_manager_id', None)
    if manager is None:
        try:
            from employee.models import EmployeeWorkInformation

            employee_id = getattr(req, 'employee_id_id', None) or getattr(employee, 'id', None)
            if employee_id:
                work_info = EmployeeWorkInformation.objects.filter(employee_id=employee_id).select_related('reporting_manager_id__employee_user_id').first()
                manager = getattr(work_info, 'reporting_manager_id', None)
        except Exception:
            manager = None
    return _employee_user(manager)


def send_work_mode_request_notification(*, actor, req, event: str, recipient=None, recipient_role: Optional[str] = None, reason: Optional[str] = None):
    mode_label = _work_mode_label(getattr(req, 'mode', None))
    actor_name = _employee_name(actor)
    date_value, date_range = _date_or_range(req)
    when = date_value or (f"{date_range['start']} to {date_range['end']}" if date_range else 'requested period')

    if recipient is None:
        if recipient_role == 'approver':
            recipient = _approver_user(req)
        else:
            recipient = _requester_user(req)
    if recipient_role is None:
        recipient_role = 'requester'

    event_map = {
        'work_mode_request_created': ('requested', f'{mode_label} request for {when} is awaiting your approval.', f'Pengajuan {mode_label} {when} menunggu persetujuan Anda.'),
        'work_mode_request_approved': ('approved', f'Your {mode_label} request has been approved.', f'Pengajuan {mode_label} Anda disetujui.'),
        'work_mode_request_rejected': ('rejected', f'Your {mode_label} request has been rejected.', f'Pengajuan {mode_label} Anda ditolak. Lihat alasannya.'),
        'work_mode_request_canceled': ('canceled', f'Your {mode_label} request has been canceled.', f'Pengajuan {mode_label} Anda dibatalkan.'),
        'work_mode_request_revoked': ('revoked', f'Your {mode_label} request has been revoked.', f'Pengajuan {mode_label} Anda direvoke.'),
        'work_mode_document_uploaded': ('document_uploaded', f'{mode_label} document was uploaded and is waiting for review.', f'Dokumen {mode_label} baru diunggah dan menunggu verifikasi.'),
        'work_mode_document_verified': ('document_verified', f'Your {mode_label} document has been verified.', f'Dokumen {mode_label} Anda telah diverifikasi.'),
        'work_mode_document_rejected': ('document_rejected', f'Your {mode_label} document has been rejected.', f'Dokumen {mode_label} Anda ditolak. Lihat alasan dan unggah ulang.'),
        'work_mode_request_auto_rejected': ('rejected', f'Your {mode_label} request has been automatically rejected.', f'Pengajuan {mode_label} Anda otomatis ditolak karena melewati batas persetujuan.'),
    }
    if event not in event_map:
        raise ValueError(f'Unsupported work mode event: {event}')
    status, verb, message = event_map[event]
    payload = _work_mode_payload(req, event=event, status=status, message=message, recipient_role=recipient_role, reason=reason, actor_name=actor_name)
    return _notify_domain_event(
        actor=actor,
        recipient=recipient,
        verb=verb,
        redirect=reverse('work-type-request-view') + f'?id={req.id}',
        icon='briefcase-outline',
        payload=payload,
    )


def _leave_payload(leave_request, *, event: str, status: str, message: str, recipient_role: str, actor_name: Optional[str] = None, reason: Optional[str] = None):
    start = getattr(leave_request, 'start_date', None)
    end = getattr(leave_request, 'end_date', None)
    payload = {
        'category': 'leave',
        'event': event,
        'entity_type': 'leave_request',
        'entity_id': leave_request.id,
        'status': status,
        'message': message,
        'recipient_role': recipient_role,
        'mobile_route': '/leave_request',
        'mobile_args': {
            'request_id': leave_request.id,
            'focus_action': 'open_detail',
        },
    }
    if start and end:
        if start == end:
            payload['date'] = start.isoformat()
        else:
            payload['date_range'] = {'start': start.isoformat(), 'end': end.isoformat()}
    elif start:
        payload['date'] = start.isoformat()
    if actor_name:
        payload['actor_name'] = actor_name
    if reason:
        payload['reason'] = reason
    return payload


def send_leave_request_notification(*, actor, recipient, leave_request, event: str, recipient_role: str, reason: Optional[str] = None):
    actor_name = _employee_name(getattr(actor, 'employee_get', None) or actor)
    employee_name = _employee_name(getattr(leave_request, 'employee_id', None))
    event_map = {
        'leave_request_created': ('requested', 'You have a new leave request to validate.', 'Pengajuan cuti baru menunggu persetujuan Anda.'),
        'leave_request_approved': ('approved', 'Your Leave request has been approved', 'Pengajuan cuti Anda disetujui.'),
        'leave_request_rejected': ('rejected', 'Your leave request has been rejected.', 'Pengajuan cuti Anda ditolak. Lihat alasannya.'),
        'leave_request_canceled': ('cancelled', 'Your leave request has been cancelled.', 'Pengajuan cuti Anda dibatalkan.'),
    }
    if event not in event_map:
        raise ValueError(f'Unsupported leave event: {event}')
    status, default_verb, message = event_map[event]
    verb = default_verb if recipient_role == 'requester' else f'New leave request created for {employee_name}.'
    payload = _leave_payload(leave_request, event=event, status=status, message=message, recipient_role=recipient_role, actor_name=actor_name, reason=reason)
    redirect_name = 'user-request-view' if recipient_role == 'requester' else 'request-view'
    return _notify_domain_event(
        actor=actor,
        recipient=recipient,
        verb=verb,
        redirect=reverse(redirect_name) + f'?id={leave_request.id}',
        icon='people-circle',
        payload=payload,
    )
