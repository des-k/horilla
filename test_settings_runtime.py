from apscheduler.schedulers import background as aps_background

aps_background.BackgroundScheduler.start = lambda self, *args, **kwargs: None
aps_background.BackgroundScheduler.add_job = lambda self, *args, **kwargs: None

from horilla.settings import *

MIGRATION_MODULES = {
    'notifications': None,
    'base': None,
    'employee': None,
    'recruitment': None,
    'leave': None,
    'pms': None,
    'onboarding': None,
    'asset': None,
    'attendance': None,
    'payroll': None,
    'accessibility': None,
    'horilla_audit': None,
    'horilla_widgets': None,
    'horilla_crumbs': None,
    'horilla_documents': None,
    'horilla_views': None,
    'horilla_automations': None,
    'biometric': None,
    'helpdesk': None,
    'offboarding': None,
    'horilla_backup': None,
    'project': None,
    'geofencing': None,
    'facedetection': None,
}
