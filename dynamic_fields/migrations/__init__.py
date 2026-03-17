"""Dynamic fields migrations package.

Keep this module import-safe during test discovery. Signals are loaded by the
app config; importing them here causes Django to import models before the app
registry is ready.
"""
