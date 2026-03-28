import os
import sys

if os.environ.get("HORILLA_DISABLE_SCHEDULERS") != "1" and not any(
    cmd in sys.argv
    for cmd in ["makemigrations", "migrate", "compilemessages", "flush", "shell", "test"]
):
    from . import scheduler
