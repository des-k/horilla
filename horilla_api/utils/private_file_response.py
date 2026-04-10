import hashlib
import mimetypes
import os
from email.utils import formatdate

from django.http import FileResponse, Http404


def private_file_response(file_field, filename=None, as_attachment=False):
    if not file_field:
        raise Http404("File not found")
    try:
        file_handle = file_field.open("rb")
    except Exception as exc:
        raise Http404("File not found") from exc

    final_name = filename or os.path.basename(getattr(file_field, "name", "") or "file")
    content_type, _ = mimetypes.guess_type(final_name)
    response = FileResponse(file_handle, as_attachment=as_attachment, filename=final_name)
    if content_type:
        response["Content-Type"] = content_type

    try:
        storage_name = getattr(file_field, "name", "") or ""
        file_size = getattr(file_field, "size", None)
        file_path = None
        if hasattr(file_field, "path"):
            try:
                file_path = file_field.path
            except Exception:
                file_path = None
        mtime = int(os.path.getmtime(file_path)) if file_path and os.path.exists(file_path) else None
        etag_source = f"{storage_name}:{file_size}:{mtime}"
        response["Cache-Control"] = "private, max-age=300"
        if mtime is not None:
            response["Last-Modified"] = formatdate(mtime, usegmt=True)
        response["ETag"] = hashlib.md5(etag_source.encode("utf-8")).hexdigest()
    except Exception:
        response["Cache-Control"] = "private, max-age=300"

    return response
