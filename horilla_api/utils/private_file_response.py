import mimetypes
import os

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
    return response
