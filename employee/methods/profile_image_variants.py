import io
import os
from typing import Optional

from django.core.files.base import ContentFile
from django.core.files.storage import default_storage
from PIL import Image, ImageOps


_AVATAR_SUFFIX = "__avatar.jpg"
_AVATAR_SIZE = (128, 128)


class StoredPrivateFile:
    def __init__(self, storage, name: str):
        self.storage = storage
        self.name = name

    def open(self, mode="rb"):
        return self.storage.open(self.name, mode)

    @property
    def size(self):
        return self.storage.size(self.name)

    @property
    def path(self):
        return self.storage.path(self.name)


def employee_profile_avatar_storage_name(employee) -> Optional[str]:
    profile = getattr(employee, "employee_profile", None)
    name = getattr(profile, "name", "") or ""
    if not name:
        return None
    root, _ext = os.path.splitext(name)
    return f"{root}{_AVATAR_SUFFIX}"


def delete_employee_profile_avatar_by_profile_name(profile_name: Optional[str], storage=None) -> None:
    if not profile_name:
        return
    root, _ext = os.path.splitext(profile_name)
    avatar_name = f"{root}{_AVATAR_SUFFIX}"
    storage = storage or default_storage
    try:
        if storage.exists(avatar_name):
            storage.delete(avatar_name)
    except Exception:
        return


def _load_raster_image(profile):
    try:
        profile.open("rb")
        image = Image.open(profile)
        image = ImageOps.exif_transpose(image)
        if image.mode not in ("RGB", "L"):
            background = Image.new("RGB", image.size, (255, 255, 255))
            if image.mode in ("RGBA", "LA"):
                background.paste(image, mask=image.getchannel("A"))
            else:
                background.paste(image)
            image = background
        else:
            image = image.convert("RGB")
        return image
    except Exception:
        return None
    finally:
        try:
            profile.close()
        except Exception:
            pass


def _build_avatar_content(image: Image.Image) -> ContentFile:
    width, height = image.size
    side = min(width, height)
    left = max((width - side) // 2, 0)
    top = max((height - side) // 2, 0)
    cropped = image.crop((left, top, left + side, top + side))
    resized = cropped.resize(_AVATAR_SIZE, Image.LANCZOS)
    buffer = io.BytesIO()
    resized.save(buffer, format="JPEG", quality=80, optimize=True)
    return ContentFile(buffer.getvalue())


def ensure_employee_profile_avatar(employee, force: bool = False) -> Optional[str]:
    profile = getattr(employee, "employee_profile", None)
    profile_name = getattr(profile, "name", "") or ""
    if not profile_name:
        return None
    storage = getattr(profile, "storage", None)
    if storage is None:
        return None

    avatar_name = employee_profile_avatar_storage_name(employee)
    if not avatar_name:
        return None

    if not force:
        try:
            if storage.exists(avatar_name):
                profile_mtime = storage.get_modified_time(profile_name)
                avatar_mtime = storage.get_modified_time(avatar_name)
                if avatar_mtime >= profile_mtime:
                    return avatar_name
        except Exception:
            pass

    image = _load_raster_image(profile)
    if image is None:
        return None

    try:
        if storage.exists(avatar_name):
            storage.delete(avatar_name)
    except Exception:
        pass

    content = _build_avatar_content(image)
    storage.save(avatar_name, content)
    return avatar_name


def employee_profile_avatar_file(employee):
    profile = getattr(employee, "employee_profile", None)
    storage = getattr(profile, "storage", None)
    avatar_name = employee_profile_avatar_storage_name(employee)
    if storage is None or not avatar_name:
        return None
    try:
        if storage.exists(avatar_name):
            return StoredPrivateFile(storage, avatar_name)
    except Exception:
        return None
    return None
