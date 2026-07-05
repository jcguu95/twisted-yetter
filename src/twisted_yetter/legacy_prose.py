"""Relative locators for archived legacy prose records."""

from __future__ import annotations

from typing import Final

LEGACY_PROSE_ARCHIVE_MANIFEST: Final = (
    "legacy-archives/prose-corpus-2026-07-05.manifest.json"
)
LEGACY_PROSE_ARCHIVE: Final = "legacy-archives/prose-corpus-2026-07-05.tar"


def legacy_prose_member_ref(member_path: str) -> str:
    """Return a repo-relative locator for a member of the legacy prose archive."""

    if not member_path or member_path.startswith("/"):
        raise ValueError("legacy prose member path must be a nonempty relative path")
    if "#" in member_path or ".." in member_path.split("/"):
        raise ValueError("legacy prose member path must not contain fragments or '..'")
    return f"{LEGACY_PROSE_ARCHIVE_MANIFEST}#archive_member_path={member_path}"
