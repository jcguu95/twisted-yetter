from __future__ import annotations

import re
from pathlib import Path


ARCHIVE_ID = "prose-corpus-2026-07-05"
ARCHIVE_REL_PATH = f"legacy-archives/{ARCHIVE_ID}.tar"
MANIFEST_REL_PATH = f"legacy-archives/{ARCHIVE_ID}.manifest.json"
ARCHIVE_MEMBER_REF_PREFIX = f"{MANIFEST_REL_PATH}#archive_member_path="

PROSE_SUFFIXES = {
    ".adoc",
    ".markdown",
    ".md",
    ".org",
    ".rst",
    ".txt",
}

ALLOWED_PROSE_PATHS = {
    "AGENTS.md",
    "ctl-dogfood/README.org",
    "experiments/README.org",
    "experiments/sage/README.org",
}

ALLOWED_LEGACY_ARCHIVE_PATHS = {
    ARCHIVE_REL_PATH,
    MANIFEST_REL_PATH,
}

GENERATED_CACHE_DIRS = {
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".sage",
    ".uv-cache",
    ".venv",
    "__pycache__",
}

RAW_LEGACY_REF_RE = re.compile(
    r"(?<!archive_member_path=)(twisted-yetter\.org|wiki/[^\s\"'`),\]}]+)"
)
ARCHIVE_MEMBER_REF_RE = re.compile(
    re.escape(ARCHIVE_MEMBER_REF_PREFIX) + r"([^\s\"'`),\]}]+)"
)


def repo_path(repo_root: Path, path: Path) -> str:
    return path.relative_to(repo_root).as_posix()


def archive_path(repo_root: Path) -> Path:
    return repo_root / ARCHIVE_REL_PATH


def manifest_path(repo_root: Path) -> Path:
    return repo_root / MANIFEST_REL_PATH


def is_under_git_dir(repo_root: Path, path: Path) -> bool:
    try:
        path.relative_to(repo_root / ".git")
        return True
    except ValueError:
        return False


def is_under_legacy_archives(repo_root: Path, path: Path) -> bool:
    try:
        path.relative_to(repo_root / "legacy-archives")
        return True
    except ValueError:
        return False


def is_under_generated_cache(repo_root: Path, path: Path) -> bool:
    try:
        rel = path.relative_to(repo_root)
    except ValueError:
        return False
    return any(part in GENERATED_CACHE_DIRS for part in rel.parts)


def is_allowed_loose_prose(rel_path: str) -> bool:
    return rel_path in ALLOWED_PROSE_PATHS


def validate_archive_member_path(member_path: object) -> str:
    if not isinstance(member_path, str):
        raise ValueError("archive member path must be string")
    if member_path == "":
        raise ValueError("archive member path must be nonempty")
    if member_path.startswith("/"):
        raise ValueError(f"absolute archive member path: {member_path}")
    if "#" in member_path:
        raise ValueError(f"fragment marker in archive member path: {member_path}")
    if ".." in member_path.split("/"):
        raise ValueError(f"parent traversal in archive member path: {member_path}")
    return member_path


def legacy_archive_ref(member_path: str) -> str:
    return ARCHIVE_MEMBER_REF_PREFIX + validate_archive_member_path(member_path)


def raw_legacy_refs_in_string(value: str) -> list[str]:
    return [match.group(1) for match in RAW_LEGACY_REF_RE.finditer(value)]


def archive_member_refs_in_string(value: str) -> list[str]:
    return [
        validate_archive_member_path(match.group(1))
        for match in ARCHIVE_MEMBER_REF_RE.finditer(value)
    ]
