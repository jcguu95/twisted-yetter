#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tarfile
from io import BytesIO
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT_DIR = Path(__file__).resolve().parent
ARCHIVE_DIR = REPO_ROOT / "legacy-archives"

sys.path.insert(0, str(SCRIPT_DIR))
from prose_policy import (  # noqa: E402
    ALLOWED_PROSE_PATHS,
    ARCHIVE_ID,
    MANIFEST_REL_PATH,
    PROSE_SUFFIXES,
    archive_path,
    is_allowed_loose_prose,
    is_under_generated_cache,
    is_under_git_dir,
    is_under_legacy_archives,
    manifest_path,
    repo_path,
)

ARCHIVE_PATH = archive_path(REPO_ROOT)
MANIFEST_PATH = manifest_path(REPO_ROOT)


def run_git(args: list[str]) -> str:
    return subprocess.check_output(["git", "-C", str(REPO_ROOT), *args], text=True).strip()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def find_prose_files() -> list[Path]:
    out = []
    for path in REPO_ROOT.rglob("*"):
        if not path.is_file():
            continue
        if (
            is_under_git_dir(REPO_ROOT, path)
            or is_under_legacy_archives(REPO_ROOT, path)
            or is_under_generated_cache(REPO_ROOT, path)
        ):
            continue
        if path.suffix.lower() not in PROSE_SUFFIXES:
            continue
        rel = repo_path(REPO_ROOT, path)
        if is_allowed_loose_prose(rel):
            continue
        out.append(path)
    return sorted(out, key=lambda path: repo_path(REPO_ROOT, path))


def tracked_status(rel_path: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "ls-files", "--error-unmatch", "--", rel_path],
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return "tracked" if result.returncode == 0 else "untracked"


def git_blob_id(path: Path) -> str:
    return run_git(["hash-object", "--", repo_path(REPO_ROOT, path)])


def legacy_role(rel_path: str) -> str:
    if rel_path == "twisted-yetter.org":
        return "legacy-research-plan"
    if rel_path.startswith("wiki/lab-notes/"):
        return "legacy-lab-note"
    if rel_path.startswith("wiki/understandings/"):
        return "legacy-understanding"
    if rel_path.startswith("wiki/references/"):
        return "legacy-reference"
    if rel_path.startswith("wiki/roadmaps/"):
        return "legacy-roadmap"
    if rel_path.startswith("wiki/env/"):
        return "legacy-environment-note"
    if rel_path.startswith("wiki/"):
        return "legacy-wiki-entry"
    if rel_path.startswith("ctl-dogfood/run-"):
        return "legacy-run-transcript"
    return "legacy-human-prose"


def build_manifest() -> dict[str, Any]:
    files = []
    for path in find_prose_files():
        rel = repo_path(REPO_ROOT, path)
        files.append(
            {
                "original_repo_path": rel,
                "archive_member_path": rel,
                "sha256": file_sha256(path),
                "git_blob_id": git_blob_id(path),
                "size_bytes": path.stat().st_size,
                "tracked_status": tracked_status(rel),
                "legacy_role": legacy_role(rel),
                "normative_status": "archived-human-prose-not-normative",
            }
        )
    return {
        "schema": "twisted-yetter/legacy-prose-archive-manifest/1",
        "archive_id": ARCHIVE_ID,
        "created_at": "2026-07-05T19:45:00Z",
        "archive_path": archive_path(REPO_ROOT).relative_to(REPO_ROOT).as_posix(),
        "manifest_path": MANIFEST_REL_PATH,
        "allowed_prose_paths": sorted(ALLOWED_PROSE_PATHS),
        "prose_suffixes": sorted(PROSE_SUFFIXES),
        "file_count": len(files),
        "files": files,
        "claim_boundary": (
            "This manifest preserves legacy human prose files faithfully by hash "
            "and archive member path. It is not a semantic conversion and does "
            "not promote archived prose to normative experiment history."
        ),
    }


def write_manifest(manifest: dict[str, Any]) -> None:
    ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
    if MANIFEST_PATH.exists():
        raise SystemExit(f"refusing to overwrite existing manifest: {repo_path(REPO_ROOT, MANIFEST_PATH)}")
    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


def write_archive(manifest: dict[str, Any]) -> None:
    ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
    if ARCHIVE_PATH.exists():
        raise SystemExit(f"refusing to overwrite existing archive: {repo_path(REPO_ROOT, ARCHIVE_PATH)}")
    with tarfile.open(ARCHIVE_PATH, "w", format=tarfile.PAX_FORMAT) as archive:
        for item in manifest["files"]:
            rel = item["original_repo_path"]
            data = (REPO_ROOT / rel).read_bytes()
            info = tarfile.TarInfo(item["archive_member_path"])
            info.size = len(data)
            info.mtime = 0
            info.mode = 0o444
            info.uid = 0
            info.gid = 0
            info.uname = ""
            info.gname = ""
            archive.addfile(info, BytesIO(data))


def load_manifest() -> dict[str, Any]:
    if not MANIFEST_PATH.exists():
        raise SystemExit(f"missing archive manifest: {repo_path(REPO_ROOT, MANIFEST_PATH)}")
    manifest = json.loads(MANIFEST_PATH.read_text())
    if manifest.get("schema") != "twisted-yetter/legacy-prose-archive-manifest/1":
        raise SystemExit("bad legacy prose archive manifest schema")
    if manifest.get("archive_id") != ARCHIVE_ID:
        raise SystemExit("legacy prose archive id mismatch")
    if manifest.get("archive_path") != repo_path(REPO_ROOT, ARCHIVE_PATH):
        raise SystemExit("legacy prose archive path mismatch")
    if manifest.get("manifest_path") != repo_path(REPO_ROOT, MANIFEST_PATH):
        raise SystemExit("legacy prose manifest path mismatch")
    return manifest


def verify_archive(manifest: dict[str, Any]) -> None:
    if not ARCHIVE_PATH.exists():
        raise SystemExit(f"missing archive: {repo_path(REPO_ROOT, ARCHIVE_PATH)}")
    expected_archive_sha256 = manifest.get("archive_sha256")
    if expected_archive_sha256 is not None and archive_sha256() != expected_archive_sha256:
        raise SystemExit("archive sha256 mismatch")
    if manifest.get("file_count") != len(manifest.get("files", [])):
        raise SystemExit("manifest file_count does not match files array")
    expected = {item["archive_member_path"]: item for item in manifest["files"]}
    if len(expected) != len(manifest["files"]):
        raise SystemExit("duplicate archive member path in manifest")
    with tarfile.open(ARCHIVE_PATH, "r") as archive:
        members = sorted(
            (member for member in archive.getmembers() if member.isfile()),
            key=lambda member: member.name,
        )
        names = [member.name for member in members]
        if names != sorted(expected):
            raise SystemExit("archive member list does not match manifest")
        for member in members:
            extracted = archive.extractfile(member)
            if extracted is None:
                raise SystemExit(f"could not read archive member: {member.name}")
            data = extracted.read()
            item = expected[member.name]
            if sha256_bytes(data) != item["sha256"]:
                raise SystemExit(f"archive member hash mismatch: {member.name}")
            if len(data) != item["size_bytes"]:
                raise SystemExit(f"archive member size mismatch: {member.name}")


def remove_archived_files(manifest: dict[str, Any]) -> None:
    for item in manifest["files"]:
        path = REPO_ROOT / item["original_repo_path"]
        if not path.exists():
            continue
        if file_sha256(path) != item["sha256"]:
            raise SystemExit(f"refusing to remove changed file: {item['original_repo_path']}")
        path.unlink()

    for directory in sorted((REPO_ROOT / "wiki").glob("**/*"), reverse=True):
        if directory.is_dir() and not any(directory.iterdir()):
            directory.rmdir()
    wiki = REPO_ROOT / "wiki"
    if wiki.exists() and wiki.is_dir() and not any(wiki.iterdir()):
        wiki.rmdir()


def archive_sha256() -> str:
    return file_sha256(ARCHIVE_PATH)


def create_or_load_archive(*, create: bool, allow_empty: bool) -> tuple[dict[str, Any], bool]:
    manifest_exists = MANIFEST_PATH.exists()
    archive_exists = ARCHIVE_PATH.exists()
    if manifest_exists or archive_exists:
        if not manifest_exists or not archive_exists:
            raise SystemExit(
                "refusing to continue with only one legacy archive output present: "
                f"{repo_path(REPO_ROOT, MANIFEST_PATH)} exists={manifest_exists}, "
                f"{repo_path(REPO_ROOT, ARCHIVE_PATH)} exists={archive_exists}"
            )
        manifest = load_manifest()
        verify_archive(manifest)
        return manifest, False

    if not create:
        raise SystemExit("legacy archive outputs are missing; rerun with --create to create them")
    manifest = build_manifest()
    if manifest["file_count"] == 0 and not allow_empty:
        raise SystemExit("refusing to create an empty legacy prose archive without --allow-empty")
    write_archive(manifest)
    manifest["archive_sha256"] = archive_sha256()
    write_manifest(manifest)
    verify_archive(manifest)
    return manifest, True


def main() -> int:
    parser = argparse.ArgumentParser(description="Archive non-whitelisted legacy prose files.")
    parser.add_argument("--create", action="store_true", help="create archive outputs when absent")
    parser.add_argument("--allow-empty", action="store_true", help="allow --create with zero archived files")
    parser.add_argument("--remove-archived-files", action="store_true")
    args = parser.parse_args()

    manifest, created = create_or_load_archive(create=args.create, allow_empty=args.allow_empty)
    if args.remove_archived_files:
        remove_archived_files(manifest)
    print(
        json.dumps(
            {
                "archive": manifest["archive_path"],
                "archive_sha256": manifest["archive_sha256"],
                "created": created,
                "file_count": manifest["file_count"],
                "manifest": manifest["manifest_path"],
                "removed": args.remove_archived_files,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
