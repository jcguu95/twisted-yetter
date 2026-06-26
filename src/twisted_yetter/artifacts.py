"""JSON certificate helpers for reproducible experiment artifacts.

This module defines the metadata envelope used by generated certificates.  It
does not evaluate twisted Yetter formulas; it only validates that future
computations record enough provenance to be audited.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any, Literal


ARTIFACT_SCHEMA = "twisted-yetter.certificate.v1"
ARTIFACT_STATUSES = frozenset({"pass", "fail", "inconclusive"})

ArtifactStatus = Literal["pass", "fail", "inconclusive"]
JsonObject = dict[str, Any]


class ArtifactValidationError(ValueError):
    """Raised when an artifact certificate is missing required audit fields."""


@dataclass(frozen=True)
class LogReference:
    """Reference to a large log stored outside the JSON certificate."""

    path: str
    sha256: str
    bytes: int
    description: str | None = None

    def to_json(self) -> JsonObject:
        payload: JsonObject = {
            "path": self.path,
            "sha256": self.sha256,
            "bytes": self.bytes,
        }
        if self.description is not None:
            payload["description"] = self.description
        return payload


def utc_now_iso() -> str:
    """Return a UTC timestamp in the certificate format."""

    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def hash_bytes(data: bytes) -> str:
    """Return a sha256 digest for exact input/output payloads."""

    return hashlib.sha256(data).hexdigest()


def hash_json(value: Any) -> str:
    """Hash a JSON-compatible value using canonical key ordering."""

    return hash_bytes(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def file_sha256(path: str | Path) -> str:
    """Return the sha256 digest of a file without loading it all into memory."""

    digest = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_metadata(repo_root: str | Path = ".") -> JsonObject:
    """Collect git commit and dirty flag for artifact provenance."""

    root = Path(repo_root)
    commit = _run_git(root, "rev-parse", "HEAD")
    status = _run_git(root, "status", "--porcelain")
    return {
        "commit": commit,
        "dirty": bool(status),
    }


def default_tool_versions() -> JsonObject:
    """Return the minimal tool version record available from this process."""

    return {
        "python": sys.version.split()[0],
    }


def make_certificate(
    *,
    status: ArtifactStatus,
    command: str,
    argv: list[str],
    git: JsonObject,
    tool_versions: JsonObject,
    input_hash: str,
    exact_output: Any,
    generator_script: str | None = None,
    reproduce_command: str | None = None,
    started_at_utc: str | None = None,
    finished_at_utc: str | None = None,
    elapsed_seconds: int | float | None = None,
    repo_root: str | None = None,
    log_references: list[LogReference | JsonObject] | None = None,
    notes: list[str] | None = None,
) -> JsonObject:
    """Build and validate a certificate JSON object."""

    payload: JsonObject = {
        "schema": ARTIFACT_SCHEMA,
        "status": status,
        "command": command,
        "argv": list(argv),
        "git": dict(git),
        "tool_versions": dict(tool_versions),
        "input_hash": input_hash,
        "exact_output": exact_output,
        "log_references": [
            item.to_json() if isinstance(item, LogReference) else dict(item)
            for item in (log_references or [])
        ],
    }
    optional_fields: JsonObject = {
        "generator_script": generator_script,
        "reproduce_command": reproduce_command,
        "started_at_utc": started_at_utc,
        "finished_at_utc": finished_at_utc,
        "elapsed_seconds": elapsed_seconds,
        "repo_root": repo_root,
        "notes": notes,
    }
    payload.update({key: value for key, value in optional_fields.items() if value is not None})
    validate_certificate(payload)
    return payload


def validate_certificate(payload: JsonObject) -> None:
    """Validate the minimal v1 certificate schema.

    The function intentionally checks only structural audit requirements.  It
    leaves domain-specific checks, such as Kirby matrix sanity tests, to later
    nodes.
    """

    required = {
        "schema",
        "status",
        "command",
        "argv",
        "git",
        "tool_versions",
        "input_hash",
        "exact_output",
        "log_references",
    }
    missing = sorted(required.difference(payload))
    if missing:
        raise ArtifactValidationError(f"missing required fields: {', '.join(missing)}")

    if payload["schema"] != ARTIFACT_SCHEMA:
        raise ArtifactValidationError(f"unsupported schema: {payload['schema']!r}")
    if payload["status"] not in ARTIFACT_STATUSES:
        raise ArtifactValidationError(f"unsupported status: {payload['status']!r}")
    if not isinstance(payload["command"], str) or not payload["command"]:
        raise ArtifactValidationError("command must be a non-empty string")
    if not _is_list_of_strings(payload["argv"]):
        raise ArtifactValidationError("argv must be a list of strings")
    if not isinstance(payload["tool_versions"], dict) or not payload["tool_versions"]:
        raise ArtifactValidationError("tool_versions must be a non-empty object")
    if not isinstance(payload["input_hash"], str) or not payload["input_hash"]:
        raise ArtifactValidationError("input_hash must be a non-empty string")
    if not isinstance(payload["log_references"], list):
        raise ArtifactValidationError("log_references must be a list")

    _validate_git(payload["git"])
    _validate_log_references(payload["log_references"])
    _validate_no_float(payload["exact_output"], "exact_output")
    _validate_json_compatible(payload)


def dumps_certificate(payload: JsonObject) -> str:
    """Serialize a validated certificate as stable, human-readable JSON."""

    validate_certificate(payload)
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def _run_git(repo_root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _validate_git(git: Any) -> None:
    if not isinstance(git, dict):
        raise ArtifactValidationError("git must be an object")
    if not isinstance(git.get("commit"), str) or not git["commit"]:
        raise ArtifactValidationError("git.commit must be a non-empty string")
    if not isinstance(git.get("dirty"), bool):
        raise ArtifactValidationError("git.dirty must be a boolean")


def _validate_log_references(log_references: list[Any]) -> None:
    for index, item in enumerate(log_references):
        if not isinstance(item, dict):
            raise ArtifactValidationError(f"log_references[{index}] must be an object")
        for field in ("path", "sha256", "bytes"):
            if field not in item:
                raise ArtifactValidationError(f"log_references[{index}] missing {field}")
        if not isinstance(item["path"], str) or not item["path"]:
            raise ArtifactValidationError(f"log_references[{index}].path must be non-empty")
        if not isinstance(item["sha256"], str) or not item["sha256"]:
            raise ArtifactValidationError(f"log_references[{index}].sha256 must be non-empty")
        if not isinstance(item["bytes"], int) or item["bytes"] < 0:
            raise ArtifactValidationError(f"log_references[{index}].bytes must be non-negative")


def _validate_json_compatible(value: Any) -> None:
    try:
        json.dumps(value, sort_keys=True)
    except (TypeError, ValueError) as error:
        raise ArtifactValidationError("certificate must be JSON serializable") from error


def _validate_no_float(value: Any, path: str) -> None:
    if isinstance(value, float):
        raise ArtifactValidationError(f"{path} must use exact JSON values, not floats")
    if isinstance(value, dict):
        for key, item in value.items():
            _validate_no_float(item, f"{path}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _validate_no_float(item, f"{path}[{index}]")


def _is_list_of_strings(value: Any) -> bool:
    return isinstance(value, list) and all(isinstance(item, str) for item in value)
