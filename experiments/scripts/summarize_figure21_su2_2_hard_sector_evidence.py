#!/usr/bin/env python3
"""Summarize the preserved Figure 21 SU(2)_2 hard-sector runtime evidence."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import platform
import socket
import subprocess
import sys
import tarfile
import time


REPO = Path(__file__).resolve().parents[2]
EVIDENCE_ROOT = REPO / "experiments/results/akbulut-yasui/evidence"
FRONTIER_ARCHIVE = EVIDENCE_ROOT / "figure21-su22-frontier16-hetzner-evidence-v1.tar.gz"
PATH_ARCHIVE = EVIDENCE_ROOT / "figure21-su22-sector95378-path128-calibration-evidence-v1.tar.gz"
CODE_SNAPSHOT = EVIDENCE_ROOT / "twisted-yetter-su2-2-direct-snapshot-v1.tar.gz"
COMPLEXITY_CERTIFICATE = (
    REPO
    / "experiments/results/akbulut-yasui"
    / "figure21-right-su2-2-sector95378-complexity-certificate-v1.json"
)
DEFAULT_OUTPUT = (
    REPO
    / "experiments/results/akbulut-yasui"
    / "figure21-right-su2-2-sector95378-runtime-barrier-v1.json"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(*args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=REPO,
        check=check,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _head_blob(relative: str) -> str | None:
    value = _git("rev-parse", f"HEAD:{relative}", check=False)
    return value or None


def _record(path: Path) -> dict:
    relative = str(path.relative_to(REPO))
    working_blob = _git("hash-object", relative)
    head_blob = _head_blob(relative)
    return {
        "path": relative,
        "bytes": path.stat().st_size,
        "sha256": _sha256(path),
        "git_blob": working_blob,
        "head_git_blob": head_blob,
        "matches_head": head_blob == working_blob,
    }


def _json_members(archive: Path) -> dict[str, dict]:
    result = {}
    with tarfile.open(archive, "r:gz") as handle:
        for member in handle.getmembers():
            if not member.isfile() or not member.name.endswith(".json"):
                continue
            stream = handle.extractfile(member)
            if stream is None:
                raise ValueError(f"could not read tar member {member.name!r}")
            result[member.name] = json.loads(stream.read())
    return result


def build_summary() -> dict:
    started = datetime.now(UTC)
    start_clock = time.monotonic()
    frontier = _json_members(FRONTIER_ARCHIVE)
    path_calibration = _json_members(PATH_ARCHIVE)
    frontier_sectors = [
        payload
        for name, payload in frontier.items()
        if "/sector-" in name
    ]
    environments = [
        payload
        for name, payload in frontier.items()
        if name.endswith("hetzner-environment-v1.json")
    ]
    calibration_summaries = [
        payload
        for name, payload in path_calibration.items()
        if name.endswith("path128-calibration-summary-v1.json")
    ]
    if len(frontier_sectors) != 16:
        raise AssertionError(f"expected 16 frontier sector records, found {len(frontier_sectors)}")
    if len(environments) != 1 or len(calibration_summaries) != 1:
        raise AssertionError("evidence archives have unexpected summary cardinality")
    environment = environments[0]
    calibration = calibration_summaries[0]
    frontier_status_counts = Counter(
        record["status"] for record in frontier_sectors
    )
    if frontier_status_counts != {"PASS": 3, "TIMEOUT": 13}:
        raise AssertionError(
            f"unexpected frontier status counts: {frontier_status_counts!r}"
        )
    if calibration["status_counts"] != {"TIMEOUT": 16}:
        raise AssertionError("path calibration no longer records 16 timeouts")
    if environment["snapshot_sha256"] != _sha256(CODE_SNAPSHOT):
        raise AssertionError("preserved code snapshot does not match remote environment")

    hard_sector = next(
        record for record in frontier_sectors if record["sector_id"] == 95_378
    )
    complexity = json.loads(COMPLEXITY_CERTIFICATE.read_text())
    if complexity["sector"]["sector_id"] != hard_sector["sector_id"]:
        raise AssertionError("complexity and runtime evidence refer to different sectors")
    if complexity["projector_slice"]["projector_vacuum_rank"] != hard_sector["projector_rank"]:
        raise AssertionError("complexity and runtime projector ranks disagree")

    inputs = [FRONTIER_ARCHIVE, PATH_ARCHIVE, CODE_SNAPSHOT]
    finished = datetime.now(UTC)
    return {
        "schema": "twisted-yetter.figure21-su2-2-hard-sector-runtime-barrier.v1",
        "status": "ESTABLISHED_CURRENT_BACKEND_RUNTIME_BARRIER",
        "mathematical_status": "PERFORMANCE_EVIDENCE_NOT_A_COMPLEXITY_THEOREM",
        "scope_warning": (
            "The evidence rules out the preserved full-state/path-sharded backend "
            "as a practical route for this sector. It does not rule out future "
            "tensor-network, recoupling, compiled, or Kirby-calculus algorithms."
        ),
        "generator_script": (
            "experiments/scripts/"
            "summarize_figure21_su2_2_hard_sector_evidence.py"
        ),
        "argv": list(sys.argv),
        "reproduce_command": (
            "PYTHONPATH=. uv run python experiments/scripts/"
            "summarize_figure21_su2_2_hard_sector_evidence.py --write"
        ),
        "utc_start": started.isoformat(),
        "utc_finish": finished.isoformat(),
        "elapsed_seconds": time.monotonic() - start_clock,
        "repo_root": str(REPO),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "environment": {
            "hostname": socket.gethostname(),
            "platform": platform.platform(),
            "python": sys.version,
        },
        "presentation_subject": (
            "subject:twisted-yetter:presentation:"
            "akbulut-yasui-2008-figure21-e3prime"
        ),
        "category_subject": "subject:twisted-yetter:category-family:su2-k",
        "category_id": "su2-k2",
        "sector_id": 95_378,
        "projector_rank": hard_sector["projector_rank"],
        "complexity_certificate": {
            "path": str(COMPLEXITY_CERTIFICATE.relative_to(REPO)),
            "sha256": _sha256(COMPLEXITY_CERTIFICATE),
            "active_vacuum_fusion_dimension": complexity["projector_slice"][
                "active_vacuum_fusion_dimension"
            ],
        },
        "frontier_probe": {
            "host": environment["host"],
            "cpu_count": 16,
            "memory_summary": environment["memory"],
            "sector_count": len(frontier_sectors),
            "status_counts": dict(sorted(frontier_status_counts.items())),
            "timeout_seconds": hard_sector["max_seconds"],
            "minimum_elapsed_seconds": min(
                record["elapsed_seconds"] for record in frontier_sectors
            ),
            "maximum_elapsed_seconds": max(
                record["elapsed_seconds"] for record in frontier_sectors
            ),
            "hard_sector_record": hard_sector,
        },
        "path_shard_calibration": {
            "projector_path_count": calibration["projector_rank"],
            "shard_count": 128,
            "paths_per_shard": calibration["paths_per_shard"],
            "sampled_shard_count": calibration["sampled_shard_count"],
            "status_counts": calibration["status_counts"],
            "recorded_worker_seconds": calibration["worker_seconds_recorded"],
            "minimum_total_worker_hours": calibration[
                "minimum_total_worker_hours_from_128_shards"
            ],
            "minimum_ideal_wall_hours_at_16_workers": calibration[
                "minimum_ideal_wall_hours_at_16_workers"
            ],
            "historical_evaluation_run_identity": calibration[
                "evaluation_run_identity"
            ],
            "historical_decision": calibration["decision"],
        },
        "historical_code_snapshot": {
            "path": str(CODE_SNAPSHOT.relative_to(REPO)),
            "sha256": _sha256(CODE_SNAPSHOT),
            "matches_remote_environment": True,
        },
        "evidence_files": [_record(path) for path in inputs],
        "sanity_checks": {
            "frontier_status_is_3_pass_13_timeout": True,
            "all_16_sampled_path_shards_timed_out": True,
            "hard_sector_projector_rank_matches_exact_certificate": True,
            "code_snapshot_hash_matches_remote_environment": True,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = build_summary()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(rendered)
        temporary.replace(args.output)
        print(args.output)
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
