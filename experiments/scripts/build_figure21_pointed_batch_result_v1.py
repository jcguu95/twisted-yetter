#!/usr/bin/env python3
"""Build the terminal result for the Figure 21 pointed modular batch."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-worker-plan-v1.json"
)
WORKER_SMOKE_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-worker-smoke-v1.json"
)
PREHETZNER_SMOKE_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-prehetzner-smoke-v1.json"
)
PREFIX_SWEEP_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-vs-standard-pointed-modular-sweep-v1.json"
)
CHUNK_ROOT = (
    REPO_ROOT / "experiments/results/akbulut-yasui/figure21-pointed-chunks-v1"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-batch-result-v1.json"
)


def _git(*args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        if args == ("rev-parse", "HEAD"):
            return os.environ.get("TWISTED_YETTER_GIT_COMMIT", "REMOTE_GIT_UNAVAILABLE")
        if args == ("status", "--porcelain"):
            return os.environ.get("TWISTED_YETTER_GIT_DIRTY", "REMOTE_GIT_UNAVAILABLE")
        raise


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def _sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def _content_hash(payload: Any) -> str:
    data = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(data).hexdigest()}"


def _rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _artifact_ref(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "path": _rel(path),
        "sha256": _sha256_path(path),
        "content_hash": payload.get("content_hash") or payload.get("content_sha256"),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def _prefix_rows(prefix: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["realization_id"]: row for row in prefix.get("rows", [])}


def _aggregate_path(work_root: Path, realization_id: str) -> Path:
    return work_root / realization_id / "aggregate.json"


def _validate_aggregate(
    *,
    row: dict[str, Any],
    work_root: Path,
) -> dict[str, Any]:
    path = _aggregate_path(work_root, row["realization_id"])
    if not path.exists():
        return {
            "row_status": "TERMINAL_BLOCKED_MISSING_CHUNKS",
            "aggregate_path": _rel(path),
            "reason": "No complete aggregate exists for this ready worker row.",
        }
    aggregate = _load_json(path)
    chunk_hashes = aggregate.get("chunk_hashes", [])
    duplicate_hash_count = len(chunk_hashes) - len(set(chunk_hashes))
    if duplicate_hash_count:
        return {
            "row_status": "TERMINAL_BLOCKED_STALE_CHUNK",
            "aggregate_path": _rel(path),
            "aggregate_sha256": _sha256_path(path),
            "reason": "Aggregate contains duplicate chunk hashes.",
            "duplicate_chunk_hash_count": duplicate_hash_count,
        }
    checks = {
        "status_pass": aggregate.get("status") == "PASS_AGGREGATE_COMPLETE",
        "expected_matches_row": aggregate.get("expected_sector_count")
        == row.get("full_sector_count"),
        "observed_matches_expected": aggregate.get("observed_sector_count")
        == aggregate.get("expected_sector_count"),
        "chunk_count_matches_plan": aggregate.get("chunk_count")
        == row.get("chunk_count"),
        "chunk_hash_count_matches_plan": len(chunk_hashes) == row.get("chunk_count"),
    }
    if not all(checks.values()):
        failed = [name for name, passed in checks.items() if not passed]
        return {
            "row_status": "TERMINAL_BLOCKED_STALE_CHUNK",
            "aggregate_path": _rel(path),
            "aggregate_sha256": _sha256_path(path),
            "checks": checks,
            "failed_checks": failed,
            "reason": "Aggregate exists but is not bound to the expected worker plan.",
        }
    return {
        "row_status": "COMPLETE_FROM_WORKER_AGGREGATE",
        "aggregate_path": _rel(path),
        "aggregate_sha256": _sha256_path(path),
        "observed_sector_count": aggregate["observed_sector_count"],
        "expected_sector_count": aggregate["expected_sector_count"],
        "chunk_count": aggregate["chunk_count"],
        "elapsed_worker_seconds": aggregate.get("elapsed_worker_seconds"),
        "value_distribution": aggregate.get("value_distribution"),
        "projector_rank_distribution": aggregate.get("projector_rank_distribution"),
    }


def _validate_prefix_complete(
    *,
    row: dict[str, Any],
    prefix_by_id: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    prefix_row = prefix_by_id.get(row["realization_id"], {})
    figure21 = prefix_row.get("figure21_right", {})
    checks = {
        "status_full": figure21.get("status") == "FULL",
        "sector_count_matches_full": figure21.get("sector_count")
        == figure21.get("full_sector_count"),
        "full_sector_count_matches_plan": figure21.get("full_sector_count")
        == row.get("full_sector_count"),
    }
    if all(checks.values()):
        return {
            "row_status": "COMPLETE_FROM_PREFIX_SWEEP",
            "prefix_sweep_status": figure21.get("status"),
            "sector_count": figure21.get("sector_count"),
            "full_sector_count": figure21.get("full_sector_count"),
        }
    return {
        "row_status": "TERMINAL_BLOCKED_STALE_CHUNK",
        "checks": checks,
        "failed_checks": [name for name, passed in checks.items() if not passed],
        "reason": "Prefix sweep no longer certifies this rank-2 row as full.",
    }


def _validate_existing_aggregate(row: dict[str, Any]) -> dict[str, Any]:
    aggregate_ref = row.get("existing_aggregate") or {}
    path_text = aggregate_ref.get("path")
    if not path_text:
        return {
            "row_status": "TERMINAL_BLOCKED_MISSING_CHUNKS",
            "reason": "Worker plan says aggregate exists, but no path is pinned.",
        }
    path = REPO_ROOT / path_text
    if not path.exists():
        return {
            "row_status": "TERMINAL_BLOCKED_MISSING_CHUNKS",
            "aggregate_path": path_text,
            "reason": "Pinned existing aggregate path is missing.",
        }
    aggregate = _load_json(path)
    checks = {
        "status_pass": aggregate.get("status") == "PASS_AGGREGATE_COMPLETE",
        "expected_matches_row": aggregate.get("expected_sector_count")
        == row.get("full_sector_count"),
        "observed_matches_expected": aggregate.get("observed_sector_count")
        == aggregate.get("expected_sector_count"),
    }
    if all(checks.values()):
        return {
            "row_status": "COMPLETE_FROM_EXISTING_AGGREGATE",
            "aggregate_path": path_text,
            "aggregate_sha256": _sha256_path(path),
            "observed_sector_count": aggregate["observed_sector_count"],
            "expected_sector_count": aggregate["expected_sector_count"],
            "chunk_count": aggregate.get("chunk_count"),
            "elapsed_worker_seconds": aggregate.get("elapsed_worker_seconds"),
            "value_distribution": aggregate.get("value_distribution"),
            "projector_rank_distribution": aggregate.get("projector_rank_distribution"),
        }
    return {
        "row_status": "TERMINAL_BLOCKED_STALE_CHUNK",
        "aggregate_path": path_text,
        "aggregate_sha256": _sha256_path(path),
        "checks": checks,
        "failed_checks": [name for name, passed in checks.items() if not passed],
        "reason": "Pinned existing aggregate is not complete for this row.",
    }


def build_result(
    *,
    plan_path: Path,
    worker_smoke_path: Path,
    prehetzner_smoke_path: Path,
    prefix_sweep_path: Path,
    work_root: Path,
    remote_capacity_provided: bool,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    plan = _load_json(plan_path)
    worker_smoke = _load_json(worker_smoke_path)
    prehetzner_smoke = _load_json(prehetzner_smoke_path)
    prefix = _load_json(prefix_sweep_path)
    prefix_by_id = _prefix_rows(prefix)
    rows = []
    blockers = []

    local_smoke_checks = {
        "paid_batch_preflight_pass": plan.get("paid_batch_preflight_status")
        == "PASS_PAID_BATCH_PREFLIGHT",
        "worker_smoke_pass": worker_smoke.get("status") == "PASS_WORKER_SMOKE",
        "prehetzner_smoke_pass": prehetzner_smoke.get("status")
        == "PASS_PREHETZNER_SMOKE",
        "prehetzner_smoked_all_ready_rows": prehetzner_smoke.get(
            "ready_row_count_smoked"
        )
        == plan.get("ready_count"),
    }
    preflight_pass = all(local_smoke_checks.values())
    for row in plan.get("rows", []):
        status = row.get("worker_plan_status")
        common = {
            "realization_id": row["realization_id"],
            "family_id": row["family_id"],
            "rank": row["rank"],
            "worker_plan_status": status,
            "full_sector_count": row["full_sector_count"],
        }
        if status == "SKIP_ALREADY_COMPLETE_IN_PREFIX_SWEEP":
            result = _validate_prefix_complete(row=row, prefix_by_id=prefix_by_id)
        elif status == "SKIP_ALREADY_AGGREGATED_COMPLETE":
            result = _validate_existing_aggregate(row)
        elif status == "READY_FOR_WORKERS":
            if not preflight_pass:
                result = {
                    "row_status": "TERMINAL_BLOCKED_WORKER_FAILURE",
                    "reason": "Worker plan preflight is not pass.",
                    "paid_batch_preflight_status": plan.get(
                        "paid_batch_preflight_status"
                    ),
                }
            elif not remote_capacity_provided:
                result = {
                    "row_status": "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED",
                    "chunk_count": row.get("chunk_count"),
                    "logical_worker_shards": 16,
                    "reason": (
                        "No Hetzner/remote host list was provided for this paid "
                        "batch, so ready rows are terminally blocked at execution."
                    ),
                }
            else:
                result = _validate_aggregate(row=row, work_root=work_root)
        else:
            result = {
                "row_status": row.get(
                    "worker_plan_status", "TERMINAL_BLOCKED_WORKER_FAILURE"
                ),
                "reason": row.get("reason", "Worker plan row is not runnable."),
            }
        terminal = {**common, **result}
        rows.append(terminal)
        if not terminal["row_status"].startswith("COMPLETE_FROM_"):
            blockers.append(
                {
                    "realization_id": terminal["realization_id"],
                    "family_id": terminal["family_id"],
                    "row_status": terminal["row_status"],
                    "reason": terminal.get("reason"),
                }
            )

    complete = not blockers
    remote_blocked = any(
        blocker["row_status"] == "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED"
        for blocker in blockers
    )
    if complete:
        status = "PASS_POINTED_FIGURE21_BATCH_COMPLETE"
    elif remote_blocked:
        status = "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED"
    else:
        status = "TERMINAL_BLOCKED_POINTED_BATCH_INCOMPLETE"

    finished = datetime.now(UTC)
    payload = {
        "schema": "twisted-yetter.figure21-pointed-batch-result.v1",
        "status": status,
        "mathematical_status": "POINTED_FIGURE21_BATCH_TERMINAL_NOT_EXOTICNESS_CLAIM",
        "generator_script": "experiments/scripts/build_figure21_pointed_batch_result_v1.py",
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "worker_plan": _artifact_ref(plan_path, plan),
            "worker_smoke": _artifact_ref(worker_smoke_path, worker_smoke),
            "prehetzner_smoke": _artifact_ref(
                prehetzner_smoke_path, prehetzner_smoke
            ),
            "prefix_sweep": _rel(prefix_sweep_path),
            "prefix_sweep_sha256": _sha256_path(prefix_sweep_path),
        },
        "parameters": {
            "work_root": _rel(work_root),
            "remote_capacity_provided": remote_capacity_provided,
            "logical_worker_shards": 16,
        },
        "prelaunch_check_status": (
            "PASS_PRELAUNCH_LOCAL_SMOKE"
            if preflight_pass
            else "TERMINAL_BLOCKED_LOCAL_SMOKE_FAILED"
        ),
        "local_smoke_checks": local_smoke_checks,
        "row_count": len(rows),
        "complete_row_count": len(rows) - len(blockers),
        "blocked_row_count": len(blockers),
        "blockers": blockers,
        "rows": rows,
        "claim_boundary": (
            "Terminal status for the Figure 21 pointed modular fixed-label "
            "distribution batch only."
        ),
        "non_claims": [
            "Does not cover nonpointed low-rank categories.",
            "Does not cover trivial-universal-group rows for nontrivial-character scans.",
            "Does not compare Figure 21 to the standard side by H2 coordinates.",
            "Does not claim Figure 21 is exotic or standard.",
            "Does not claim no signal for all low-rank MTCs.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path, default=PLAN_PATH)
    parser.add_argument("--worker-smoke", type=Path, default=WORKER_SMOKE_PATH)
    parser.add_argument("--prehetzner-smoke", type=Path, default=PREHETZNER_SMOKE_PATH)
    parser.add_argument("--prefix-sweep", type=Path, default=PREFIX_SWEEP_PATH)
    parser.add_argument("--work-root", type=Path, default=CHUNK_ROOT)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--remote-capacity-provided", action="store_true")
    args = parser.parse_args()
    result = build_result(
        plan_path=args.plan,
        worker_smoke_path=args.worker_smoke,
        prehetzner_smoke_path=args.prehetzner_smoke,
        prefix_sweep_path=args.prefix_sweep,
        work_root=args.work_root,
        remote_capacity_provided=args.remote_capacity_provided,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
