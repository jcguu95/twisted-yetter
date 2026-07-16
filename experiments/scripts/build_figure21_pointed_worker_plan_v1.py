#!/usr/bin/env python3
"""Build a fail-closed worker plan for Figure 21 pointed modular chunks."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import subprocess
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
LADDER_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-runtime-ladder-v1.json"
)
PREFIX_SWEEP_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-vs-standard-pointed-modular-sweep-v1.json"
)
CHUNK_ROOT = (
    REPO_ROOT / "experiments/results/akbulut-yasui/figure21-pointed-chunks-v1"
)
PORTABLE_COMMAND_WORK_ROOT = (
    "$PWD/experiments/results/akbulut-yasui/figure21-pointed-chunks-v1"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-worker-plan-v1.json"
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


def _prefix_rows(prefix: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["realization_id"]: row for row in prefix.get("rows", [])}


def _aggregate_status(work_root: Path, realization_id: str) -> dict[str, Any] | None:
    path = work_root / realization_id / "aggregate.json"
    if not path.exists():
        return None
    payload = _load_json(path)
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": _sha256_path(path),
        "status": payload.get("status"),
        "observed_sector_count": payload.get("observed_sector_count"),
        "expected_sector_count": payload.get("expected_sector_count"),
    }


def _chunk_count(
    *,
    estimated_seconds: float,
    target_chunk_seconds: int,
    min_chunks: int,
    worker_count_hint: int,
) -> int:
    raw = max(min_chunks, math.ceil(float(estimated_seconds) / target_chunk_seconds))
    if worker_count_hint > 1:
        raw = math.ceil(raw / worker_count_hint) * worker_count_hint
    return int(raw)


def _smoke_sector_ids(row: dict[str, Any]) -> list[int]:
    ids: list[int] = []
    vacuum_aware = row.get("vacuum_aware_estimate", {})
    for item in vacuum_aware.get("samples", [])[:1]:
        ids.append(int(item["sector_id"]))
    bins = row.get("bins", [])
    found_rank_one = False
    for desired_rank in ("0", "1"):
        for item in bins:
            if str(item.get("projector_rank")) == desired_rank:
                ids.append(int(item["selected_sector_id"]))
                found_rank_one = found_rank_one or desired_rank == "1"
                break
    if not found_rank_one and row.get("full_sector_count"):
        ids.append(0)
    if not ids and row.get("full_sector_count"):
        ids.append(0)
    return sorted(set(ids))


def _runtime_estimate_warnings(row: dict[str, Any]) -> list[str]:
    warnings = []
    vacuum_aware = row.get("vacuum_aware_estimate", {})
    if int(row.get("rank", 0)) == 5 and vacuum_aware.get("status") != (
        "PASS_RANK5_VACUUM_AWARE_TIMING"
    ):
        warnings.append(
            "rank5 vacuum-aware timing is missing; paid-batch cost model is unsafe"
        )
        return warnings
    if int(row.get("rank", 0)) == 5:
        return warnings
    rank_distribution = row.get("projector_rank_distribution_on_samples", {})
    if (
        row.get("status") == "RUNTIME_LADDER_ESTIMATED_FROM_HARD_DECILE_SAMPLES"
        and "1" not in rank_distribution
    ):
        warnings.append(
            "hard-decile samples contain no vacuum-sector timing; worker-hour "
            "estimate may understate full runtime"
        )
    return warnings


def build_plan(
    *,
    target_chunk_seconds: int,
    min_chunks: int,
    worker_count_hint: int,
    work_root: Path,
    command_work_root: str = PORTABLE_COMMAND_WORK_ROOT,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    ladder = _load_json(LADDER_PATH)
    prefix = _load_json(PREFIX_SWEEP_PATH)
    prefix_by_id = _prefix_rows(prefix)
    rows = []
    ready_count = 0
    blocked_count = 0
    skipped_count = 0
    mean_worker_seconds = 0.0
    max_worker_seconds = 0.0

    for row in ladder["rows"]:
        realization_id = row["realization_id"]
        prefix_row = prefix_by_id.get(realization_id, {})
        figure21 = prefix_row.get("figure21_right", {})
        modular = figure21.get("modular_cross_check", {})
        aggregate = _aggregate_status(work_root, realization_id)
        command_base = (
            "UV_CACHE_DIR=/tmp/uv-cache PYTHONPATH=. uv run python "
            "experiments/scripts/run_figure21_pointed_category_chunks_v1.py "
            f"--realization-id {realization_id}"
        )
        common = {
            "realization_id": realization_id,
            "family_id": row["family_id"],
            "rank": row["rank"],
            "full_sector_count": row["full_sector_count"],
            "prefix_figure21_status": figure21.get("status"),
            "prefix_modular_cross_check_status": modular.get("status"),
            "existing_aggregate": aggregate,
        }
        if aggregate and aggregate["status"] == "PASS_AGGREGATE_COMPLETE":
            skipped_count += 1
            rows.append(
                {
                    **common,
                    "worker_plan_status": "SKIP_ALREADY_AGGREGATED_COMPLETE",
                    "reason": "Complete chunk aggregate already exists locally.",
                }
            )
            continue
        if figure21.get("status") == "FULL":
            skipped_count += 1
            rows.append(
                {
                    **common,
                    "worker_plan_status": "SKIP_ALREADY_COMPLETE_IN_PREFIX_SWEEP",
                    "reason": "Full sector space already completed by prefix sweep artifact.",
                }
            )
            continue
        if modular.get("status") != "PASS":
            blocked_count += 1
            rows.append(
                {
                    **common,
                    "worker_plan_status": "BLOCKED_PREFIX_MODULAR_CROSS_CHECK_NOT_PASS",
                    "reason": "Do not spend worker time before modular-vs-pointed prefix check passes.",
                }
            )
            continue
        if row.get("status") != "RUNTIME_LADDER_ESTIMATED_FROM_HARD_DECILE_SAMPLES":
            blocked_count += 1
            rows.append(
                {
                    **common,
                    "worker_plan_status": "BLOCKED_NO_RUNTIME_LADDER_ESTIMATE",
                    "runtime_ladder_status": row.get("status"),
                    "reason": "No hard-decile timing estimate exists for this row.",
                }
            )
            continue
        warnings = _runtime_estimate_warnings(row)
        if any("rank5 vacuum-aware timing is missing" in item for item in warnings):
            blocked_count += 1
            rows.append(
                {
                    **common,
                    "worker_plan_status": (
                        "TERMINAL_BLOCKED_RANK5_COST_MODEL_UNSAFE_FOR_PAID_BATCH"
                    ),
                    "runtime_estimate_warnings": warnings,
                    "runtime_ladder_status": row.get("status"),
                    "reason": (
                        "Rank-5 paid-batch planning requires explicit "
                        "projector-rank-1/vacuum-sector timing."
                    ),
                }
            )
            continue
        if int(row.get("rank", 0)) == 5:
            max_seconds = row.get(
                "estimated_total_seconds_vacuum_aware_max_observed_classes"
            )
            mean_seconds = row.get("estimated_total_seconds_vacuum_aware_mean")
            runtime_cost_model = "VACUUM_AWARE_RANK5_WEIGHTED_ESTIMATE"
        else:
            max_seconds = row.get("estimated_total_seconds_max_hard_samples")
            mean_seconds = row.get("estimated_total_seconds_mean_hard_samples")
            runtime_cost_model = "HARD_DECILE_SAMPLE_ESTIMATE"
        if not max_seconds or not mean_seconds:
            blocked_count += 1
            rows.append(
                {
                    **common,
                    "worker_plan_status": "BLOCKED_MISSING_RUNTIME_SECONDS",
                    "reason": "Runtime ladder row is missing mean/max worker seconds.",
                }
            )
            continue
        chunks = _chunk_count(
            estimated_seconds=float(max_seconds),
            target_chunk_seconds=target_chunk_seconds,
            min_chunks=min_chunks,
            worker_count_hint=worker_count_hint,
        )
        ready_count += 1
        mean_worker_seconds += float(mean_seconds)
        max_worker_seconds += float(max_seconds)
        rows.append(
            {
                **common,
                "worker_plan_status": "READY_FOR_WORKERS",
                "chunk_count": chunks,
                "target_chunk_seconds": target_chunk_seconds,
                "estimated_worker_seconds_mean_hard_samples": mean_seconds,
                "estimated_worker_seconds_max_hard_samples": max_seconds,
                "estimated_worker_hours_mean_hard_samples": float(mean_seconds)
                / 3600.0,
                "estimated_worker_hours_max_hard_samples": float(max_seconds)
                / 3600.0,
                "runtime_cost_model": runtime_cost_model,
                "runtime_estimate_warnings": warnings,
                "vacuum_aware_estimate": row.get("vacuum_aware_estimate"),
                "worker_command_template": (
                    f"{command_base} --chunk-count {chunks} "
                    "--worker-index {worker_index} --worker-count {worker_count} "
                    f"--work-root {command_work_root} --no-aggregate"
                ),
                "single_chunk_command_template": (
                    f"{command_base} --chunk-count {chunks} "
                    "--chunk-id {chunk_id} "
                    f"--work-root {command_work_root} --no-aggregate"
                ),
                "aggregate_command": (
                    f"{command_base} --chunk-count {chunks} "
                    f"--aggregate-only --work-root {command_work_root}"
                ),
                "smoke_sector_ids": _smoke_sector_ids(row),
                "smoke_command_template": (
                    f"{command_base} --chunk-count {row['full_sector_count']} "
                    "--chunk-id {sector_id} --work-root {smoke_work_root} "
                    "--no-aggregate"
                ),
            }
        )

    finished = datetime.now(UTC)
    terminal_rank5_cost_blocked = any(
        row.get("worker_plan_status")
        == "TERMINAL_BLOCKED_RANK5_COST_MODEL_UNSAFE_FOR_PAID_BATCH"
        for row in rows
    )
    paid_batch_preflight_status = (
        "TERMINAL_BLOCKED_RANK5_COST_MODEL_UNSAFE_FOR_PAID_BATCH"
        if terminal_rank5_cost_blocked
        else (
            "PASS_PAID_BATCH_PREFLIGHT"
            if blocked_count == 0
            else "BLOCKED_WORKER_PLAN_HAS_UNRUNNABLE_ROWS"
        )
    )
    payload = {
        "schema": "twisted-yetter.figure21-pointed-worker-plan.v1",
        "status": (
            "PASS_WORKER_PLAN_READY"
            if paid_batch_preflight_status == "PASS_PAID_BATCH_PREFLIGHT"
            else paid_batch_preflight_status
        ),
        "paid_batch_preflight_status": paid_batch_preflight_status,
        "mathematical_status": "RUNTIME_WORKER_PLAN_NOT_SCAN_RESULT",
        "generator_script": "experiments/scripts/build_figure21_pointed_worker_plan_v1.py",
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "runtime_ladder": str(LADDER_PATH.relative_to(REPO_ROOT)),
            "runtime_ladder_sha256": _sha256_path(LADDER_PATH),
            "prefix_sweep": str(PREFIX_SWEEP_PATH.relative_to(REPO_ROOT)),
            "prefix_sweep_sha256": _sha256_path(PREFIX_SWEEP_PATH),
        },
        "parameters": {
            "target_chunk_seconds": target_chunk_seconds,
            "min_chunks": min_chunks,
            "worker_count_hint": worker_count_hint,
            "work_root": str(work_root),
            "command_work_root": command_work_root,
            "logical_worker_shards": 16,
        },
        "row_count": len(rows),
        "ready_count": ready_count,
        "blocked_count": blocked_count,
        "skipped_count": skipped_count,
        "estimated_ready_worker_hours_mean_hard_samples": mean_worker_seconds
        / 3600.0,
        "estimated_ready_worker_hours_max_hard_samples": max_worker_seconds / 3600.0,
        "runbook": {
            "logical_worker_shards": 16,
            "remote_work_root": PORTABLE_COMMAND_WORK_ROOT,
            "execution_rule": (
                "For each READY_FOR_WORKERS row, run worker_command_template with "
                "worker_index = 0..15 and worker_count = 16, then run "
                "aggregate_command after all chunks are synced."
            ),
            "remote_capacity_policy": (
                "If no host list or remote capacity is provided, the terminal "
                "batch result must be TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED."
            ),
        },
        "rows": rows,
        "claim_boundary": (
            "This only prepares Figure 21 pointed modular category worker chunks. "
            "It is not a scan aggregate and not an exoticness comparison."
        ),
        "non_claims": [
            "Does not cover nonpointed low-rank categories.",
            "Does not compare Figure 21 against the standard side by H2 coordinates.",
            "Does not claim no signal.",
            "Does not prove runtime estimates are upper bounds.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--target-chunk-seconds", type=int, default=300)
    parser.add_argument("--min-chunks", type=int, default=32)
    parser.add_argument("--worker-count-hint", type=int, default=16)
    parser.add_argument("--work-root", type=Path, default=CHUNK_ROOT)
    parser.add_argument("--command-work-root", default=PORTABLE_COMMAND_WORK_ROOT)
    args = parser.parse_args()
    result = build_plan(
        target_chunk_seconds=args.target_chunk_seconds,
        min_chunks=args.min_chunks,
        worker_count_hint=args.worker_count_hint,
        work_root=args.work_root,
        command_work_root=args.command_work_root,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
