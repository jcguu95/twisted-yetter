#!/usr/bin/env python3
"""Pre-Hetzner smoke checks for the Figure 21 pointed worker batch."""

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

from experiments.sage.pointed_premodular_categories import (
    SnapshotPointedModularCategory,
)
from experiments.sage.ribbon_graph_evaluator import PointedVacuumProjectorEvaluator
from experiments.scripts.run_figure21_pointed_category_chunks_v1 import (
    _chunk_bounds,
    _find_snapshot,
)
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    _complex_key,
    _labels_from_id,
    _load_figure21,
)
from experiments.scripts.special_dotted_morphism import stable_json_hash


REPO_ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-worker-plan-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-prehetzner-smoke-v1.json"
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


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _chunk_id_for_sector(total: int, chunk_count: int, sector_id: int) -> int:
    if not (0 <= sector_id < total):
        raise ValueError(f"sector_id out of range: {sector_id}")
    low = 0
    high = chunk_count - 1
    while low <= high:
        mid = (low + high) // 2
        start, end = _chunk_bounds(total, chunk_count, mid)
        if sector_id < start:
            high = mid - 1
        elif sector_id >= end:
            low = mid + 1
        else:
            return mid
    raise ValueError(f"sector_id not covered by chunks: {sector_id}")


def _sector_smoke(
    *,
    evaluator: PointedVacuumProjectorEvaluator,
    context: dict[str, Any],
    category: SnapshotPointedModularCategory,
    total: int,
    chunk_count: int,
    worker_count: int,
    sector_id: int,
    expected_projector_rank: int | None = None,
) -> dict[str, Any]:
    chunk_id = _chunk_id_for_sector(total, chunk_count, sector_id)
    start, end = _chunk_bounds(total, chunk_count, chunk_id)
    labels_tuple = _labels_from_id(
        category.labels, sector_id, len(context["ordinary"])
    )
    labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
    started = time.perf_counter()
    value, stats = evaluator.fixed_label_value(context["graph"], labels)
    elapsed = time.perf_counter() - started
    rank = int(stats["projector_rank"])
    checks = {
        "sector_inside_chunk_bounds": start <= sector_id < end,
        "assigned_worker_index_in_range": 0 <= (chunk_id % worker_count) < worker_count,
        "evaluation_status_pass": stats["status"] in {
            "EVALUATED_POINTED_VACUUM_SECTOR",
            "PRUNED_NO_VACUUM",
        },
        "expected_projector_rank_matches": (
            True
            if expected_projector_rank is None
            else rank == expected_projector_rank
        ),
    }
    return {
        "sector_id": sector_id,
        "chunk_id": chunk_id,
        "chunk_start_sector_id": start,
        "chunk_end_sector_id_exclusive": end,
        "worker_index": chunk_id % worker_count,
        "worker_count": worker_count,
        "elapsed_seconds": elapsed,
        "value_key": _complex_key(value),
        "status": stats["status"],
        "projector_rank": rank,
        "expected_projector_rank": expected_projector_rank,
        "selected_labels": {
            component: str(label)
            for component, label in zip(
                context["ordinary"], labels_tuple, strict=True
            )
        },
        "checks": checks,
        "failed_checks": [name for name, passed in checks.items() if not passed],
    }


def _row_smoke(
    *,
    row: dict[str, Any],
    context: dict[str, Any],
    worker_count: int,
) -> dict[str, Any]:
    item = _find_snapshot(row["realization_id"])
    category = SnapshotPointedModularCategory(item["payload"])
    total = len(category.labels) ** len(context["ordinary"])
    chunk_count = int(row["chunk_count"])
    first_start, first_end = _chunk_bounds(total, chunk_count, 0)
    last_start, last_end = _chunk_bounds(total, chunk_count, chunk_count - 1)
    partition_sector_count = sum(
        _chunk_bounds(total, chunk_count, chunk_id)[1]
        - _chunk_bounds(total, chunk_count, chunk_id)[0]
        for chunk_id in range(chunk_count)
    )
    evaluator = PointedVacuumProjectorEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )

    planned_sector_ids = {
        first_start,
        max(first_start, first_end - 1),
        last_start,
        last_end - 1,
    }
    expected_by_sector: dict[int, int | None] = {
        sector_id: None for sector_id in planned_sector_ids
    }
    if int(row["rank"]) == 5:
        smoke_ids = list(row.get("smoke_sector_ids", []))
        if smoke_ids:
            expected_by_sector[int(smoke_ids[0])] = 1
        if len(smoke_ids) > 1:
            expected_by_sector[int(smoke_ids[1])] = 0

    sector_results = [
        _sector_smoke(
            evaluator=evaluator,
            context=context,
            category=category,
            total=total,
            chunk_count=chunk_count,
            worker_count=worker_count,
            sector_id=sector_id,
            expected_projector_rank=expected_rank,
        )
        for sector_id, expected_rank in sorted(expected_by_sector.items())
    ]
    command_checks = {
        "worker_command_uses_portable_pwd_root": "--work-root $PWD/" in row[
            "worker_command_template"
        ],
        "aggregate_command_uses_portable_pwd_root": "--work-root $PWD/" in row[
            "aggregate_command"
        ],
        "worker_command_has_no_aggregate": "--no-aggregate"
        in row["worker_command_template"],
        "chunk_count_multiple_of_worker_count": chunk_count % worker_count == 0,
        "partition_covers_full_sector_count": partition_sector_count == total,
        "plan_full_sector_count_matches_snapshot": row["full_sector_count"] == total,
    }
    if int(row["rank"]) == 5:
        command_checks["rank5_has_vacuum_aware_cost_model"] = (
            row.get("runtime_cost_model") == "VACUUM_AWARE_RANK5_WEIGHTED_ESTIMATE"
        )
        command_checks["rank5_has_no_cost_warnings"] = not row.get(
            "runtime_estimate_warnings"
        )
        command_checks["rank5_smoked_vacuum_sector"] = any(
            result["projector_rank"] == 1 for result in sector_results
        )
        command_checks["rank5_smoked_pruned_sector"] = any(
            result["projector_rank"] == 0 for result in sector_results
        )
    failed_checks = [
        name for name, passed in command_checks.items() if not passed
    ]
    for result in sector_results:
        failed_checks.extend(
            f"sector-{result['sector_id']}:{name}"
            for name in result["failed_checks"]
        )
    return {
        "realization_id": row["realization_id"],
        "family_id": row["family_id"],
        "rank": row["rank"],
        "status": "PASS" if not failed_checks else "FAIL",
        "chunk_count": chunk_count,
        "worker_count": worker_count,
        "full_sector_count": total,
        "first_chunk_sector_count": first_end - first_start,
        "last_chunk_sector_count": last_end - last_start,
        "partition_sector_count": partition_sector_count,
        "command_checks": command_checks,
        "sector_results": sector_results,
        "failed_checks": failed_checks,
    }


def run_smoke(*, plan_path: Path, output: Path | None = None) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    plan = _load_json(plan_path)
    context = _load_figure21()
    worker_count = int(plan.get("runbook", {}).get("logical_worker_shards", 16))
    ready_rows = [
        row
        for row in plan.get("rows", [])
        if row.get("worker_plan_status") == "READY_FOR_WORKERS"
    ]
    row_results = [
        _row_smoke(row=row, context=context, worker_count=worker_count)
        for row in ready_rows
    ]
    failed_rows = [row for row in row_results if row["status"] != "PASS"]
    finished = datetime.now(UTC)
    payload = {
        "schema": "twisted-yetter.figure21-pointed-prehetzner-smoke.v1",
        "status": "PASS_PREHETZNER_SMOKE" if not failed_rows else "FAIL_PREHETZNER_SMOKE",
        "mathematical_status": "RUNTIME_PREFLIGHT_NOT_SCAN_RESULT",
        "generator_script": "experiments/scripts/run_figure21_pointed_prehetzner_smoke_v1.py",
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "worker_plan": _display_path(plan_path),
            "worker_plan_sha256": _sha256_path(plan_path),
            "worker_plan_content_hash": plan.get("content_hash"),
            "figure21_projected_ir_hash": stable_json_hash(context["ir"]),
            "figure21_coupon_graph_hash": context["graph"]["graph_hash"],
        },
        "parameters": {
            "logical_worker_shards": worker_count,
            "ready_row_count": len(ready_rows),
            "smoke_kind": "planned-chunk-boundary-and-rank5-vacuum-sector",
        },
        "ready_row_count_smoked": len(ready_rows),
        "failed_row_count": len(failed_rows),
        "failed_rows": [
            {
                "realization_id": row["realization_id"],
                "failed_checks": row["failed_checks"],
            }
            for row in failed_rows
        ],
        "rows": row_results,
        "claim_boundary": (
            "Checks local planned-chunk shape, command portability, evaluator "
            "entry points, and rank5 vacuum/pruned sectors before remote launch."
        ),
        "non_claims": [
            "Does not execute full chunks.",
            "Does not prove Hetzner runtime estimates are upper bounds.",
            "Does not aggregate complete category results.",
            "Does not compare Figure 21 to a standard side.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    if output is not None:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path, default=PLAN_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    result = run_smoke(plan_path=args.plan, output=args.output)
    print(args.output)
    if result["status"] != "PASS_PREHETZNER_SMOKE":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
