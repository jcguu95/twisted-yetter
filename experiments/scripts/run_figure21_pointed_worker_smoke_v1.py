#!/usr/bin/env python3
"""Smoke-test Figure 21 pointed worker commands before remote execution."""

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
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-worker-smoke-v1.json"
)
DEFAULT_SMOKE_ROOT = Path("/tmp/figure21-pointed-worker-smoke-v1")


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


def _run_one(
    *,
    realization_id: str,
    full_sector_count: int,
    sector_id: int,
    smoke_root: Path,
) -> dict[str, Any]:
    command = [
        "uv",
        "run",
        "python",
        "experiments/scripts/run_figure21_pointed_category_chunks_v1.py",
        "--realization-id",
        realization_id,
        "--chunk-count",
        str(full_sector_count),
        "--chunk-id",
        str(sector_id),
        "--work-root",
        str(smoke_root),
        "--no-aggregate",
    ]
    started = time.perf_counter()
    completed = subprocess.run(
        command,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        env={
            **dict(os.environ),
            "PYTHONPATH": ".",
            "UV_CACHE_DIR": "/tmp/uv-cache",
        },
    )
    stdout_lines = [line for line in completed.stdout.splitlines() if line.strip()]
    parsed = None
    if stdout_lines:
        try:
            parsed = json.loads(stdout_lines[-1])
        except json.JSONDecodeError:
            parsed = None
    return {
        "realization_id": realization_id,
        "sector_id": sector_id,
        "chunk_count": full_sector_count,
        "status": "PASS" if completed.returncode == 0 else "FAIL",
        "returncode": completed.returncode,
        "elapsed_seconds": time.perf_counter() - started,
        "command": command,
        "stdout_tail": stdout_lines[-5:],
        "stderr_tail": completed.stderr.splitlines()[-20:],
        "parsed_last_stdout_json": parsed,
    }


def run_smoke(
    *,
    plan_path: Path,
    smoke_root: Path,
    max_rows: int | None,
    sectors_per_row: int,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    plan = _load_json(plan_path)
    ready_rows = [
        row
        for row in plan["rows"]
        if row.get("worker_plan_status") == "READY_FOR_WORKERS"
    ]
    if max_rows is not None:
        ready_rows = ready_rows[:max_rows]
    results = []
    for row in ready_rows:
        sector_ids = list(row.get("smoke_sector_ids", []))[:sectors_per_row]
        if not sector_ids:
            sector_ids = [0]
        for sector_id in sector_ids:
            results.append(
                _run_one(
                    realization_id=row["realization_id"],
                    full_sector_count=int(row["full_sector_count"]),
                    sector_id=int(sector_id),
                    smoke_root=smoke_root,
                )
            )
    failed = [row for row in results if row["status"] != "PASS"]
    rank5_vacuum_failures = []
    for row in ready_rows:
        if int(row.get("rank", 0)) != 5:
            continue
        row_results = [
            result
            for result in results
            if result["realization_id"] == row["realization_id"]
        ]
        has_vacuum = any(
            str(
                (
                    result.get("parsed_last_stdout_json") or {}
                ).get("projector_rank_distribution", {}).get("1", 0)
            )
            not in {"0", "None"}
            for result in row_results
            if result["status"] == "PASS"
        )
        if not has_vacuum:
            rank5_vacuum_failures.append(row["realization_id"])
    finished = datetime.now(UTC)
    payload = {
        "schema": "twisted-yetter.figure21-pointed-worker-smoke.v1",
        "status": (
            "PASS_WORKER_SMOKE"
            if not failed and not rank5_vacuum_failures
            else "FAIL_WORKER_SMOKE"
        ),
        "mathematical_status": "RUNTIME_SMOKE_NOT_SCAN_RESULT",
        "generator_script": "experiments/scripts/run_figure21_pointed_worker_smoke_v1.py",
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "worker_plan": str(plan_path),
            "worker_plan_sha256": _sha256_path(plan_path),
            "worker_plan_content_hash": plan.get("content_hash"),
        },
        "parameters": {
            "smoke_root": str(smoke_root),
            "max_rows": max_rows,
            "sectors_per_row": sectors_per_row,
        },
        "ready_row_count_smoked": len(ready_rows),
        "smoke_case_count": len(results),
        "failed_case_count": len(failed),
        "rank5_vacuum_smoke_failures": rank5_vacuum_failures,
        "results": results,
        "claim_boundary": "This only proves worker commands start and write tiny chunks locally.",
        "non_claims": [
            "Does not prove the full worker run will finish within estimate.",
            "Does not aggregate complete category results.",
            "Does not compare Figure 21 to a standard side.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path, default=PLAN_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--smoke-root", type=Path, default=DEFAULT_SMOKE_ROOT)
    parser.add_argument("--max-rows", type=int, default=None)
    parser.add_argument("--sectors-per-row", type=int, default=2)
    args = parser.parse_args()
    result = run_smoke(
        plan_path=args.plan,
        smoke_root=args.smoke_root,
        max_rows=args.max_rows,
        sectors_per_row=args.sectors_per_row,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)
    if result["status"] != "PASS_WORKER_SMOKE":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
