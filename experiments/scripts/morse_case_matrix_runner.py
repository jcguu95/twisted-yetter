"""Run a lane from a machine-readable native-Morse case matrix plan."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

from experiments.scripts.morse_singleton_workload import atomic_write_json, file_sha256


REPO_ROOT = Path(__file__).resolve().parents[2]


def run(argv, env):
    started = datetime.now(UTC)
    clock = time.perf_counter()
    completed = subprocess.run(
        argv, cwd=REPO_ROOT, env=env, text=True, capture_output=True
    )
    return {
        "argv": argv,
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "returncode": completed.returncode,
        "stdout_tail": completed.stdout[-2000:],
        "stderr_tail": completed.stderr[-4000:],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--lane", required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    started = datetime.now(UTC)
    clock = time.perf_counter()
    plan = json.loads(args.plan.read_text())
    cases = [case for case in plan["cases"] if case["lane"] == args.lane]
    if not cases:
        parser.error(f"plan has no cases for lane {args.lane!r}")

    env = dict(os.environ)
    env.update(
        {
            "PYTHONPATH": ".",
            "DOT_SAGE": str(REPO_ROOT / ".sage"),
            "OMP_NUM_THREADS": "1",
            "OPENBLAS_NUM_THREADS": "1",
            "VECLIB_MAXIMUM_THREADS": "1",
            "MKL_NUM_THREADS": "1",
        }
    )
    rows = []
    for case in cases:
        case_root = args.output_root / case["case_id"]
        ranking_root = case_root / "ranking"
        ranking_summary = ranking_root / "summary.json"
        ranking_argv = [
            "sage", "--python", "experiments/sage/morse_complexity_rank.sage.py",
            "--input", plan["input"], "--category", case["category"],
            "--shards", str(plan["shards"]),
            "--shard-dir", str(ranking_root / "shards"),
            "--ranking-output", str(ranking_root / "ranking.jsonl"),
            "--output", str(ranking_summary),
        ]
        if case.get("level") is not None:
            ranking_argv.extend(["--level", str(case["level"])])
        ranking_run = None
        if not (args.resume and ranking_summary.exists()):
            ranking_run = run(ranking_argv, env)
            if ranking_run["returncode"]:
                rows.append({"case": case, "ranking": ranking_run, "character_runs": []})
                break

        character_runs = []
        for character in case["characters"]:
            output_root = case_root / character["id"]
            pool_argv = [
                sys.executable,
                "experiments/scripts/morse_singleton_pool.py",
                "--input", plan["input"],
                "--category", case["category"],
                "--characters", character["path"],
                "--shard-dir", str(ranking_root / "shards"),
                "--shard-indices", f"0:{plan['shards']}",
                "--output-root", str(output_root),
                "--workers", str(plan["workers"]),
                "--run-id", f"{args.run_id}-{case['case_id']}-{character['id']}",
            ]
            if case.get("level") is not None:
                pool_argv.extend(["--level", str(case["level"])])
            if args.resume:
                pool_argv.append("--resume")
            result = run(pool_argv, env)
            character_runs.append({"character": character, "run": result})
            if result["returncode"]:
                break
        rows.append(
            {
                "case": case,
                "ranking": ranking_run or {"status": "reused-existing"},
                "character_runs": character_runs,
            }
        )
        if any(row["run"]["returncode"] for row in character_runs):
            break

    payload = {
        "schema": "twisted-yetter.native-morse-case-matrix-run.v1",
        "status": "pass" if all(
            all(item["run"]["returncode"] == 0 for item in row["character_runs"])
            and row["ranking"].get("returncode", 0) == 0
            for row in rows
        ) and len(rows) == len(cases) else "needs-review",
        "mathematical_status": "DISTRIBUTED_RUN_LEDGER_NOT_AGGREGATED_COMPARISON",
        "generator_script": "experiments/scripts/morse_case_matrix_runner.py",
        "plan": str(args.plan),
        "plan_sha256": file_sha256(args.plan),
        "lane": args.lane,
        "run_id": args.run_id,
        "environment": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "python": sys.version,
            "cpu_count": os.cpu_count(),
            "thread_env": {key: env[key] for key in (
                "OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS",
                "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"
            )},
        },
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "rows": rows,
    }
    output = args.output_root / "matrix-run-summary.json"
    atomic_write_json(output, payload)
    print(output.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
