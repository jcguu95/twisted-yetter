"""Aggregate and compare every completed case in a matrix lane."""

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
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    started = datetime.now(UTC)
    clock = time.perf_counter()
    plan = json.loads(args.plan.read_text())
    cases = [case for case in plan["cases"] if case["lane"] == args.lane]
    env = dict(os.environ)
    env.update({"PYTHONPATH": ".", "DOT_SAGE": str(REPO_ROOT / ".sage")})
    rows = []
    for case in cases:
        ranking = json.loads(
            (args.run_root / case["case_id"] / "ranking" / "summary.json").read_text()
        )
        for character in case["characters"]:
            case_output = args.output_root / case["case_id"]
            aggregate_path = case_output / f"{character['id']}-aggregate.json"
            compare_path = case_output / f"{character['id']}-tham511-comparison.json"
            aggregate_argv = [
                sys.executable,
                "experiments/scripts/morse_singleton_aggregate.py",
                "--expected-count", str(ranking["sector_total"]),
                "--output", str(aggregate_path),
                str(args.run_root / case["case_id"] / character["id"]),
            ]
            aggregate_run = run(aggregate_argv, env)
            compare_run = None
            if aggregate_run["returncode"] == 0:
                compare_argv = [
                    "sage", "--python",
                    "experiments/sage/morse_figure2_tham511_compare.sage.py",
                    "--aggregate", str(aggregate_path),
                    "--category", case["category"],
                    "--standard-character", character["id"].removeprefix("h"),
                    "--output", str(compare_path),
                ]
                if case.get("level") is not None:
                    compare_argv.extend(["--level", str(case["level"])])
                compare_run = run(compare_argv, env)
            rows.append(
                {
                    "case_id": case["case_id"],
                    "character": character,
                    "expected_sector_count": ranking["sector_total"],
                    "aggregate": aggregate_run,
                    "aggregate_path": str(aggregate_path),
                    "comparison": compare_run,
                    "comparison_path": str(compare_path),
                }
            )

    status = "pass" if all(
        row["aggregate"]["returncode"] == 0
        and row["comparison"] is not None
        and row["comparison"]["returncode"] == 0
        for row in rows
    ) else "needs-review"
    payload = {
        "schema": "twisted-yetter.native-morse-case-matrix-comparison.v1",
        "status": status,
        "mathematical_status": "NUMERICAL_CROSS_PRESENTATION_CONSISTENCY_MATRIX",
        "generator_script": "experiments/scripts/morse_case_matrix_compare.py",
        "plan": str(args.plan),
        "plan_sha256": file_sha256(args.plan),
        "lane": args.lane,
        "run_root": str(args.run_root),
        "output_root": str(args.output_root),
        "environment": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "python": sys.version,
            "cpu_count": os.cpu_count(),
        },
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "rows": rows,
    }
    output = args.output or args.output_root / "matrix-comparison-summary.json"
    atomic_write_json(output, payload)
    print(output.resolve())
    if status != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
