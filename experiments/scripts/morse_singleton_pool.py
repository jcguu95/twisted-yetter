"""Launch one restartable Sage singleton worker per balanced shard."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
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


def parse_indices(raw):
    indices = set()
    for part in raw.split(","):
        if not part.strip():
            continue
        if ":" in part:
            start, stop = (int(item) for item in part.split(":", 1))
            indices.update(range(start, stop))
        else:
            indices.add(int(part))
    return indices


def command(argv):
    try:
        return subprocess.check_output(
            argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def environment_metadata():
    return {
        "hostname": platform.node(),
        "platform": platform.platform(),
        "python": sys.version,
        "cpu_count": os.cpu_count(),
        "environment": {
            key: os.environ.get(key)
            for key in (
                "DOT_SAGE",
                "OMP_NUM_THREADS",
                "OPENBLAS_NUM_THREADS",
                "VECLIB_MAXIMUM_THREADS",
                "MKL_NUM_THREADS",
                "PYTHONPATH",
            )
            if key in os.environ
        },
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--characters")
    parser.add_argument("--planner-mode", choices=("hybrid", "sequential"), default="hybrid")
    parser.add_argument(
        "--checkpoint-format", choices=("files", "jsonl"), default="files"
    )
    parser.add_argument("--reverse-orientation", action="append", default=[])
    parser.add_argument("--shard-dir", type=Path, required=True)
    parser.add_argument(
        "--shard-indices",
        help="comma-separated indices or half-open ranges, e.g. 0:16,32",
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")

    shard_paths = sorted(args.shard_dir.glob("shard-*.jsonl"))
    if args.shard_indices:
        selected = parse_indices(args.shard_indices)
        shard_paths = [
            path
            for path in shard_paths
            if int(path.stem.split("-")[-1]) in selected
        ]
    if not shard_paths:
        parser.error("no shard files selected")

    started = datetime.now(UTC)
    clock = time.perf_counter()
    args.output_root.mkdir(parents=True, exist_ok=True)
    pool_output = args.output or args.output_root / "pool-summary.json"
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

    def run_shard(path):
        shard_index = int(path.stem.split("-")[-1])
        worker_id = f"{platform.node()}-shard-{shard_index:04d}"
        output_dir = args.output_root / f"shard-{shard_index:04d}"
        output_dir.mkdir(parents=True, exist_ok=True)
        summary_path = output_dir / "worker-summary.json"
        argv = [
            "sage",
            "--python",
            "experiments/sage/morse_native_evaluate.sage.py",
            "--input",
            str(args.input),
            "--category",
            args.category,
            "--mode",
            "chunk",
            "--sector-index-file",
            str(path),
            "--planner-mode",
            args.planner_mode,
            "--singleton-output-dir",
            str(output_dir),
            "--checkpoint-format",
            args.checkpoint_format,
            "--run-id",
            args.run_id,
            "--worker-id",
            worker_id,
            "--output",
            str(summary_path),
        ]
        if args.level is not None:
            argv.extend(["--level", str(args.level)])
        if args.characters:
            argv.extend(["--characters", args.characters])
        for component in args.reverse_orientation:
            argv.extend(["--reverse-orientation", component])
        if args.resume:
            argv.append("--resume")
        shard_started = datetime.now(UTC)
        shard_clock = time.perf_counter()
        completed = subprocess.run(
            argv,
            cwd=REPO_ROOT,
            env=env,
            text=True,
            capture_output=True,
        )
        return {
            "shard_index": shard_index,
            "shard_path": str(path),
            "shard_sha256": file_sha256(path),
            "worker_id": worker_id,
            "argv": argv,
            "utc_start": shard_started.isoformat(),
            "utc_finish": datetime.now(UTC).isoformat(),
            "elapsed_seconds": time.perf_counter() - shard_clock,
            "returncode": completed.returncode,
            "worker_summary": str(summary_path),
            "stdout_tail": completed.stdout[-2000:],
            "stderr_tail": completed.stderr[-4000:],
        }

    rows = []
    with ThreadPoolExecutor(max_workers=min(args.workers, len(shard_paths))) as pool:
        futures = {pool.submit(run_shard, path): path for path in shard_paths}
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
            atomic_write_json(
                pool_output,
                {
                    "schema": "twisted-yetter.native-morse-singleton-pool.v1",
                    "status": "running",
                    "run_id": args.run_id,
                    "completed_shard_count": len(rows),
                    "selected_shard_count": len(shard_paths),
                    "rows": sorted(rows, key=lambda item: item["shard_index"]),
                },
            )

    payload = {
        "schema": "twisted-yetter.native-morse-singleton-pool.v1",
        "status": "pass" if all(row["returncode"] == 0 for row in rows) else "needs-review",
        "mathematical_status": "DISTRIBUTED_RUN_LEDGER_NOT_AN_AGGREGATE_RESULT",
        "generator_script": "experiments/scripts/morse_singleton_pool.py",
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. python3 " + " ".join(sys.argv),
        "run_id": args.run_id,
        "input": str(args.input),
        "input_sha256": file_sha256(args.input),
        "category": args.category,
        "level": args.level,
        "characters": args.characters,
        "planner_mode": args.planner_mode,
        "checkpoint_format": args.checkpoint_format,
        "reverse_orientation": args.reverse_orientation,
        "workers": args.workers,
        "selected_shard_count": len(shard_paths),
        "selected_shards": [str(path) for path in shard_paths],
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "git_dirty": bool(command(["git", "status", "--short"])),
        },
        "environment": environment_metadata(),
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "rows": sorted(rows, key=lambda item: item["shard_index"]),
    }
    atomic_write_json(pool_output, payload)
    print(pool_output.resolve())
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
