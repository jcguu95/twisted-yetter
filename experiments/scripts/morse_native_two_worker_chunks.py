"""Run bounded native-Morse chunks with a small subprocess worker pool."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import subprocess
import time


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--chunk-size", type=int, required=True)
    parser.add_argument("--workers", type=int, default=2, choices=(1, 2))
    parser.add_argument("--level", type=int, default=2)
    parser.add_argument("--group-components")
    parser.add_argument("--record-sector-values", action="store_true")
    return parser.parse_args()


def main():
    args = parse_args()
    repo = Path(__file__).resolve().parents[2]
    output_dir = Path(args.output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    chunks = [
        (start, min(args.chunk_size, args.stop - start))
        for start in range(args.start, args.stop, args.chunk_size)
    ]

    def run(chunk):
        start, count = chunk
        output = output_dir / f"chunk-{start:05d}-{start + count:05d}.json"
        command = [
            "sage", "--python",
            "experiments/sage/morse_native_evaluate.sage.py",
            "--input", args.input,
            "--category", "su2", "--level", str(args.level),
            "--mode", "chunk", "--sector-start", str(start),
            "--sector-count", str(count), "--output", str(output),
        ]
        if args.group_components:
            command.extend(["--group-components", args.group_components])
        if args.record_sector_values:
            command.append("--record-sector-values")
        env = dict(os.environ)
        env["PYTHONPATH"] = "."
        env["DOT_SAGE"] = str(repo / ".sage")
        began = time.perf_counter()
        completed = subprocess.run(
            command, cwd=repo, env=env, text=True, capture_output=True
        )
        return {
            "start": start,
            "count": count,
            "elapsed_seconds": time.perf_counter() - began,
            "returncode": completed.returncode,
            "output": str(output),
            "stdout_tail": completed.stdout[-1000:],
            "stderr_tail": completed.stderr[-2000:],
        }

    began = time.perf_counter()
    rows = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run, chunk): chunk for chunk in chunks}
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
            if row["returncode"]:
                raise SystemExit(row["returncode"])
    summary = {
        "status": "pass",
        "workers": args.workers,
        "start": args.start,
        "stop": args.stop,
        "chunk_size": args.chunk_size,
        "sector_count": args.stop - args.start,
        "wall_seconds": time.perf_counter() - began,
        "chunks": sorted(rows, key=lambda row: row["start"]),
    }
    (output_dir / "run-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )


if __name__ == "__main__":
    main()
