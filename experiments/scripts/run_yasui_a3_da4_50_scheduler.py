#!/usr/bin/env python3
"""Schedule Yasui a=3 D(A4) untwisted sectors in 50-sector ranges.

The scheduler is intentionally operational: it limits local Sage workers and
optional SSH workers, writes a machine-readable run summary, and treats each
range as complete only when all per-sector chunk JSON files are present locally.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import UTC, datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
SAGE_SCRIPT = "experiments/sage/yasui_figure3_a3_da4_untwisted_chunked.sage.py"
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
CHUNK_DIR = RESULT_DIR / "figure3-a3-da4-omega0-untwisted-chunks-v1"
SUMMARY_PATH = RESULT_DIR / "figure3-a3-da4-omega0-untwisted-50-scheduler-v1.json"


def command(
    argv: list[str],
    *,
    cwd: Path = REPO_ROOT,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(argv, cwd=cwd, check=check, text=True, capture_output=True, env=env)


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def chunk_path(start: int) -> Path:
    return CHUNK_DIR / f"chunk-{start:07d}-{start + 1:07d}.json"


def range_complete(start: int, count: int) -> bool:
    return all(chunk_path(index).exists() for index in range(start, start + count))


def profile_path(start: int, end: int) -> Path:
    return RESULT_DIR / f"figure3-a3-da4-omega0-untwisted-profile-{start:07d}-{end:07d}-v1.json"


def run_local(start: int, count: int) -> dict[str, Any]:
    started = time.monotonic()
    argv = [
        "sage",
        SAGE_SCRIPT,
        "--start",
        str(start),
        "--count",
        str(count),
        "--quiet",
    ]
    env = dict(os.environ)
    env["DOT_SAGE"] = str(REPO_ROOT / ".sage")
    completed = command(argv, check=False, env=env)
    elapsed = time.monotonic() - started
    return {
        "runner": "local",
        "start": start,
        "end": start + count,
        "returncode": completed.returncode,
        "elapsed_wall_seconds": elapsed,
        "stdout_tail": completed.stdout[-2000:],
        "stderr_tail": completed.stderr[-2000:],
        "complete_after_run": range_complete(start, count),
        "profile_artifact": rel(profile_path(start, start + count)) if profile_path(start, start + count).exists() else None,
    }


def ssh_base(remote: str) -> list[str]:
    return ["ssh", "-o", "BatchMode=yes", remote]


def run_remote(start: int, count: int, *, remote: str, remote_root: str) -> dict[str, Any]:
    started = time.monotonic()
    remote_cmd = (
        f"cd {shell_quote(remote_root)} && "
        f'DOT_SAGE="$PWD/.sage" sage {shell_quote(SAGE_SCRIPT)} '
        f"--start {start} --count {count} --quiet"
    )
    completed = command(ssh_base(remote) + [remote_cmd], check=False)
    fetch = None
    if completed.returncode == 0:
        fetch = fetch_remote_range(remote, remote_root, start, count)
    elapsed = time.monotonic() - started
    return {
        "runner": "remote",
        "remote": remote,
        "remote_root": remote_root,
        "start": start,
        "end": start + count,
        "returncode": completed.returncode,
        "elapsed_wall_seconds": elapsed,
        "stdout_tail": completed.stdout[-2000:],
        "stderr_tail": completed.stderr[-2000:],
        "fetch": fetch,
        "complete_after_run": range_complete(start, count),
        "profile_artifact": rel(profile_path(start, start + count)) if profile_path(start, start + count).exists() else None,
    }


def fetch_remote_range(remote: str, remote_root: str, start: int, count: int) -> dict[str, Any]:
    paths = [
        f"{remote_root}/experiments/results/yasui/figure3-a3-da4-omega0-untwisted-profile-{start:07d}-{start + count:07d}-v1.json",
    ]
    for index in range(start, start + count):
        paths.append(
            f"{remote_root}/experiments/results/yasui/figure3-a3-da4-omega0-untwisted-chunks-v1/chunk-{index:07d}-{index + 1:07d}.json"
        )
    RESULT_DIR.mkdir(parents=True, exist_ok=True)
    CHUNK_DIR.mkdir(parents=True, exist_ok=True)
    ok = True
    errors = []
    for path in paths:
        destination = REPO_ROOT / Path(path).relative_to(remote_root)
        destination.parent.mkdir(parents=True, exist_ok=True)
        completed = command(["rsync", "-az", f"{remote}:{path}", str(destination)], check=False)
        if completed.returncode != 0:
            ok = False
            errors.append({"path": path, "stderr": completed.stderr[-1000:]})
    return {"ok": ok, "error_count": len(errors), "errors": errors[:5]}


def shell_quote(value: str) -> str:
    return "'" + value.replace("'", "'\"'\"'") + "'"


def sync_remote_bundle(remote: str, remote_root: str) -> dict[str, Any]:
    command(ssh_base(remote) + [f"mkdir -p {shell_quote(remote_root)}"])
    files = [
        SAGE_SCRIPT,
        "experiments/sage/yasui_figure3_a3_su2_2_untwisted_comparison.sage.py",
        "experiments/inputs/yasui/figure3-a3-crossing-table.json",
        "experiments/results/mtc-candidates/drinfeld-double-a4-omega0-mtc-fr-data-v1.json",
        "src/twisted_yetter/__init__.py",
        "src/twisted_yetter/local_piece.py",
    ]
    argv = ["rsync", "-azR", *files, f"{remote}:{remote_root}/"]
    completed = command(argv, check=False)
    return {
        "remote": remote,
        "remote_root": remote_root,
        "returncode": completed.returncode,
        "stdout_tail": completed.stdout[-1000:],
        "stderr_tail": completed.stderr[-2000:],
    }


def schedule(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    started_at = datetime.now(UTC).isoformat()
    ranges = [
        (start, min(args.range_size, args.end - start))
        for start in range(args.start, args.end, args.range_size)
    ]
    skipped = [
        {
            "start": start,
            "end": start + count,
            "status": "already-complete",
            "chunk_count": count,
        }
        for start, count in ranges
        if range_complete(start, count)
    ]
    pending = [(start, count) for start, count in ranges if not range_complete(start, count)]

    sync = None
    remote_enabled = bool(args.remote and args.remote_root and args.remote_workers > 0)
    if remote_enabled:
        sync = sync_remote_bundle(args.remote, args.remote_root)
        if sync["returncode"] != 0:
            remote_enabled = False

    workers: list[tuple[str, int]] = []
    workers.extend(("local", index) for index in range(args.local_workers))
    if remote_enabled:
        workers.extend(("remote", index) for index in range(args.remote_workers))
    if not workers:
        raise ValueError("at least one worker is required")

    results: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=len(workers)) as executor:
        in_flight = {}
        pending_iter = iter(pending)

        def submit_next(worker: tuple[str, int]) -> bool:
            try:
                start, count = next(pending_iter)
            except StopIteration:
                return False
            kind, _index = worker
            if kind == "local":
                future = executor.submit(run_local, start, count)
            else:
                future = executor.submit(
                    run_remote,
                    start,
                    count,
                    remote=args.remote,
                    remote_root=args.remote_root,
                )
            in_flight[future] = worker
            return True

        for worker in workers:
            submit_next(worker)

        while in_flight:
            done, _ = wait(in_flight, return_when=FIRST_COMPLETED)
            for future in done:
                worker = in_flight.pop(future)
                result = future.result()
                results.append(result)
                print(json.dumps({"phase": "range-complete", **summary_row(result)}, sort_keys=True), flush=True)
                submit_next(worker)

    finished_at = datetime.now(UTC).isoformat()
    return {
        "schema": "twisted-yetter.yasui-figure3-a3-da4-untwisted-50-scheduler.v1",
        "status": "complete" if all(row.get("complete_after_run") for row in results) else "partial-or-failed",
        "created_at": finished_at,
        "utc_start": started_at,
        "utc_finish": finished_at,
        "elapsed_wall_seconds": time.monotonic() - started,
        "generator_script": "experiments/scripts/run_yasui_a3_da4_50_scheduler.py",
        "argv": sys.argv[1:],
        "scope": "Schedule 50-sector Yasui a=3 D(A4) untwisted range jobs with bounded local/remote concurrency.",
        "claim_boundary": "Operational timing/distribution artifact only; not a complete invariant claim by itself.",
        "configuration": {
            "start": args.start,
            "end": args.end,
            "range_size": args.range_size,
            "local_workers": args.local_workers,
            "remote": args.remote,
            "remote_root": args.remote_root,
            "remote_workers": args.remote_workers if remote_enabled else 0,
        },
        "remote_sync": sync,
        "skipped_already_complete": skipped,
        "results": sorted(results, key=lambda row: row["start"]),
        "summary": summarize(skipped, results, args),
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]).stdout.strip(),
            "dirty": bool(command(["git", "status", "--short"]).stdout.strip()),
            "status_short": command(["git", "status", "--short"]).stdout,
        },
    }


def summary_row(result: dict[str, Any]) -> dict[str, Any]:
    return {
        "runner": result["runner"],
        "start": result["start"],
        "end": result["end"],
        "returncode": result["returncode"],
        "elapsed_wall_seconds": result["elapsed_wall_seconds"],
        "complete_after_run": result["complete_after_run"],
    }


def summarize(skipped: list[dict[str, Any]], results: list[dict[str, Any]], args: argparse.Namespace) -> dict[str, Any]:
    complete_ranges = len(skipped) + sum(1 for row in results if row.get("complete_after_run"))
    failed_ranges = sum(1 for row in results if not row.get("complete_after_run"))
    return {
        "planned_ranges": len(range(args.start, args.end, args.range_size)),
        "skipped_ranges": len(skipped),
        "run_ranges": len(results),
        "complete_ranges": complete_ranges,
        "failed_ranges": failed_ranges,
        "complete_sector_count": sum(args.range_size for _ in skipped)
        + sum((row["end"] - row["start"]) for row in results if row.get("complete_after_run")),
    }


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--end", type=int, default=2700)
    parser.add_argument("--range-size", type=int, default=50)
    parser.add_argument("--local-workers", type=int, default=2)
    parser.add_argument("--remote", default="xilingdai@xil-m2.local")
    parser.add_argument("--remote-root", default="/Users/xilingdai/twisted-yetter-da4-run")
    parser.add_argument("--remote-workers", type=int, default=2)
    parser.add_argument("--summary-output", type=Path, default=SUMMARY_PATH)
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    payload = schedule(args)
    args.summary_output.parent.mkdir(parents=True, exist_ok=True)
    args.summary_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"phase": "scheduler-complete", "artifact": rel(args.summary_output), "status": payload["status"], **payload["summary"]}, sort_keys=True))
    return 0 if payload["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
