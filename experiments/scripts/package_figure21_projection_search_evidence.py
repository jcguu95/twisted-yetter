#!/usr/bin/env python3
"""Package Figure 21 projection-search checkpoints without embedding them in CTL."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import platform
import subprocess
import tarfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = REPO_ROOT / "experiments/results/akbulut-yasui/evidence/figure21-black-cancel-projection-search-evidence-v2.tar.gz"
DEFAULT_SUMMARY = REPO_ROOT / "experiments/results/akbulut-yasui/figure21-black-cancel-projection-search-checkpoint-v2.json"


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _utc(timestamp: float) -> str:
    return datetime.fromtimestamp(timestamp, timezone.utc).isoformat().replace("+00:00", "Z")


def _git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def _read_xil_mtimes(path: Path) -> dict[str, float]:
    result: dict[str, float] = {}
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        fields = raw_line.replace("\\t", "\t").split("\t")
        if len(fields) >= 2:
            result[Path(fields[0]).parent.name] = float(fields[1])
    return result


def _checkpoint_row(path: Path, host: str, original_mtime: float | None = None) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    elapsed = float(payload["elapsed_seconds"])
    observed = original_mtime if original_mtime is not None else path.stat().st_mtime
    best = payload.get("best") or {}
    return {
        "host": host,
        "directory": path.parent.name,
        "strategy": payload["strategy"],
        "status": payload["status"],
        "completed": payload["completed"],
        "total": payload["total"],
        "elapsed_seconds": format(elapsed, ".15g"),
        "best_regular_crossings": best.get("regular_crossings"),
        "best_parameters": best,
        "checkpoint_sha256": _sha256(path),
        "checkpoint_mtime_utc": _utc(observed),
        "inferred_start_utc": _utc(observed - elapsed),
        "time_interpretation": "Start is inferred as checkpoint mtime minus elapsed_seconds. For interrupted RUNNING rows, mtime is the last checkpoint observation, not a finish time.",
    }


def _archive_name(path: Path, local_root: Path, xil_root: Path) -> str:
    if path.is_relative_to(local_root):
        return "local-searches/" + str(path.relative_to(local_root))
    if path.is_relative_to(xil_root):
        return "xil-searches/" + str(path.relative_to(xil_root))
    return "support/" + path.name


def _write_deterministic_bundle(output: Path, files: list[tuple[Path, str]], inventory: dict[str, Any]) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    raw_tar = io.BytesIO()
    with tarfile.open(fileobj=raw_tar, mode="w") as archive:
        manifest_bytes = (json.dumps(inventory, indent=2, sort_keys=True) + "\n").encode()
        manifest_info = tarfile.TarInfo("inventory.json")
        manifest_info.size = len(manifest_bytes)
        manifest_info.mtime = 0
        manifest_info.mode = 0o644
        archive.addfile(manifest_info, io.BytesIO(manifest_bytes))
        for source, name in sorted(files, key=lambda item: item[1]):
            info = tarfile.TarInfo(name)
            info.size = source.stat().st_size
            info.mtime = 0
            info.mode = 0o644
            with source.open("rb") as stream:
                archive.addfile(info, stream)
    with output.open("wb") as stream:
        with gzip.GzipFile(filename="", mode="wb", fileobj=stream, mtime=0) as compressor:
            compressor.write(raw_tar.getvalue())


def package(args: argparse.Namespace) -> dict[str, Any]:
    local_dirs = sorted(args.local_parent.glob("figure21-black-cancel-search-local-*"))
    xil_dirs = sorted(path for path in args.xil_root.glob("search-xil-*") if path.is_dir())
    xil_mtimes = _read_xil_mtimes(args.xil_stats)
    rows = [_checkpoint_row(path / "checkpoint.json", "jin-m2") for path in local_dirs]
    rows.extend(
        _checkpoint_row(path / "checkpoint.json", "xil-m2", xil_mtimes.get(path.name))
        for path in xil_dirs
    )

    files: list[tuple[Path, str]] = []
    for directory in local_dirs + xil_dirs:
        for filename in ("checkpoint.json", "best-metadata.json"):
            candidate = directory / filename
            if candidate.exists():
                files.append((candidate, _archive_name(candidate, args.local_parent, args.xil_root)))
    for directory in (args.best_3988_dir, args.best_3990_dir):
        candidate = directory / "best-lowered.json"
        files.append((candidate, "selected-lowered/" + directory.name + ".json"))
    support_files = [
        args.source_lift,
        args.local_search_script,
        args.xil_search_script,
        args.local_launch,
        args.xil_launch,
        args.xil_stats,
        args.local_environment,
        args.xil_environment,
        *args.prior_bundles,
    ]
    for source in support_files:
        files.append((source, _archive_name(source, args.local_parent, args.xil_root)))

    inventory = {
        "schema": "twisted-yetter.figure21-projection-search-evidence-inventory.v2",
        "status": "RECOVERED_TRANSIENT_EVIDENCE",
        "checkpoint_rows": rows,
        "files": [
            {"archive_path": name, "sha256": _sha256(path), "bytes": path.stat().st_size}
            for path, name in sorted(files, key=lambda item: item[1])
        ],
    }
    _write_deterministic_bundle(args.output, files, inventory)

    completed = [row for row in rows if row["status"] == "PASS"]
    interrupted = [row for row in rows if row["status"] != "PASS"]
    summary = {
        "schema": "twisted-yetter.figure21-black-cancel-projection-search-checkpoint.v2",
        "status": "RECOVERED_REPRODUCIBLE_SEARCH_CHECKPOINT",
        "generated_at_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "mathematical_status": "EXPERIMENTAL_DIAGRAM_REWRITE_NOT_INDEPENDENTLY_CERTIFIED_AS_KIRBY_EQUIVALENT",
        "top_notice": "This supersedes the v1 claim that transient search evidence was lost. Checkpoints and scripts were recovered from /private/tmp and XIL. Search timestamps are inferred from checkpoint mtimes unless an exact launch record exists.",
        "presentation_subject": "subject:twisted-yetter:presentation:akbulut-yasui-2008-figure21-e3prime",
        "category_subject": "subject:twisted-yetter:category-family:su2-k",
        "result": {
            "baseline_crossings": 7443,
            "best_evaluator_ready_crossings": min(row["best_regular_crossings"] for row in completed),
            "maximum_active_strands_at_3988": 170,
            "maximum_su2_2_boundary_fusion_dimension": "2^84",
            "decision": "STOP_PROJECTION_DIRECTION_SEARCH_AND_REQUIRE_A_STRUCTURALLY_BETTER_KIRBY_SLIDE_SEQUENCE",
        },
        "execution": {
            "checkpoint_count": len(rows),
            "completed_checkpoint_count": len(completed),
            "interrupted_checkpoint_count": len(interrupted),
            "checkpoint_rows": rows,
            "hosts": [
                json.loads(args.local_environment.read_text(encoding="utf-8")),
                json.loads(args.xil_environment.read_text(encoding="utf-8")),
            ],
            "exact_launch_records": [
                json.loads(args.local_launch.read_text(encoding="utf-8")),
                json.loads(args.xil_launch.read_text(encoding="utf-8")),
            ],
        },
        "evidence_bundle": {
            "path": str(args.output.relative_to(REPO_ROOT)),
            "sha256": _sha256(args.output),
            "bytes": args.output.stat().st_size,
            "contents": "All 17 checkpoint JSONs, available best metadata, local/XIL search scripts, source lift, exact launch records, host summaries, prior bundles, and the 3988/3990 lowered candidates.",
        },
        "generator_script": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "argv": [str(value) for value in os.sys.argv],
        "reproduce_command": "python3 experiments/scripts/package_figure21_projection_search_evidence.py --write",
        "source_checkpoint": {
            "git_commit": _git("rev-parse", "HEAD"),
            "git_dirty": bool(_git("status", "--porcelain")),
        },
    }
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--local-parent", type=Path, default=Path("/private/tmp"))
    parser.add_argument("--xil-root", type=Path, default=Path("/private/tmp/figure21-xil-checkpoints-20260715"))
    parser.add_argument("--xil-stats", type=Path, default=Path("/private/tmp/figure21-xil-checkpoints-20260715/original-checkpoint-stats.tsv"))
    parser.add_argument("--source-lift", type=Path, default=Path("/private/tmp/figure21-black-cancel-final-pl-lift-v1.json"))
    parser.add_argument("--local-search-script", type=Path, default=Path("/private/tmp/search_figure21_black_cancel_projection.py"))
    parser.add_argument("--xil-search-script", type=Path, default=Path("/private/tmp/figure21-xil-checkpoints-20260715/search_figure21_black_cancel_projection.py"))
    parser.add_argument("--local-launch", type=Path, default=Path("/private/tmp/figure21-black-cancel-local-search-logs/launch.json"))
    parser.add_argument("--xil-launch", type=Path, default=Path("/private/tmp/figure21-xil-checkpoints-20260715/search-launch.json"))
    parser.add_argument("--local-environment", type=Path, default=Path("/private/tmp/figure21-local-environment.json"))
    parser.add_argument("--xil-environment", type=Path, default=Path("/private/tmp/figure21-xil-environment.json"))
    parser.add_argument("--best-3988-dir", type=Path, default=Path("/private/tmp/figure21-black-cancel-search-local-boundary-jitter"))
    parser.add_argument("--best-3990-dir", type=Path, default=Path("/private/tmp/figure21-black-cancel-search-local-best3990"))
    parser.add_argument("--prior-bundles", type=Path, nargs="*", default=[Path("/private/tmp/figure21-black-cancel-projection-search-bundle-20260715.tar.gz"), Path("/private/tmp/figure21-black-cancel-overnight-bundle-20260715.tar.gz")])
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--summary", type=Path, default=DEFAULT_SUMMARY)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    summary = package(args)
    rendered = json.dumps(summary, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
