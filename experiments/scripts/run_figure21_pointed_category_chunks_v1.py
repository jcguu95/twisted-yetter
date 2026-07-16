#!/usr/bin/env python3
"""Run one pointed Figure 21 category as resumable sector chunks."""

from __future__ import annotations

import argparse
from collections import Counter
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
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    _complex_key,
    _labels_from_id,
    _load_figure21,
    _pointed_snapshots,
)
from experiments.scripts.special_dotted_morphism import stable_json_hash


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_WORK_ROOT = (
    REPO_ROOT / "experiments/results/akbulut-yasui/figure21-pointed-chunks-v1"
)


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


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


def _atomic_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _find_snapshot(realization_id: str) -> dict[str, Any]:
    for item in _pointed_snapshots():
        if item["realization_id"] == realization_id:
            return item
    raise ValueError(f"unknown pointed realization_id: {realization_id!r}")


def _chunk_bounds(total: int, chunk_count: int, chunk_id: int) -> tuple[int, int]:
    quotient, remainder = divmod(total, chunk_count)
    start = chunk_id * quotient + min(chunk_id, remainder)
    end = start + quotient + (1 if chunk_id < remainder else 0)
    return start, end


def _run_chunk(
    *,
    item: dict[str, Any],
    context: dict[str, Any],
    chunk_count: int,
    chunk_id: int,
    work_root: Path,
    worker_index: int | None,
    worker_count: int | None,
) -> dict[str, Any]:
    snapshot = item["payload"]
    category = SnapshotPointedModularCategory(snapshot)
    total = len(category.labels) ** len(context["ordinary"])
    start, end = _chunk_bounds(total, chunk_count, chunk_id)
    chunk_path = work_root / item["realization_id"] / f"chunk-{chunk_id:04d}.json"
    if chunk_path.exists():
        existing = json.loads(chunk_path.read_text())
        if (
            existing.get("snapshot_content_hash") == snapshot["content_hash"]
            and existing.get("chunk_count") == chunk_count
            and existing.get("start_sector_id") == start
            and existing.get("end_sector_id_exclusive") == end
        ):
            return existing
        raise ValueError(f"stale chunk exists: {chunk_path}")

    evaluator = PointedVacuumProjectorEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    value_distribution: Counter[str] = Counter()
    status_distribution: Counter[str] = Counter()
    rank_distribution: Counter[str] = Counter()
    started_at = datetime.now(UTC)
    started = time.perf_counter()
    for sector_id in range(start, end):
        labels_tuple = _labels_from_id(
            category.labels, sector_id, len(context["ordinary"])
        )
        labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
        value, stats = evaluator.fixed_label_value(context["graph"], labels)
        value_distribution[_complex_key(value)] += 1
        status_distribution[stats["status"]] += 1
        rank_distribution[str(stats["projector_rank"])] += 1
    payload = {
        "schema": "twisted-yetter.figure21-pointed-category-chunk.v1",
        "status": "PASS_CHUNK_COMPLETE",
        "realization_id": item["realization_id"],
        "family_id": snapshot["family_id"],
        "rank": item["rank"],
        "snapshot_content_hash": snapshot["content_hash"],
        "category_data_hash": snapshot["category_data_hash"],
        "chunk_id": chunk_id,
        "chunk_count": chunk_count,
        "start_sector_id": start,
        "end_sector_id_exclusive": end,
        "sector_count": end - start,
        "full_sector_count": total,
        "started_at_utc": started_at.isoformat(),
        "finished_at_utc": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - started,
        "worker_index": worker_index,
        "worker_count": worker_count,
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "figure21_projected_ir_hash": stable_json_hash(context["ir"]),
        "figure21_coupon_graph_hash": context["graph"]["graph_hash"],
        "value_distribution": dict(sorted(value_distribution.items())),
        "status_distribution": dict(sorted(status_distribution.items())),
        "projector_rank_distribution": dict(sorted(rank_distribution.items())),
    }
    payload["content_sha256"] = _sha256_bytes(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    )
    _atomic_json(chunk_path, payload)
    return payload


def _aggregate(
    *,
    item: dict[str, Any],
    chunk_count: int,
    work_root: Path,
) -> dict[str, Any] | None:
    chunk_dir = work_root / item["realization_id"]
    chunks = []
    for chunk_id in range(chunk_count):
        path = chunk_dir / f"chunk-{chunk_id:04d}.json"
        if not path.exists():
            return None
        chunks.append(json.loads(path.read_text()))
    value_distribution: Counter[str] = Counter()
    status_distribution: Counter[str] = Counter()
    rank_distribution: Counter[str] = Counter()
    for chunk in chunks:
        value_distribution.update(chunk["value_distribution"])
        status_distribution.update(chunk["status_distribution"])
        rank_distribution.update(chunk["projector_rank_distribution"])
    expected = chunks[0]["full_sector_count"]
    observed = sum(chunk["sector_count"] for chunk in chunks)
    status = "PASS_AGGREGATE_COMPLETE" if observed == expected else "INCOMPLETE"
    payload = {
        "schema": "twisted-yetter.figure21-pointed-category-aggregate.v1",
        "status": status,
        "realization_id": item["realization_id"],
        "family_id": chunks[0]["family_id"],
        "rank": chunks[0]["rank"],
        "snapshot_content_hash": chunks[0]["snapshot_content_hash"],
        "category_data_hash": chunks[0]["category_data_hash"],
        "chunk_count": chunk_count,
        "expected_sector_count": expected,
        "observed_sector_count": observed,
        "elapsed_worker_seconds": sum(chunk["elapsed_seconds"] for chunk in chunks),
        "value_distribution": dict(sorted(value_distribution.items())),
        "status_distribution": dict(sorted(status_distribution.items())),
        "projector_rank_distribution": dict(sorted(rank_distribution.items())),
        "chunk_hashes": [chunk["content_sha256"] for chunk in chunks],
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "claim_boundary": "Complete fixed-label Figure 21 pointed category aggregate; not an exotic-vs-standard H2-character comparison.",
    }
    payload["content_sha256"] = _sha256_bytes(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    )
    _atomic_json(chunk_dir / "aggregate.json", payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--realization-id", required=True)
    parser.add_argument("--chunk-count", type=int, default=20)
    parser.add_argument("--chunk-id", type=int, default=None)
    parser.add_argument("--worker-index", type=int, default=None)
    parser.add_argument("--worker-count", type=int, default=None)
    parser.add_argument("--max-chunks", type=int, default=None)
    parser.add_argument("--aggregate-only", action="store_true")
    parser.add_argument("--no-aggregate", action="store_true")
    parser.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    args = parser.parse_args()
    if args.chunk_count < 1:
        parser.error("--chunk-count must be positive")
    if args.chunk_id is not None and not (0 <= args.chunk_id < args.chunk_count):
        parser.error("--chunk-id must be in [0, --chunk-count)")
    if (args.worker_index is None) != (args.worker_count is None):
        parser.error("--worker-index and --worker-count must be supplied together")
    if args.worker_count is not None:
        if args.worker_count < 1:
            parser.error("--worker-count must be positive")
        if not (0 <= args.worker_index < args.worker_count):
            parser.error("--worker-index must be in [0, --worker-count)")
        if args.chunk_id is not None:
            parser.error("--chunk-id cannot be combined with worker sharding")
    if args.aggregate_only and (
        args.chunk_id is not None
        or args.worker_index is not None
        or args.max_chunks is not None
        or args.no_aggregate
    ):
        parser.error("--aggregate-only cannot be combined with chunk execution arguments")
    item = _find_snapshot(args.realization_id)
    if args.aggregate_only:
        aggregate = _aggregate(
            item=item, chunk_count=args.chunk_count, work_root=args.work_root
        )
        if aggregate is None:
            raise SystemExit("aggregate incomplete: one or more chunks are missing")
        print(
            json.dumps(
                {
                    "aggregate": str(
                        _display_path(
                            args.work_root
                            / item["realization_id"]
                            / "aggregate.json"
                        )
                    ),
                    "status": aggregate["status"],
                    "observed_sector_count": aggregate["observed_sector_count"],
                    "elapsed_worker_seconds": aggregate["elapsed_worker_seconds"],
                },
                sort_keys=True,
            ),
            flush=True,
        )
        return
    context = _load_figure21()
    if args.chunk_id is not None:
        chunk_ids = [args.chunk_id]
    else:
        chunk_ids = list(range(args.chunk_count))
        if args.worker_count is not None:
            chunk_ids = [
                chunk_id
                for chunk_id in chunk_ids
                if chunk_id % args.worker_count == args.worker_index
            ]
        if args.max_chunks is not None:
            chunk_ids = chunk_ids[: args.max_chunks]
    for chunk_id in chunk_ids:
        payload = _run_chunk(
            item=item,
            context=context,
            chunk_count=args.chunk_count,
            chunk_id=chunk_id,
            work_root=args.work_root,
            worker_index=args.worker_index,
            worker_count=args.worker_count,
        )
        print(
            json.dumps(
                {
                    "realization_id": payload["realization_id"],
                    "chunk_id": payload["chunk_id"],
                    "sector_count": payload["sector_count"],
                    "elapsed_seconds": payload["elapsed_seconds"],
                    "status": payload["status"],
                    "projector_rank_distribution": payload[
                        "projector_rank_distribution"
                    ],
                },
                sort_keys=True,
            ),
            flush=True,
        )
    if args.no_aggregate:
        return
    aggregate = _aggregate(item=item, chunk_count=args.chunk_count, work_root=args.work_root)
    if aggregate is not None:
        print(
            json.dumps(
                {
                    "aggregate": str(
                        _display_path(
                            args.work_root
                            / item["realization_id"]
                            / "aggregate.json"
                        )
                    ),
                    "status": aggregate["status"],
                    "observed_sector_count": aggregate["observed_sector_count"],
                    "elapsed_worker_seconds": aggregate["elapsed_worker_seconds"],
                },
                sort_keys=True,
            ),
            flush=True,
        )


if __name__ == "__main__":
    main()
