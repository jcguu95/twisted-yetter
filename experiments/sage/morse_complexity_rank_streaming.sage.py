"""Memory-bounded full ranking and LPT sharding for large Morse workloads."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import heapq
import importlib.util
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_registry import CATEGORY_CHOICES, build_category
from experiments.sage.morse_fusion_evaluator import analyze_topology
from experiments.scripts.morse_singleton_workload import (
    atomic_write_json,
    canonical_json_bytes,
    file_sha256,
    payload_sha256,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
RANKER_PATH = REPO_ROOT / "experiments" / "sage" / "morse_complexity_rank.sage.py"


def load_ranker():
    spec = importlib.util.spec_from_file_location("native_morse_ranker_shared", RANKER_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def command(argv):
    try:
        return subprocess.check_output(
            argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def iter_jsonl(path):
    with path.open() as handle:
        for line_number, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            try:
                yield json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"bad JSONL row at {path}:{line_number}") from error


def descending_key(row):
    return (
        -float(row["estimated_work"]),
        -int(row["max_boundary_fusion_dimension"]),
        -int(row["sector_index"]),
    )


def write_score_chunk(path, rows):
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("wb") as handle:
        for row in rows:
            handle.write(canonical_json_bytes(row) + b"\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", choices=CATEGORY_CHOICES, required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--shards", type=int, required=True)
    parser.add_argument("--chunk-size", type=int, default=20_000)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--shard-dir", type=Path, required=True)
    parser.add_argument("--quantile-output", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    if args.shards < 1 or args.chunk_size < 1:
        parser.error("--shards and --chunk-size must be positive")

    started = datetime.now(UTC)
    clock = time.perf_counter()
    ranker = load_ranker()
    input_payload = json.loads(args.input.read_text())
    forms = tuple(input_payload["forms"])
    topology = analyze_topology(forms)
    category, display_name, category_id = build_category(args.category, args.level)
    sector_total = len(category.labels) ** len(topology.component_order)
    identity = {
        "schema": "twisted-yetter.native-morse-streaming-ranking-identity.v1",
        "input_sha256": file_sha256(args.input),
        "category_id": category_id,
        "level": args.level,
        "component_order": list(topology.component_order),
        "simple_labels": list(category.labels),
        "sector_total": sector_total,
        "chunk_size": args.chunk_size,
        "ranking_model_script_sha256": file_sha256(RANKER_PATH),
    }
    identity_sha256 = payload_sha256(identity)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    context_path = args.work_dir / "ranking-context.json"
    if context_path.exists():
        context = json.loads(context_path.read_text())
        if context.get("identity_sha256") != identity_sha256:
            raise ValueError("streaming ranking work directory identity mismatch")
        if not args.resume:
            raise ValueError("ranking work directory exists; pass --resume to reuse it")
    else:
        atomic_write_json(
            context_path,
            {
                "schema": "twisted-yetter.native-morse-streaming-ranking-context.v1",
                "status": "running",
                "identity": identity,
                "identity_sha256": identity_sha256,
                "utc_start": started.isoformat(),
            },
        )

    cost_profile = category.cost_profile()
    fusion_dimension = ranker.fusion_space_dimension_function(category)
    active_order_cache = {}
    chunk_records = []
    score_clock = time.perf_counter()
    for start in range(0, sector_total, args.chunk_size):
        stop = min(start + args.chunk_size, sector_total)
        path = args.work_dir / f"score-{start:012d}-{stop:012d}.jsonl"
        if args.resume and path.exists():
            rows = None
        else:
            rows = []
            for sector_index in range(start, stop):
                labels = ranker.labels_at_index(
                    category.labels, len(topology.component_order), sector_index
                )
                component_labels = dict(
                    zip(topology.component_order, labels, strict=True)
                )
                rows.append(
                    {
                        "sector_index": sector_index,
                        "labels": list(labels),
                        **ranker.score_sector(
                            category,
                            forms,
                            topology,
                            component_labels,
                            cost_profile,
                            fusion_dimension,
                            active_order_cache,
                        ),
                    }
                )
            rows.sort(key=descending_key)
            write_score_chunk(path, rows)
        chunk_records.append(
            {
                "start": start,
                "stop": stop,
                "path": str(path),
                "sha256": file_sha256(path),
            }
        )
        atomic_write_json(
            args.work_dir / "ranking-progress.json",
            {
                "schema": "twisted-yetter.native-morse-streaming-ranking-progress.v1",
                "status": "scoring",
                "identity_sha256": identity_sha256,
                "completed_sector_count": stop,
                "sector_total": sector_total,
                "completed_chunk_count": len(chunk_records),
                "elapsed_seconds": time.perf_counter() - score_clock,
                "updated_at_utc": datetime.now(UTC).isoformat(),
            },
        )

    merge_clock = time.perf_counter()
    args.shard_dir.mkdir(parents=True, exist_ok=True)
    shard_paths = [args.shard_dir / f"shard-{index:04d}.jsonl" for index in range(args.shards)]
    temporary_paths = [path.with_suffix(path.suffix + ".tmp") for path in shard_paths]
    handles = [path.open("wb") for path in temporary_paths]
    shard_loads = [0.0] * args.shards
    shard_counts = [0] * args.shards
    shard_heap = [(0.0, 0, index) for index in range(args.shards)]
    heapq.heapify(shard_heap)
    quantile_positions = {
        round(position * (sector_total - 1) / 100): position / 100
        for position in range(101)
    }
    quantile_rows = []
    dimension_counts = Counter()
    merged = heapq.merge(
        *(iter_jsonl(Path(row["path"])) for row in chunk_records),
        key=descending_key,
    )
    for descending_position, row in enumerate(merged):
        rank = sector_total - 1 - descending_position
        row["complexity_rank"] = rank
        row["complexity_quantile"] = (rank + 1) / sector_total
        load, count, shard_index = heapq.heappop(shard_heap)
        handles[shard_index].write(canonical_json_bytes(row) + b"\n")
        weight = float(row["estimated_work"])
        shard_loads[shard_index] += weight
        shard_counts[shard_index] += 1
        heapq.heappush(
            shard_heap,
            (load + weight, count + 1, shard_index),
        )
        dimension_counts[int(row["max_boundary_fusion_dimension"])] += 1
        if descending_position in quantile_positions:
            quantile_rows.append(
                {
                    "descending_position": descending_position,
                    "requested_upper_tail_quantile": quantile_positions[
                        descending_position
                    ],
                    **row,
                }
            )

    for handle in handles:
        handle.flush()
        os.fsync(handle.fileno())
        handle.close()
    for temporary, final in zip(temporary_paths, shard_paths, strict=True):
        os.replace(temporary, final)
    args.quantile_output.parent.mkdir(parents=True, exist_ok=True)
    args.quantile_output.write_text(
        "".join(
            json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
            for row in sorted(quantile_rows, key=lambda item: item["complexity_rank"])
        )
    )
    shard_records = [
        {
            "shard_index": index,
            "path": str(path),
            "sha256": file_sha256(path),
            "sector_count": shard_counts[index],
            "estimated_work": shard_loads[index],
        }
        for index, path in enumerate(shard_paths)
    ]
    payload = {
        "schema": "twisted-yetter.native-morse-streaming-complexity-ranking.v1",
        "status": "pass",
        "mathematical_status": "HEURISTIC_RUNTIME_RANKING_NOT_AN_RT_EVALUATION",
        "generator_script": "experiments/sage/morse_complexity_rank_streaming.sage.py",
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python "
        + " ".join(sys.argv),
        "identity": identity,
        "identity_sha256": identity_sha256,
        "input_status": input_payload.get("status"),
        "category": display_name,
        "category_cost_profile": cost_profile,
        "score_chunks": chunk_records,
        "shards": shard_records,
        "quantile_output": str(args.quantile_output),
        "quantile_output_sha256": file_sha256(args.quantile_output),
        "max_boundary_dimension_counts": [
            {"dimension": dimension, "count": count}
            for dimension, count in sorted(dimension_counts.items())
        ],
        "timing": {
            "scoring_seconds": merge_clock - score_clock,
            "merge_and_shard_seconds": time.perf_counter() - merge_clock,
            "total_seconds": time.perf_counter() - clock,
        },
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": command(["git", "rev-parse", "HEAD"]),
            "git_dirty": bool(command(["git", "status", "--short"])),
        },
        "environment": {
            "hostname": platform.node(),
            "platform": platform.platform(),
            "cpu_count": os.cpu_count(),
            "sage": SAGE_VERSION,
            "python": sys.version,
        },
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
    }
    atomic_write_json(args.output, payload)
    print(args.output.resolve())


if __name__ == "__main__":
    main()
