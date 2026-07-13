"""Rank native-Morse singleton sectors from fusion-space boundary dimensions.

This performs no F/R evaluation.  It replays the Morse topology, removes
tensor-unit components exactly as the evaluator does, and estimates work from
the dimensions of ``Hom(1, tensor(active strand labels))`` at each event.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import UTC, datetime
from functools import lru_cache
from itertools import product
import json
import math
import os
from pathlib import Path
import platform
import random
import subprocess
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_registry import CATEGORY_CHOICES, build_category
from experiments.sage.morse_fusion_evaluator import (
    analyze_topology,
    prune_unit_components,
)
from experiments.scripts.morse_singleton_workload import (
    balanced_lpt_shards,
    file_sha256,
)


REPO_ROOT = Path(__file__).resolve().parents[2]


def command(argv):
    try:
        return subprocess.check_output(
            argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def cup_gap(order, form):
    if form.get("at") == "far-left":
        return 0
    if form.get("at") == "far-right":
        return len(order)
    if "between" in form:
        return order.index(form["between"][0]) + 1
    if "after" in form:
        return order.index(form["after"]) + 1
    raise ValueError(f"unsupported cup placement: {form!r}")


def event_active_orders(forms):
    order = []
    rows = []
    for form_index, form in enumerate(forms):
        kind = form["kind"]
        if kind == "cup":
            gap = cup_gap(order, form)
            piece = form["piece"]
            order[gap:gap] = [f"{piece}.left", f"{piece}.right"]
        elif kind == "cross":
            over, under = form["over"], form["under"]
            left, right = order.index(over), order.index(under)
            order[left], order[right] = order[right], order[left]
        elif kind == "cap":
            left, right = form["strands"]
            order = [strand for strand in order if strand not in {left, right}]
        elif kind != "kink":
            raise ValueError(f"unknown Morse form: {form!r}")
        rows.append((form_index, kind, tuple(order)))
    if order:
        raise ValueError("Morse replay did not close")
    return tuple(rows)


def labels_at_index(labels, component_count, sector_index):
    base = len(labels)
    digits = [0] * component_count
    value = int(sector_index)
    for position in range(component_count - 1, -1, -1):
        value, digit = divmod(value, base)
        digits[position] = digit
    return tuple(labels[digit] for digit in digits)


def sampled_sector_indices(base, component_count, sector_total, sample_count, seed):
    if sample_count >= sector_total:
        return list(range(sector_total))
    anchors = {0, sector_total - 1}
    repeated_place_value = sum(base**position for position in range(component_count))
    for digit in range(base):
        anchors.add(digit * repeated_place_value)
        for position in range(component_count):
            anchors.add(digit * base**position)
    generator = random.Random(seed)
    target = max(sample_count, len(anchors))
    while len(anchors) < target:
        anchors.add(generator.randrange(sector_total))
    return sorted(anchors)


def fusion_space_dimension_function(category):
    @lru_cache(maxsize=None)
    def dimension(labels):
        distribution = {category.unit: 1}
        for label in labels:
            updated = defaultdict(int)
            for left, left_count in distribution.items():
                for output, multiplicity in category.fusion_outputs(left, label):
                    updated[output] += left_count * int(multiplicity)
            distribution = dict(updated)
        return int(distribution.get(category.unit, 0))

    return dimension


def score_sector(
    category,
    forms,
    topology,
    component_labels,
    cost_profile,
    dimension,
    active_order_cache=None,
):
    retained = frozenset(
        component
        for component, label in component_labels.items()
        if label != category.unit
    )
    if not retained:
        return {
            "estimated_work": 1.0,
            "max_boundary_fusion_dimension": 1,
            "sum_boundary_fusion_dimension": 1,
            "sum_squared_boundary_fusion_dimension": 1,
            "effective_event_count": 0,
            "unit_pruned_component_count": len(component_labels),
        }
    if active_order_cache is not None and retained in active_order_cache:
        active_rows = active_order_cache[retained]
    else:
        effective_forms = prune_unit_components(forms, topology, retained)
        active_rows = event_active_orders(effective_forms)
        if active_order_cache is not None:
            active_order_cache[retained] = active_rows
    maximum = 1
    dimension_sum = 0
    squared_sum = 0
    estimated = 0.0
    kind_counts = defaultdict(int)
    for _, kind, active_order in active_rows:
        active_labels = []
        for strand in active_order:
            component = topology.component_by_strand[strand]
            label = component_labels[component]
            if topology.strand_orientation(strand) < 0:
                label = category.dual(label)
            active_labels.append(label)
        boundary_dimension = max(1, dimension(tuple(active_labels)))
        maximum = max(maximum, boundary_dimension)
        dimension_sum += boundary_dimension
        squared_sum += boundary_dimension * boundary_dimension
        kind_counts[kind] += 1
        if kind == "cross":
            event_cost = cost_profile["f"] + cost_profile["r"]
        elif kind == "cap":
            event_cost = cost_profile["f"]
        elif kind == "cup":
            event_cost = 0.25
        else:
            event_cost = 0.05
        estimated += event_cost * boundary_dimension * boundary_dimension
    return {
        "estimated_work": max(1.0, float(estimated)),
        "max_boundary_fusion_dimension": maximum,
        "sum_boundary_fusion_dimension": dimension_sum,
        "sum_squared_boundary_fusion_dimension": squared_sum,
        "effective_event_count": len(active_rows),
        "effective_event_kind_counts": dict(sorted(kind_counts.items())),
        "unit_pruned_component_count": len(component_labels) - len(retained),
    }


def write_jsonl(path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in rows)
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--category", choices=CATEGORY_CHOICES, required=True)
    parser.add_argument("--level", type=int)
    parser.add_argument("--shards", type=int, required=True)
    parser.add_argument("--shard-dir", type=Path, required=True)
    parser.add_argument("--ranking-output", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-sectors", type=int, default=1_000_000)
    parser.add_argument("--sample-count", type=int)
    parser.add_argument("--sample-seed", type=int, default=20260712)
    args = parser.parse_args()

    started = datetime.now(UTC)
    clock = time.perf_counter()
    input_payload = json.loads(args.input.read_text())
    forms = tuple(input_payload["forms"])
    topology = analyze_topology(forms)
    category, display_name, category_id = build_category(args.category, args.level)
    sector_total = len(category.labels) ** len(topology.component_order)
    if sector_total > args.max_sectors:
        raise ValueError(
            f"refusing to rank {sector_total} sectors; raise --max-sectors explicitly"
        )
    cost_profile = category.cost_profile()
    fusion_dimension = fusion_space_dimension_function(category)
    active_order_cache = {}
    if args.sample_count is not None and args.sample_count < 1:
        parser.error("--sample-count must be positive")
    sector_indices = sampled_sector_indices(
        len(category.labels),
        len(topology.component_order),
        sector_total,
        args.sample_count if args.sample_count is not None else sector_total,
        args.sample_seed,
    )
    rows = []
    for sector_index in sector_indices:
        labels = labels_at_index(
            category.labels, len(topology.component_order), sector_index
        )
        component_labels = dict(zip(topology.component_order, labels, strict=True))
        rows.append(
            {
                "sector_index": sector_index,
                "labels": list(labels),
                **score_sector(
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
    rows.sort(
        key=lambda row: (
            row["estimated_work"],
            row["max_boundary_fusion_dimension"],
            row["sector_index"],
        )
    )
    for rank, row in enumerate(rows):
        row["complexity_rank"] = rank
        row["complexity_quantile"] = (rank + 1) / len(rows)

    write_jsonl(args.ranking_output, rows)
    shards = balanced_lpt_shards(rows, args.shards, "estimated_work")
    args.shard_dir.mkdir(parents=True, exist_ok=True)
    shard_records = []
    for shard_index, shard in enumerate(shards):
        path = args.shard_dir / f"shard-{shard_index:04d}.jsonl"
        write_jsonl(path, shard["rows"])
        shard_records.append(
            {
                "shard_index": shard_index,
                "path": str(path),
                "sha256": file_sha256(path),
                "sector_count": len(shard["rows"]),
                "estimated_work": shard["estimated_work"],
                "min_complexity_rank": min(
                    row["complexity_rank"] for row in shard["rows"]
                ),
                "max_complexity_rank": max(
                    row["complexity_rank"] for row in shard["rows"]
                ),
            }
        )

    payload = {
        "schema": "twisted-yetter.native-morse-complexity-ranking.v1",
        "status": "pass",
        "mathematical_status": "HEURISTIC_RUNTIME_RANKING_NOT_AN_RT_EVALUATION",
        "generator_script": "experiments/sage/morse_complexity_rank.sage.py",
        "argv": sys.argv,
        "reproduce_command": "PYTHONPATH=. DOT_SAGE=\"$PWD/.sage\" sage --python "
        + " ".join(sys.argv),
        "input": str(args.input),
        "input_sha256": file_sha256(args.input),
        "input_status": input_payload.get("status"),
        "category": display_name,
        "category_id": category_id,
        "simple_count": len(category.labels),
        "component_order": list(topology.component_order),
        "sector_total": sector_total,
        "ranked_sector_count": len(rows),
        "sample": {
            "is_sample": len(rows) != sector_total,
            "requested_count": args.sample_count,
            "actual_count": len(rows),
            "seed": args.sample_seed,
            "anchors": "all-equal labels and one-position non-unit labels",
        },
        "category_cost_profile": cost_profile,
        "ranking_model": {
            "boundary_space": "dim Hom(1, tensor(active oriented strand labels))",
            "unit_pruning": "same tensor-unit component pruning as native evaluator",
            "event_cost": "boundary_dimension^2 times category mean F/R nonzero-entry cost",
            "warning": "heuristic scheduling score; not a proven runtime bound",
        },
        "ranking_output": str(args.ranking_output),
        "ranking_output_sha256": file_sha256(args.ranking_output),
        "shard_count": args.shards,
        "balanced_shards": shard_records,
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
        "elapsed_seconds": time.perf_counter() - clock,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(args.output.resolve())


if __name__ == "__main__":
    main()
