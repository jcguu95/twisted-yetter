#!/usr/bin/env python3
"""Rank pointed Figure 21 workloads and time hard samples per decile."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any

from experiments.sage.pointed_premodular_categories import (
    SnapshotPointedModularCategory,
)
from experiments.sage.ribbon_graph_evaluator import (
    PointedVacuumProjectorEvaluator,
)
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    OUTPUT as PREFIX_SWEEP_OUTPUT,
    _complex_key,
    _labels_from_id,
    _load_figure21,
    _pointed_snapshots,
)
from experiments.scripts.special_dotted_morphism import piece_of, stable_json_hash


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-pointed-runtime-ladder-v1.json"
)


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _load_previous_sweep() -> dict[str, Any]:
    if not PREFIX_SWEEP_OUTPUT.exists():
        return {}
    return json.loads(PREFIX_SWEEP_OUTPUT.read_text())


def _component_by_strand(context: dict[str, Any], strand: str) -> str:
    return context["source"]["component_by_piece"][piece_of(strand)]


def _sector_topology_cost(
    context: dict[str, Any],
    ordinary: tuple[str, ...],
    labels_tuple: tuple[Any, ...],
    unit: Any,
) -> int:
    active = {
        component
        for component, label in zip(ordinary, labels_tuple, strict=True)
        if str(label) != str(unit)
    }
    cost = 1 + len(active)
    for form in context["forms"]:
        kind = form.get("kind")
        if kind == "cross":
            over = _component_by_strand(context, form["over"])
            under = _component_by_strand(context, form["under"])
            if over in active and under in active:
                cost += 3
        elif kind == "kink":
            component = _component_by_strand(context, form["strand"])
            if component in active:
                cost += abs(int(form.get("times", 1)))
    return cost


def _candidate_ids(start: int, end: int, *, exact_limit: int, sample_count: int) -> list[int]:
    length = end - start
    if length <= 0:
        return []
    if length <= exact_limit:
        return list(range(start, end))
    ids = {start, end - 1}
    denominator = max(1, sample_count - 1)
    for index in range(sample_count):
        ids.add(start + ((length - 1) * index) // denominator)
    return sorted(ids)


def _hard_sector_for_bin(
    *,
    category: SnapshotPointedModularCategory,
    context: dict[str, Any],
    start: int,
    end: int,
    exact_limit: int,
    sample_count: int,
) -> dict[str, Any]:
    best_id = None
    best_labels = None
    best_cost = -1
    method = "EXACT_BIN_SCAN" if end - start <= exact_limit else "SAMPLED_BIN_SCAN"
    candidates = _candidate_ids(
        start,
        end,
        exact_limit=exact_limit,
        sample_count=sample_count,
    )
    for sector_id in candidates:
        labels_tuple = _labels_from_id(
            category.labels, sector_id, len(context["ordinary"])
        )
        cost = _sector_topology_cost(
            context, context["ordinary"], labels_tuple, category.unit
        )
        if cost > best_cost:
            best_id = sector_id
            best_labels = labels_tuple
            best_cost = cost
    if best_id is None or best_labels is None:
        raise ValueError("empty bin")
    return {
        "sector_id": best_id,
        "labels_tuple": best_labels,
        "estimated_topology_cost": best_cost,
        "selection_method": method,
        "candidate_count": len(candidates),
    }


def _time_sector(
    evaluator: PointedVacuumProjectorEvaluator,
    context: dict[str, Any],
    labels_tuple: tuple[Any, ...],
) -> dict[str, Any]:
    labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
    started = time.perf_counter()
    value, stats = evaluator.fixed_label_value(context["graph"], labels)
    elapsed = time.perf_counter() - started
    return {
        "elapsed_seconds": elapsed,
        "value_key": _complex_key(value),
        "status": stats["status"],
        "projector_rank": stats["projector_rank"],
    }


def _rank5_vacuum_probe_ids(total: int, limit: int) -> list[int]:
    if total <= 0 or limit <= 0:
        return []
    ids = [0]
    # 104729 is coprime to 5^n, so it walks rank-5 sector ids without getting
    # trapped in a small residue class.
    for attempt in range(1, limit):
        ids.append((17 + attempt * 104_729) % total)
    return ids


def _rank5_vacuum_aware_estimate(
    *,
    category: SnapshotPointedModularCategory,
    context: dict[str, Any],
    evaluator: PointedVacuumProjectorEvaluator,
    total: int,
    bins: list[dict[str, Any]],
    sample_count: int,
    search_limit: int,
) -> dict[str, Any]:
    samples = []
    attempts = 0
    seen: set[int] = set()
    for sector_id in _rank5_vacuum_probe_ids(total, search_limit):
        if sector_id in seen:
            continue
        seen.add(sector_id)
        attempts += 1
        labels_tuple = _labels_from_id(
            category.labels, sector_id, len(context["ordinary"])
        )
        timed = _time_sector(evaluator, context, labels_tuple)
        if int(timed["projector_rank"]) != 1:
            continue
        samples.append(
            {
                "sector_id": sector_id,
                "selected_labels": {
                    component: str(label)
                    for component, label in zip(
                        context["ordinary"], labels_tuple, strict=True
                    )
                },
                **timed,
            }
        )
        if len(samples) >= sample_count:
            break

    pruned_elapsed = [
        float(item["elapsed_seconds"])
        for item in bins
        if int(item.get("projector_rank", -1)) == 0
    ]
    vacuum_elapsed = [float(item["elapsed_seconds"]) for item in samples]
    if not samples or not pruned_elapsed:
        return {
            "status": "BLOCKED_RANK5_VACUUM_AWARE_TIMING_INCOMPLETE",
            "requested_vacuum_sample_count": sample_count,
            "search_limit": search_limit,
            "search_attempt_count": attempts,
            "vacuum_sample_count": len(samples),
            "pruned_hard_sample_count": len(pruned_elapsed),
            "samples": samples,
            "reason": (
                "rank5 paid-batch planning requires at least one projector-rank-1 "
                "sector and at least one projector-rank-0 hard sample."
            ),
        }

    vacuum_fraction = 1.0 / float(len(category.labels))
    mean_vacuum = sum(vacuum_elapsed) / len(vacuum_elapsed)
    max_vacuum = max(vacuum_elapsed)
    mean_pruned = sum(pruned_elapsed) / len(pruned_elapsed)
    max_pruned = max(pruned_elapsed)
    weighted_mean = total * (
        vacuum_fraction * mean_vacuum
        + (1.0 - vacuum_fraction) * mean_pruned
    )
    weighted_max_observed_classes = total * (
        vacuum_fraction * max_vacuum
        + (1.0 - vacuum_fraction) * max_pruned
    )
    return {
        "status": "PASS_RANK5_VACUUM_AWARE_TIMING",
        "requested_vacuum_sample_count": sample_count,
        "search_limit": search_limit,
        "search_attempt_count": attempts,
        "vacuum_sample_count": len(samples),
        "pruned_hard_sample_count": len(pruned_elapsed),
        "estimated_vacuum_sector_fraction": vacuum_fraction,
        "vacuum_fraction_assumption": (
            "pointed fixed-label sectors are weighted by one universal-group "
            "constraint, so projector-rank-1 sectors are estimated at 1/|G|"
        ),
        "mean_vacuum_sample_seconds": mean_vacuum,
        "max_vacuum_sample_seconds": max_vacuum,
        "mean_pruned_hard_sample_seconds": mean_pruned,
        "max_pruned_hard_sample_seconds": max_pruned,
        "estimated_total_seconds_vacuum_aware_mean": weighted_mean,
        "estimated_total_seconds_vacuum_aware_max_observed_classes": (
            weighted_max_observed_classes
        ),
        "samples": samples,
    }


def _previous_status_by_realization(previous: dict[str, Any]) -> dict[str, str]:
    rows = previous.get("rows", [])
    return {
        row.get("realization_id"): row.get("figure21_right", {}).get("status")
        for row in rows
    }


def _estimate_row(
    *,
    item: dict[str, Any],
    context: dict[str, Any],
    previous_status: str | None,
    exact_limit: int,
    sample_count: int,
    rank5_vacuum_sample_count: int,
    rank5_vacuum_search_limit: int,
) -> dict[str, Any]:
    snapshot = item["payload"]
    category = SnapshotPointedModularCategory(snapshot)
    total = len(category.labels) ** len(context["ordinary"])
    if previous_status == "FAILED_MODULAR_CROSS_CHECK":
        return {
            "realization_id": item["realization_id"],
            "family_id": snapshot["family_id"],
            "rank": item["rank"],
            "status": "BLOCKED_PREVIOUS_MODULAR_CROSS_CHECK_FAILED",
            "full_sector_count": total,
            "reason": "Do not estimate formal Figure 21 workload for a row whose modular-vs-pointed check failed closed.",
        }
    if previous_status == "FULL":
        return {
            "realization_id": item["realization_id"],
            "family_id": snapshot["family_id"],
            "rank": item["rank"],
            "status": "ALREADY_COMPLETE_IN_PREFIX_SWEEP_ARTIFACT",
            "full_sector_count": total,
            "previous_artifact": str(PREFIX_SWEEP_OUTPUT.relative_to(REPO_ROOT)),
        }
    evaluator = PointedVacuumProjectorEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    bins = []
    elapsed_values = []
    rank_distribution: Counter[str] = Counter()
    status_distribution: Counter[str] = Counter()
    quotient, remainder = divmod(total, 10)
    for bin_id in range(10):
        start = bin_id * quotient + min(bin_id, remainder)
        end = start + quotient + (1 if bin_id < remainder else 0)
        hard = _hard_sector_for_bin(
            category=category,
            context=context,
            start=start,
            end=end,
            exact_limit=exact_limit,
            sample_count=sample_count,
        )
        timed = _time_sector(evaluator, context, hard["labels_tuple"])
        elapsed_values.append(timed["elapsed_seconds"])
        rank_distribution[str(timed["projector_rank"])] += 1
        status_distribution[timed["status"]] += 1
        bins.append(
            {
                "bin_id": bin_id,
                "start_sector_id": start,
                "end_sector_id_exclusive": end,
                "selected_sector_id": hard["sector_id"],
                "selected_labels": {
                    component: str(label)
                    for component, label in zip(
                        context["ordinary"], hard["labels_tuple"], strict=True
                    )
                },
                "estimated_topology_cost": hard["estimated_topology_cost"],
                "selection_method": hard["selection_method"],
                "selection_candidate_count": hard["candidate_count"],
                **timed,
            }
        )
    mean_elapsed = sum(elapsed_values) / len(elapsed_values)
    max_elapsed = max(elapsed_values)
    row = {
        "realization_id": item["realization_id"],
        "family_id": snapshot["family_id"],
        "rank": item["rank"],
        "status": "RUNTIME_LADDER_ESTIMATED_FROM_HARD_DECILE_SAMPLES",
        "full_sector_count": total,
        "decile_sample_count": len(bins),
        "mean_hard_sample_seconds": mean_elapsed,
        "max_hard_sample_seconds": max_elapsed,
        "estimated_total_seconds_mean_hard_samples": mean_elapsed * total,
        "estimated_total_seconds_max_hard_samples": max_elapsed * total,
        "projector_rank_distribution_on_samples": dict(sorted(rank_distribution.items())),
        "status_distribution_on_samples": dict(sorted(status_distribution.items())),
        "bins": bins,
    }
    if int(item["rank"]) == 5:
        vacuum_aware = _rank5_vacuum_aware_estimate(
            category=category,
            context=context,
            evaluator=evaluator,
            total=total,
            bins=bins,
            sample_count=rank5_vacuum_sample_count,
            search_limit=rank5_vacuum_search_limit,
        )
        row["vacuum_aware_estimate"] = vacuum_aware
        if vacuum_aware["status"] == "PASS_RANK5_VACUUM_AWARE_TIMING":
            row["estimated_total_seconds_vacuum_aware_mean"] = vacuum_aware[
                "estimated_total_seconds_vacuum_aware_mean"
            ]
            row["estimated_total_seconds_vacuum_aware_max_observed_classes"] = (
                vacuum_aware[
                    "estimated_total_seconds_vacuum_aware_max_observed_classes"
                ]
            )
    return row


def generate(
    *,
    exact_limit: int,
    sample_count: int,
    rank5_vacuum_sample_count: int,
    rank5_vacuum_search_limit: int,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    context = _load_figure21()
    previous = _load_previous_sweep()
    previous_status = _previous_status_by_realization(previous)
    rows = []
    for item in _pointed_snapshots():
        rows.append(
            _estimate_row(
                item=item,
                context=context,
                previous_status=previous_status.get(item["realization_id"]),
                exact_limit=exact_limit,
                sample_count=sample_count,
                rank5_vacuum_sample_count=rank5_vacuum_sample_count,
                rank5_vacuum_search_limit=rank5_vacuum_search_limit,
            )
        )
    runnable = [
        row
        for row in rows
        if row["status"] == "RUNTIME_LADDER_ESTIMATED_FROM_HARD_DECILE_SAMPLES"
    ]
    ranking = sorted(
        rows,
        key=lambda row: (
            row["status"] != "ALREADY_COMPLETE_IN_PREFIX_SWEEP_ARTIFACT",
            row["status"] == "BLOCKED_PREVIOUS_MODULAR_CROSS_CHECK_FAILED",
            row["full_sector_count"],
            row["realization_id"],
        ),
    )
    finished = datetime.now(UTC)
    return {
        "schema": "twisted-yetter.figure21-pointed-runtime-ladder.v1",
        "status": "PASS_RUNTIME_LADDER_ESTIMATE_BUILT",
        "mathematical_status": "RUNTIME_PLANNING_ARTIFACT_NOT_SCAN_RESULT",
        "generator_script": "experiments/scripts/estimate_figure21_pointed_runtime_ladder_v1.py",
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "figure21_projected_ir_hash": stable_json_hash(context["ir"]),
            "figure21_coupon_graph_hash": context["graph"]["graph_hash"],
            "previous_prefix_sweep": (
                str(PREFIX_SWEEP_OUTPUT.relative_to(REPO_ROOT))
                if PREFIX_SWEEP_OUTPUT.exists()
                else None
            ),
        },
        "method": {
            "ranking": "already-complete first, then runnable small-to-large full sector count, failed cross-check rows last",
            "decile_sampling": "split sector ids into 10 consecutive bins and time the highest estimated-topology-cost sampled sector per bin",
            "exact_bin_scan_limit": exact_limit,
            "large_bin_sample_count": sample_count,
            "estimate_is_conservative": "uses hard decile samples, not random average sectors",
            "rank5_vacuum_aware_timing": (
                "rank-5 paid-batch rows additionally time projector-rank-1 "
                "sectors and record a separate vacuum-aware estimate"
            ),
            "rank5_vacuum_sample_count": rank5_vacuum_sample_count,
            "rank5_vacuum_search_limit": rank5_vacuum_search_limit,
        },
        "row_count": len(rows),
        "already_complete_count": sum(
            row["status"] == "ALREADY_COMPLETE_IN_PREFIX_SWEEP_ARTIFACT"
            for row in rows
        ),
        "blocked_count": sum(
            row["status"] == "BLOCKED_PREVIOUS_MODULAR_CROSS_CHECK_FAILED"
            for row in rows
        ),
        "estimated_count": len(runnable),
        "ranking": [
            {
                "rank_order": index,
                "realization_id": row["realization_id"],
                "family_id": row["family_id"],
                "rank": row["rank"],
                "status": row["status"],
                "full_sector_count": row["full_sector_count"],
                "estimated_total_seconds_mean_hard_samples": row.get(
                    "estimated_total_seconds_mean_hard_samples"
                ),
                "estimated_total_seconds_max_hard_samples": row.get(
                    "estimated_total_seconds_max_hard_samples"
                ),
                "estimated_total_seconds_vacuum_aware_mean": row.get(
                    "estimated_total_seconds_vacuum_aware_mean"
                ),
                "estimated_total_seconds_vacuum_aware_max_observed_classes": row.get(
                    "estimated_total_seconds_vacuum_aware_max_observed_classes"
                ),
            }
            for index, row in enumerate(ranking)
        ],
        "rows": rows,
        "claim_boundary": "This is a runtime estimate and ordering artifact, not a completed Figure 21 scan.",
        "non_claims": [
            "Does not claim unmeasured sectors are complete.",
            "Does not resolve rows with failed modular-vs-pointed checks.",
            "Does not compare Figure 21 to the standard side by an H2 coordinate map.",
            "Does not make an exoticness claim."
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--exact-bin-scan-limit", type=int, default=50_000)
    parser.add_argument("--large-bin-sample-count", type=int, default=1024)
    parser.add_argument("--rank5-vacuum-sample-count", type=int, default=10)
    parser.add_argument("--rank5-vacuum-search-limit", type=int, default=5000)
    args = parser.parse_args()
    result = generate(
        exact_limit=args.exact_bin_scan_limit,
        sample_count=args.large_bin_sample_count,
        rank5_vacuum_sample_count=args.rank5_vacuum_sample_count,
        rank5_vacuum_search_limit=args.rank5_vacuum_search_limit,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
