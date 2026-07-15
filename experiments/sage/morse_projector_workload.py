"""Semantic, geometry-independent sharding for vacuum-projector paths."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
import math
from typing import Any

from experiments.scripts.special_dotted_morphism import stable_json_hash


SCHEMA = "twisted-yetter.vacuum-projector-path-workload.v1"
BASIS_CONVENTION = "ORDERED_PUNCTURE_WORD_CANONICAL_RIGHT_COMB_PATH_BASIS"


def balanced_path_ranges(path_basis_rank: int, shard_count: int) -> tuple[tuple[int, int], ...]:
    """Partition ``range(path_basis_rank)`` into deterministic contiguous shards."""

    path_basis_rank = int(path_basis_rank)
    shard_count = int(shard_count)
    if path_basis_rank < 0:
        raise ValueError("path basis rank must be nonnegative")
    if shard_count < 1:
        raise ValueError("shard count must be positive")
    quotient, remainder = divmod(path_basis_rank, shard_count)
    ranges = []
    start = 0
    for shard_index in range(shard_count):
        size = quotient + int(shard_index < remainder)
        stop = start + size
        ranges.append((start, stop))
        start = stop
    if start != path_basis_rank:
        raise AssertionError("path ranges do not cover the requested basis")
    return tuple(ranges)


def build_projector_path_workload(
    *,
    category_id: str,
    category_projector_data_hash: str,
    sector_labels: Mapping[str, Any],
    component_order: Iterable[str],
    projector_id: str,
    ordered_puncture_word: Iterable[Mapping[str, Any]],
    path_basis_rank: int,
    shard_count: int,
) -> dict[str, Any]:
    """Build a workload that survives crossing and Morse-layer optimization."""

    component_order = tuple(component_order)
    if set(component_order) != set(sector_labels):
        raise ValueError("component order does not exactly cover sector labels")
    punctures = tuple(dict(factor) for factor in ordered_puncture_word)
    required = {"cut_id", "component", "variance", "oriented_label"}
    for factor in punctures:
        missing = required - set(factor)
        if missing:
            raise ValueError(f"puncture factor is missing fields: {sorted(missing)!r}")
        if factor["component"] not in sector_labels:
            raise ValueError(f"unknown puncture component: {factor['component']!r}")
        if factor["variance"] not in {"label", "dual"}:
            raise ValueError(f"unknown puncture variance: {factor['variance']!r}")

    semantic_identity = {
        "category_id": category_id,
        "category_projector_data_hash": category_projector_data_hash,
        "component_order": list(component_order),
        "sector_labels": {component: sector_labels[component] for component in component_order},
        "projector_id": projector_id,
        "basis_convention": BASIS_CONVENTION,
        "ordered_puncture_word": list(punctures),
        "path_basis_rank": int(path_basis_rank),
    }
    semantic_hash = stable_json_hash(semantic_identity)
    shards = []
    for shard_index, (start, stop) in enumerate(
        balanced_path_ranges(path_basis_rank, shard_count)
    ):
        term_identity = {
            "semantic_workload_hash": semantic_hash,
            "path_start": start,
            "path_stop": stop,
        }
        shards.append(
            {
                "shard_index": shard_index,
                "path_start": start,
                "path_stop": stop,
                "path_count": stop - start,
                "semantic_term_hash": stable_json_hash(term_identity),
            }
        )
    payload = {
        "schema": SCHEMA,
        "status": "READY_SEMANTIC_PROJECTOR_PATH_WORKLOAD",
        "semantic_identity": semantic_identity,
        "semantic_workload_hash": semantic_hash,
        "shard_count": len(shards),
        "shards": shards,
    }
    validate_projector_path_workload(payload)
    return payload


def validate_projector_path_workload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema") != SCHEMA:
        raise ValueError("unsupported projector path workload schema")
    identity = payload["semantic_identity"]
    if stable_json_hash(identity) != payload.get("semantic_workload_hash"):
        raise ValueError("semantic projector workload hash mismatch")
    rank = int(identity["path_basis_rank"])
    shards = sorted(payload["shards"], key=lambda row: int(row["shard_index"]))
    if [int(row["shard_index"]) for row in shards] != list(range(len(shards))):
        raise ValueError("projector path shard indices are not contiguous")
    cursor = 0
    for row in shards:
        start, stop = int(row["path_start"]), int(row["path_stop"])
        if start != cursor or stop < start:
            raise ValueError("projector path ranges overlap or leave a gap")
        if int(row["path_count"]) != stop - start:
            raise ValueError("projector path shard count is inconsistent")
        expected_hash = stable_json_hash(
            {
                "semantic_workload_hash": payload["semantic_workload_hash"],
                "path_start": start,
                "path_stop": stop,
            }
        )
        if row.get("semantic_term_hash") != expected_hash:
            raise ValueError("projector path term hash mismatch")
        cursor = stop
    if cursor != rank:
        raise ValueError("projector path ranges do not cover the full basis")


def evaluation_run_identity(
    workload: Mapping[str, Any],
    *,
    input_hash: str,
    lowering_hash: str,
    evaluator_hash: str,
) -> dict[str, Any]:
    """Bind reusable semantic shards to one concrete evaluator realization."""

    validate_projector_path_workload(workload)
    identity = {
        "semantic_workload_hash": workload["semantic_workload_hash"],
        "input_hash": input_hash,
        "lowering_hash": lowering_hash,
        "evaluator_hash": evaluator_hash,
    }
    return {**identity, "evaluation_run_hash": stable_json_hash(identity)}


def annotate_ranked_path_shards(
    workload: dict[str, Any],
    *,
    path_costs: Iterable[float],
    calibration_width: int,
    estimator: Mapping[str, Any],
) -> dict[str, Any]:
    """Attach a generic static ranking and a quantile calibration wave.

    The semantic path partition remains unchanged.  Ranking is scheduling
    metadata only, so a later geometric lowering may reuse the same shards
    while producing a distinct evaluation-run identity.
    """

    validate_projector_path_workload(workload)
    costs = tuple(float(cost) for cost in path_costs)
    rank = int(workload["semantic_identity"]["path_basis_rank"])
    if len(costs) != rank:
        raise ValueError("one static cost is required for every projector path")
    if any(not math.isfinite(cost) or cost < 0 for cost in costs):
        raise ValueError("projector path costs must be finite and nonnegative")
    calibration_width = int(calibration_width)
    if calibration_width < 1:
        raise ValueError("calibration width must be positive")

    for shard in workload["shards"]:
        start, stop = int(shard["path_start"]), int(shard["path_stop"])
        selected = costs[start:stop]
        shard["estimated_cost_sum"] = math.fsum(selected)
        shard["estimated_cost_mean"] = (
            math.fsum(selected) / len(selected) if selected else 0.0
        )
        shard["estimated_cost_max"] = max(selected, default=0.0)

    ranked = sorted(
        workload["shards"],
        key=lambda row: (
            float(row["estimated_cost_mean"]),
            float(row["estimated_cost_max"]),
            int(row["shard_index"]),
        ),
    )
    calibration_count = min(calibration_width, len(ranked))
    calibration_positions = sorted(
        {
            math.ceil((index + 1) * len(ranked) / calibration_count) - 1
            for index in range(calibration_count)
        }
    )
    calibration_indices = [
        int(ranked[position]["shard_index"]) for position in calibration_positions
    ]
    calibration_set = set(calibration_indices)
    dispatch = calibration_indices + [
        int(row["shard_index"])
        for row in ranked
        if int(row["shard_index"]) not in calibration_set
    ]
    dispatch_rank = {shard_index: index for index, shard_index in enumerate(dispatch)}
    for shard in workload["shards"]:
        shard_index = int(shard["shard_index"])
        shard["calibration_wave"] = 0 if shard_index in calibration_set else None
        shard["dispatch_rank"] = dispatch_rank[shard_index]
    workload["ranking"] = {
        "status": "STATIC_ESTIMATE_WITH_QUANTILE_CALIBRATION",
        "estimator": dict(estimator),
        "calibration_width": calibration_count,
        "calibration_shard_indices": calibration_indices,
        "dispatch_shard_indices": dispatch,
        "policy": (
            "first wave samples the maximum-cost shard in every estimated-cost "
            "quantile; remaining shards are dispatched from low to high estimate"
        ),
    }
    return workload
