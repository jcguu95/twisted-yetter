#!/usr/bin/env python3
"""Cross-check Figure 21 SU(2)_2 through the exact side projector slice."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import UTC, datetime
import hashlib
from itertools import product
import json
import math
from pathlib import Path
import platform
import signal
import socket
import subprocess
import sys
import time

from experiments.sage.morse_category_registry import build_category
from experiments.sage.morse_fusion_evaluator import (
    Leaf,
    LeafState,
    MorseEvaluator,
    Node,
    NodeState,
    analyze_topology,
    right_comb_fusion_path_basis,
    root_label,
)
from experiments.sage.morse_projector_workload import (
    annotate_ranked_path_shards,
    build_projector_path_workload,
    evaluation_run_identity,
    validate_projector_path_workload,
)
from experiments.sage.ribbon_graph_evaluator import RibbonGraphEvaluator
from experiments.scripts.morse_pl_lift import (
    build_blockwise_flat_side_lift,
    build_morse_pl_lift,
    lower_exact_side_projection_to_morse,
    make_exact_side_projection_lift,
    optimize_special_disk_sides,
)
from experiments.scripts.special_dotted_morphism import (
    build_vacuum_coupon_graph,
    compile_projected_morphism,
    replay_forms,
    stable_json_hash,
)


REPO = Path(__file__).resolve().parents[2]
INPUT = REPO / "experiments/inputs/akbulut-yasui/figure21-right-morse-draft-v1.json"
DEFAULT_OUTPUT = Path("/tmp/figure21-su2-2-direct-side-projector-controls-v1.json")
SIDE_PARAMETERS = {
    "bump_fraction": 0.06,
    "crossing_height_mode": "minimal-local",
    "crossing_margin": 0.001,
    "block_order_strategy": "projected-mean-descending",
    "block_order_angle_degrees": 110.0,
    "side_projection_angle_degrees": 70.0,
}


class SectorTimeout(TimeoutError):
    pass


def decode_sector(sector_id: int, width: int, base: int = 3) -> tuple[int, ...]:
    if not 0 <= sector_id < base**width:
        raise ValueError(f"sector id {sector_id} is outside the base-{base} workload")
    labels = [0] * width
    for index in range(width - 1, -1, -1):
        sector_id, labels[index] = divmod(sector_id, base)
    return tuple(labels)


def encode_sector(labels: tuple[int, ...], base: int = 3) -> int:
    sector_id = 0
    for label in labels:
        sector_id = sector_id * base + int(label)
    return sector_id


def json_safe(value):
    if isinstance(value, complex):
        return [float(value.real), float(value.imag)]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(item) for item in value]
    return value


def atomic_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n"
    )
    temporary.replace(path)


def _timeout_handler(_signum, _frame) -> None:
    raise SectorTimeout("sector exceeded its wall-time limit")


def _semantic_topology_map(lowered: dict, topology) -> dict[str, str]:
    semantics_by_topology: dict[str, set[str]] = defaultdict(set)
    for token, semantic in lowered["semantic_component_by_token"].items():
        semantics_by_topology[topology.component_by_strand[token]].add(semantic)
    ambiguous = {
        component: sorted(semantics)
        for component, semantics in semantics_by_topology.items()
        if len(semantics) != 1
    }
    if ambiguous:
        raise ValueError(f"lowered topology mixes semantic components: {ambiguous!r}")
    result = {
        next(iter(semantics)): component
        for component, semantics in semantics_by_topology.items()
    }
    if set(result) != set(lowered["component_by_piece"].values()):
        raise ValueError("lowered topology omitted a semantic component")
    return result


def _visible_self_writhe(lowered: dict, topology) -> tuple[dict[str, int], list[dict]]:
    trace = replay_forms(lowered["forms"])
    semantic_by_token = lowered["semantic_component_by_token"]
    visible: dict[str, int] = defaultdict(int)
    records = []
    for entry in trace:
        form = entry["form"]
        if form["kind"] != "cross":
            continue
        over, under = form["over"], form["under"]
        before, after = entry["before_order"], entry["after_order"]
        determinant = (
            topology.strand_orientation(over)
            * topology.strand_orientation(under)
            * (
                after.index(over)
                - before.index(over)
                - after.index(under)
                + before.index(under)
            )
        )
        if determinant == 0:
            raise ValueError("lowered crossing has zero oriented determinant")
        sign = 1 if determinant > 0 else -1
        over_component = semantic_by_token[over]
        under_component = semantic_by_token[under]
        if over_component == under_component:
            visible[over_component] += sign
        records.append(
            {
                "form_index": entry["form_index"],
                "over": over,
                "under": under,
                "over_component": over_component,
                "under_component": under_component,
                "sign": sign,
            }
        )
    return dict(visible), records


def build_context(
    *, state_backend: str = "object", compact_state_threshold: int = 750_000
) -> dict:
    source = json.loads(INPUT.read_text())
    forms = tuple(source["forms"])
    lift = build_morse_pl_lift(
        forms,
        component_by_piece=source["component_by_piece"],
        special_components=source["special_components"],
    )
    side_assignment = optimize_special_disk_sides(lift, "red")
    flattened = build_blockwise_flat_side_lift(
        lift,
        side_assignment,
        bump_fraction=SIDE_PARAMETERS["bump_fraction"],
        crossing_height_mode=SIDE_PARAMETERS["crossing_height_mode"],
        crossing_margin=SIDE_PARAMETERS["crossing_margin"],
        block_order_strategy=SIDE_PARAMETERS["block_order_strategy"],
        block_order_angle_degrees=SIDE_PARAMETERS["block_order_angle_degrees"],
    )
    side = make_exact_side_projection_lift(
        flattened,
        "red",
        SIDE_PARAMETERS["side_projection_angle_degrees"],
    )
    lowered = lower_exact_side_projection_to_morse(side)
    topology = analyze_topology(lowered["forms"])
    semantic_to_topology = _semantic_topology_map(lowered, topology)
    visible_self_writhe, crossing_records = _visible_self_writhe(
        lowered, topology
    )
    ordinary = tuple(
        component for component in source["component_order"] if component != "red"
    )
    framing_corrections = {
        component: int(source["framing_labels"][component])
        - visible_self_writhe.get(component, 0)
        for component in ordinary
    }
    category, category_name, category_id = build_category("su2", 2)
    direct = MorseEvaluator(
        category,
        state_backend=state_backend,
        compact_state_threshold=compact_state_threshold,
    )
    original_ir = compile_projected_morphism(
        forms,
        component_by_piece=source["component_by_piece"],
        special_components=source["special_components"],
        component_order=source["component_order"],
    )
    original_graph = build_vacuum_coupon_graph(forms, original_ir)
    oracle = RibbonGraphEvaluator(
        category,
        source_forms=forms,
        component_by_piece=source["component_by_piece"],
        projected_ir=original_ir,
        total_framings=source["framing_labels"],
    )
    return {
        "source": source,
        "ordinary": ordinary,
        "category": category,
        "category_name": category_name,
        "category_id": category_id,
        "direct": direct,
        "oracle": oracle,
        "oracle_graph": original_graph,
        "side": side,
        "lowered": lowered,
        "topology": topology,
        "semantic_to_topology": semantic_to_topology,
        "visible_self_writhe": visible_self_writhe,
        "framing_corrections": framing_corrections,
        "crossing_records": crossing_records,
    }


def direct_value(
    context: dict,
    labels: dict[str, int],
    *,
    projector_path_ranges: dict[str, tuple[int, int]] | None = None,
) -> tuple[complex, dict]:
    topology_labels = {
        context["semantic_to_topology"][semantic]: label
        for semantic, label in labels.items()
    }
    value, stats = context["direct"].fixed_label_value(
        tuple(context["lowered"]["forms"]),
        topology_labels,
        projector_path_ranges=projector_path_ranges,
    )
    framing_phase = 1.0 + 0.0j
    for component, label in labels.items():
        framing_phase *= complex(context["category"].twist(label)) ** context[
            "framing_corrections"
        ][component]
    return value * framing_phase, {
        "morse": stats,
        "framing_phase": [framing_phase.real, framing_phase.imag],
    }


def projector_rank(context: dict, labels: dict[str, int]) -> int:
    category = context["category"]
    reachable = {category.unit: 1}
    for token in context["lowered"]["projector_order"]:
        semantic = context["lowered"]["semantic_component_by_token"][token]
        label = labels[semantic]
        if context["topology"].strand_orientation(token) < 0:
            label = category.dual(label)
        following: dict[int, int] = defaultdict(int)
        for left, count in reachable.items():
            for output, multiplicity in category.fusion_outputs(left, label):
                following[output] += count * int(multiplicity)
        reachable = dict(following)
    return int(reachable.get(category.unit, 0))


def _projector_form(context: dict) -> dict:
    forms = [
        form
        for form in context["lowered"]["forms"]
        if form["kind"] == "vacuum-projector"
    ]
    if len(forms) != 1:
        raise ValueError(f"expected exactly one vacuum projector, found {len(forms)}")
    return forms[0]


def _ordered_puncture_word(context: dict, labels: dict[str, int]) -> list[dict]:
    category = context["category"]
    result = []
    for token in context["lowered"]["projector_order"]:
        component = context["lowered"]["semantic_component_by_token"][token]
        variance = (
            "dual" if context["topology"].strand_orientation(token) < 0 else "label"
        )
        oriented_label = labels[component]
        if variance == "dual":
            oriented_label = category.dual(oriented_label)
        result.append(
            {
                "cut_id": token,
                "component": component,
                "variance": variance,
                "oriented_label": oriented_label,
            }
        )
    return result


def _category_projector_data_hash(context: dict) -> str:
    category = context["category"]
    payload = {
        "category_id": context["category_id"],
        "labels": list(category.labels),
        "unit": category.unit,
        "duals": {str(label): category.dual(label) for label in category.labels},
        "dimensions": {
            str(label): json_safe(category.dimension(label)) for label in category.labels
        },
        "twists": {
            str(label): json_safe(category.twist(label)) for label in category.labels
        },
        "fusion_outputs": {
            f"{left}|{right}": [list(row) for row in category.fusion_outputs(left, right)]
            for left in category.labels
            for right in category.labels
        },
        "path_basis_is_orthonormal": bool(category.path_basis_is_orthonormal),
        "pivotal_profile": json_safe(category.pivotal_profile),
    }
    return stable_json_hash(payload)


def _evaluator_source_hash() -> str:
    paths = (
        Path(__file__).resolve(),
        REPO / "experiments/sage/morse_fusion_evaluator.py",
        REPO / "experiments/sage/morse_projector_workload.py",
    )
    digest = hashlib.sha256()
    for path in paths:
        relative = str(path.relative_to(REPO)).encode()
        content = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def _fusion_path_static_cost(category, tree, state) -> float:
    """Estimate path work without referring to a diagram or category name."""

    if isinstance(tree, Leaf):
        if not isinstance(state, LeafState):
            raise ValueError("fusion path leaf/state mismatch")
        return 1.0
    if not isinstance(tree, Node) or not isinstance(state, NodeState):
        raise ValueError("fusion path node/state mismatch")
    left_label = root_label(tree.left, state.left)
    right_label = root_label(tree.right, state.right)
    local_branching = sum(
        int(multiplicity)
        for _output, multiplicity in category.fusion_outputs(left_label, right_label)
    )
    local_cost = (
        1.0
        + math.log2(1.0 + abs(complex(category.dimension(state.output))))
        + math.log2(1.0 + local_branching)
    )
    return (
        local_cost
        + _fusion_path_static_cost(category, tree.left, state.left)
        + _fusion_path_static_cost(category, tree.right, state.right)
    )


def _projector_path_static_costs(
    context: dict, ordered_word: list[dict]
) -> tuple[float, ...]:
    factors = tuple(
        (factor["cut_id"], factor["oriented_label"]) for factor in ordered_word
    )
    tree, basis = right_comb_fusion_path_basis(
        context["category"], factors, target=context["category"].unit
    )
    if tree is None:
        return (1.0,) if basis else ()
    return tuple(
        _fusion_path_static_cost(context["category"], tree, state)
        for state in basis
    )


def write_projector_path_plan(
    context: dict,
    *,
    sector_id: int,
    shard_count: int,
    calibration_width: int,
    output: Path,
) -> int:
    label_tuple = decode_sector(sector_id, len(context["ordinary"]))
    labels = dict(zip(context["ordinary"], label_tuple, strict=True))
    rank = projector_rank(context, labels)
    projector_id = _projector_form(context).get("projector_id")
    if not projector_id:
        raise ValueError("vacuum projector is missing a stable projector id")
    ordered_word = _ordered_puncture_word(context, labels)
    workload = build_projector_path_workload(
        category_id=context["category_id"],
        category_projector_data_hash=_category_projector_data_hash(context),
        sector_labels=labels,
        component_order=context["ordinary"],
        projector_id=projector_id,
        ordered_puncture_word=ordered_word,
        path_basis_rank=rank,
        shard_count=shard_count,
    )
    path_costs = _projector_path_static_costs(context, ordered_word)
    annotate_ranked_path_shards(
        workload,
        path_costs=path_costs,
        calibration_width=calibration_width,
        estimator={
            "name": "fusion-path-local-branching-and-absolute-dimension-v1",
            "category_specific": False,
            "formula": (
                "sum over canonical path vertices of "
                "1 + log2(1+abs(qdim(output))) + log2(1+local fusion branching)"
            ),
            "purpose": "dispatch ranking only; never changes the scalar",
        },
    )
    workload.update(
        {
            "sector_id": sector_id,
            "input_path": str(INPUT.relative_to(REPO)),
            "input_hash_at_plan_time": stable_json_hash(context["source"]),
            "generated_at": datetime.now(UTC).isoformat(),
            "generator_script": str(Path(__file__).resolve().relative_to(REPO)),
            "argv": list(sys.argv),
        }
    )
    atomic_json(output, workload)
    print(
        json.dumps(
            {
                "status": workload["status"],
                "sector_id": sector_id,
                "projector_rank": rank,
                "shard_count": shard_count,
                "calibration_shard_indices": workload["ranking"][
                    "calibration_shard_indices"
                ],
                "semantic_workload_hash": workload["semantic_workload_hash"],
                "output": str(output),
            },
            sort_keys=True,
        )
    )
    return 0


def _load_matching_projector_path_workload(context: dict, plan_path: Path) -> dict:
    workload = json.loads(plan_path.read_text())
    validate_projector_path_workload(workload)
    identity = workload["semantic_identity"]
    if identity["category_id"] != context["category_id"]:
        raise ValueError("projector workload category does not match this evaluator")
    if identity["category_projector_data_hash"] != _category_projector_data_hash(context):
        raise ValueError("projector workload category data hash does not match")
    sector_id = int(workload["sector_id"])
    label_tuple = decode_sector(sector_id, len(context["ordinary"]))
    labels = dict(zip(context["ordinary"], label_tuple, strict=True))
    expected_word = _ordered_puncture_word(context, labels)
    if identity["ordered_puncture_word"] != expected_word:
        raise ValueError("projector workload puncture word does not match")
    if identity["sector_labels"] != labels:
        raise ValueError("projector workload sector labels do not match")
    if int(identity["path_basis_rank"]) != projector_rank(context, labels):
        raise ValueError("projector workload path rank does not match")
    return workload


def run_projector_path_shard(
    context: dict,
    *,
    plan_path: Path,
    shard_index: int,
    work_root: Path,
    max_seconds: float,
) -> int:
    workload = _load_matching_projector_path_workload(context, plan_path)
    shards = {int(row["shard_index"]): row for row in workload["shards"]}
    if shard_index not in shards:
        raise ValueError(f"projector workload has no shard {shard_index}")
    shard = shards[shard_index]
    output = work_root / f"projector-path-{shard_index:04d}.json"
    if output.exists():
        existing = json.loads(output.read_text())
        print(json.dumps({"status": "EXISTS", "output": str(output), "result": existing["status"]}))
        return 0 if existing["status"] == "PASS" else 2

    run_identity = evaluation_run_identity(
        workload,
        input_hash=stable_json_hash(context["source"]),
        lowering_hash=context["lowered"]["lowering_hash"],
        evaluator_hash=_evaluator_source_hash(),
    )
    sector_id = int(workload["sector_id"])
    label_tuple = decode_sector(sector_id, len(context["ordinary"]))
    labels = dict(zip(context["ordinary"], label_tuple, strict=True))
    projector_id = workload["semantic_identity"]["projector_id"]
    path_range = (int(shard["path_start"]), int(shard["path_stop"]))
    started_at = datetime.now(UTC).isoformat()
    started = time.perf_counter()
    previous_handler = signal.signal(signal.SIGALRM, _timeout_handler)
    if max_seconds > 0:
        signal.setitimer(signal.ITIMER_REAL, max_seconds)
    try:
        value, stats = direct_value(
            context,
            labels,
            projector_path_ranges={projector_id: path_range},
        )
        status = "PASS"
        error = None
    except SectorTimeout as caught:
        value, stats, status, error = None, None, "TIMEOUT", str(caught)
    except Exception as caught:
        value, stats, status = None, None, "FAILED"
        error = f"{type(caught).__name__}: {caught}"
    finally:
        if max_seconds > 0:
            signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-projector-path-shard.v1",
        "status": status,
        "sector_id": sector_id,
        "labels": labels,
        "projector_rank": int(workload["semantic_identity"]["path_basis_rank"]),
        "shard": shard,
        "partial_value": json_safe(value),
        "stats": json_safe(stats),
        "error": error,
        "semantic_workload_hash": workload["semantic_workload_hash"],
        "evaluation_run_identity": run_identity,
        "started_at": started_at,
        "elapsed_seconds": time.perf_counter() - started,
        "host": socket.gethostname(),
        "pid": __import__("os").getpid(),
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "argv": list(sys.argv),
        "finished_at": datetime.now(UTC).isoformat(),
    }
    atomic_json(output, payload)
    print(
        json.dumps(
            {
                "status": status,
                "sector_id": sector_id,
                "shard_index": shard_index,
                "path_range": path_range,
                "elapsed_seconds": payload["elapsed_seconds"],
                "output": str(output),
            },
            sort_keys=True,
        ),
        flush=True,
    )
    return 0 if status == "PASS" else 2


def summarize_projector_path_root(
    context: dict,
    *,
    plan_path: Path,
    work_root: Path,
    output: Path,
    compare_oracle: bool,
    max_oracle_seconds: float,
) -> int:
    workload = _load_matching_projector_path_workload(context, plan_path)
    paths = sorted(work_root.glob("projector-path-*.json"))
    records = [json.loads(path.read_text()) for path in paths]
    expected = {int(row["shard_index"]): row for row in workload["shards"]}
    found = {int(row["shard"]["shard_index"]): row for row in records}
    if len(found) != len(records):
        raise ValueError("duplicate projector path shard indices")
    missing = sorted(set(expected) - set(found))
    unexpected = sorted(set(found) - set(expected))
    if unexpected:
        raise ValueError(f"unexpected projector path shards: {unexpected!r}")
    expected_run_identity = evaluation_run_identity(
        workload,
        input_hash=stable_json_hash(context["source"]),
        lowering_hash=context["lowered"]["lowering_hash"],
        evaluator_hash=_evaluator_source_hash(),
    )
    incompatible = sorted(
        index
        for index, record in found.items()
        if record.get("evaluation_run_identity") != expected_run_identity
        or record.get("semantic_workload_hash") != workload["semantic_workload_hash"]
        or record.get("shard") != expected[index]
    )
    failed = sorted(
        index for index, record in found.items() if record.get("status") != "PASS"
    )
    complete = not missing and not incompatible and not failed
    partial_sum = None
    if complete:
        partial_sum = complex(
            math.fsum(float(found[index]["partial_value"][0]) for index in sorted(found)),
            math.fsum(float(found[index]["partial_value"][1]) for index in sorted(found)),
        )

    oracle_value = None
    oracle_stats = None
    oracle_error = None
    if complete and compare_oracle:
        sector_id = int(workload["sector_id"])
        label_tuple = decode_sector(sector_id, len(context["ordinary"]))
        labels = dict(zip(context["ordinary"], label_tuple, strict=True))
        previous_handler = signal.signal(signal.SIGALRM, _timeout_handler)
        if max_oracle_seconds > 0:
            signal.setitimer(signal.ITIMER_REAL, max_oracle_seconds)
        try:
            oracle_value, oracle_stats = context["oracle"].fixed_label_value(
                context["oracle_graph"], labels
            )
        except Exception as caught:
            oracle_error = f"{type(caught).__name__}: {caught}"
        finally:
            if max_oracle_seconds > 0:
                signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, previous_handler)

    difference = (
        abs(partial_sum - oracle_value)
        if partial_sum is not None and oracle_value is not None
        else None
    )
    if not complete:
        status = "INCOMPLETE"
    elif compare_oracle and oracle_value is None:
        status = "ORACLE_INCOMPLETE"
    elif compare_oracle and difference > 1e-8:
        status = "MISMATCH"
    else:
        status = "PASS"
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-projector-path-summary.v1",
        "status": status,
        "sector_id": int(workload["sector_id"]),
        "projector_rank": int(workload["semantic_identity"]["path_basis_rank"]),
        "semantic_workload_hash": workload["semantic_workload_hash"],
        "evaluation_run_identity": expected_run_identity,
        "expected_shard_count": len(expected),
        "found_shard_count": len(found),
        "missing_shards": missing,
        "incompatible_shards": incompatible,
        "failed_shards": failed,
        "partial_sum": json_safe(partial_sum),
        "oracle_value": json_safe(oracle_value),
        "absolute_difference": difference,
        "oracle_stats": json_safe(oracle_stats),
        "oracle_error": oracle_error,
        "worker_seconds": sum(float(row["elapsed_seconds"]) for row in records),
        "finished_at": datetime.now(UTC).isoformat(),
    }
    atomic_json(output, payload)
    print(json.dumps({**payload, "oracle_stats": None}, sort_keys=True))
    return 0 if status == "PASS" else 2


def _even_bucket_sample(values: list[int], count: int) -> list[int]:
    if count <= 0:
        raise ValueError("samples per bucket must be positive")
    if len(values) <= count:
        return list(values)
    if count == 1:
        return [values[len(values) // 2]]
    indices = {
        round(index * (len(values) - 1) / (count - 1))
        for index in range(count)
    }
    return [values[index] for index in sorted(indices)]


def write_ranked_plan(
    context: dict,
    *,
    output: Path,
    shard_count: int,
    samples_per_bucket: int,
    min_projector_rank: int | None,
    max_projector_rank: int | None,
    exclude_plan: Path | None,
) -> int:
    if shard_count <= 0:
        raise ValueError("shard count must be positive")
    started = time.perf_counter()
    excluded_sector_ids = set()
    if exclude_plan is not None:
        excluded = json.loads(exclude_plan.read_text())
        excluded_sector_ids = {
            int(sector_id)
            for shard in excluded["shards"]
            for sector_id in shard["sector_ids"]
        }
    buckets: dict[tuple[int, int], list[int]] = defaultdict(list)
    category = context["category"]
    for label_tuple in product(category.labels, repeat=len(context["ordinary"])):
        labels = dict(zip(context["ordinary"], label_tuple, strict=True))
        weight = sum(label != category.unit for label in label_tuple)
        rank = projector_rank(context, labels)
        if min_projector_rank is not None and rank < min_projector_rank:
            continue
        if max_projector_rank is not None and rank > max_projector_rank:
            continue
        buckets[(weight, rank)].append(encode_sector(tuple(label_tuple)))

    selected = []
    bucket_rows = []
    for (weight, rank), sector_ids in sorted(buckets.items()):
        sampled = _even_bucket_sample(sorted(sector_ids), samples_per_bucket)
        sampled = [
            sector_id
            for sector_id in sampled
            if sector_id not in excluded_sector_ids
        ]
        bucket_rows.append(
            {
                "hamming_weight": weight,
                "projector_rank": rank,
                "sector_count": len(sector_ids),
                "selected_sector_ids": sampled,
            }
        )
        selected.extend((rank, weight, sector_id) for sector_id in sampled)
    selected.sort()
    shards = [[] for _ in range(shard_count)]
    for index, (_rank, _weight, sector_id) in enumerate(selected):
        shards[index % shard_count].append(sector_id)

    payload = {
        "schema": "twisted-yetter.figure21-su2-2-direct-ranked-controls-plan.v1",
        "status": "READY",
        "category_id": context["category_id"],
        "input_hash": stable_json_hash(context["source"]),
        "side_lift_hash": context["side"]["lift_hash"],
        "lowering_hash": context["lowered"]["lowering_hash"],
        "ordinary_component_order": list(context["ordinary"]),
        "selection": {
            "method": "even-deterministic-samples-per-(hamming-weight,projector-rank)-bucket",
            "samples_per_bucket": samples_per_bucket,
            "minimum_projector_rank": min_projector_rank,
            "maximum_projector_rank": max_projector_rank,
            "exclude_plan": str(exclude_plan) if exclude_plan is not None else None,
            "excluded_sector_count": len(excluded_sector_ids),
            "bucket_count": len(bucket_rows),
            "selected_sector_count": len(selected),
            "bucket_rows": bucket_rows,
        },
        "shard_count": shard_count,
        "shards": [
            {"shard_index": index, "sector_ids": sector_ids}
            for index, sector_ids in enumerate(shards)
        ],
        "elapsed_seconds": time.perf_counter() - started,
        "generated_at": datetime.now(UTC).isoformat(),
        "generator_script": str(Path(__file__).resolve().relative_to(REPO)),
        "argv": list(sys.argv),
    }
    atomic_json(output, payload)
    print(
        json.dumps(
            {
                "status": "READY",
                "bucket_count": len(bucket_rows),
                "selected_sector_count": len(selected),
                "shard_count": shard_count,
                "output": str(output),
            },
            sort_keys=True,
        )
    )
    return 0


def evaluate_sector(
    context: dict,
    sector_id: int,
    *,
    max_seconds: float,
) -> dict:
    label_tuple = decode_sector(sector_id, len(context["ordinary"]))
    labels = dict(zip(context["ordinary"], label_tuple, strict=True))
    rank = projector_rank(context, labels)
    row_started = time.perf_counter()
    phase = "direct"
    previous_handler = signal.signal(signal.SIGALRM, _timeout_handler)
    if max_seconds > 0:
        signal.setitimer(signal.ITIMER_REAL, max_seconds)
    try:
        if rank == 0:
            direct = 0.0 + 0.0j
            direct_stats = {
                "prepruned_no_vacuum": True,
                "reason": "Hom(1, ordered puncture tensor product) has rank zero",
            }
        else:
            direct, direct_stats = direct_value(context, labels)
        phase = "oracle"
        oracle, oracle_stats = context["oracle"].fixed_label_value(
            context["oracle_graph"], labels
        )
        difference = abs(direct - oracle)
        return {
            "status": "PASS" if difference <= 1e-8 else "MISMATCH",
            "sector_id": sector_id,
            "labels": labels,
            "hamming_weight": sum(label != context["category"].unit for label in label_tuple),
            "projector_rank": rank,
            "direct_value": [direct.real, direct.imag],
            "modular_oracle_value": [oracle.real, oracle.imag],
            "absolute_difference": difference,
            "tolerance": 1e-8,
            "elapsed_seconds": time.perf_counter() - row_started,
            "direct_stats": direct_stats,
            "oracle_stats": oracle_stats,
        }
    except SectorTimeout as error:
        return {
            "status": "TIMEOUT",
            "sector_id": sector_id,
            "labels": labels,
            "hamming_weight": sum(label != context["category"].unit for label in label_tuple),
            "projector_rank": rank,
            "timeout_phase": phase,
            "max_seconds": max_seconds,
            "elapsed_seconds": time.perf_counter() - row_started,
            "error": str(error),
        }
    except Exception as error:
        return {
            "status": "FAILED",
            "sector_id": sector_id,
            "labels": labels,
            "hamming_weight": sum(label != context["category"].unit for label in label_tuple),
            "projector_rank": rank,
            "failure_phase": phase,
            "elapsed_seconds": time.perf_counter() - row_started,
            "error_type": type(error).__name__,
            "error": str(error),
        }
    finally:
        if max_seconds > 0:
            signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)


def run_ranked_shard(
    context: dict,
    *,
    plan_path: Path,
    shard_index: int,
    work_root: Path,
    max_sector_seconds: float,
) -> int:
    plan = json.loads(plan_path.read_text())
    if plan["input_hash"] != stable_json_hash(context["source"]):
        raise ValueError("ranked plan input hash does not match this checkout")
    if plan["side_lift_hash"] != context["side"]["lift_hash"]:
        raise ValueError("ranked plan side-lift hash does not match this checkout")
    if plan["lowering_hash"] != context["lowered"]["lowering_hash"]:
        raise ValueError("ranked plan lowering hash does not match this checkout")
    shards = {row["shard_index"]: row["sector_ids"] for row in plan["shards"]}
    if shard_index not in shards:
        raise ValueError(f"plan has no shard {shard_index}")
    output_root = work_root / f"shard-{shard_index:04d}"
    output_root.mkdir(parents=True, exist_ok=True)
    counts: dict[str, int] = defaultdict(int)
    for sector_id in shards[shard_index]:
        output = output_root / f"sector-{sector_id:06d}.json"
        if output.exists():
            existing = json.loads(output.read_text())
            counts[existing["status"]] += 1
            continue
        row = evaluate_sector(
            context, sector_id, max_seconds=max_sector_seconds
        )
        row.update(
            {
                "schema": "twisted-yetter.figure21-su2-2-direct-ranked-control-sector.v1",
                "category_id": context["category_id"],
                "input_hash": stable_json_hash(context["source"]),
                "side_lift_hash": context["side"]["lift_hash"],
                "lowering_hash": context["lowered"]["lowering_hash"],
                "host": socket.gethostname(),
                "pid": __import__("os").getpid(),
                "shard_index": shard_index,
                "finished_at": datetime.now(UTC).isoformat(),
            }
        )
        atomic_json(output, row)
        counts[row["status"]] += 1
        print(
            json.dumps(
                {
                    "shard": shard_index,
                    "sector_id": sector_id,
                    "status": row["status"],
                    "rank": row["projector_rank"],
                    "weight": row["hamming_weight"],
                    "elapsed_seconds": row["elapsed_seconds"],
                },
                sort_keys=True,
            ),
            flush=True,
        )
        if row["status"] in {"MISMATCH", "FAILED"}:
            break
    print(json.dumps({"shard": shard_index, "counts": counts}, sort_keys=True))
    return 2 if counts.get("MISMATCH") or counts.get("FAILED") else 0


def summarize_control_roots(roots: list[Path], output: Path) -> int:
    records = []
    source_paths = []
    for root in roots:
        paths = sorted(root.glob("shard-*/sector-*.json"))
        source_paths.extend(paths)
        records.extend(json.loads(path.read_text()) for path in paths)
    if not records:
        raise ValueError("no sector records found under summary roots")
    sector_ids = [int(record["sector_id"]) for record in records]
    duplicates = sorted(
        sector_id
        for sector_id, count in Counter(sector_ids).items()
        if count != 1
    )
    if duplicates:
        raise ValueError(f"duplicate sector ids across control roots: {duplicates[:10]!r}")
    input_hashes = sorted({record["input_hash"] for record in records})
    side_hashes = sorted({record["side_lift_hash"] for record in records})
    lowering_hashes = sorted({record["lowering_hash"] for record in records})
    category_ids = sorted({record["category_id"] for record in records})
    if not all(
        len(values) == 1
        for values in (input_hashes, side_hashes, lowering_hashes, category_ids)
    ):
        raise ValueError("control records do not share one evaluation identity")
    status_counts = Counter(record["status"] for record in records)
    pass_records = [record for record in records if record["status"] == "PASS"]
    timeout_records = [
        record for record in records if record["status"] == "TIMEOUT"
    ]
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-direct-ranked-controls-summary.v1",
        "status": (
            "MISMATCH_OR_FAILURE"
            if status_counts.get("MISMATCH") or status_counts.get("FAILED")
            else "NO_MISMATCH_IN_COMPLETED_CONTROLS"
        ),
        "mathematical_status": "DIAGNOSTIC_SAMPLED_CONTROL_NOT_EXHAUSTIVE",
        "category_id": category_ids[0],
        "input_hash": input_hashes[0],
        "side_lift_hash": side_hashes[0],
        "lowering_hash": lowering_hashes[0],
        "source_roots": [str(root) for root in roots],
        "source_record_count": len(source_paths),
        "unique_sector_count": len(sector_ids),
        "status_counts": dict(sorted(status_counts.items())),
        "completed_comparison_count": len(pass_records)
        + status_counts.get("MISMATCH", 0),
        "maximum_completed_projector_rank": max(
            record["projector_rank"] for record in pass_records
        ),
        "maximum_completed_hamming_weight": max(
            record["hamming_weight"] for record in pass_records
        ),
        "maximum_absolute_difference": max(
            float(record["absolute_difference"]) for record in pass_records
        ),
        "pass_rank_distribution": dict(
            sorted(Counter(record["projector_rank"] for record in pass_records).items())
        ),
        "timeout_rank_distribution": dict(
            sorted(
                Counter(record["projector_rank"] for record in timeout_records).items()
            )
        ),
        "worker_seconds_recorded": sum(
            float(record["elapsed_seconds"]) for record in records
        ),
        "hosts": sorted({record["host"] for record in records}),
        "mismatch_records": [
            record for record in records if record["status"] == "MISMATCH"
        ],
        "failure_records": [
            record for record in records if record["status"] == "FAILED"
        ],
        "finished_at": datetime.now(UTC).isoformat(),
        "generator_script": str(Path(__file__).resolve().relative_to(REPO)),
        "argv": list(sys.argv),
    }
    atomic_json(output, payload)
    print(
        json.dumps(
            {
                "status": payload["status"],
                "unique_sector_count": payload["unique_sector_count"],
                "status_counts": payload["status_counts"],
                "maximum_completed_projector_rank": payload[
                    "maximum_completed_projector_rank"
                ],
                "maximum_absolute_difference": payload[
                    "maximum_absolute_difference"
                ],
                "output": str(output),
            },
            sort_keys=True,
        )
    )
    return 2 if payload["status"] == "MISMATCH_OR_FAILURE" else 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--sector-ids",
        default="0,2,6,18,30,465,536,1571,1704,2068",
        help="comma-separated base-3 sector ids in Figure 21 ordinary component order",
    )
    parser.add_argument("--write-ranked-plan", type=Path)
    parser.add_argument("--plan-shards", type=int, default=20)
    parser.add_argument("--samples-per-bucket", type=int, default=4)
    parser.add_argument("--plan-min-projector-rank", type=int)
    parser.add_argument("--plan-max-projector-rank", type=int)
    parser.add_argument("--plan-exclude-plan", type=Path)
    parser.add_argument("--run-ranked-plan", type=Path)
    parser.add_argument("--shard-index", type=int)
    parser.add_argument("--work-root", type=Path, default=Path("/tmp/figure21-su2-2-direct-ranked-controls"))
    parser.add_argument("--max-sector-seconds", type=float, default=300.0)
    parser.add_argument("--summarize-roots")
    parser.add_argument("--summary-output", type=Path)
    parser.add_argument("--write-projector-path-plan", type=Path)
    parser.add_argument("--projector-sector-id", type=int)
    parser.add_argument("--projector-path-shards", type=int, default=16)
    parser.add_argument("--projector-calibration-width", type=int, default=16)
    parser.add_argument("--run-projector-path-plan", type=Path)
    parser.add_argument("--projector-path-shard-index", type=int)
    parser.add_argument(
        "--projector-path-work-root",
        type=Path,
        default=Path("/tmp/figure21-su2-2-projector-path-work"),
    )
    parser.add_argument("--summarize-projector-path-plan", type=Path)
    parser.add_argument("--projector-path-summary-output", type=Path)
    parser.add_argument("--compare-projector-path-oracle", action="store_true")
    parser.add_argument("--max-oracle-seconds", type=float, default=1800.0)
    parser.add_argument(
        "--state-backend", choices=("object", "compact"), default="object"
    )
    parser.add_argument("--compact-state-threshold", type=int, default=750_000)
    args = parser.parse_args()
    started = time.perf_counter()
    if args.summarize_roots is not None:
        if args.summary_output is None:
            parser.error("--summarize-roots requires --summary-output")
        return summarize_control_roots(
            [Path(value) for value in args.summarize_roots.split(",") if value],
            args.summary_output,
        )
    context = build_context(
        state_backend=args.state_backend,
        compact_state_threshold=args.compact_state_threshold,
    )
    if args.write_ranked_plan is not None:
        return write_ranked_plan(
            context,
            output=args.write_ranked_plan,
            shard_count=args.plan_shards,
            samples_per_bucket=args.samples_per_bucket,
            min_projector_rank=args.plan_min_projector_rank,
            max_projector_rank=args.plan_max_projector_rank,
            exclude_plan=args.plan_exclude_plan,
        )
    if args.write_projector_path_plan is not None:
        if args.projector_sector_id is None:
            parser.error("--write-projector-path-plan requires --projector-sector-id")
        return write_projector_path_plan(
            context,
            sector_id=args.projector_sector_id,
            shard_count=args.projector_path_shards,
            calibration_width=args.projector_calibration_width,
            output=args.write_projector_path_plan,
        )
    if args.run_projector_path_plan is not None:
        if args.projector_path_shard_index is None:
            parser.error(
                "--run-projector-path-plan requires --projector-path-shard-index"
            )
        return run_projector_path_shard(
            context,
            plan_path=args.run_projector_path_plan,
            shard_index=args.projector_path_shard_index,
            work_root=args.projector_path_work_root,
            max_seconds=args.max_sector_seconds,
        )
    if args.summarize_projector_path_plan is not None:
        if args.projector_path_summary_output is None:
            parser.error(
                "--summarize-projector-path-plan requires "
                "--projector-path-summary-output"
            )
        return summarize_projector_path_root(
            context,
            plan_path=args.summarize_projector_path_plan,
            work_root=args.projector_path_work_root,
            output=args.projector_path_summary_output,
            compare_oracle=args.compare_projector_path_oracle,
            max_oracle_seconds=args.max_oracle_seconds,
        )
    if args.run_ranked_plan is not None:
        if args.shard_index is None:
            parser.error("--run-ranked-plan requires --shard-index")
        return run_ranked_shard(
            context,
            plan_path=args.run_ranked_plan,
            shard_index=args.shard_index,
            work_root=args.work_root,
            max_sector_seconds=args.max_sector_seconds,
        )
    sector_ids = [int(value) for value in args.sector_ids.split(",") if value]
    rows = []
    all_match = True
    for sector_id in sector_ids:
        label_tuple = decode_sector(sector_id, len(context["ordinary"]))
        labels = dict(zip(context["ordinary"], label_tuple, strict=True))
        row_started = time.perf_counter()
        direct, direct_stats = direct_value(context, labels)
        oracle, oracle_stats = context["oracle"].fixed_label_value(
            context["oracle_graph"], labels
        )
        difference = abs(direct - oracle)
        matches = difference <= 1e-8
        all_match &= matches
        rows.append(
            {
                "sector_id": sector_id,
                "labels": labels,
                "direct_value": [direct.real, direct.imag],
                "modular_oracle_value": [oracle.real, oracle.imag],
                "absolute_difference": difference,
                "matches": matches,
                "elapsed_seconds": time.perf_counter() - row_started,
                "direct_stats": direct_stats,
                "oracle_stats": oracle_stats,
            }
        )
        if not matches:
            break
    git_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
    ).strip()
    git_status = subprocess.check_output(
        ["git", "status", "--short"], cwd=REPO, text=True
    ).splitlines()
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-direct-side-projector-controls.v1",
        "status": "PASS" if all_match else "MISMATCH_STOPPED",
        "category_id": context["category_id"],
        "category_name": context["category_name"],
        "input_path": str(INPUT.relative_to(REPO)),
        "input_hash": stable_json_hash(context["source"]),
        "side_parameters": SIDE_PARAMETERS,
        "side_lift_hash": context["side"]["lift_hash"],
        "lowering_hash": context["lowered"]["lowering_hash"],
        "lowering_summary": {
            key: context["lowered"][key]
            for key in (
                "minimum_count",
                "maximum_count",
                "crossing_count",
                "projector_factor_count",
                "projector_slice_active_count",
                "projector_routing_crossing_count_each_way",
                "total_routing_crossing_count",
            )
        },
        "ordinary_component_order": list(context["ordinary"]),
        "semantic_to_topology": context["semantic_to_topology"],
        "visible_self_writhe": context["visible_self_writhe"],
        "total_framings": {
            component: context["source"]["framing_labels"][component]
            for component in context["ordinary"]
        },
        "framing_corrections": context["framing_corrections"],
        "rows": rows,
        "elapsed_seconds": time.perf_counter() - started,
        "generated_at": datetime.now(UTC).isoformat(),
        "git_commit": git_commit,
        "git_dirty": bool(git_status),
        "git_status_short": git_status,
        "generator_script": str(Path(__file__).resolve().relative_to(REPO)),
        "argv": list(sys.argv),
    }
    atomic_json(args.output, payload)
    print(
        json.dumps(
            {
                "status": payload["status"],
                "rows": [
                    {
                        "sector_id": row["sector_id"],
                        "direct_value": row["direct_value"],
                        "modular_oracle_value": row["modular_oracle_value"],
                        "absolute_difference": row["absolute_difference"],
                        "elapsed_seconds": row["elapsed_seconds"],
                    }
                    for row in rows
                ],
                "output": str(args.output),
                "lowering_summary": payload["lowering_summary"],
                "visible_self_writhe": payload["visible_self_writhe"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if all_match else 2


if __name__ == "__main__":
    raise SystemExit(main())
