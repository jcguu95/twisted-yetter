#!/usr/bin/env python3
"""Plan, run, trace, and aggregate Figure 21 untwisted SU(2)_2 sectors."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import UTC, datetime
import gzip
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
from typing import Any

from experiments.sage.morse_category_registry import build_category
from experiments.sage.ribbon_graph_evaluator import RibbonGraphEvaluator
from experiments.scripts.special_dotted_morphism import (
    build_vacuum_coupon_graph,
    compile_projected_morphism,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = (
    REPO_ROOT
    / "experiments"
    / "inputs"
    / "akbulut-yasui"
    / "figure21-right-morse-draft-v1.json"
)
DEFAULT_WORK_ROOT = Path("/tmp/twisted-yetter-figure21-su2-2-full")
EXPECTED_INPUT_SHA256 = (
    "b6f8459547a7cec415eb6c70acb89a40c37ab4cabd364330206685d8e579cbc5"
)
EXPECTED_GRAPH_HASH = (
    "sha256:f66f1ef64661c432c389b6c1db726de605055ea0cabe74005fa649ebbd32a26c"
)
EXPECTED_STANDARD_VALUE = -1024.0 + 0.0j
MATCH_TOLERANCE = 1e-8
SUMMATION_ORDER_TOLERANCE = 1e-10
NUMERIC_ZERO_TOLERANCE = 1e-13
EXPECTED_TOTAL_SECTORS = 177_147
EXPECTED_ZERO_SECTORS = 90_477
EXPECTED_SURVIVING_SECTORS = 86_670
EXPECTED_UNIQUE_PUNCTURE_WORDS = 2_187


class SectorTimeout(TimeoutError):
    pass


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_hash(value: Any) -> str:
    return "sha256:" + sha256_bytes(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    )


def complex_json(value: complex) -> list[float]:
    return [float(value.real), float(value.imag)]


def decode_sector(sector_id: int, width: int, base: int = 3) -> tuple[int, ...]:
    if sector_id < 0 or sector_id >= base**width:
        raise ValueError(f"sector id is outside 0..{base**width - 1}")
    digits = [0] * width
    remaining = sector_id
    for index in range(width - 1, -1, -1):
        remaining, digits[index] = divmod(remaining, base)
    return tuple(digits)


def encode_sector(labels: tuple[int, ...], base: int = 3) -> int:
    value = 0
    for label in labels:
        if not 0 <= int(label) < base:
            raise ValueError(f"label {label!r} is outside base {base}")
        value = value * base + int(label)
    return value


def utc_now() -> str:
    return datetime.now(UTC).isoformat()


def git_metadata() -> dict[str, Any]:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True
    ).strip()
    status = subprocess.check_output(
        ["git", "status", "--short"], cwd=REPO_ROOT, text=True
    ).splitlines()
    return {"commit": commit, "dirty": bool(status), "status_short": status}


def atomic_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def load_context() -> dict[str, Any]:
    source_bytes = INPUT.read_bytes()
    input_sha256 = sha256_bytes(source_bytes)
    if input_sha256 != EXPECTED_INPUT_SHA256:
        raise ValueError(
            "Figure 21 input hash changed: "
            f"expected {EXPECTED_INPUT_SHA256}, got {input_sha256}"
        )
    source = json.loads(source_bytes)
    forms = tuple(source["forms"])
    ir = compile_projected_morphism(
        forms,
        component_by_piece=source["component_by_piece"],
        special_components=source["special_components"],
        component_order=source["component_order"],
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    if graph["graph_hash"] != EXPECTED_GRAPH_HASH:
        raise ValueError(
            "Figure 21 coupon graph hash changed: "
            f"expected {EXPECTED_GRAPH_HASH}, got {graph['graph_hash']}"
        )
    category, display_name, category_id = build_category("su2", 2)
    evaluator = RibbonGraphEvaluator(
        category,
        source_forms=forms,
        component_by_piece=source["component_by_piece"],
        projected_ir=ir,
    )
    coupon = next(
        node
        for node in graph["nodes"]
        if node["kind"] == "vacuum-projector-coupon"
    )
    ordinary = tuple(
        component for component in source["component_order"] if component != "red"
    )
    puncture_counts = Counter(
        factor["component"] for factor in coupon["factor_order"]
    )
    puncture_components = tuple(
        component for component in ordinary if component in puncture_counts
    )
    if len(coupon["factor_order"]) != 29:
        raise ValueError("Figure 21 contract requires exactly 29 punctures")
    if len(ordinary) != 11 or len(puncture_components) != 7:
        raise ValueError("Figure 21 component contract changed")
    return {
        "source": source,
        "source_bytes": source_bytes,
        "input_sha256": input_sha256,
        "forms": forms,
        "ir": ir,
        "graph": graph,
        "coupon": coupon,
        "category": category,
        "category_name": display_name,
        "category_id": category_id,
        "evaluator": evaluator,
        "ordinary": ordinary,
        "puncture_counts": dict(puncture_counts),
        "puncture_components": puncture_components,
    }


def fusion_reachability_trace(category, labels: tuple[int, ...]) -> list[dict[str, Any]]:
    reachable = {category.unit: 1}
    trace = [{"step": 0, "reachable": {str(category.unit): 1}}]
    for index, label in enumerate(labels, 1):
        next_reachable: dict[Any, int] = defaultdict(int)
        for left, count in reachable.items():
            for output, multiplicity in category.fusion_outputs(left, label):
                next_reachable[output] += int(count) * int(multiplicity)
        reachable = dict(next_reachable)
        trace.append(
            {
                "step": index,
                "factor_label": label,
                "reachable": {
                    str(root): count
                    for root, count in sorted(reachable.items(), key=lambda item: str(item[0]))
                },
            }
        )
    return trace


def puncture_word_payloads(context: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[tuple[int, ...], int]]:
    category = context["category"]
    components = context["puncture_components"]
    factors = tuple(context["coupon"]["factor_order"])
    payloads = []
    word_id_by_component_labels = {}
    for component_labels in product(category.labels, repeat=len(components)):
        word_id = encode_sector(tuple(int(label) for label in component_labels))
        label_by_component = dict(zip(components, component_labels, strict=True))
        ordered_factors = tuple(
            category.dual(label_by_component[factor["component"]])
            if factor["variance"] == "dual"
            else label_by_component[factor["component"]]
            for factor in factors
        )
        trace = fusion_reachability_trace(category, ordered_factors)
        final_reachable = trace[-1]["reachable"]
        rank = int(final_reachable.get(str(category.unit), 0))
        payloads.append(
            {
                "puncture_word_id": word_id,
                "component_order": list(components),
                "component_labels": list(component_labels),
                "ordered_factor_labels": list(ordered_factors),
                "factor_provenance": [
                    {
                        "cut_id": factor["cut_id"],
                        "component": factor["component"],
                        "variance": factor["variance"],
                        "oriented_label": ordered_factors[index],
                    }
                    for index, factor in enumerate(factors)
                ],
                "fusion_reachability_trace": trace,
                "vacuum_rank": rank,
                "status": "VACUUM_PRESENT" if rank else "NO_VACUUM_CHANNEL",
            }
        )
        word_id_by_component_labels[tuple(component_labels)] = word_id
    if len(payloads) != EXPECTED_UNIQUE_PUNCTURE_WORDS:
        raise AssertionError("unexpected unique puncture word count")
    return payloads, word_id_by_component_labels


def sector_cost(context: dict[str, Any], labels: dict[str, int]) -> int:
    active = {component for component, label in labels.items() if label != 0}
    cost = 1 + len(active)
    for form in context["forms"]:
        kind = form["kind"]
        if kind == "cross":
            over = context["source"]["component_by_piece"][piece_from_strand(form["over"])]
            under = context["source"]["component_by_piece"][piece_from_strand(form["under"])]
            if over in active and under in active:
                cost += 3
        elif kind == "kink":
            component = context["source"]["component_by_piece"][piece_from_strand(form["strand"])]
            if component in active:
                cost += abs(int(form.get("times", 1)))
    return cost


def piece_from_strand(strand: str) -> str:
    return strand.rsplit(".", 1)[0]


def build_plan(work_root: Path, chunk_count: int, allow_dirty: bool) -> dict[str, Any]:
    context = load_context()
    repo = git_metadata()
    if repo["dirty"] and not allow_dirty:
        raise ValueError("refusing to create an evaluation plan from a dirty worktree")
    words, word_id_by_labels = puncture_word_payloads(context)
    rank_by_word = {word["puncture_word_id"]: word["vacuum_rank"] for word in words}
    puncture_index = tuple(
        context["ordinary"].index(component)
        for component in context["puncture_components"]
    )
    pruned = []
    surviving = []
    rank_distribution = Counter()
    for sector_id in range(EXPECTED_TOTAL_SECTORS):
        labels_tuple = decode_sector(sector_id, len(context["ordinary"]))
        puncture_labels = tuple(labels_tuple[index] for index in puncture_index)
        word_id = word_id_by_labels[puncture_labels]
        rank = rank_by_word[word_id]
        rank_distribution[rank] += 1
        base = {
            "sector_id": sector_id,
            "labels": list(labels_tuple),
            "puncture_word_id": word_id,
            "projector_rank": rank,
        }
        if rank == 0:
            pruned.append({**base, "status": "PRUNED_NO_VACUUM"})
        else:
            labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
            surviving.append({**base, "estimated_cost": sector_cost(context, labels)})
    if len(pruned) != EXPECTED_ZERO_SECTORS or len(surviving) != EXPECTED_SURVIVING_SECTORS:
        raise AssertionError("projector sweep counts changed")

    chunk_count = min(max(1, int(chunk_count)), len(surviving))
    ordered_surviving = sorted(
        surviving, key=lambda item: (item["estimated_cost"], item["sector_id"])
    )
    quotient, remainder = divmod(len(ordered_surviving), chunk_count)
    bins = []
    offset = 0
    for chunk_id in range(chunk_count):
        size = quotient + (1 if chunk_id < remainder else 0)
        sectors = ordered_surviving[offset : offset + size]
        offset += size
        costs = [sector["estimated_cost"] for sector in sectors]
        bins.append({
            "cost": sum(costs),
            "min_cost": min(costs),
            "max_cost": max(costs),
            "sector_ids": [sector["sector_id"] for sector in sectors],
        })
    if offset != len(ordered_surviving):
        raise AssertionError("microchunk partition did not cover every surviving sector")

    evaluator_sha = sha256_bytes(
        (REPO_ROOT / "experiments/sage/ribbon_graph_evaluator.py").read_bytes()
    )
    runner_sha = sha256_bytes(Path(__file__).read_bytes())
    identity_payload = {
        "schema": "twisted-yetter.figure21-su2-2-evaluation-identity.v1",
        "input_sha256": context["input_sha256"],
        "projected_ir_hash": stable_hash(context["ir"]),
        "coupon_graph_hash": context["graph"]["graph_hash"],
        "category_id": context["category_id"],
        "projector_normalization": "OMEGA_SPECIAL_LOOP_DIVIDED_BY_SUM_D_SQUARED",
        "character_twist": "untwisted",
        "ordinary_component_order": list(context["ordinary"]),
        "evaluator_source_sha256": evaluator_sha,
        "runner_source_sha256": runner_sha,
        "git_commit": repo["commit"],
    }
    evaluation_id = stable_hash(identity_payload)
    plan = {
        "schema": "twisted-yetter.figure21-su2-2-workload-plan.v1",
        "status": "READY",
        "evaluation_id": evaluation_id,
        "evaluation_identity": identity_payload,
        "created_at_utc": utc_now(),
        "repo": repo,
        "input": str(INPUT.relative_to(REPO_ROOT)),
        "category": context["category_name"],
        "ordinary_component_order": list(context["ordinary"]),
        "puncture_component_order": list(context["puncture_components"]),
        "puncture_component_counts": context["puncture_counts"],
        "total_sector_count": EXPECTED_TOTAL_SECTORS,
        "pruned_sector_count": len(pruned),
        "surviving_sector_count": len(surviving),
        "rank_distribution": {
            str(rank): count for rank, count in sorted(rank_distribution.items())
        },
        "chunk_count": len(bins),
        "scheduling": {
            "strategy": "GLOBAL_COST_ASCENDING_CONTIGUOUS_MICROCHUNKS",
            "estimated_cost_definition": "active non-unit crossing and kink count",
            "worker_assignment": "chunk_id modulo worker_count",
        },
        "chunks": [
            {
                "chunk_id": index,
                "estimated_cost": chunk["cost"],
                "minimum_sector_cost": chunk["min_cost"],
                "maximum_sector_cost": chunk["max_cost"],
                "sector_ids": chunk["sector_ids"],
            }
            for index, chunk in enumerate(bins)
        ],
        "pruned_sectors": pruned,
    }
    atomic_json(work_root / "puncture-words.json", {
        "schema": "twisted-yetter.figure21-su2-2-puncture-words.v1",
        "evaluation_id": evaluation_id,
        "word_count": len(words),
        "words": words,
    })
    atomic_json(work_root / "workload-plan.json", plan)
    return plan


def load_plan(work_root: Path) -> dict[str, Any]:
    return json.loads((work_root / "workload-plan.json").read_text())


def evaluate_sector(
    context: dict[str, Any],
    plan: dict[str, Any],
    sector_id: int,
    projector_rank: int,
    puncture_word_id: int,
) -> dict[str, Any]:
    started = time.perf_counter()
    labels_tuple = decode_sector(sector_id, len(context["ordinary"]))
    labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
    value, stats = context["evaluator"].fixed_label_value(context["graph"], labels)
    kirby_weight = math.prod(
        float(context["category"].dimension(label)) for label in labels_tuple
    )
    weighted = kirby_weight * value
    absolute = abs(value)
    if value == 0.0 + 0.0j:
        status = "EVALUATED_EXACT_ZERO"
    elif absolute <= NUMERIC_ZERO_TOLERANCE:
        status = "NUMERICALLY_SMALL"
    else:
        status = "EVALUATED_NONZERO"
    contributions = [
        {
            "special_label": item["special_label"],
            "omega_coefficient": item["omega_coefficient"],
            "source_value": complex_json(item["source_value"]),
            "weighted_source_value": complex_json(item["weighted_source_value"]),
            "source_stats": {
                key: item["source_stats"].get(key)
                for key in (
                    "f_rotations",
                    "leaf_r",
                    "block_r",
                    "cups",
                    "caps",
                    "kinks",
                    "max_active_strands",
                    "max_state_support",
                    "unit_pruned_components",
                )
                if key in item["source_stats"]
            },
        }
        for item in stats["special_label_contributions"]
    ]
    return {
        "sector_id": sector_id,
        "labels": list(labels_tuple),
        "puncture_word_id": puncture_word_id,
        "projector_rank": projector_rank,
        "status": status,
        "raw_graph_scalar": complex_json(value),
        "kirby_weight": kirby_weight,
        "weighted_contribution": complex_json(weighted),
        "imaginary_residual": abs(value.imag),
        "elapsed_seconds": time.perf_counter() - started,
        "special_label_contributions": contributions,
        "evaluation_id": plan["evaluation_id"],
    }


def _timeout_handler(_signum, _frame):
    raise SectorTimeout("fixed-sector evaluation exceeded max seconds")


def run_chunk(work_root: Path, chunk_id: int, max_seconds: float) -> dict[str, Any]:
    plan = load_plan(work_root)
    if not 0 <= chunk_id < plan["chunk_count"]:
        raise ValueError("chunk id out of range")
    output = work_root / "chunks" / f"chunk-{chunk_id:04d}.json"
    if output.exists():
        existing = json.loads(output.read_text())
        if existing.get("evaluation_id") != plan["evaluation_id"]:
            raise ValueError(f"chunk {chunk_id} belongs to another evaluation")
        return existing
    context = load_context()
    chunk = plan["chunks"][chunk_id]
    pruned_by_id = {
        item["sector_id"]: item for item in plan["pruned_sectors"]
    }
    if any(sector_id in pruned_by_id for sector_id in chunk["sector_ids"]):
        raise AssertionError("surviving chunk contains a pruned sector")
    word_payload = json.loads((work_root / "puncture-words.json").read_text())
    rank_by_word = {
        item["puncture_word_id"]: item["vacuum_rank"]
        for item in word_payload["words"]
    }
    puncture_index = tuple(
        plan["ordinary_component_order"].index(component)
        for component in plan["puncture_component_order"]
    )
    records = []
    started_at = utc_now()
    started_clock = time.perf_counter()
    old_handler = signal.signal(signal.SIGALRM, _timeout_handler)
    try:
        for sector_id in chunk["sector_ids"]:
            labels_tuple = decode_sector(
                sector_id, len(plan["ordinary_component_order"])
            )
            puncture_labels = tuple(labels_tuple[index] for index in puncture_index)
            word_id = encode_sector(puncture_labels)
            rank = rank_by_word[word_id]
            try:
                if max_seconds > 0:
                    signal.setitimer(signal.ITIMER_REAL, max_seconds)
                record = evaluate_sector(
                    context, plan, sector_id, rank, word_id
                )
            except SectorTimeout as exc:
                failure = {
                    "schema": "twisted-yetter.figure21-su2-2-sector-failure.v1",
                    "evaluation_id": plan["evaluation_id"],
                    "chunk_id": chunk_id,
                    "sector_id": sector_id,
                    "labels": list(labels_tuple),
                    "puncture_word_id": word_id,
                    "projector_rank": rank,
                    "status": "TIMEOUT",
                    "reason": str(exc),
                    "max_seconds": max_seconds,
                    "utc": utc_now(),
                }
                atomic_json(work_root / "failures" / f"sector-{sector_id:06d}.json", failure)
                raise
            except Exception as exc:
                failure = {
                    "schema": "twisted-yetter.figure21-su2-2-sector-failure.v1",
                    "evaluation_id": plan["evaluation_id"],
                    "chunk_id": chunk_id,
                    "sector_id": sector_id,
                    "labels": list(labels_tuple),
                    "puncture_word_id": word_id,
                    "projector_rank": rank,
                    "status": "FAILED",
                    "exception_type": type(exc).__name__,
                    "reason": str(exc),
                    "utc": utc_now(),
                }
                atomic_json(work_root / "failures" / f"sector-{sector_id:06d}.json", failure)
                raise
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            records.append(record)
    finally:
        signal.signal(signal.SIGALRM, old_handler)
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-sector-chunk.v1",
        "status": "PASS",
        "evaluation_id": plan["evaluation_id"],
        "chunk_id": chunk_id,
        "host": socket.gethostname(),
        "pid": __import__("os").getpid(),
        "utc_start": started_at,
        "utc_finish": utc_now(),
        "elapsed_seconds": time.perf_counter() - started_clock,
        "sector_count": len(records),
        "records": records,
    }
    payload["records_sha256"] = sha256_bytes(
        json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    )
    atomic_json(output, payload)
    return payload


def run_worker(work_root: Path, worker_index: int, worker_count: int, max_seconds: float) -> None:
    plan = load_plan(work_root)
    if not 0 <= worker_index < worker_count:
        raise ValueError("worker index must be in 0..worker_count-1")
    for chunk_id in range(worker_index, plan["chunk_count"], worker_count):
        payload = run_chunk(work_root, chunk_id, max_seconds)
        print(
            json.dumps(
                {
                    "chunk_id": chunk_id,
                    "sector_count": payload["sector_count"],
                    "elapsed_seconds": payload["elapsed_seconds"],
                },
                sort_keys=True,
            ),
            flush=True,
        )


def workload_status(work_root: Path) -> dict[str, Any]:
    plan = load_plan(work_root)
    completed_chunks = []
    completed_sector_count = 0
    elapsed_worker_seconds = 0.0
    recent_rates = []
    hosts = Counter()
    for chunk in plan["chunks"]:
        chunk_id = chunk["chunk_id"]
        path = work_root / "chunks" / f"chunk-{chunk_id:04d}.json"
        if not path.exists():
            continue
        payload = json.loads(path.read_text())
        if payload.get("evaluation_id") != plan["evaluation_id"]:
            raise ValueError(f"chunk {chunk_id} evaluation identity mismatch")
        sector_count = int(payload["sector_count"])
        elapsed = float(payload["elapsed_seconds"])
        completed_chunks.append(chunk_id)
        completed_sector_count += sector_count
        elapsed_worker_seconds += elapsed
        hosts[payload["host"]] += sector_count
        if elapsed > 0:
            recent_rates.append((chunk_id, sector_count / elapsed))

    recent_rates.sort()
    recent_rates = recent_rates[-min(100, len(recent_rates)):]
    recent_sector_rate = (
        sum(rate for _, rate in recent_rates) / len(recent_rates)
        if recent_rates else None
    )
    remaining_sector_count = plan["surviving_sector_count"] - completed_sector_count
    failure_count = len(list((work_root / "failures").glob("sector-*.json")))
    first_missing = next(
        (
            chunk["chunk_id"]
            for chunk in plan["chunks"]
            if chunk["chunk_id"] not in set(completed_chunks)
        ),
        None,
    )
    return {
        "schema": "twisted-yetter.figure21-su2-2-workload-status.v1",
        "evaluation_id": plan["evaluation_id"],
        "utc": utc_now(),
        "scheduling": plan.get("scheduling"),
        "chunk_count": plan["chunk_count"],
        "completed_chunk_count": len(completed_chunks),
        "completed_surviving_sector_count": completed_sector_count,
        "remaining_surviving_sector_count": remaining_sector_count,
        "projector_pruned_sector_count": plan["pruned_sector_count"],
        "completed_total_sector_count": plan["pruned_sector_count"] + completed_sector_count,
        "total_sector_count": plan["total_sector_count"],
        "completed_fraction": (
            plan["pruned_sector_count"] + completed_sector_count
        ) / plan["total_sector_count"],
        "elapsed_worker_seconds": elapsed_worker_seconds,
        "recent_sector_rate_per_worker_second": recent_sector_rate,
        "optimistic_remaining_worker_seconds_at_recent_rate": (
            remaining_sector_count / recent_sector_rate
            if recent_sector_rate else None
        ),
        "first_missing_chunk_id": first_missing,
        "failure_count": failure_count,
        "completed_sectors_by_host": dict(sorted(hosts.items())),
    }


def trace_sector(work_root: Path, sector_id: int, output: Path) -> None:
    plan = load_plan(work_root)
    context = load_context()
    labels_tuple = decode_sector(sector_id, len(context["ordinary"]))
    puncture_index = tuple(
        plan["ordinary_component_order"].index(component)
        for component in plan["puncture_component_order"]
    )
    puncture_labels = tuple(labels_tuple[index] for index in puncture_index)
    word_id = encode_sector(puncture_labels)
    words = json.loads((work_root / "puncture-words.json").read_text())["words"]
    word = next(item for item in words if item["puncture_word_id"] == word_id)
    if word["vacuum_rank"] == 0:
        payload = {
            "schema": "twisted-yetter.figure21-su2-2-sector-trace.v1",
            "evaluation_id": plan["evaluation_id"],
            "sector_id": sector_id,
            "labels": list(labels_tuple),
            "status": "PRUNED_NO_VACUUM",
            "puncture_word": word,
        }
    else:
        record = evaluate_sector(
            context, plan, sector_id, word["vacuum_rank"], word_id
        )
        payload = {
            "schema": "twisted-yetter.figure21-su2-2-sector-trace.v1",
            "evaluation_id": plan["evaluation_id"],
            "sector_id": sector_id,
            "status": record["status"],
            "puncture_word": word,
            "record": record,
        }
    atomic_json(output, payload)


def aggregate(work_root: Path, output: Path, ledger: Path) -> dict[str, Any]:
    plan = load_plan(work_root)
    records_by_id: dict[int, dict[str, Any]] = {
        item["sector_id"]: item for item in plan["pruned_sectors"]
    }
    chunk_metadata = []
    for chunk_id in range(plan["chunk_count"]):
        path = work_root / "chunks" / f"chunk-{chunk_id:04d}.json"
        if not path.exists():
            raise ValueError(f"missing chunk {chunk_id}")
        chunk = json.loads(path.read_text())
        if chunk.get("evaluation_id") != plan["evaluation_id"]:
            raise ValueError(f"chunk {chunk_id} evaluation identity mismatch")
        expected_hash = sha256_bytes(
            json.dumps(chunk["records"], sort_keys=True, separators=(",", ":")).encode()
        )
        if expected_hash != chunk.get("records_sha256"):
            raise ValueError(f"chunk {chunk_id} record checksum mismatch")
        for record in chunk["records"]:
            sector_id = record["sector_id"]
            if sector_id in records_by_id:
                raise ValueError(f"duplicate sector {sector_id}")
            records_by_id[sector_id] = record
        chunk_metadata.append(
            {
                "chunk_id": chunk_id,
                "sector_count": chunk["sector_count"],
                "elapsed_seconds": chunk["elapsed_seconds"],
                "host": chunk["host"],
                "records_sha256": chunk["records_sha256"],
            }
        )
    expected_ids = set(range(EXPECTED_TOTAL_SECTORS))
    if set(records_by_id) != expected_ids:
        missing = sorted(expected_ids - set(records_by_id))
        extra = sorted(set(records_by_id) - expected_ids)
        raise ValueError(f"sector coverage mismatch: missing={missing[:20]}, extra={extra[:20]}")
    ordered = [records_by_id[index] for index in range(EXPECTED_TOTAL_SECTORS)]
    contributions = [
        complex(*record["weighted_contribution"])
        for record in ordered
        if "weighted_contribution" in record
    ]
    forward = complex(
        math.fsum(value.real for value in contributions),
        math.fsum(value.imag for value in contributions),
    )
    reverse = complex(
        math.fsum(value.real for value in reversed(contributions)),
        math.fsum(value.imag for value in reversed(contributions)),
    )
    order_difference = abs(forward - reverse)
    difference = forward - EXPECTED_STANDARD_VALUE
    statuses = Counter(record["status"] for record in ordered)
    controls_pass = (
        order_difference <= SUMMATION_ORDER_TOLERANCE
        and not statuses.get("FAILED")
        and not statuses.get("TIMEOUT")
    )
    match = (
        controls_pass
        and abs(difference) <= MATCH_TOLERANCE
        and abs(forward.imag) <= MATCH_TOLERANCE
    )
    ledger.parent.mkdir(parents=True, exist_ok=True)
    with gzip.open(ledger, "wt") as handle:
        handle.write(json.dumps({
            "record_kind": "header",
            "schema": "twisted-yetter.figure21-su2-2-sector-ledger.v1",
            "evaluation_id": plan["evaluation_id"],
            "component_order": plan["ordinary_component_order"],
            "sector_count": EXPECTED_TOTAL_SECTORS,
        }, sort_keys=True) + "\n")
        for record in ordered:
            handle.write(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n")
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-full-evaluation.v1",
        "status": "YES" if match else "NO",
        "mathematical_status": "DRAFT_TRANSCRIPTION_NUMERIC_COMPARISON",
        "evaluation_id": plan["evaluation_id"],
        "evaluation_identity": plan["evaluation_identity"],
        "figure21_value": complex_json(forward),
        "reverse_order_value": complex_json(reverse),
        "summation_order_difference": order_difference,
        "standard_value": complex_json(EXPECTED_STANDARD_VALUE),
        "absolute_difference": abs(difference),
        "imaginary_residual": abs(forward.imag),
        "match_tolerance": MATCH_TOLERANCE,
        "summation_order_tolerance": SUMMATION_ORDER_TOLERANCE,
        "match": "YES" if match else "NO",
        "sector_status_counts": dict(sorted(statuses.items())),
        "total_sector_count": len(ordered),
        "evaluated_sector_count": len(contributions),
        "chunk_count": len(chunk_metadata),
        "chunks": chunk_metadata,
        "ledger": str(ledger),
        "ledger_sha256": sha256_bytes(ledger.read_bytes()),
        "controls_pass": controls_pass,
        "utc_finish": utc_now(),
        "environment": {
            "python": platform.python_version(),
            "host": socket.gethostname(),
        },
        "reproduce_commands": {
            "plan": f"sage --python {Path(__file__).relative_to(REPO_ROOT)} plan --work-root {work_root}",
            "worker": f"sage --python {Path(__file__).relative_to(REPO_ROOT)} run-worker --work-root {work_root} --worker-index 0 --worker-count 2",
            "aggregate": f"sage --python {Path(__file__).relative_to(REPO_ROOT)} aggregate --work-root {work_root} --output {output} --ledger {ledger}",
        },
    }
    atomic_json(output, payload)
    return payload


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser()
    sub = root.add_subparsers(dest="command", required=True)
    plan = sub.add_parser("plan")
    plan.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    plan.add_argument("--chunk-count", type=int, default=12000)
    plan.add_argument("--allow-dirty", action="store_true")
    chunk = sub.add_parser("run-chunk")
    chunk.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    chunk.add_argument("--chunk-id", type=int, required=True)
    chunk.add_argument("--max-seconds", type=float, default=300.0)
    worker = sub.add_parser("run-worker")
    worker.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    worker.add_argument("--worker-index", type=int, required=True)
    worker.add_argument("--worker-count", type=int, required=True)
    worker.add_argument("--max-seconds", type=float, default=300.0)
    status = sub.add_parser("status")
    status.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    trace = sub.add_parser("trace-sector")
    trace.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    trace.add_argument("--sector-id", type=int, required=True)
    trace.add_argument("--output", type=Path, required=True)
    aggregate_parser = sub.add_parser("aggregate")
    aggregate_parser.add_argument("--work-root", type=Path, default=DEFAULT_WORK_ROOT)
    aggregate_parser.add_argument("--output", type=Path, required=True)
    aggregate_parser.add_argument("--ledger", type=Path, required=True)
    return root


def main() -> None:
    args = parser().parse_args()
    if args.command == "plan":
        payload = build_plan(args.work_root, args.chunk_count, args.allow_dirty)
        print(json.dumps({
            "status": payload["status"],
            "evaluation_id": payload["evaluation_id"],
            "pruned": payload["pruned_sector_count"],
            "surviving": payload["surviving_sector_count"],
            "chunks": payload["chunk_count"],
        }, indent=2))
    elif args.command == "run-chunk":
        print(json.dumps(run_chunk(args.work_root, args.chunk_id, args.max_seconds), indent=2, default=str))
    elif args.command == "run-worker":
        run_worker(args.work_root, args.worker_index, args.worker_count, args.max_seconds)
    elif args.command == "status":
        print(json.dumps(workload_status(args.work_root), indent=2))
    elif args.command == "trace-sector":
        trace_sector(args.work_root, args.sector_id, args.output)
    elif args.command == "aggregate":
        print(json.dumps(aggregate(args.work_root, args.output, args.ledger), indent=2))
    else:
        raise AssertionError(args.command)


if __name__ == "__main__":
    main()
