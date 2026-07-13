#!/usr/bin/env python3
"""Sweep SU(2)_2 vacuum-projector ranks for Figure 21 (right)."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

from sage.env import SAGE_VERSION

from experiments.sage.morse_category_registry import build_category
from experiments.sage.morse_fusion_evaluator import (
    MorseEvaluator,
    analyze_topology,
    expand_vacuum_coupon_graph_term,
    right_comb_fusion_path_counts,
    vacuum_coupon_path_basis,
)
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
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut-yasui"
    / "figure21-right-su2-2-untwisted-projector-sweep-v1.json"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_hash(value) -> str:
    return sha256_bytes(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    )


def git_metadata() -> dict:
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True
    ).strip()
    status = subprocess.check_output(
        ["git", "status", "--short"], cwd=REPO_ROOT, text=True
    ).splitlines()
    return {"commit": commit, "dirty": bool(status), "status_short": status}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    started_at = datetime.now(UTC)
    started_clock = time.perf_counter()

    source_bytes = INPUT.read_bytes()
    source = json.loads(source_bytes)
    forms = tuple(source["forms"])
    component_order = tuple(source["component_order"])
    special = tuple(source["special_components"])
    if special != ("red",):
        raise ValueError("Figure 21 SU(2)_2 control expects red as the sole special component")
    ordinary = tuple(component for component in component_order if component != "red")

    ir = compile_projected_morphism(
        forms,
        component_by_piece=source["component_by_piece"],
        special_components=special,
        component_order=component_order,
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    coupon = next(
        node
        for node in graph["nodes"]
        if node["kind"] == "vacuum-projector-coupon"
    )
    category, display_name, category_id = build_category("su2", 2)
    factors = tuple(coupon["factor_order"])

    def tensor_word(labels: dict[str, int]) -> tuple[int, ...]:
        return tuple(
            category.dual(labels[factor["component"]])
            if factor["variance"] == "dual"
            else labels[factor["component"]]
            for factor in factors
        )

    @lru_cache(maxsize=None)
    def vacuum_rank(word: tuple[int, ...]) -> int:
        return int(
            right_comb_fusion_path_counts(category, word).get(category.unit, 0)
        )

    rank_distribution: Counter[int] = Counter()
    first_zero = None
    first_nontrivial_survivor = None
    for assignment in product(category.labels, repeat=len(ordinary)):
        labels = dict(zip(ordinary, assignment, strict=True))
        rank = vacuum_rank(tensor_word(labels))
        rank_distribution[rank] += 1
        if rank == 0 and first_zero is None:
            first_zero = dict(labels)
        if rank and any(assignment) and first_nontrivial_survivor is None:
            first_nontrivial_survivor = (dict(labels), rank)

    all_unit = {component: category.unit for component in ordinary}
    _, all_unit_basis, all_unit_basis_metadata = vacuum_coupon_path_basis(
        category, coupon, all_unit
    )
    ordinary_all_unit_labels = {
        component: category.unit
        for component in analyze_topology(forms).component_order
    }
    all_unit_value, all_unit_stats = MorseEvaluator(category).fixed_label_value(
        forms, ordinary_all_unit_labels
    )

    zero_labels = {component: category.unit for component in ordinary}
    zero_labels["black"] = 1
    zero_rank = vacuum_rank(tensor_word(zero_labels))
    if zero_rank != 0:
        raise AssertionError("one black sigma puncture should have no vacuum channel")

    survivor_labels = {component: category.unit for component in ordinary}
    survivor_labels["green"] = 1
    survivor_rank = vacuum_rank(tensor_word(survivor_labels))
    if survivor_rank != 2:
        raise AssertionError("four green sigma punctures should have two vacuum paths")
    survivor_terms = [
        expand_vacuum_coupon_graph_term(
            category,
            graph,
            survivor_labels,
            basis_index=index,
            namespace="figure21-su2-2-green",
        )
        for index in range(survivor_rank)
    ]

    total_sectors = len(category.labels) ** len(ordinary)
    zero_sectors = rank_distribution[0]
    payload = {
        "schema": "twisted-yetter.figure21-su2-2-untwisted-projector-sweep.v1",
        "status": "PROJECTOR_SELECTION_CONTROLS_PASS_FULL_RT_VALUE_NOT_COMPUTED",
        "mathematical_status": "DRAFT_TRANSCRIPTION_NUMERIC_CONTROL_NOT_EXOTIC_DETECTION",
        "scope": "Untwisted SU(2)_2 fixed-color sector pruning by the special-disk vacuum projector.",
        "generator_script": "experiments/sage/figure21_su2_2_untwisted_projector_sweep.sage.py",
        "argv": sys.argv,
        "reproduce_command": (
            "DOT_SAGE=\"$PWD/.sage\" PYTHONPATH=. sage --python "
            "experiments/sage/figure21_su2_2_untwisted_projector_sweep.sage.py"
        ),
        "input": str(INPUT.relative_to(REPO_ROOT)),
        "input_sha256": sha256_bytes(source_bytes),
        "source_ref": source["source_ref"],
        "source_locator": source["source_locator"],
        "category": display_name,
        "category_id": category_id,
        "character_twist": "untwisted",
        "component_order": list(component_order),
        "ordinary_component_order": list(ordinary),
        "special_components": list(special),
        "coupon_graph_hash": graph["graph_hash"],
        "puncture_count": len(factors),
        "puncture_component_counts": dict(
            sorted(Counter(factor["component"] for factor in factors).items())
        ),
        "sector_sweep": {
            "total_sector_count": total_sectors,
            "zero_sector_count": zero_sectors,
            "surviving_sector_count": total_sectors - zero_sectors,
            "rank_distribution": {
                str(rank): count for rank, count in sorted(rank_distribution.items())
            },
            "unique_puncture_words_evaluated": vacuum_rank.cache_info().currsize,
        },
        "all_unit_control": {
            "labels": all_unit,
            "vacuum_rank": len(all_unit_basis),
            "projector_metadata": all_unit_basis_metadata,
            "projected_value": [all_unit_value.real, all_unit_value.imag],
            "reason": "all wires and the projector root are the tensor unit",
            "morse_stats": all_unit_stats,
        },
        "exact_zero_control": {
            "labels": zero_labels,
            "vacuum_rank": zero_rank,
            "projected_value": [0.0, 0.0],
            "reason": "one black sigma puncture has no total-unit fusion channel",
        },
        "collective_survivor_control": {
            "labels": survivor_labels,
            "vacuum_rank": survivor_rank,
            "reason": "four green sigma punctures retain two collective unit paths",
            "expanded_term_count": len(survivor_terms),
            "expanded_term_hashes": [stable_hash(term) for term in survivor_terms],
            "expanded_projection_vertex_counts": [
                term["expanded_coupon"]["projection_vertex_count"]
                for term in survivor_terms
            ],
            "expanded_inclusion_vertex_counts": [
                term["expanded_coupon"]["inclusion_vertex_count"]
                for term in survivor_terms
            ],
            "scalar_status": "NOT_COMPUTED_REQUIRES_NONHORIZONTAL_TRIVALENT_GRAPH_CONTRACTION",
        },
        "first_zero_assignment_in_lexicographic_sweep": first_zero,
        "first_nontrivial_survivor_in_lexicographic_sweep": {
            "labels": first_nontrivial_survivor[0],
            "vacuum_rank": first_nontrivial_survivor[1],
        },
        "full_untwisted_kirby_color_value": {
            "status": "BLOCKED",
            "reason": "The surviving nonhorizontal trivalent coupon graphs are expanded but not yet contracted.",
        },
        "environment": {
            "python": platform.python_version(),
            "sage": SAGE_VERSION,
        },
        "repo": git_metadata(),
        "utc_start": started_at.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - started_clock,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(
        json.dumps(
            {
                "status": payload["status"],
                "output": str(args.output.resolve()),
                "total_sectors": total_sectors,
                "zero_sectors": zero_sectors,
                "surviving_sectors": total_sectors - zero_sectors,
                "all_unit_value": payload["all_unit_control"]["projected_value"],
                "zero_control_value": payload["exact_zero_control"]["projected_value"],
                "green_survivor_rank": survivor_rank,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
