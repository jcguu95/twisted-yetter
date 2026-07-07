#!/usr/bin/env python3
"""Yasui Figure 3 a=1 SU(3)_2 AnyonWiki F/R aggregate evaluator."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
from itertools import product
import json
from pathlib import Path
import sys
import time

import su3_2_anyonwiki_fr_braid_evaluator as su3


REPO_ROOT = Path(__file__).resolve().parents[2]
BRAID_PAYLOAD = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-braid-payload-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-su3-2-anyonwiki-aggregate-v1.json"
)
PRIMARY_TWIST_BY_COMPONENT = {"C": 0, "A": 1, "B": 0}


def parse_args(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--braid-payload", type=Path, default=BRAID_PAYLOAD)
    parser.add_argument("--category-parameter", default="cat_1_3_1", choices=["cat_1_3_1", "cat_1_3_2"])
    parser.add_argument(
        "--braiding-convention",
        default="anyonwiki_direct",
        choices=["anyonwiki_direct", "orientation_reversed"],
    )
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--include-rows", action="store_true", default=True)
    return parser.parse_args(argv)


def sector_labels(labels: tuple[str, ...], index: int, component_count: int) -> tuple[str, ...]:
    total = len(labels) ** component_count
    if index < 0 or index >= total:
        raise ValueError(f"sector index {index} outside [0, {total})")
    remaining = index
    output = []
    for power in range(component_count - 1, -1, -1):
        place = len(labels) ** power
        digit = remaining // place
        remaining %= place
        output.append(labels[digit])
    return tuple(output)


def coefficient(evaluator: su3.SU32AnyonWikiFRBraidEvaluator, labels: tuple[str, ...], alpha: tuple[int, ...]) -> complex:
    value = 1.0 + 0.0j
    for label, character_power in zip(labels, alpha, strict=True):
        value *= evaluator.dimension(label) * su3.character_value(character_power, label)
    return value


def alpha_by_component(braid: dict) -> tuple[int, ...]:
    return tuple(
        int(PRIMARY_TWIST_BY_COMPONENT[component]) % 3
        for component in braid["component_order_in_braid"]
    )


def aggregate_json(value: complex, global_dim: float) -> dict:
    return {
        "raw": su3.complex_json(value),
        "normalized_by_global_dimension": su3.complex_json(value / global_dim),
        "normalized_by_global_dimension_squared": su3.complex_json(value / (global_dim * global_dim)),
    }


def run_aggregate(args) -> dict:
    evaluator = su3.SU32AnyonWikiFRBraidEvaluator(
        category_parameter=args.category_parameter,
        braiding_convention=args.braiding_convention,
    )
    braid = su3.read_json(args.braid_payload)
    n_strands = int(braid["n_strands"])
    braid_word = tuple(int(item) for item in braid["braid_word"])
    framings = tuple(int(item) for item in braid["framings_in_braid_order"])
    component_count = len(braid["component_order_in_braid"])
    alphas = tuple(product(range(3), repeat=component_count))
    primary_alpha = alpha_by_component(braid)
    aggregates = {alpha: 0.0 + 0.0j for alpha in alphas}
    rows = []
    stats_summary = {
        "max_basis_size": 0,
        "max_state_size": 0,
        "unit_pruned_count": 0,
    }

    sector_total = len(evaluator.labels) ** component_count
    for index in range(sector_total):
        fixed_labels = sector_labels(evaluator.labels, index, component_count)
        amplitude, stats = evaluator.fixed_label_value(
            n_strands,
            braid_word,
            fixed_labels,
            framings,
        )
        for alpha in alphas:
            aggregates[alpha] += coefficient(evaluator, fixed_labels, alpha) * amplitude
        stats_summary["max_basis_size"] = max(
            stats_summary["max_basis_size"],
            int(stats.get("max_basis_size", 0)),
        )
        stats_summary["max_state_size"] = max(
            stats_summary["max_state_size"],
            int(stats.get("max_state_size", 0)),
        )
        if stats.get("unit_pruned"):
            stats_summary["unit_pruned_count"] += 1
        if args.include_rows:
            rows.append(
                {
                    "sector_index": index,
                    "fixed_component_labels": list(fixed_labels),
                    "fixed_sector_amplitude": su3.complex_json(amplitude),
                    "untwisted_coefficient": su3.complex_json(coefficient(evaluator, fixed_labels, (0, 0, 0))),
                    "primary_twisted_coefficient": su3.complex_json(coefficient(evaluator, fixed_labels, primary_alpha)),
                    "weighted_untwisted_contribution": su3.complex_json(
                        coefficient(evaluator, fixed_labels, (0, 0, 0)) * amplitude
                    ),
                    "weighted_primary_twisted_contribution": su3.complex_json(
                        coefficient(evaluator, fixed_labels, primary_alpha) * amplitude
                    ),
                    "evaluator_stats": stats,
                }
            )

    global_dim = su3.global_dimension(evaluator)
    untwisted = aggregates[(0, 0, 0)]
    primary = aggregates[primary_alpha]
    alpha_rows = []
    for alpha in alphas:
        value = aggregates[alpha]
        ratio = value / untwisted if abs(untwisted) > 0 else complex("nan")
        alpha_rows.append(
            {
                "alpha_order": list(braid["component_order_in_braid"]),
                "alpha": list(alpha),
                "raw_value": su3.complex_json(value),
                "ratio_to_untwisted": su3.complex_json(ratio),
                "differs_from_untwisted_abs": repr(float(abs(value - untwisted))),
                "is_primary_component_a_twist": bool(alpha == primary_alpha),
            }
        )

    split_untwisted = su3.cp2_2cpbar_split_value(evaluator, (0, 0, 0))
    split_primary = su3.cp2_2cpbar_split_value(evaluator, (0, 1, 0))
    return {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-su3-2-anyonwiki-aggregate.v1",
        "status": "computed-numeric",
        "generator_script": su3.rel(Path(__file__)),
        "evaluator_script": "experiments/sage/su3_2_anyonwiki_fr_braid_evaluator.py",
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/sage/yasui_figure3_a1_r1_normalized_su3_2_anyonwiki_aggregate.py",
        "repo": su3.repo_metadata(),
        "environment": su3.environment_metadata(),
        "category": su3.evaluator_metadata(evaluator),
        "link_id": "yasui-figure3-a1-r1-normalized",
        "case": {
            "source_braid_payload": su3.rel(args.braid_payload),
            "source_braid_payload_sha256": su3.file_sha256(args.braid_payload),
            "n_strands": n_strands,
            "braid_word_length": len(braid_word),
            "component_order_in_braid": braid["component_order_in_braid"],
            "framings_in_braid_order": list(framings),
            "sector_total": sector_total,
            "character_group_scanned": "(Z/3)^3 on braid components",
            "primary_twist": {
                "description": "generator character on source component A, matching the prior D(A4)c3w1 component-A route",
                "omega_by_component": PRIMARY_TWIST_BY_COMPONENT,
                "alpha_order": list(braid["component_order_in_braid"]),
                "alpha": list(primary_alpha),
            },
        },
        "global_dimension": repr(float(global_dim)),
        "aggregate_untwisted": aggregate_json(untwisted, global_dim),
        "aggregate_primary_component_a_twist": aggregate_json(primary, global_dim),
        "primary_ratio_to_untwisted": su3.complex_json(primary / untwisted),
        "primary_abs_difference_from_untwisted": repr(float(abs(primary - untwisted))),
        "all_character_aggregates": alpha_rows,
        "cp2_2cpbar_split_reference": {
            "presentation": "ordinary split unlink with framings (+1,-1,-1)",
            "standard_alpha_order": ["h", "e1", "e2"],
            "baseline_alpha": [0, 0, 0],
            "primary_reference_alpha": [0, 1, 0],
            "baseline_raw_value": su3.complex_json(split_untwisted),
            "primary_raw_value": su3.complex_json(split_primary),
            "primary_ratio_to_baseline": su3.complex_json(split_primary / split_untwisted),
            "note": "This split reference is the cheap CP2#2CPbar character signal, not a Yasui-link equality target.",
        },
        "evaluator_stats_summary": stats_summary,
        "rows": rows if args.include_rows else None,
        "claim_boundary": (
            "Numeric SU(3)_2 AnyonWiki F/R aggregate over the audited Yasui a=1 "
            "R1-normalized braid payload. This is not an exact theorem-level "
            "certificate and does not by itself prove an exotic-pair separation."
        ),
    }


def main(argv=None) -> int:
    args = parse_args(argv)
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    payload = run_aggregate(args)
    payload["utc_start"] = utc_start
    payload["utc_finish"] = datetime.now(UTC).isoformat()
    payload["elapsed_seconds"] = time.monotonic() - started
    su3.write_json(args.output, payload)
    print(
        json.dumps(
            {
                "artifact": su3.rel(args.output),
                "status": payload["status"],
                "sector_total": payload["case"]["sector_total"],
                "primary_ratio_to_untwisted": payload["primary_ratio_to_untwisted"]["display"],
                "primary_abs_difference_from_untwisted": payload["primary_abs_difference_from_untwisted"],
                "elapsed_seconds": payload["elapsed_seconds"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
