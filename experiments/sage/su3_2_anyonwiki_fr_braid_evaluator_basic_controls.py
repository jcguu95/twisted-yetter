#!/usr/bin/env python3
"""Basic controls for the SU(3)_2 AnyonWiki F/R braid evaluator."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import json
from pathlib import Path
import sys
import time

import su3_2_anyonwiki_fr_braid_evaluator as su3


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "anyon-wiki-su3-2"
    / "su3-2-anyonwiki-fr-braid-evaluator-basic-controls-v1.json"
)
TOLERANCE = 1e-8


def row_json(control: str, labels, observed: complex, expected: complex, extra=None):
    difference = observed - expected
    return {
        "control": control,
        "labels": list(labels),
        "observed": su3.complex_json(observed),
        "expected": su3.complex_json(expected),
        "difference": su3.complex_json(difference),
        "abs_difference": repr(float(abs(difference))),
        "pass": bool(abs(difference) <= TOLERANCE),
        **(extra or {}),
    }


def parse_args(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--category-parameter", default="cat_1_3_1", choices=["cat_1_3_1", "cat_1_3_2"])
    parser.add_argument(
        "--braiding-convention",
        default="anyonwiki_direct",
        choices=["orientation_reversed", "anyonwiki_direct"],
    )
    parser.add_argument("--output", type=Path, default=OUTPUT)
    return parser.parse_args(argv)


def run_controls(args) -> dict:
    evaluator = su3.SU32AnyonWikiFRBraidEvaluator(
        category_parameter=args.category_parameter,
        braiding_convention=args.braiding_convention,
    )
    rows = []

    for label in evaluator.labels:
        for framing in (-2, -1, 0, 1, 2):
            observed, stats = evaluator.fixed_label_value(1, (), (label,), (framing,))
            expected = evaluator.dimension(label) * (evaluator.twist(label) ** framing)
            rows.append(
                row_json(
                    "framed_unknot",
                    (label,),
                    observed,
                    expected,
                    {"framing": framing, "evaluator_stats": stats},
                )
            )

    for left in evaluator.labels:
        for right in evaluator.labels:
            for framings in ((0, 0), (1, -1)):
                observed, stats = evaluator.fixed_label_value(2, (), (left, right), framings)
                expected = (
                    evaluator.dimension(left)
                    * evaluator.dimension(right)
                    * evaluator.twist(left) ** framings[0]
                    * evaluator.twist(right) ** framings[1]
                )
                rows.append(
                    row_json(
                        "split_two_component_unlink",
                        (left, right),
                        observed,
                        expected,
                        {"framings": list(framings), "evaluator_stats": stats},
                    )
                )

    for left in evaluator.labels:
        for right in evaluator.labels:
            observed, stats = evaluator.fixed_label_value(2, (1, 1), (left, right), (0, 0))
            rows.append(
                row_json(
                    "positive_hopf_sigma1_squared",
                    (left, right),
                    observed,
                    su3.hopf_expected(evaluator, left, right, positive=True),
                    {"braid_word": [1, 1], "framings": [0, 0], "evaluator_stats": stats},
                )
            )
            observed, stats = evaluator.fixed_label_value(2, (-1, -1), (left, right), (0, 0))
            rows.append(
                row_json(
                    "negative_hopf_sigma1_inverse_squared",
                    (left, right),
                    observed,
                    su3.hopf_expected(evaluator, left, right, positive=False),
                    {"braid_word": [-1, -1], "framings": [0, 0], "evaluator_stats": stats},
                )
            )

    simple_current_target_by_character = su3.simple_current_targets(evaluator)
    global_dim = su3.global_dimension(evaluator)
    for character in range(3):
        target = simple_current_target_by_character[(-character) % 3]
        for fixed_label in evaluator.labels:
            observed = 0.0 + 0.0j
            max_basis_size = 0
            for summand in evaluator.labels:
                fixed_value, stats = evaluator.fixed_label_value(
                    2,
                    (1, 1),
                    (summand, fixed_label),
                    (0, 0),
                )
                observed += (
                    evaluator.dimension(summand)
                    * su3.character_value(character, summand)
                    * fixed_value
                )
                max_basis_size = max(max_basis_size, int(stats.get("max_basis_size", 0)))
            expected = global_dim if fixed_label == target else 0.0 + 0.0j
            rows.append(
                row_json(
                    "colored_positive_hopf_projector",
                    (f"omega_{character}", fixed_label),
                    observed,
                    expected,
                    {
                        "target_simple_current": target,
                        "global_dimension": repr(float(global_dim)),
                        "max_basis_size": max_basis_size,
                    },
                )
            )

    split_baseline = su3.cp2_2cpbar_split_value(evaluator, (0, 0, 0))
    split_component_a = su3.cp2_2cpbar_split_value(evaluator, (0, 1, 0))
    split_ratio = split_component_a / split_baseline
    split_expected = evaluator.twist("(2,0)")
    rows.append(
        row_json(
            "cp2_2cpbar_split_alpha_010_phase",
            ("h", "e1", "e2"),
            split_ratio,
            split_expected,
            {
                "standard_alpha_order": ["h", "e1", "e2"],
                "standard_alpha": [0, 1, 0],
                "baseline_raw_value": su3.complex_json(split_baseline),
                "twisted_raw_value": su3.complex_json(split_component_a),
            },
        )
    )

    failures = [row for row in rows if not row["pass"]]
    return {
        "schema": "twisted-yetter.su3-2-anyonwiki-fr-braid-evaluator-basic-controls.v1",
        "status": "pass" if not failures else "fail",
        "generator_script": su3.rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/sage/su3_2_anyonwiki_fr_braid_evaluator_basic_controls.py",
        "utc_start": datetime.now(UTC).isoformat(),
        "repo": su3.repo_metadata(),
        "environment": su3.environment_metadata(),
        "category": su3.evaluator_metadata(evaluator),
        "simple_current_target_by_character": {
            str(key): value for key, value in simple_current_target_by_character.items()
        },
        "tolerance": repr(float(TOLERANCE)),
        "row_count": len(rows),
        "failure_count": len(failures),
        "failures": failures[:20],
        "rows": rows,
        "claim_boundary": (
            "Numeric controls for the selected AnyonWiki SU(3)_2 F/R evaluator. "
            "This checks the evaluator convention against framed unknots, split "
            "unlinks, Hopf links, and the Z/3 character projector; it is not a "
            "Yasui invariant computation."
        ),
    }


def main(argv=None) -> int:
    args = parse_args(argv)
    started = time.monotonic()
    payload = run_controls(args)
    payload["utc_finish"] = datetime.now(UTC).isoformat()
    payload["elapsed_seconds"] = time.monotonic() - started
    su3.write_json(args.output, payload)
    print(
        json.dumps(
            {
                "artifact": su3.rel(args.output),
                "status": payload["status"],
                "row_count": payload["row_count"],
                "failure_count": payload["failure_count"],
                "elapsed_seconds": payload["elapsed_seconds"],
            },
            sort_keys=True,
        )
    )
    return 0 if payload["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
