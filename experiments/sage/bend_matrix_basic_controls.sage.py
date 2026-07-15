#!/usr/bin/env python3
"""Check F-derived trivalent bend matrices on calibrated category adapters."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import platform
import subprocess
import sys

from experiments.sage.morse_category_registry import build_category
from experiments.sage.morse_fusion_evaluator import (
    MorseEvaluator,
    left_bend_fusion_matrix,
    right_bend_fusion_matrix,
)
from experiments.sage.morse_pivotal_contract import PivotalCapabilityError


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "category-pivotal"
    / "bend-matrix-basic-controls-v1.json"
)
DEFAULT_CASES = (
    "su2:2",
    "su2:3",
    "su2:4",
    "su2:5",
    "su2:6",
    "su2:8",
    "su3-2",
    "dic3",
    "da4",
)
EXPECTED_BEND_STATUS = {"da4": "fail"}
EXPECTED_MORSE_STATUS = {"da4": "rejected-missing-pivotal-profile"}


def adjoint_identity_residual(entries) -> float:
    size = len(entries)
    if any(len(row) != size for row in entries):
        return math.inf
    return max(
        (
            abs(
                sum(
                    entries[index][row].conjugate() * entries[index][column]
                    for index in range(size)
                )
                - float(row == column)
            )
            for row in range(size)
            for column in range(size)
        ),
        default=0.0,
    )


def parse_case(spec: str):
    if spec.startswith("su2:"):
        return "su2", int(spec.split(":", 1)[1])
    return spec, None


def check_category(spec: str, tolerance: float, *, include_channels: bool) -> dict:
    category_name, level = parse_case(spec)
    category, display_name, category_id = build_category(category_name, level)
    channels = []
    max_residual = 0.0
    max_multiplicity = 0
    failed_channel_count = 0
    worst_channel = None
    for a in category.labels:
        for b in category.labels:
            for c, multiplicity in category.fusion_outputs(a, b):
                multiplicity = int(multiplicity)
                channel = {
                    "a": a,
                    "b": b,
                    "c": c,
                    "source_multiplicity": multiplicity,
                }
                max_multiplicity = max(max_multiplicity, multiplicity)
                for name, constructor in (
                    ("left", left_bend_fusion_matrix),
                    ("right", right_bend_fusion_matrix),
                ):
                    matrix = constructor(category, a, b, c)
                    residual = adjoint_identity_residual(matrix["entries"])
                    channel[f"{name}_target_multiplicity"] = len(
                        matrix["target_basis"]
                    )
                    channel[f"{name}_unitarity_residual"] = residual
                    max_residual = max(max_residual, residual)
                channel_residual = max(
                    channel["left_unitarity_residual"],
                    channel["right_unitarity_residual"],
                )
                if channel_residual > tolerance:
                    failed_channel_count += 1
                if worst_channel is None or channel_residual > worst_channel[0]:
                    worst_channel = (channel_residual, channel)
                channels.append(channel)
    status = "pass" if max_residual <= tolerance else "fail"
    unknot = (
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
    )
    try:
        unit_value, _ = MorseEvaluator(category).fixed_label_value(
            unknot, {"A": category.unit}
        )
        morse_status = "pass"
        morse_value = [unit_value.real, unit_value.imag]
        morse_error = None
    except PivotalCapabilityError as exc:
        morse_status = "rejected-missing-pivotal-profile"
        morse_value = None
        morse_error = str(exc)
    expected_bend = EXPECTED_BEND_STATUS.get(spec, "pass")
    expected_morse = EXPECTED_MORSE_STATUS.get(spec, "pass")
    return {
        "case": spec,
        "display_name": display_name,
        "category_id": category_id,
        "status": status,
        "expected_bend_status": expected_bend,
        "expected_morse_status": expected_morse,
        "expectation_met": status == expected_bend and morse_status == expected_morse,
        "morse_contract_status": morse_status,
        "morse_unit_unknot_value": morse_value,
        "morse_contract_error": morse_error,
        "admissible_channel_count": len(channels),
        "max_fusion_multiplicity": max_multiplicity,
        "max_adjoint_identity_residual": max_residual,
        "failed_channel_count": failed_channel_count,
        "worst_channel": worst_channel[1] if worst_channel is not None else None,
        "adapter_path_basis_is_orthonormal_claim": getattr(
            category, "path_basis_is_orthonormal", None
        ),
        "adapter_svd_orthonormalization_applied": getattr(
            category, "orthonormalize_svd_intertwiners", None
        ),
        "pivotal_profile_present": getattr(category, "pivotal_profile", None)
        is not None,
        **({"channels": channels} if include_channels else {}),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--tolerance", type=float, default=1e-9)
    parser.add_argument("--include-channels", action="store_true")
    args = parser.parse_args()

    started = datetime.now(timezone.utc)
    cases = args.cases or list(DEFAULT_CASES)
    results = [
        check_category(
            spec, args.tolerance, include_channels=args.include_channels
        )
        for spec in cases
    ]
    finished = datetime.now(timezone.utc)
    try:
        git_commit = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True
        ).strip()
        git_status = subprocess.check_output(
            ["git", "status", "--short"], cwd=REPO_ROOT, text=True
        ).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        git_commit = None
        git_status = None
    payload = {
        "schema": "twisted-yetter.bend-matrix-basic-controls.v1",
        "status": "pass" if all(case["expectation_met"] for case in results) else "fail",
        "mathematical_status": "ALGEBRAIC_CONTROL_NOT_FIGURE21_EVALUATION",
        "scope": (
            "F-derived left/right currying matrices for trivalent vertices; "
            "plus the fail-closed pivotal contract on a unit-labelled Morse unknot. "
            "Frobenius-Schur flag reversals and general graph contraction are not included"
        ),
        "generator_script": "experiments/sage/bend_matrix_basic_controls.sage.py",
        "argv": sys.argv,
        "started_at": started.isoformat(),
        "finished_at": finished.isoformat(),
        "elapsed_seconds": (finished - started).total_seconds(),
        "python": sys.version,
        "platform": platform.platform(),
        "repo_root": str(REPO_ROOT),
        "git_commit": git_commit,
        "dirty": bool(git_status),
        "git_status_short": git_status,
        "tolerance": args.tolerance,
        "cases": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(json.dumps({
        "status": payload["status"],
        "output": str(args.output.resolve()),
        "elapsed_seconds": payload["elapsed_seconds"],
        "cases": [
            {
                "case": case["case"],
                "status": case["status"],
                "channels": case["admissible_channel_count"],
                "max_multiplicity": case["max_fusion_multiplicity"],
                "max_residual": case["max_adjoint_identity_residual"],
                "morse_contract_status": case["morse_contract_status"],
                "expectation_met": case["expectation_met"],
            }
            for case in results
        ],
    }, indent=2))
    if payload["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
