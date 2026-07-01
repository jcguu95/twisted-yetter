"""Fusion-channel gate for non-pointed MTC candidate testing.

Run from the repository root:

    uv run python experiments/scripts/mtc_fusion_channel_gate.py

This is not a full colored link evaluator.  It covers the part of a Hopf-star
diagram that is forced by the modular-data projector identity:

    central Omega_a around leaves X_1,...,X_n
      = global_dimension * mult(g_a in X_1 tensor ... tensor X_n)

For SU(2)_6, the target simple current is g_0=0 and g_1=6.  The gate uses only
fusion multiplicities and the SU(2)_6 projector identities already checked in
su2-6-modular-supported-v1.json.
"""

from __future__ import annotations

import argparse
import json
from itertools import product
from pathlib import Path
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
CANDIDATE_DATA = REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "mtc-candidate-data-v1.json"
SU2_PROJECTOR_DATA = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "su2-6-modular-supported-v1.json"
)
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "mtc-fusion-channel-gate-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import (  # noqa: E402
    default_tool_versions,
    dumps_certificate,
    file_sha256,
    git_metadata,
    hash_json,
    make_certificate,
    utc_now_iso,
)


Json = dict[str, Any]


def run_gate() -> Json:
    categories = load_categories()
    su2 = categories["SU(2)_6"]
    su3 = categories["SU(3)_2"]

    step3 = su2_hopf_star_gate(su2)
    step4 = su2_fusion_pressure_gate(su2)
    step5 = su3_next_candidate_gate(su3)
    validations = [
        {"name": "su2_step3_hopf_star_controls", "status": step3["status"]},
        {"name": "su2_step4_fusion_pressure_controls", "status": step4["status"]},
        {"name": "su3_step5_readiness_gate_is_structured", "status": step5["status"]},
    ]
    status = "pass" if all(item["status"] == "pass" for item in validations) else "fail"
    return {
        "schema": "twisted-yetter.mtc-fusion-channel-gate.v1",
        "status": status,
        "claim_level": "computed fusion-channel evidence / not full F-R evaluator",
        "scope": (
            "central Omega projector gates for Hopf-star style encircling diagrams, "
            "fusion associativity pressure, and next-candidate readiness"
        ),
        "not_scope": (
            "arbitrary braid closure, arbitrary planar diagram, full local-piece F/R evaluator, "
            "Kirby diagram parser, special-link/dotted-component evaluation, or exotic-pair computation"
        ),
        "source_artifacts": {
            "candidate_data": str(CANDIDATE_DATA.relative_to(REPO_ROOT)),
            "su2_projector_data": str(SU2_PROJECTOR_DATA.relative_to(REPO_ROOT)),
        },
        "validations": validations,
        "step_3_su2_6_hopf_star_fusion_channel_gate": step3,
        "step_4_su2_6_pressure_controls": step4,
        "step_5_su3_2_next_candidate_gate": step5,
    }


def su2_hopf_star_gate(category: Json) -> Json:
    targets = {"0": "0", "1": "6"}
    controls = [
        su2_star_control(category, targets, "1x1_omega0_keeps_vacuum", "0", ["1", "1"], 1),
        su2_star_control(category, targets, "1x1_omega1_rejects_simple_current", "1", ["1", "1"], 0),
        su2_star_control(category, targets, "3x3_omega0_keeps_vacuum", "0", ["3", "3"], 1),
        su2_star_control(category, targets, "3x3_omega1_keeps_simple_current", "1", ["3", "3"], 1),
        su2_star_control(category, targets, "2x4_omega0_rejects_vacuum", "0", ["2", "4"], 0),
        su2_star_control(category, targets, "2x4_omega1_keeps_simple_current", "1", ["2", "4"], 1),
        su2_star_control(category, targets, "1x5_omega1_keeps_simple_current", "1", ["1", "5"], 1),
    ]
    return {
        "status": "pass" if all(item["status"] == "pass" for item in controls) else "fail",
        "category_id": "SU(2)_6",
        "projector_formula": (
            "central Omega_a around fixed leaves equals global_dimension times "
            "multiplicity of target simple current g_a in the fusion product"
        ),
        "target_simple_currents": targets,
        "value_unit": {
            "kind": "global_dimension",
            "category_id": "SU(2)_6",
            "value": category["global_dimension"],
        },
        "controls": controls,
    }


def su2_star_control(
    category: Json,
    targets: dict[str, str],
    name: str,
    central_omega: str,
    leaf_labels: list[str],
    expected_multiplier: int,
) -> Json:
    target = targets[central_omega]
    fusion_distribution = fuse_sequence(category["fusion_rules"], leaf_labels)
    actual = fusion_distribution.get(target, 0)
    return {
        "name": name,
        "central_omega": central_omega,
        "target_simple_current": target,
        "leaf_labels": leaf_labels,
        "fusion_distribution": fusion_distribution,
        "expected_global_dimension_multiplier": expected_multiplier,
        "actual_global_dimension_multiplier": actual,
        "value": multiplier_value(category, actual),
        "status": "pass" if actual == expected_multiplier else "fail",
    }


def su2_fusion_pressure_gate(category: Json) -> Json:
    triples = list(product(category["simple_labels"], repeat=3))
    associativity_failures = []
    for labels in triples:
        left = fuse_three_left(category["fusion_rules"], list(labels))
        right = fuse_three_right(category["fusion_rules"], list(labels))
        if left != right:
            associativity_failures.append(
                {
                    "leaf_labels": list(labels),
                    "left_associated": left,
                    "right_associated": right,
                }
            )

    same_linking_witnesses = [
        {
            "name": "omega1_distinguishes_1x1_from_2x4",
            "central_omega": "1",
            "pairwise_linking_signature": "central links each leaf once; leaves mutually unlinked",
            "left_leaf_labels": ["1", "1"],
            "right_leaf_labels": ["2", "4"],
            "left_multiplier": star_multiplier(category, "6", ["1", "1"]),
            "right_multiplier": star_multiplier(category, "6", ["2", "4"]),
        },
        {
            "name": "omega0_distinguishes_1x1_from_2x4",
            "central_omega": "0",
            "pairwise_linking_signature": "central links each leaf once; leaves mutually unlinked",
            "left_leaf_labels": ["1", "1"],
            "right_leaf_labels": ["2", "4"],
            "left_multiplier": star_multiplier(category, "0", ["1", "1"]),
            "right_multiplier": star_multiplier(category, "0", ["2", "4"]),
        },
    ]
    for item in same_linking_witnesses:
        item["status"] = "pass" if item["left_multiplier"] != item["right_multiplier"] else "fail"
        item["interpretation"] = (
            "same pairwise linking data gives different central Omega projector output; "
            "a linking-matrix-only evaluator would be wrong for this non-pointed gate"
        )

    sample_triples = [
        ["1", "1", "2"],
        ["1", "3", "4"],
        ["2", "3", "5"],
        ["3", "3", "3"],
    ]
    associativity_samples = [
        {
            "leaf_labels": labels,
            "fusion_distribution": fuse_sequence(category["fusion_rules"], labels),
            "omega0_multiplier": star_multiplier(category, "0", labels),
            "omega1_multiplier": star_multiplier(category, "6", labels),
        }
        for labels in sample_triples
    ]

    status = "pass"
    if associativity_failures:
        status = "fail"
    if any(item["status"] != "pass" for item in same_linking_witnesses):
        status = "fail"

    return {
        "status": status,
        "category_id": "SU(2)_6",
        "associativity_triple_count": len(triples),
        "associativity_failure_count": len(associativity_failures),
        "associativity_failures": associativity_failures[:10],
        "associativity_samples": associativity_samples,
        "same_linking_matrix_not_enough_witnesses": same_linking_witnesses,
    }


def su3_next_candidate_gate(category: Json) -> Json:
    invertibles = [
        label
        for label in category["simple_labels"]
        if category["quantum_dimensions"][label]["display"] == "1"
    ]
    samples = [
        ["(1,0)", "(1,0)"],
        ["(1,0)", "(0,1)"],
        ["(0,1)", "(0,1)"],
        ["(1,1)", "(1,0)"],
        ["(1,1)", "(0,1)"],
    ]
    sample_payloads = []
    for labels in samples:
        distribution = fuse_sequence(category["fusion_rules"], labels)
        sample_payloads.append(
            {
                "leaf_labels": labels,
                "fusion_distribution": distribution,
                "invertible_multiplicities": {
                    label: distribution.get(label, 0)
                    for label in invertibles
                },
            }
        )

    return {
        "status": "pass",
        "category_id": "SU(3)_2",
        "readiness": "structured-blocker",
        "invertible_labels_detected_from_dimension_one": invertibles,
        "fusion_channel_samples": sample_payloads,
        "blocker": {
            "reason_id": "su3-2-projector-target-map-not-yet-certified",
            "message": (
                "The fusion multiplicity side is ready, but we have not yet certified "
                "which invertible label realizes each universal-grading character in "
                "the S-matrix row, nor do we have a full F/R-symbol backend."
            ),
            "needed_next": [
                "exact simple-current character row check for SU(3)_2",
                "central Omega projector identity for all three characters",
                "then reuse this fusion-channel gate with certified character targets",
            ],
        },
    }


def star_multiplier(category: Json, target: str, leaf_labels: list[str]) -> int:
    return fuse_sequence(category["fusion_rules"], leaf_labels).get(target, 0)


def multiplier_value(category: Json, multiplier: int) -> Json:
    return {
        "kind": "global_dimension_multiple",
        "multiplier": multiplier,
        "global_dimension": category["global_dimension"],
    }


def fuse_sequence(fusion_rules: Json, labels: list[str]) -> dict[str, int]:
    if not labels:
        raise ValueError("leaf label sequence must be nonempty")
    distribution = {labels[0]: 1}
    for label in labels[1:]:
        distribution = fuse_distribution_with_label(fusion_rules, distribution, label)
    return sort_distribution(distribution)


def fuse_three_left(fusion_rules: Json, labels: list[str]) -> dict[str, int]:
    if len(labels) != 3:
        raise ValueError("expected exactly three labels")
    left_pair = fuse_sequence(fusion_rules, labels[:2])
    return sort_distribution(fuse_distribution_with_label(fusion_rules, left_pair, labels[2]))


def fuse_three_right(fusion_rules: Json, labels: list[str]) -> dict[str, int]:
    if len(labels) != 3:
        raise ValueError("expected exactly three labels")
    right_pair = fuse_sequence(fusion_rules, labels[1:])
    distribution: dict[str, int] = {}
    for middle, multiplicity in right_pair.items():
        for output, coefficient in fusion_rules[f"{labels[0]}*{middle}"].items():
            distribution[output] = distribution.get(output, 0) + multiplicity * coefficient
    return sort_distribution(distribution)


def fuse_distribution_with_label(
    fusion_rules: Json,
    distribution: dict[str, int],
    label: str,
) -> dict[str, int]:
    output_distribution: dict[str, int] = {}
    for left, left_multiplicity in distribution.items():
        for output, coefficient in fusion_rules[f"{left}*{label}"].items():
            output_distribution[output] = (
                output_distribution.get(output, 0) + left_multiplicity * coefficient
            )
    return sort_distribution(output_distribution)


def sort_distribution(distribution: dict[str, int]) -> dict[str, int]:
    return {
        key: distribution[key]
        for key in sorted(distribution)
        if distribution[key] != 0
    }


def load_categories() -> dict[str, Json]:
    payload = json.loads(CANDIDATE_DATA.read_text())
    if payload["status"] != "pass" or payload["exact_output"]["status"] != "pass":
        raise ValueError("candidate data artifact is not passing")
    projector_payload = json.loads(SU2_PROJECTOR_DATA.read_text())
    projector_controls = projector_payload["exact_output"]["modular_data_controls"]
    required_projector_controls = {
        "simple_current_character_matches_degree",
        "omega_hopf_projector_identity",
    }
    present = {
        item["name"]
        for item in projector_controls
        if item["status"] == "pass"
    }
    if not required_projector_controls.issubset(present):
        raise ValueError("SU(2)_6 projector controls have not passed")
    return {
        category["category_id"]: category
        for category in payload["exact_output"]["categories"]
    }


def build_certificate(exact_output: Json, output_path: Path, started_at: str, elapsed: float) -> Json:
    input_definition = {
        "suite": "mtc-fusion-channel-gate-v1",
        "candidate_data_sha256": file_sha256(CANDIDATE_DATA),
        "su2_projector_data_sha256": file_sha256(SU2_PROJECTOR_DATA),
        "output_path": str(output_path.relative_to(REPO_ROOT)),
    }
    return make_certificate(
        status=exact_output["status"],
        command="uv run python experiments/scripts/mtc_fusion_channel_gate.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(REPO_ROOT),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            "uv run python experiments/scripts/mtc_fusion_channel_gate.py "
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed),
        repo_root=str(REPO_ROOT),
        notes=[
            "This gate is a fusion-channel projector test, not a full F/R-symbol evaluator.",
            "SU(3)_2 is intentionally kept at structured-blocker status in this artifact.",
        ],
    )


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    output_path = args.output
    if not output_path.is_absolute():
        output_path = REPO_ROOT / output_path
    output_path.parent.mkdir(parents=True, exist_ok=True)

    started_at = utc_now_iso()
    start = time.time()
    exact_output = run_gate()
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(
        "su2 associativity triples:",
        exact_output["step_4_su2_6_pressure_controls"]["associativity_triple_count"],
    )
    print("su3 readiness:", exact_output["step_5_su3_2_next_candidate_gate"]["readiness"])

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
