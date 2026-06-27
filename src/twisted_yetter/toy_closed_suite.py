"""Blocked ledger for the n55 toy closed suite.

This module intentionally does not compute closed 4-manifold invariant values.
It records which toy cases already have upstream diagram/decorated-core/pair
metadata and why the suite remains blocked until the ordinary surgery and
decorated Kirby move gates pass.
"""

from __future__ import annotations

import json
import argparse
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    git_metadata,
    hash_json,
    make_certificate,
)
from twisted_yetter.candidate_validation_suite import (
    CANDIDATE_VALIDATION_SUITE_SCHEMA,
    many_case_candidate_validation_suite_artifact,
    validate_candidate_validation_suite_metadata,
)
from twisted_yetter.decorated_kirby_gate import (
    DECORATED_KIRBY_GATE_SCHEMA,
    ORDINARY_SURGERY_BLOCKER_ID,
    decorated_kirby_gate_artifact,
    validate_decorated_kirby_gate_artifact,
)
from twisted_yetter.ordinary_surgery_gate import (
    ORDINARY_SURGERY_GATE_SCHEMA,
    ordinary_surgery_gate_certificate,
)
from twisted_yetter.presentation_pairs import (
    PRESENTATION_PAIR_REGISTRY_SCHEMA,
    presentation_pair_registry_artifact,
    validate_presentation_pair_registry_metadata,
)

TOY_CLOSED_SUITE_SCHEMA: Final = "twisted-yetter.toy-closed-suite-ledger.v1"
TOY_CLOSED_SUITE_NOTE: Final = "wiki/understandings/toy-closed-suite.org"
TOY_CLOSED_SUITE_ARTIFACT: Final = (
    "experiments/results/toy-suite/n55-toy-closed-suite.json"
)

NODE_ID: Final = "n55-toy-closed-suite"
CLAIM_LEVEL: Final = "blocked ledger/certificate"

N24_GATE_BLOCKER_ID: Final = "n24-ordinary-surgery-gate-blocked"
N50_GATE_BLOCKER_ID: Final = "n50-decorated-kirby-move-gate-blocked"
MISSING_PAIR_METADATA_BLOCKER_ID: Final = "missing-presentation-pair-metadata"

BLOCKED_CLAIMS: Final = (
    "closed 4-manifold invariant value",
    "ordinary surgery theorem claim",
    "decorated Kirby theorem claim",
    "exotic detection claim",
)


def toy_closed_suite_ledger_artifact(
    *,
    candidate_suite: Mapping[str, object] | None = None,
    pair_registry: Mapping[str, object] | None = None,
    ordinary_gate: Mapping[str, object] | None = None,
    decorated_gate: Mapping[str, object] | None = None,
    claim_closed_invariant: bool = False,
    claim_decorated_kirby_theorem: bool = False,
    claim_exotic_detection: bool = False,
) -> dict[str, object]:
    """Return the deterministic n55 blocked ledger.

    Claim flags are explicit refusal checks.  They make this API hard to use as
    an accidental closed-invariant calculator while n24 and n50 are blocked.
    """

    if (
        claim_closed_invariant
        or claim_decorated_kirby_theorem
        or claim_exotic_detection
    ):
        raise ValueError(
            "n55-toy-closed-suite is a blocked ledger and refuses closed "
            "4-manifold invariant, decorated Kirby theorem, and exotic claims"
        )

    n24 = (
        ordinary_surgery_gate_certificate()
        if ordinary_gate is None
        else dict(ordinary_gate)
    )
    suite = (
        many_case_candidate_validation_suite_artifact()
        if candidate_suite is None
        else dict(candidate_suite)
    )
    registry = (
        presentation_pair_registry_artifact()
        if pair_registry is None
        else dict(pair_registry)
    )
    n50 = (
        decorated_kirby_gate_artifact(registry)
        if decorated_gate is None
        else dict(decorated_gate)
    )

    pair_classifications = n50.get("pair_classifications", [])
    pair_list = pair_classifications if isinstance(pair_classifications, list) else []
    pair_ids_by_case = _pair_ids_by_case(pair_list)
    decorated_gate_inventory = _decorated_gate_inventory(n50, pair_list)

    cases = suite.get("cases", [])
    case_list = cases if isinstance(cases, list) else []
    toy_cases = [
        _case_readiness(case, pair_ids_by_case=pair_ids_by_case)
        for case in sorted(case_list, key=lambda item: str(item.get("case_id", "")))
        if isinstance(case, Mapping)
    ]

    global_blockers = []
    if n24.get("status") != "pass":
        global_blockers.append(
            {
                "reason_id": N24_GATE_BLOCKER_ID,
                "source_node": "n24-ordinary-surgery-gate",
                "status": "blocked",
                "observed": n24.get("status", "missing"),
                "required": "pass",
                "upstream_schema": n24.get("schema"),
                "upstream_blocker_reason_ids": [
                    str(reason["reason_id"])
                    for reason in n24.get("blocked_reasons", [])
                    if isinstance(reason, Mapping) and "reason_id" in reason
                ],
                "claim_boundary": (
                    "toy closed cases cannot be promoted to closed 4-manifold "
                    "invariant values while ordinary surgery is blocked"
                ),
            }
        )
    if n50.get("status") != "pass":
        global_blockers.append(
            {
                "reason_id": N50_GATE_BLOCKER_ID,
                "source_node": "n50-decorated-kirby-move-gate",
                "status": "blocked",
                "observed": n50.get("status", "missing"),
                "required": "pass",
                "upstream_schema": n50.get("schema"),
                "classification_status_counts": decorated_gate_inventory[
                    "classification_status_counts"
                ],
                "pair_count": decorated_gate_inventory["pair_count"],
                "diagram_pair_count": decorated_gate_inventory["diagram_pair_count"],
                "matrix_pair_count": decorated_gate_inventory["matrix_pair_count"],
                "evaluator_comparison_input_pair_ids": decorated_gate_inventory[
                    "evaluator_comparison_input_pair_ids"
                ],
                "upstream_pair_blocker_reason_ids": sorted(
                    {
                        str(reason_id)
                        for pair in pair_list
                        if isinstance(pair, Mapping)
                        for reason_id in pair.get("blocked_reason_ids", [])
                    }
                ),
                "claim_boundary": (
                    "toy closed cases cannot be used as decorated Kirby "
                    "invariance evidence while n50 is blocked"
                ),
            }
        )

    artifact: dict[str, object] = {
        "schema": TOY_CLOSED_SUITE_SCHEMA,
        "status": "blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "n55 consumes n36/n45/n50/n24 metadata as a blocked ledger; it "
            "does not evaluate or output closed 4-manifold invariant values"
        ),
        "upstream_nodes": [
            "n24-ordinary-surgery-gate",
            "n36-many-case-candidate-validation-suite",
            "n45-kirby-presentation-pair-generator",
            "n50-decorated-kirby-move-gate",
        ],
        "input_schemas": {
            "ordinary_surgery_gate": n24.get("schema"),
            "candidate_validation_suite": suite.get("schema"),
            "presentation_pair_registry": registry.get("schema"),
            "decorated_kirby_gate": n50.get("schema"),
        },
        "input_statuses": {
            "ordinary_surgery_gate": n24.get("status"),
            "candidate_validation_suite": suite.get("status"),
            "presentation_pair_registry": registry.get("status"),
            "decorated_kirby_gate": n50.get("status"),
        },
        "input_validations": {
            "candidate_validation_suite": validate_candidate_validation_suite_metadata(
                suite
            ),
            "presentation_pair_registry": validate_presentation_pair_registry_metadata(
                registry
            ),
            "decorated_kirby_gate": validate_decorated_kirby_gate_artifact(n50),
        },
        "decorated_gate_inventory": decorated_gate_inventory,
        "case_count": len(toy_cases),
        "toy_cases": toy_cases,
        "all_cases_have_diagram_metadata": all(
            case["upstream_readiness"]["diagram_metadata"] is True
            for case in toy_cases
        ),
        "all_cases_have_decorated_core_metadata": all(
            case["upstream_readiness"]["decorated_core_metadata"] is True
            for case in toy_cases
        ),
        "all_cases_have_pair_metadata": all(
            case["upstream_readiness"]["presentation_pair_metadata"] is True
            for case in toy_cases
        ),
        "global_blocker_reason_ids": [
            str(reason["reason_id"]) for reason in global_blockers
        ],
        "global_blockers": global_blockers,
        "final_closed_suite_passed": False,
        "closed_4_manifold_invariant_claim_allowed": False,
        "ordinary_surgery_theorem_claim_allowed": False,
        "decorated_kirby_theorem_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "required_unblock_artifacts": [
            "n24 ordinary surgery gate pass certificate with sourced surgery formula support",
            "n50 decorated Kirby move gate pass certificate with machine-checkable move data",
            "accepted presentation-pair metadata for every toy closed case intended for final n55",
            "stable exact closed-suite artifact that still refuses exotic claims unless n70/n80 are reached",
        ],
        "claim_boundary": (
            "this is a machine-readable blocked ledger, not a closed "
            "4-manifold invariant calculator"
        ),
        "ledger_note": TOY_CLOSED_SUITE_NOTE,
    }
    artifact["metadata_validation"] = validate_toy_closed_suite_ledger_artifact(
        artifact
    )
    return artifact


def toy_closed_suite_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible certificate envelope for the n55 blocked ledger."""

    root = Path(repo_root)
    ordinary_gate = ordinary_surgery_gate_certificate()
    suite = many_case_candidate_validation_suite_artifact()
    registry = presentation_pair_registry_artifact()
    decorated_gate = decorated_kirby_gate_artifact(registry)
    exact_output = toy_closed_suite_ledger_artifact(
        candidate_suite=suite,
        pair_registry=registry,
        ordinary_gate=ordinary_gate,
        decorated_gate=decorated_gate,
    )
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.toy_closed_suite "
            f"--write {TOY_CLOSED_SUITE_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.toy_closed_suite",
            "--write",
            TOY_CLOSED_SUITE_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "ordinary_surgery_gate_status": ordinary_gate.get("status"),
                "candidate_validation_suite_case_ids": [
                    case.get("case_id")
                    for case in suite.get("cases", [])
                    if isinstance(case, Mapping)
                ],
                "presentation_pair_registry_schema": registry.get("schema"),
                "decorated_kirby_gate_schema": decorated_gate.get("schema"),
                "decorated_kirby_gate_status": decorated_gate.get("status"),
                "decorated_gate_pair_count": decorated_gate.get("pair_count"),
                "decorated_gate_status_counts": decorated_gate.get(
                    "classification_status_counts"
                ),
                "decorated_gate_evaluator_input_pair_ids": decorated_gate.get(
                    "evaluator_comparison_input_pair_ids"
                ),
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/toy_closed_suite.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.toy_closed_suite "
            "--write experiments/results/toy-suite/n55-toy-closed-suite.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n55 is currently a blocked ledger, not a closed invariant calculator.",
            "It consumes the n50 classification inventory but n50 has zero pass pairs.",
            "No closed 4-manifold invariant value, ordinary surgery theorem, decorated Kirby theorem, Reutter/no-go, or exotic claim is made.",
        ],
    )


def validate_toy_closed_suite_ledger_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n55 ledger shape without proving any closed-invariant claim."""

    required = {
        "schema",
        "status",
        "node_id",
        "claim_level",
        "input_schemas",
        "input_statuses",
        "decorated_gate_inventory",
        "toy_cases",
        "global_blocker_reason_ids",
        "global_blockers",
        "blocked_claims",
        "required_unblock_artifacts",
    }
    missing = sorted(field for field in required if field not in artifact)
    toy_cases = artifact.get("toy_cases", [])
    case_list_ok = isinstance(toy_cases, list) and all(
        _case_readiness_is_valid(case) for case in toy_cases
    )
    blockers = artifact.get("global_blocker_reason_ids", [])
    blockers_ok = (
        isinstance(blockers, list)
        and N24_GATE_BLOCKER_ID in blockers
        and N50_GATE_BLOCKER_ID in blockers
    )
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "final_closed_suite_passed",
            "closed_4_manifold_invariant_claim_allowed",
            "ordinary_surgery_theorem_claim_allowed",
            "decorated_kirby_theorem_claim_allowed",
            "exotic_detection_claim_allowed",
        )
    )
    input_schemas = artifact.get("input_schemas", {})
    input_schemas_ok = isinstance(input_schemas, Mapping) and input_schemas == {
        "ordinary_surgery_gate": ORDINARY_SURGERY_GATE_SCHEMA,
        "candidate_validation_suite": CANDIDATE_VALIDATION_SUITE_SCHEMA,
        "presentation_pair_registry": PRESENTATION_PAIR_REGISTRY_SCHEMA,
        "decorated_kirby_gate": DECORATED_KIRBY_GATE_SCHEMA,
    }
    decorated_gate_inventory = artifact.get("decorated_gate_inventory", {})
    decorated_gate_inventory_ok = (
        isinstance(decorated_gate_inventory, Mapping)
        and decorated_gate_inventory.get("status") == "blocked"
        and decorated_gate_inventory.get("pair_count") == 8
        and decorated_gate_inventory.get("classification_status_counts", {}).get(
            "pass"
        )
        == 0
        and decorated_gate_inventory.get("evaluator_comparison_input_pair_ids") == []
    )
    return {
        "valid": (
            not missing
            and artifact.get("schema") == TOY_CLOSED_SUITE_SCHEMA
            and artifact.get("status") == "blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("claim_level") == CLAIM_LEVEL
            and input_schemas_ok
            and decorated_gate_inventory_ok
            and case_list_ok
            and blockers_ok
            and blocked_claims_ok
        ),
        "missing_required_fields": missing,
        "input_schemas_ok": input_schemas_ok,
        "decorated_gate_inventory_ok": decorated_gate_inventory_ok,
        "case_list_ok": case_list_ok,
        "blockers_ok": blockers_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "scope": "blocked ledger only; no closed 4-manifold invariant values",
    }


def stable_toy_closed_suite_ledger_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n55 ledger artifact deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _decorated_gate_inventory(
    decorated_gate: Mapping[str, object],
    pair_classifications: list[object],
) -> dict[str, object]:
    evaluator_pair_ids = decorated_gate.get("evaluator_comparison_input_pair_ids", [])
    return {
        "source_node": "n50-decorated-kirby-move-gate",
        "schema": decorated_gate.get("schema"),
        "status": decorated_gate.get("status"),
        "classification_status_counts": decorated_gate.get(
            "classification_status_counts", {}
        ),
        "pair_count": decorated_gate.get("pair_count", len(pair_classifications)),
        "diagram_pair_count": decorated_gate.get("diagram_pair_count", 0),
        "matrix_pair_count": decorated_gate.get("matrix_pair_count", 0),
        "evaluator_comparison_input_pair_ids": (
            list(evaluator_pair_ids) if isinstance(evaluator_pair_ids, list) else []
        ),
        "all_pairs_blocked_or_metadata_only": decorated_gate.get(
            "all_pairs_blocked_or_metadata_only"
        ),
        "all_pairs_have_structured_blockers": decorated_gate.get(
            "all_pairs_have_structured_blockers"
        ),
        "claim_boundary": (
            "n55 may consume this classification inventory, but zero n50 "
            "pass pairs means no evaluator comparison inputs and no closed "
            "decorated invariant values"
        ),
    }


def _case_readiness(
    case: Mapping[str, object],
    *,
    pair_ids_by_case: Mapping[str, list[str]],
) -> dict[str, object]:
    case_id = str(case.get("case_id", "missing-case-id"))
    metadata_validation = case.get("metadata_validation", {})
    decorated_core_metadata = (
        isinstance(metadata_validation, Mapping)
        and metadata_validation.get("valid") is True
    )
    pair_ids = pair_ids_by_case.get(case_id, [])
    blocker_ids = [N24_GATE_BLOCKER_ID, N50_GATE_BLOCKER_ID]
    if not pair_ids:
        blocker_ids.append(MISSING_PAIR_METADATA_BLOCKER_ID)

    return {
        "case_id": case_id,
        "fixture_path": case.get("fixture_path"),
        "diagram_id": case.get("diagram_id"),
        "finite_group_id": case.get("finite_group_id"),
        "decoration_by_component": case.get("decoration_by_component"),
        "zero_decoration": case.get("zero_decoration"),
        "component_sector_ids": case.get("component_sector_ids"),
        "upstream_readiness": {
            "diagram_metadata": bool(
                case.get("fixture_path")
                and case.get("diagram_id")
                and "diagram_component_ids" in case
            ),
            "decorated_core_metadata": decorated_core_metadata,
            "presentation_pair_metadata": bool(pair_ids),
        },
        "presentation_pair_refs": pair_ids,
        "status": "blocked",
        "blocked_reason_ids": blocker_ids,
        "claim_boundary": (
            "case metadata is inventory/readiness evidence only and does not "
            "support a closed invariant value"
        ),
    }


def _pair_ids_by_case(
    pair_classifications: list[object],
) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    for pair in pair_classifications:
        if not isinstance(pair, Mapping):
            continue
        pair_id = str(pair.get("pair_id", "missing-pair-id"))
        for side_key in ("left_case_id", "right_case_id"):
            case_id = pair.get(side_key)
            if case_id is None:
                continue
            result.setdefault(str(case_id), []).append(pair_id)
    return {case_id: sorted(set(pair_ids)) for case_id, pair_ids in result.items()}


def _case_readiness_is_valid(case: object) -> bool:
    if not isinstance(case, dict):
        return False
    required = {
        "case_id",
        "fixture_path",
        "diagram_id",
        "upstream_readiness",
        "presentation_pair_refs",
        "status",
        "blocked_reason_ids",
    }
    if any(field not in case for field in required):
        return False
    if case.get("status") != "blocked":
        return False
    readiness = case.get("upstream_readiness")
    blocker_ids = case.get("blocked_reason_ids")
    return (
        isinstance(readiness, dict)
        and readiness.get("diagram_metadata") is True
        and readiness.get("decorated_core_metadata") is True
        and isinstance(blocker_ids, list)
        and N24_GATE_BLOCKER_ID in blocker_ids
        and N50_GATE_BLOCKER_ID in blocker_ids
    )


def _main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the n55 certificate JSON")
    args = parser.parse_args()

    certificate = toy_closed_suite_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is None:
        print(output, end="")
        return
    args.write.parent.mkdir(parents=True, exist_ok=True)
    args.write.write_text(output, encoding="utf-8")


if __name__ == "__main__":
    _main()


__all__ = [
    "BLOCKED_CLAIMS",
    "CLAIM_LEVEL",
    "MISSING_PAIR_METADATA_BLOCKER_ID",
    "N24_GATE_BLOCKER_ID",
    "N50_GATE_BLOCKER_ID",
    "NODE_ID",
    "TOY_CLOSED_SUITE_ARTIFACT",
    "TOY_CLOSED_SUITE_NOTE",
    "TOY_CLOSED_SUITE_SCHEMA",
    "stable_toy_closed_suite_ledger_json",
    "toy_closed_suite_certificate",
    "toy_closed_suite_ledger_artifact",
    "validate_toy_closed_suite_ledger_artifact",
]
