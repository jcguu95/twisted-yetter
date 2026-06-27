"""Executable classifier for the n50 decorated Kirby move gate.

This module consumes the n45 presentation-pair registry and classifies each
toy or matrix pair for later evaluator comparisons.  It is intentionally gate
discipline, not a decorated Kirby theorem: dry-run diagram metadata is blocked,
matrix-only consistency is metadata-only, and no pair is currently accepted as a
link-diagram decorated Kirby move input.
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

from twisted_yetter.presentation_pairs import (
    PRESENTATION_PAIR_REGISTRY_SCHEMA,
    presentation_pair_registry_artifact,
    validate_presentation_pair_registry_metadata,
)

DECORATED_KIRBY_GATE_SCHEMA: Final = "twisted-yetter.decorated-kirby-gate.v2"
DECORATED_KIRBY_GATE_NOTE: Final = (
    "wiki/understandings/decorated-kirby-move-gate.org"
)
DECORATED_KIRBY_GATE_ARTIFACT: Final = (
    "experiments/results/decorated-kirby-gate/"
    "n50-decorated-kirby-move-gate.json"
)

NODE_ID: Final = "n50-decorated-kirby-move-gate"
CLAIM_LEVEL: Final = "executable blocker/certificate"

PAIR_DRY_RUN_BLOCKER_ID: Final = "presentation-pair-candidate-dry-run"
NOT_GENERATED_LINK_MOVE_BLOCKER_ID: Final = "not-generated-link-diagram-move"
DECORATED_MOVE_CERT_BLOCKER_ID: Final = (
    "missing-decorated-move-certificate"
)
COMPONENT_LINEAGE_BLOCKER_ID: Final = "missing-component-lineage-certificate"
BASIS_MATRIX_BLOCKER_ID: Final = "missing-basis-matrix-certificate"
MATRIX_LEVEL_ONLY_BLOCKER_ID: Final = "matrix-level-only-not-link-diagram-proof"
ORDINARY_SURGERY_BLOCKER_ID: Final = "ordinary-surgery-gate-blocked"
SOURCE_PROOF_BLOCKER_ID: Final = "missing-source-proof"
N35_PLANNED_CALLS_BLOCKER_ID: Final = "n35-decorated-core-planned-calls-only"

BLOCKED_FINAL_CLAIMS: Final = (
    "presentation equivalence theorem",
    "decorated Kirby move theorem",
    "claim-supporting closed 4D invariant",
    "exotic detection claim",
)

REQUIRED_PAIR_FIELDS: Final = (
    "pair_id",
    "left",
    "right",
    "relation_type",
    "relation_status",
    "component_lineage",
    "basis_map",
    "decorated_core_case_refs",
    "decorated_core_cases",
    "does_not_prove",
)


def decorated_kirby_gate_artifact(
    registry_artifact: Mapping[str, object] | None = None,
    *,
    claim_presentation_equivalence_theorem: bool = False,
    claim_decorated_kirby_move_theorem: bool = False,
    claim_closed_invariant: bool = False,
    claim_exotic_detection: bool = False,
) -> dict[str, object]:
    """Return the deterministic n50 decorated Kirby gate certificate.

    The default input is ``presentation_pair_registry_artifact()``.  Claim flags
    are refused while the gate is blocked, so callers cannot accidentally use
    this scaffold as a theorem or closed-invariant promoter.
    """

    if (
        claim_presentation_equivalence_theorem
        or claim_decorated_kirby_move_theorem
        or claim_closed_invariant
        or claim_exotic_detection
    ):
        raise ValueError(
            "n50-decorated-kirby-move-gate refuses presentation theorem, "
            "decorated Kirby theorem, closed invariant, and exotic claims"
        )

    registry = (
        presentation_pair_registry_artifact()
        if registry_artifact is None
        else dict(registry_artifact)
    )
    registry_validation = validate_presentation_pair_registry_metadata(registry)
    pairs = registry.get("pairs", [])
    pair_list = pairs if isinstance(pairs, list) else []
    diagram_pair_classifications = [
        classify_registry_pair_for_decorated_gate(
            pair,
            registry_section="pairs",
            ordinary_surgery_gate_status=str(
                registry.get("ordinary_surgery_gate_status", "missing")
            ),
        )
        for pair in pair_list
    ]
    matrix_pairs = registry.get("matrix_presentation_pairs", [])
    matrix_pair_list = matrix_pairs if isinstance(matrix_pairs, list) else []
    matrix_pair_classifications = [
        classify_registry_pair_for_decorated_gate(
            pair,
            registry_section="matrix_presentation_pairs",
            ordinary_surgery_gate_status=str(
                registry.get("ordinary_surgery_gate_status", "missing")
            ),
        )
        for pair in matrix_pair_list
    ]
    pair_classifications = diagram_pair_classifications + matrix_pair_classifications
    status_counts = _status_counts(pair_classifications)
    all_pairs_blocked_or_metadata_only = all(
        pair["status"] in {"blocked", "metadata-only"}
        for pair in pair_classifications
    )

    artifact: dict[str, object] = {
        "schema": DECORATED_KIRBY_GATE_SCHEMA,
        "status": "blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "n50 gate classifier over n45 dry-run and matrix-level pair "
            "metadata; no generated link-diagram decorated Kirby move "
            "certificate is present"
        ),
        "input_registry_schema": registry.get("schema"),
        "input_registry_status": registry.get("status"),
        "input_registry_node_id": registry.get("node_id"),
        "input_registry_validation": registry_validation,
        "ordinary_surgery_gate_status": registry.get("ordinary_surgery_gate_status"),
        "diagram_pair_count": len(diagram_pair_classifications),
        "matrix_pair_count": len(matrix_pair_classifications),
        "pair_count": len(pair_classifications),
        "classification_status_counts": status_counts,
        "classification_status_semantics": {
            "pass": (
                "accepted as later evaluator comparison input; currently no "
                "pair has this status"
            ),
            "blocked": (
                "cannot be used as evaluator input because required decorated "
                "Kirby move evidence is absent or upstream gates are blocked"
            ),
            "not-applicable": (
                "outside the decorated Kirby move gate scope; currently no "
                "registry entry requires this status"
            ),
            "metadata-only": (
                "machine-checkable auxiliary metadata may be retained, but it "
                "is not a link-diagram move proof or evaluator input"
            ),
        },
        "pair_classifications": pair_classifications,
        "all_pairs_blocked_or_metadata_only": all_pairs_blocked_or_metadata_only,
        "evaluator_comparison_input_pair_ids": [
            str(pair["pair_id"])
            for pair in pair_classifications
            if pair["status"] == "pass"
        ],
        "all_pairs_have_structured_blockers": all(
            bool(pair["blocked_reason_ids"]) for pair in pair_classifications
        ),
        "final_decorated_gate_passed": False,
        "presentation_equivalence_theorem_claim_allowed": False,
        "decorated_kirby_move_theorem_claim_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "blocked_final_claims": list(BLOCKED_FINAL_CLAIMS),
        "required_unblock_artifacts": [
            "generated link-diagram decorated Kirby move certificate for each accepted pair",
            "certified component lineage, not placeholder lineage prose",
            "integer basis matrix with claim_certified true",
            "ordinary surgery gate support for closed 4D claims",
            "n35 decorated-core calls upgraded from planned metadata to executed evaluator-backed calls",
            "source-audited proof/reference record for the decorated move rule",
        ],
        "matrix_level_consistency": {
            "status": "metadata-only",
            "matrix_pair_count": len(matrix_pair_classifications),
            "machine_checked_matrix_pair_ids": [
                str(pair["pair_id"])
                for pair in matrix_pair_classifications
                if pair.get("matrix_level_consistency_check", {}).get("status")
                == "pass"
            ],
            "claim_boundary": (
                "GL(n,Z) matrix consistency is an auxiliary sanity check only "
                "and is not upgraded to a link-diagram Kirby move proof"
            ),
        },
        "downstream_decision": {
            "n55-toy-closed-suite": "blocked",
            "reason": (
                "n55 may read the classification inventory, but may not treat "
                "n45 toy or matrix pairs as closed 4-manifold invariance "
                "evidence until n50 has generated link-diagram move certificates"
            ),
        },
        "ledger_note": DECORATED_KIRBY_GATE_NOTE,
    }
    artifact["metadata_validation"] = validate_decorated_kirby_gate_artifact(
        artifact
    )
    return artifact


def decorated_kirby_gate_artifact_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible artifact envelope for the n50 classifier."""

    root = Path(repo_root)
    registry = presentation_pair_registry_artifact()
    exact_output = decorated_kirby_gate_artifact(registry)
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.decorated_kirby_gate "
            f"--write {DECORATED_KIRBY_GATE_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.decorated_kirby_gate",
            "--write",
            DECORATED_KIRBY_GATE_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "input_registry_schema": registry.get("schema"),
                "input_registry_node_id": registry.get("node_id"),
                "diagram_pair_ids": [
                    pair.get("pair_id")
                    for pair in registry.get("pairs", [])
                    if isinstance(pair, Mapping)
                ],
                "matrix_pair_ids": [
                    pair.get("pair_id")
                    for pair in registry.get("matrix_presentation_pairs", [])
                    if isinstance(pair, Mapping)
                ],
                "ordinary_surgery_gate_status": registry.get(
                    "ordinary_surgery_gate_status"
                ),
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/decorated_kirby_gate.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.decorated_kirby_gate "
            "--write experiments/results/decorated-kirby-gate/"
            "n50-decorated-kirby-move-gate.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n50 classifies n45 registry entries for later evaluator comparisons.",
            "Diagram/decorated-core pairs remain blocked dry-run metadata.",
            "Matrix pairs are metadata-only GL(n,Z) consistency checks, not link-diagram Kirby move proofs.",
            "No decorated Kirby theorem, closed invariant, Reutter escape/no-go, or exotic claim is made.",
        ],
    )


def classify_registry_pair_for_decorated_gate(
    pair: Mapping[str, object],
    *,
    registry_section: str,
    ordinary_surgery_gate_status: str,
) -> dict[str, object]:
    """Classify one n45 pair for the decorated Kirby move gate."""

    pair_id = str(pair.get("pair_id", "missing-pair-id"))
    pair_kind = str(pair.get("pair_kind", "missing"))
    relation_status = str(pair.get("relation_status", "missing"))
    component_lineage = _mapping_or_empty(pair.get("component_lineage"))
    basis_map = _mapping_or_empty(pair.get("basis_map"))
    is_matrix_pair = registry_section == "matrix_presentation_pairs"

    blocked_reasons = []
    if is_matrix_pair:
        blocked_reasons.append(
            {
                "reason_id": MATRIX_LEVEL_ONLY_BLOCKER_ID,
                "status": "blocked",
                "field": "pair_kind",
                "observed": pair_kind,
                "required": "generated link-diagram decorated Kirby move pair",
                "claim_boundary": (
                    "exact GL(n,Z) matrix consistency is metadata-only and "
                    "cannot be promoted to a link-diagram handle-slide proof"
                ),
            }
        )
    elif relation_status != "certified/decorated-kirby-move":
        blocked_reasons.append(
            {
                "reason_id": PAIR_DRY_RUN_BLOCKER_ID,
                "status": "blocked",
                "field": "relation_status",
                "observed": relation_status,
                "required": "certified/decorated-kirby-move",
                "claim_boundary": (
                    "candidate/dry-run presentation pairs cannot support "
                    "presentation equivalence or decorated Kirby move claims"
                ),
            }
        )
    if "generated_link_diagram_move" not in pair:
        blocked_reasons.append(
            {
                "reason_id": NOT_GENERATED_LINK_MOVE_BLOCKER_ID,
                "status": "blocked",
                "field": "generated_link_diagram_move",
                "observed": "missing",
                "required": "machine-readable before/after link diagram move",
                "claim_boundary": (
                    "registry metadata is not a generated link-diagram Kirby "
                    "move"
                ),
            }
        )
    if "decorated_kirby_move_certificate" not in pair:
        blocked_reasons.append(
            {
                "reason_id": DECORATED_MOVE_CERT_BLOCKER_ID,
                "status": "blocked",
                "field": "decorated_kirby_move_certificate",
                "observed": "missing",
                "required": "machine-checkable certificate",
                "claim_boundary": (
                    "no handle-slide, stabilization, cancellation, or "
                    "component-order certificate is recorded"
                ),
            }
        )
    if component_lineage.get("claim_certified") is not True:
        blocked_reasons.append(
            {
                "reason_id": COMPONENT_LINEAGE_BLOCKER_ID,
                "status": "blocked",
                "field": "component_lineage.claim_certified",
                "observed": component_lineage.get("claim_certified", "missing"),
                "required": True,
                "component_lineage_status": component_lineage.get(
                    "status", "missing"
                ),
                "claim_boundary": (
                    "component lineage prose or placeholders are not move "
                    "certificates"
                ),
            }
        )
    if (
        not is_matrix_pair
        and (
            basis_map.get("claim_certified") is not True
            or basis_map.get("matrix") is None
        )
    ):
        blocked_reasons.append(
            {
                "reason_id": BASIS_MATRIX_BLOCKER_ID,
                "status": "blocked",
                "field": "basis_map",
                "observed": {
                    "claim_certified": basis_map.get("claim_certified", "missing"),
                    "matrix": basis_map.get("matrix"),
                },
                "required": {
                    "claim_certified": True,
                    "matrix": "integer GL(n,Z) matrix",
                },
                "basis_map_status": basis_map.get("status", "missing"),
                "claim_boundary": (
                    "basis-change placeholders cannot identify H2 markings"
                ),
            }
        )
    if not is_matrix_pair:
        blocked_reasons.append(
            {
                "reason_id": N35_PLANNED_CALLS_BLOCKER_ID,
                "status": "blocked",
                "field": "decorated_core_cases",
                "observed": "planned evaluator call metadata",
                "required": "executed evaluator-backed decorated-core comparison",
                "claim_boundary": (
                    "n35/n36 decorated-core summaries are metadata carried "
                    "forward for planning, not an executed decorated Kirby "
                    "move comparison"
                ),
            }
        )
    if ordinary_surgery_gate_status != "pass":
        blocked_reasons.append(
            {
                "reason_id": ORDINARY_SURGERY_BLOCKER_ID,
                "status": "blocked",
                "field": "ordinary_surgery_gate_status",
                "observed": ordinary_surgery_gate_status,
                "required": "pass",
                "claim_boundary": (
                    "decorated closed-invariant claims inherit the ordinary "
                    "surgery gate blocker"
                ),
            }
        )
    if "source_proof" not in pair and "source_reference" not in pair:
        blocked_reasons.append(
            {
                "reason_id": SOURCE_PROOF_BLOCKER_ID,
                "status": "blocked",
                "field": "source_proof",
                "observed": "missing",
                "required": (
                    "source-audited proposition/theorem or repo-local proof "
                    "artifact"
                ),
                "claim_boundary": (
                    "computed dry-run metadata is not a decorated Kirby theorem"
                ),
            }
        )

    status = "metadata-only" if is_matrix_pair else "blocked"
    matrix_level_consistency = _matrix_level_consistency(pair) if is_matrix_pair else None
    classification = {
        "pair_id": pair_id,
        "status": status if blocked_reasons else "pass",
        "gate_decision": "blocked" if blocked_reasons else "pass",
        "usable_as_evaluator_comparison_input": False if blocked_reasons else True,
        "final_decorated_gate_passed": False if blocked_reasons else True,
        "registry_section": registry_section,
        "pair_kind": pair_kind,
        "relation_type": pair.get("relation_type"),
        "relation_status": relation_status,
        "left_case_id": _side_case_id(pair.get("left")),
        "right_case_id": _side_case_id(pair.get("right")),
        "required_pair_fields_present": all(field in pair for field in REQUIRED_PAIR_FIELDS),
        "blocked_reason_ids": [str(reason["reason_id"]) for reason in blocked_reasons],
        "blocked_reasons": blocked_reasons,
        "blocked_final_claims": list(BLOCKED_FINAL_CLAIMS),
    }
    if matrix_level_consistency is not None:
        classification["matrix_level_consistency_check"] = matrix_level_consistency
    return classification


def classify_presentation_pair_for_decorated_gate(
    pair: Mapping[str, object],
    *,
    ordinary_surgery_gate_status: str,
) -> dict[str, object]:
    """Backward-compatible classifier for n45 diagram pair entries."""

    return classify_registry_pair_for_decorated_gate(
        pair,
        registry_section="pairs",
        ordinary_surgery_gate_status=ordinary_surgery_gate_status,
    )


def validate_decorated_kirby_gate_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Check the n50 gate artifact shape without proving Kirby moves."""

    required = {
        "schema",
        "status",
        "node_id",
        "claim_level",
        "input_registry_schema",
        "classification_status_counts",
        "pair_classifications",
        "blocked_final_claims",
        "required_unblock_artifacts",
    }
    missing = sorted(field for field in required if field not in artifact)
    pair_classifications = artifact.get("pair_classifications", [])
    pair_list_ok = isinstance(pair_classifications, list) and all(
        _pair_classification_is_valid(pair) for pair in pair_classifications
    )
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "presentation_equivalence_theorem_claim_allowed",
            "decorated_kirby_move_theorem_claim_allowed",
            "closed_4_manifold_claim_allowed",
            "exotic_detection_claim_allowed",
            "final_decorated_gate_passed",
        )
    )
    return {
        "valid": (
            not missing
            and artifact.get("schema") == DECORATED_KIRBY_GATE_SCHEMA
            and artifact.get("node_id") == NODE_ID
            and artifact.get("input_registry_schema")
            == PRESENTATION_PAIR_REGISTRY_SCHEMA
            and artifact.get("status") == "blocked"
            and pair_list_ok
            and blocked_claims_ok
        ),
        "missing_required_fields": missing,
        "pair_list_ok": pair_list_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "scope": "decorated Kirby move gate scaffold only; no theorem proof",
    }


def stable_decorated_kirby_gate_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n50 gate certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def main(argv: list[str] | None = None) -> int:
    """Write the n50 decorated Kirby gate artifact envelope."""

    parser = argparse.ArgumentParser(
        description="Generate the n50 decorated Kirby move gate certificate."
    )
    parser.add_argument("--write", type=Path, help="write certificate JSON to this path")
    args = parser.parse_args(argv)

    certificate = decorated_kirby_gate_artifact_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(output)
    else:
        print(output, end="")
    return 0


def _mapping_or_empty(value: object) -> Mapping[str, object]:
    return value if isinstance(value, Mapping) else {}


def _side_case_id(side: object) -> object:
    if isinstance(side, Mapping):
        return side.get("decorated_core_case_id")
    return None


def _status_counts(pair_classifications: list[dict[str, object]]) -> dict[str, int]:
    statuses = {"pass": 0, "blocked": 0, "not-applicable": 0, "metadata-only": 0}
    for pair in pair_classifications:
        status = str(pair.get("status", "missing"))
        statuses[status] = statuses.get(status, 0) + 1
    return statuses


def _matrix_level_consistency(pair: Mapping[str, object]) -> dict[str, object]:
    basis_map = _mapping_or_empty(pair.get("basis_map"))
    return {
        "status": (
            "pass"
            if (
                pair.get("machine_checked_matrix_equivalence") is True
                and basis_map.get("claim_certified") is True
                and basis_map.get("matrix") is not None
                and basis_map.get("inverse_matrix") is not None
                and basis_map.get("determinant_abs") == 1
            )
            else "blocked"
        ),
        "machine_checked_matrix_equivalence": pair.get(
            "machine_checked_matrix_equivalence"
        ),
        "basis_matrix_claim_certified": basis_map.get("claim_certified"),
        "determinant_abs": basis_map.get("determinant_abs"),
        "claim_boundary": (
            "matrix-level GL(n,Z) consistency only; not a generated "
            "link-diagram Kirby move proof"
        ),
    }


def _pair_classification_is_valid(pair: object) -> bool:
    if not isinstance(pair, dict):
        return False
    required = {
        "pair_id",
        "status",
        "final_decorated_gate_passed",
        "blocked_reason_ids",
        "blocked_reasons",
        "blocked_final_claims",
    }
    if any(field not in pair for field in required):
        return False
    if pair.get("status") not in {"blocked", "metadata-only"}:
        return False
    if pair.get("final_decorated_gate_passed") is not False:
        return False
    reason_ids = pair.get("blocked_reason_ids")
    reasons = pair.get("blocked_reasons")
    return (
        isinstance(reason_ids, list)
        and bool(reason_ids)
        and isinstance(reasons, list)
        and len(reason_ids) == len(reasons)
    )


__all__ = [
    "BASIS_MATRIX_BLOCKER_ID",
    "BLOCKED_FINAL_CLAIMS",
    "CLAIM_LEVEL",
    "COMPONENT_LINEAGE_BLOCKER_ID",
    "DECORATED_KIRBY_GATE_ARTIFACT",
    "DECORATED_KIRBY_GATE_NOTE",
    "DECORATED_KIRBY_GATE_SCHEMA",
    "DECORATED_MOVE_CERT_BLOCKER_ID",
    "MATRIX_LEVEL_ONLY_BLOCKER_ID",
    "N35_PLANNED_CALLS_BLOCKER_ID",
    "NODE_ID",
    "NOT_GENERATED_LINK_MOVE_BLOCKER_ID",
    "ORDINARY_SURGERY_BLOCKER_ID",
    "PAIR_DRY_RUN_BLOCKER_ID",
    "SOURCE_PROOF_BLOCKER_ID",
    "classify_registry_pair_for_decorated_gate",
    "classify_presentation_pair_for_decorated_gate",
    "decorated_kirby_gate_artifact_certificate",
    "decorated_kirby_gate_artifact",
    "stable_decorated_kirby_gate_json",
    "validate_decorated_kirby_gate_artifact",
]


if __name__ == "__main__":
    raise SystemExit(main())
