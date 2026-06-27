"""Executable blocker for the n50 decorated Kirby move gate.

This module consumes the n45 presentation-pair registry and classifies each
toy pair as blocked until it carries real decorated Kirby move evidence:
lineage, integer basis data, ordinary surgery support, and source proof.  It is
intentionally a gate scaffold, not a decorated Kirby theorem.
"""

from __future__ import annotations

import json
from typing import Final, Mapping

from twisted_yetter.presentation_pairs import (
    PRESENTATION_PAIR_REGISTRY_SCHEMA,
    presentation_pair_registry_artifact,
    validate_presentation_pair_registry_metadata,
)

DECORATED_KIRBY_GATE_SCHEMA: Final = "twisted-yetter.decorated-kirby-gate.v1"
DECORATED_KIRBY_GATE_NOTE: Final = (
    "wiki/understandings/decorated-kirby-move-gate.org"
)

NODE_ID: Final = "n50-decorated-kirby-move-gate"
CLAIM_LEVEL: Final = "executable blocker/certificate"

PAIR_DRY_RUN_BLOCKER_ID: Final = "presentation-pair-candidate-dry-run"
DECORATED_MOVE_CERT_BLOCKER_ID: Final = (
    "missing-decorated-move-certificate"
)
COMPONENT_LINEAGE_BLOCKER_ID: Final = "missing-component-lineage-certificate"
BASIS_MATRIX_BLOCKER_ID: Final = "missing-basis-matrix-certificate"
ORDINARY_SURGERY_BLOCKER_ID: Final = "ordinary-surgery-gate-blocked"
SOURCE_PROOF_BLOCKER_ID: Final = "missing-source-proof"

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
    pair_classifications = [
        classify_presentation_pair_for_decorated_gate(
            pair,
            ordinary_surgery_gate_status=str(
                registry.get("ordinary_surgery_gate_status", "missing")
            ),
        )
        for pair in pair_list
    ]
    all_pairs_blocked = all(
        pair["status"] == "blocked" for pair in pair_classifications
    )

    artifact: dict[str, object] = {
        "schema": DECORATED_KIRBY_GATE_SCHEMA,
        "status": "blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "n50 gate scaffold over n45 dry-run pair metadata; no decorated "
            "Kirby move certificate is present"
        ),
        "input_registry_schema": registry.get("schema"),
        "input_registry_status": registry.get("status"),
        "input_registry_node_id": registry.get("node_id"),
        "input_registry_validation": registry_validation,
        "ordinary_surgery_gate_status": registry.get("ordinary_surgery_gate_status"),
        "pair_count": len(pair_classifications),
        "pair_classifications": pair_classifications,
        "all_pairs_blocked": all_pairs_blocked,
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
            "decorated Kirby move certificate for each accepted pair",
            "certified component lineage, not placeholder lineage prose",
            "integer basis matrix with claim_certified true",
            "ordinary surgery gate support for closed 4D claims",
            "source-audited proof/reference record for the decorated move rule",
        ],
        "downstream_decision": {
            "n55-toy-closed-suite": "blocked",
            "reason": (
                "n55 may not treat n45 toy pairs as closed 4-manifold "
                "invariance evidence until n50 has non-placeholder move "
                "certificates"
            ),
        },
        "ledger_note": DECORATED_KIRBY_GATE_NOTE,
    }
    artifact["metadata_validation"] = validate_decorated_kirby_gate_artifact(
        artifact
    )
    return artifact


def classify_presentation_pair_for_decorated_gate(
    pair: Mapping[str, object],
    *,
    ordinary_surgery_gate_status: str,
) -> dict[str, object]:
    """Classify one n45 pair for the decorated Kirby move gate."""

    pair_id = str(pair.get("pair_id", "missing-pair-id"))
    relation_status = str(pair.get("relation_status", "missing"))
    component_lineage = _mapping_or_empty(pair.get("component_lineage"))
    basis_map = _mapping_or_empty(pair.get("basis_map"))

    blocked_reasons = []
    if relation_status != "certified/decorated-kirby-move":
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
    if basis_map.get("claim_certified") is not True or basis_map.get("matrix") is None:
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

    return {
        "pair_id": pair_id,
        "status": "blocked" if blocked_reasons else "pass",
        "final_decorated_gate_passed": False if blocked_reasons else True,
        "relation_type": pair.get("relation_type"),
        "relation_status": relation_status,
        "left_case_id": _side_case_id(pair.get("left")),
        "right_case_id": _side_case_id(pair.get("right")),
        "required_pair_fields_present": all(field in pair for field in REQUIRED_PAIR_FIELDS),
        "blocked_reason_ids": [str(reason["reason_id"]) for reason in blocked_reasons],
        "blocked_reasons": blocked_reasons,
        "blocked_final_claims": list(BLOCKED_FINAL_CLAIMS),
    }


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


def _mapping_or_empty(value: object) -> Mapping[str, object]:
    return value if isinstance(value, Mapping) else {}


def _side_case_id(side: object) -> object:
    if isinstance(side, Mapping):
        return side.get("decorated_core_case_id")
    return None


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
    if pair.get("status") != "blocked":
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
    "DECORATED_KIRBY_GATE_NOTE",
    "DECORATED_KIRBY_GATE_SCHEMA",
    "DECORATED_MOVE_CERT_BLOCKER_ID",
    "NODE_ID",
    "ORDINARY_SURGERY_BLOCKER_ID",
    "PAIR_DRY_RUN_BLOCKER_ID",
    "SOURCE_PROOF_BLOCKER_ID",
    "classify_presentation_pair_for_decorated_gate",
    "decorated_kirby_gate_artifact",
    "stable_decorated_kirby_gate_json",
    "validate_decorated_kirby_gate_artifact",
]
