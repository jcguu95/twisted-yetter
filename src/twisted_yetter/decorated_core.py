"""Decorated-core input artifact scaffold for n35.

This module aligns a machine-readable link diagram, finite-A component
decorations, and candidate Omega_a sector metadata.  It is exact deterministic
metadata only.  It does not evaluate a link, sum Kirby colors, prove decorated
Kirby moves, compute a closed invariant, or compare exotic smooth structures.
"""

from __future__ import annotations

import json
from typing import Final, Mapping

from twisted_yetter.finite_groups import FiniteAbelianGroup
from twisted_yetter.h2_marking import h2_component_decoration_certificate
from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.omega_a import omega_a_candidate_certificate
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate
from twisted_yetter.provisional_formula_policy import (
    N30_DOWNSTREAM_DECISIONS,
    claim_policy_decision,
)

DECORATED_CORE_SCHEMA: Final = "twisted-yetter.decorated-core-input.v1"
DECORATED_CORE_NOTE: Final = "wiki/understandings/twisted-decorated-core.org"

CLAIM_LEVEL: Final = "computed evidence scaffold"
SOURCE_STATUS: Final = (
    "computed evidence scaffold from n33/n34 metadata; candidate coefficients "
    "are NOT PROVED IN REPO and ordinary surgery gate remains blocked"
)

ALLOWED_CLAIM_LEVELS: Final = (
    "computed evidence scaffold",
    "provisional-low-confidence",
    "candidate-experimental",
)

DOES_NOT_COMPUTE: Final = (
    "link evaluation",
    "Kirby color sum",
    "decorated Kirby move proof",
    "closed invariant",
    "exotic detection",
)

BLOCKED_HIGH_CLAIMS: Final = (
    "decorated/twisted formula theorem",
    "claim-supporting closed 4D invariant",
    "exotic detection claim",
    "Reutter escape/no-go conclusion",
)


def decorated_core_input_artifact(
    diagram: LinkDiagram,
    group: FiniteAbelianGroup,
    *,
    basis_id: str,
    basis_status: str,
    basis_source_status: str,
    decoration_by_component: Mapping[str, tuple[int, ...]] | None = None,
    decoration_vector: tuple[tuple[int, ...], ...] | list[tuple[int, ...]] | None = None,
    claim_level: str = CLAIM_LEVEL,
    claim_theorem: bool = False,
    claim_closed_invariant: bool = False,
    claim_exotic_detection: bool = False,
) -> dict[str, object]:
    """Return deterministic decorated-core input metadata.

    The artifact maps each component decoration to the candidate Omega_a sector
    for the same finite-group element.  It consumes n34 component-decoration
    metadata and n33 coefficient metadata, but it does not evaluate any link or
    invariant.
    """

    if claim_theorem or claim_closed_invariant or claim_exotic_detection:
        raise ValueError(
            "n35 refuses theorem, closed-invariant, and exotic-detection claims"
        )
    _validate_claim_level(claim_level)

    h2_certificate = h2_component_decoration_certificate(
        diagram,
        group,
        basis_id=basis_id,
        basis_status=basis_status,
        basis_source_status=basis_source_status,
        decoration_by_component=decoration_by_component,
        decoration_vector=decoration_vector,
    )
    omega_certificate = omega_a_candidate_certificate(group)
    sectors_by_id = {
        str(sector["sector_id"]): sector for sector in omega_certificate["sectors"]
    }
    n24 = ordinary_surgery_gate_certificate()

    artifact: dict[str, object] = {
        "schema": DECORATED_CORE_SCHEMA,
        "status": "pass",
        "node_id": "n35-twisted-decorated-core",
        "claim_level": claim_level,
        "source_status": SOURCE_STATUS,
        "ordinary_surgery_gate_status": n24["status"],
        "ordinary_surgery_gate_status_explanation": (
            "n35 is decorated-core input metadata only and inherits the blocked "
            "n24 ordinary surgery gate; no closed ordinary or decorated "
            "invariant claim is allowed"
        ),
        "diagram_id": diagram.diagram_id,
        "diagram_schema": diagram.to_json()["schema"],
        "component_ids": list(diagram.component_ids),
        "finite_group_id": h2_certificate["finite_group_id"],
        "decoration_by_component": h2_certificate["decoration_by_component"],
        "decoration_vector": h2_certificate["decoration_vector"],
        "zero_decoration": h2_certificate["zero_decoration"],
        "basis": h2_certificate["basis"],
        "h2_decoration_certificate_summary": _h2_summary(h2_certificate),
        "candidate_coefficient_certificate": _omega_summary(omega_certificate),
        "component_sector_metadata": [
            _component_sector_payload(item, sectors_by_id)
            for item in h2_certificate["decoration_vector"]
        ],
        "all_components_have_candidate_sector": True,
        "theorem_claim_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "decorated_kirby_move_proof_claim_allowed": False,
        "does_not_compute": list(DOES_NOT_COMPUTE),
        "blocked_high_claims": list(BLOCKED_HIGH_CLAIMS),
        "n30_policy_decision": claim_policy_decision(claim_level),
        "n35_policy_decision": _n35_policy_decision(),
        "ledger_note": DECORATED_CORE_NOTE,
    }
    artifact["metadata_validation"] = validate_decorated_core_artifact_metadata(
        artifact
    )
    return artifact


def validate_decorated_core_artifact_metadata(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Check n35 required metadata without interpreting topology."""

    required = {
        "claim_level",
        "source_status",
        "ordinary_surgery_gate_status",
        "diagram_id",
        "component_ids",
        "finite_group_id",
        "decoration_by_component",
        "candidate_coefficient_certificate",
    }
    missing = sorted(field for field in required if field not in artifact)
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "theorem_claim_allowed",
            "closed_4_manifold_claim_allowed",
            "exotic_detection_claim_allowed",
            "decorated_kirby_move_proof_claim_allowed",
        )
    )
    claim_decision = claim_policy_decision(str(artifact.get("claim_level")))
    return {
        "valid": not missing
        and blocked_claims_ok
        and claim_decision["allowed"] is True,
        "missing_required_fields": missing,
        "blocked_claims_ok": blocked_claims_ok,
        "claim_decision": claim_decision,
        "scope": "decorated-core input metadata only; no link evaluation",
    }


def stable_decorated_core_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n35 decorated-core artifact deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _component_sector_payload(
    decoration_payload: Mapping[str, object],
    sectors_by_id: Mapping[str, object],
) -> dict[str, object]:
    component_id = str(decoration_payload["component_id"])
    element_id = str(decoration_payload["element_id"])
    sector = sectors_by_id.get(element_id)
    if sector is None:
        raise ValueError(
            f"component {component_id!r} decoration {element_id!r} has no "
            "candidate Omega_a sector"
        )
    return {
        "component_id": component_id,
        "decoration_element_id": element_id,
        "decoration_element": decoration_payload["element"],
        "candidate_sector_id": element_id,
        "candidate_sector_element": sector["element"],  # type: ignore[index]
        "candidate_coefficients": sector["coefficients"],  # type: ignore[index]
        "coefficient_certificate_ref": "candidate_coefficient_certificate",
        "source_status": "sector metadata copied from n33 candidate Omega_a scaffold",
    }


def _h2_summary(certificate: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": certificate["schema"],
        "node_id": certificate["node_id"],
        "claim_level": certificate["claim_level"],
        "source_status": certificate["source_status"],
        "basis_id": certificate["basis_id"],
        "basis_status": certificate["basis_status"],
        "basis_source_status": certificate["basis_source_status"],
        "metadata_validation": certificate["metadata_validation"],
        "ledger_note": certificate["ledger_note"],
    }


def _omega_summary(certificate: Mapping[str, object]) -> dict[str, object]:
    return {
        "schema": certificate["schema"],
        "node_id": certificate["node_id"],
        "claim_level": certificate["claim_level"],
        "source_status": certificate["source_status"],
        "candidate_formula_id": certificate["candidate_formula_id"],
        "candidate_formula_display": certificate["candidate_formula_display"],
        "finite_group_id": certificate["finite_group_id"],
        "category_id": certificate["category_id"],
        "character_table_source": certificate["character_table_source"],
        "label_character_assignment": certificate["label_character_assignment"],
        "ordinary_surgery_gate_status": certificate[
            "ordinary_surgery_gate_status"
        ],
        "metadata_validation": certificate["metadata_validation"],
        "ledger_note": certificate["ledger_note"],
    }


def _validate_claim_level(claim_level: str) -> None:
    if claim_level not in ALLOWED_CLAIM_LEVELS:
        raise ValueError(
            f"unsupported n35 claim level {claim_level!r}; allowed levels are "
            f"{', '.join(ALLOWED_CLAIM_LEVELS)}"
        )
    decision = claim_policy_decision(claim_level)
    if decision["allowed"] is not True:
        raise ValueError(f"n30 policy does not allow n35 claim level {claim_level!r}")


def _n35_policy_decision() -> dict[str, object]:
    for decision in N30_DOWNSTREAM_DECISIONS:
        if decision["node_id"] == "n35-twisted-decorated-core":
            return {
                **decision,
                "allowed_claim_levels": list(decision["allowed_claim_levels"]),
                "required_artifact_fields": list(
                    decision["required_artifact_fields"]
                ),
            }
    raise RuntimeError("n35 policy decision missing from n30")


__all__ = [
    "ALLOWED_CLAIM_LEVELS",
    "BLOCKED_HIGH_CLAIMS",
    "CLAIM_LEVEL",
    "DECORATED_CORE_SCHEMA",
    "DOES_NOT_COMPUTE",
    "SOURCE_STATUS",
    "decorated_core_input_artifact",
    "stable_decorated_core_json",
    "validate_decorated_core_artifact_metadata",
]
