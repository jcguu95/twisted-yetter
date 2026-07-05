"""Candidate contract for general finite-A Omega_a artifacts.

This n32 module is deliberately metadata-only.  It records the contract that
future n33 candidate artifacts must satisfy before any experimental finite-A
Omega_a scaffold is accepted.  It does not compute Omega_a coefficients and it
does not promote the candidate formula to a theorem.
"""

from __future__ import annotations

import json
from typing import Final, Mapping

from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate
from twisted_yetter.provisional_formula_policy import claim_policy_decision

OMEGA_A_CONTRACT_SCHEMA: Final = "twisted-yetter.omega-a-candidate-contract.v1"
OMEGA_A_CANDIDATE_FORMULA_ID: Final = "omega-a-character-weighted-kirby-color-v0"
OMEGA_A_CONTRACT_NOTE: Final = (
    legacy_prose_member_ref("wiki/understandings/general-a-candidate-contract.org")
)

ALLOWED_CONTRACT_CLAIM_LEVELS: Final = (
    "candidate-experimental",
    "schema-test-safe",
)

SOURCE_STATUS_OPTIONS: Final = (
    "candidate-experimental",
    "SOURCE NEEDED",
    "NOT PROVED IN REPO",
)

REQUIRED_ARTIFACT_FIELDS: Final = (
    "claim_level",
    "source_status",
    "candidate_formula_id",
    "finite_group_id",
    "character_table_source",
    "character_data_source_status",
    "marking_basis_status",
)

ORDINARY_SURGERY_GATE_ONE_OF_FIELDS: Final = (
    "ordinary_surgery_gate_status",
    "ordinary_surgery_gate_status_explanation",
)

SPECIALIZATION_CHECKS: Final = (
    {
        "check_id": "trivial-a-recovers-ordinary-omega-candidate",
        "description": (
            "For the trivial finite group A, the candidate contract expects "
            "the only sector to specialize to the ordinary omega candidate, "
            "while still carrying ordinary-surgery gate metadata."
        ),
        "claim_level": "candidate-experimental",
    },
    {
        "check_id": "z2-nontrivial-sector-aligns-with-theta-target-if-sourced",
        "description": (
            "For A = Z/2, the nontrivial character sector is expected to "
            "align with the theta target only after n31 source capture and "
            "convention reconciliation confirm that target."
        ),
        "claim_level": "candidate-experimental",
    },
    {
        "check_id": "character-orthogonality-and-exactness",
        "description": (
            "Finite-A character data must pass exact row and column "
            "orthogonality checks with no floating-point approximations."
        ),
        "claim_level": "schema-test-safe",
    },
    {
        "check_id": "zero-and-all-trivial-decorations",
        "description": (
            "Zero / all-trivial decorations must be represented explicitly "
            "and must route to the ordinary candidate sector, not to an "
            "unstated decorated formula."
        ),
        "claim_level": "schema-test-safe",
    },
)

REQUIRED_SOURCE_PROOF_SLOTS: Final = (
    {
        "slot_id": "formula-source-or-proof",
        "status": "SOURCE NEEDED / PROOF NEEDED",
        "description": (
            "A page-level source, theorem, proposition, or repo-local proof is "
            "needed before the display can be promoted beyond a candidate."
        ),
    },
    {
        "slot_id": "lambda-action-source",
        "status": "SOURCE NEEDED / CONVENTION NEEDED",
        "description": (
            "The meaning of lambda_i(a) must be tied to an exact character, "
            "tensor automorphism, grading, or other stated categorical action."
        ),
    },
    {
        "slot_id": "kirby-move-proof-scope",
        "status": "PROOF NEEDED",
        "description": (
            "Handle slides, handle cancellations, orientation conventions, "
            "normalization, signature anomaly, and implicit 3-handles must be "
            "covered before any closed-invariant claim."
        ),
    },
    {
        "slot_id": "ordinary-specialization-boundary",
        "status": "INHERITS n22/n24 BOUNDARY",
        "description": (
            "Trivial A or trivial decoration may reduce only to the current "
            "ordinary omega/local n22 behavior inside the n24 blocked surgery "
            "boundary."
        ),
    },
    {
        "slot_id": "z2-specialization-source",
        "status": "INHERITS n31 PROVISIONAL TARGET",
        "description": (
            "A = Z/2 may specialize to the n31 omega/theta target only as a "
            "provisional falsification target until source slots are filled."
        ),
    },
)

FALSIFICATION_CRITERIA: Final = (
    {
        "criterion_id": "toy-examples-inconsistent",
        "description": (
            "Exact toy examples violate stated specialization checks or "
            "change under accepted local controls."
        ),
    },
    {
        "criterion_id": "z2-mismatch-after-source-capture",
        "description": (
            "After n31 fills the Z/2 source slots and conventions, the "
            "candidate's nontrivial sector disagrees with the sourced theta "
            "formula."
        ),
    },
    {
        "criterion_id": "handle-slide-or-presentation-mismatch",
        "description": (
            "The candidate gives incompatible values for presentations that "
            "later decorated Kirby-move gates certify as equivalent."
        ),
    },
    {
        "criterion_id": "exact-arithmetic-inconsistency",
        "description": (
            "The same input produces nonidentical exact certificates, uses "
            "floating approximations, or fails exact character orthogonality."
        ),
    },
    {
        "criterion_id": "marking-or-basis-mismatch",
        "description": (
            "A basis or H2-marking change is guessed, omitted, or produces "
            "different candidate sectors without an explicit recorded matrix "
            "and marking interpretation."
        ),
    },
    {
        "criterion_id": "failed-example-recorded-against-candidate",
        "description": (
            "Any exact failed example must be recorded as evidence against "
            "the candidate formula, the local convention, or the code path; "
            "it must not be silently discarded as noise."
        ),
    },
)

MARKING_REQUIREMENTS: Final = (
    {
        "requirement_id": "represent-h2-basis",
        "description": (
            "Artifacts that attach sectors to decorations must record the "
            "Kirby/H2 basis or explicitly state why no marking is in scope."
        ),
    },
    {
        "requirement_id": "record-basis-change-action",
        "description": (
            "Basis changes and handle-slide lineage must be represented by "
            "explicit integer matrices or structured blockers, not guessed."
        ),
    },
    {
        "requirement_id": "separate-marked-from-unmarked-claims",
        "description": (
            "Candidate evidence must distinguish marked distinctions, orbit "
            "or multiset distinctions, and unsupported unmarked claims."
        ),
    },
)

N33_REQUIREMENTS: Final = (
    {
        "requirement_id": "preserve-contract-metadata",
        "description": (
            "Every n33 artifact must include the n32 required fields and one "
            "ordinary-surgery gate status field or explanation."
        ),
    },
    {
        "requirement_id": "keep-candidate-claim-level",
        "description": (
            "n33 outputs may use only candidate-experimental or "
            "schema-test-safe claim levels for this contract."
        ),
    },
    {
        "requirement_id": "cite-character-table-source",
        "description": (
            "n33 must identify the exact finite_group_id and "
            "character_table_source used for sector metadata, and annotate "
            "the character_data_source_status for lambda_i(a)."
        ),
    },
    {
        "requirement_id": "no-theorem-or-exotic-claim",
        "description": (
            "n33 must refuse decorated theorem, closed invariant, exotic "
            "detection, and Reutter escape/no-go claims."
        ),
    },
    {
        "requirement_id": "no-coefficient-claim-without-later-implementation",
        "description": (
            "n32 itself supplies no Omega_a coefficient implementation; n33 "
            "must keep any later coefficient scaffold visibly experimental."
        ),
    },
)


def omega_a_contract_claim_decision(claim_type: str) -> dict[str, object]:
    """Return the n32 decision for a claim level or high-claim type."""

    n30_decision = claim_policy_decision(claim_type)
    if not n30_decision["allowed"]:
        return {
            **n30_decision,
            "node_id": "n32-general-a-candidate-contract",
            "contract_reason": (
                "n32 inherits the n30 refusal for theorem, closed invariant, "
                "exotic, and Reutter-style claims"
            ),
        }

    if claim_type in ALLOWED_CONTRACT_CLAIM_LEVELS:
        return {
            "claim_type": claim_type,
            "node_id": "n32-general-a-candidate-contract",
            "decision": "allowed",
            "allowed": True,
            "required_artifact_fields": list(REQUIRED_ARTIFACT_FIELDS),
            "ordinary_surgery_gate_one_of_fields": list(
                ORDINARY_SURGERY_GATE_ONE_OF_FIELDS
            ),
            "claim_boundary": "metadata-only candidate contract",
        }

    return {
        "claim_type": claim_type,
        "node_id": "n32-general-a-candidate-contract",
        "decision": "rejected-by-n32-contract",
        "allowed": False,
        "reason": (
            "n32 accepts only candidate-experimental or schema-test-safe "
            "artifact levels, even if n30 allows other provisional work"
        ),
    }


def validate_omega_a_candidate_artifact_metadata(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Check n32 metadata requirements without inspecting formula values."""

    missing_fields = [
        field for field in REQUIRED_ARTIFACT_FIELDS if field not in artifact
    ]
    has_ordinary_gate_boundary = any(
        field in artifact for field in ORDINARY_SURGERY_GATE_ONE_OF_FIELDS
    )
    if not has_ordinary_gate_boundary:
        missing_fields.append("ordinary_surgery_gate_status_or_explanation")

    claim_level = artifact.get("claim_level")
    claim_decision = omega_a_contract_claim_decision(str(claim_level))
    formula_id_matches = (
        artifact.get("candidate_formula_id") == OMEGA_A_CANDIDATE_FORMULA_ID
    )

    valid = (
        not missing_fields
        and claim_decision["allowed"] is True
        and formula_id_matches
    )

    return {
        "schema": OMEGA_A_CONTRACT_SCHEMA + ".metadata-validation",
        "valid": valid,
        "missing_fields": missing_fields,
        "claim_decision": claim_decision,
        "candidate_formula_id_matches": formula_id_matches,
        "does_not_validate_formula_coefficients": True,
    }


def omega_a_candidate_contract_certificate() -> dict[str, object]:
    """Return the deterministic n32 candidate contract certificate."""

    n24 = ordinary_surgery_gate_certificate()
    return {
        "schema": OMEGA_A_CONTRACT_SCHEMA,
        "status": "contract-active",
        "node_id": "n32-general-a-candidate-contract",
        "claim_level": "candidate-experimental",
        "source_status": "NOT PROVED IN REPO / SOURCE NEEDED",
        "candidate_formula_id": OMEGA_A_CANDIDATE_FORMULA_ID,
        "candidate_formula_display": "Omega_a = sum_i d_i lambda_i(a) X_i",
        "candidate_formula_claim_boundary": (
            "formula display is a candidate target for experiments and "
            "falsification, not a theorem or source-audited Kirby color"
        ),
        "allowed_claim_levels": list(ALLOWED_CONTRACT_CLAIM_LEVELS),
        "source_status_options": list(SOURCE_STATUS_OPTIONS),
        "required_artifact_fields": list(REQUIRED_ARTIFACT_FIELDS),
        "ordinary_surgery_gate_requirement": {
            "one_of": list(ORDINARY_SURGERY_GATE_ONE_OF_FIELDS),
            "inherited_status": n24["status"],
            "ordinary_surgery_claim_allowed": n24[
                "ordinary_surgery_claim_allowed"
            ],
            "closed_4_manifold_claim_allowed": n24[
                "closed_4_manifold_claim_allowed"
            ],
        },
        "character_table_requirement": {
            "finite_group_id_required": True,
            "character_table_source_required": True,
            "character_data_source_status_required": True,
            "exact_character_orthogonality_required": True,
            "floating_point_allowed": False,
            "lambda_i_a_exact_required": True,
            "source_status_annotation_required": True,
        },
        "marking_requirement": {
            "marking_basis_status_required": True,
            "basis_and_h2_effects_must_be_represented": True,
            "basis_and_h2_effects_must_not_be_guessed": True,
            "requirements": [
                dict(requirement) for requirement in MARKING_REQUIREMENTS
            ],
        },
        "required_source_proof_slots": [
            dict(slot) for slot in REQUIRED_SOURCE_PROOF_SLOTS
        ],
        "specialization_checks": [
            dict(check) for check in SPECIALIZATION_CHECKS
        ],
        "falsification_criteria": [
            dict(criterion) for criterion in FALSIFICATION_CRITERIA
        ],
        "n33_requirements": [
            dict(requirement) for requirement in N33_REQUIREMENTS
        ],
        "claim_decisions": [
            omega_a_contract_claim_decision(claim_type)
            for claim_type in (
                "candidate-experimental",
                "schema-test-safe",
                "provisional-low-confidence",
                "decorated/twisted formula theorem",
                "claim-supporting closed 4D invariant",
                "exotic detection claim",
                "Reutter escape/no-go conclusion",
            )
        ],
        "does_not_implement": [
            "Omega_a coefficients",
            "colored framed link evaluation",
            "decorated Kirby move proof",
            "closed 4-manifold invariant",
        ],
        "unblocks": [
            "n33-omega-a-implementation as candidate implementation scaffold",
        ],
        "still_blocked": [
            "theorem-level general finite A Omega_a formula",
            "closed homologically twisted Yetter invariant claim",
            "exotic detection claim",
            "decorated Reutter escape/no-go conclusion",
        ],
        "ledger_note": OMEGA_A_CONTRACT_NOTE,
    }


def stable_omega_a_contract_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n32 contract certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


__all__ = [
    "ALLOWED_CONTRACT_CLAIM_LEVELS",
    "FALSIFICATION_CRITERIA",
    "MARKING_REQUIREMENTS",
    "N33_REQUIREMENTS",
    "OMEGA_A_CANDIDATE_FORMULA_ID",
    "OMEGA_A_CONTRACT_NOTE",
    "OMEGA_A_CONTRACT_SCHEMA",
    "ORDINARY_SURGERY_GATE_ONE_OF_FIELDS",
    "REQUIRED_ARTIFACT_FIELDS",
    "REQUIRED_SOURCE_PROOF_SLOTS",
    "SOURCE_STATUS_OPTIONS",
    "SPECIALIZATION_CHECKS",
    "omega_a_candidate_contract_certificate",
    "omega_a_contract_claim_decision",
    "stable_omega_a_contract_json",
    "validate_omega_a_candidate_artifact_metadata",
]
