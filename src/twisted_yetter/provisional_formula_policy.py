"""Policy gate for provisional twisted-formula experiments.

This module does not implement a twisted Yetter formula.  It records the n30
decision that downstream nodes may run candidate/provisional experiments while
the n24 ordinary surgery gate is still blocked, provided artifacts keep explicit
claim-level and source-status metadata and refuse theorem-level claims.
"""

from __future__ import annotations

import json
from typing import Final, Mapping

from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate

PROVISIONAL_FORMULA_POLICY_SCHEMA: Final = (
    "twisted-yetter.provisional-formula-policy.v1"
)
PROVISIONAL_FORMULA_POLICY_NOTE: Final = (
    "wiki/understandings/provisional-formula-policy.org"
)

ALLOWED_ARTIFACT_CLAIM_LEVELS: Final = (
    "candidate-experimental",
    "provisional-low-confidence",
    "schema-test-safe",
    "computed evidence scaffold",
)

REQUIRED_ARTIFACT_FIELDS: Final = (
    "claim_level",
    "source_status",
)

REJECTED_CLAIM_TYPES: Final = (
    "claim-supporting closed 4D invariant",
    "decorated/twisted formula theorem",
    "exotic detection claim",
    "Reutter escape/no-go conclusion",
)

N30_DOWNSTREAM_DECISIONS: Final = (
    {
        "node_id": "n31-yetter-z2-surgical-source-capture",
        "decision": "allowed",
        "allowed_activity": "source capture for the Yetter Z/2 surgical formula",
        "allowed_claim_levels": ("schema-test-safe", "provisional-low-confidence"),
        "required_artifact_fields": REQUIRED_ARTIFACT_FIELDS,
        "source_status_required": True,
        "claim_boundary": (
            "source capture may record locators, page labels, and missing "
            "slots, but it must not promote the Z/2 surgical formula to a "
            "decorated/twisted theorem while independent checks remain open"
        ),
    },
    {
        "node_id": "n32-general-a-candidate-contract",
        "decision": "allowed",
        "allowed_activity": "candidate contract for the general finite A color",
        "allowed_claim_levels": ("candidate-experimental", "schema-test-safe"),
        "required_artifact_fields": REQUIRED_ARTIFACT_FIELDS,
        "source_status_required": True,
        "claim_boundary": (
            "the general finite A contract may state falsification criteria "
            "and expected specializations, but only as a candidate contract"
        ),
    },
    {
        "node_id": "n33-omega-a-implementation",
        "decision": "allowed",
        "allowed_activity": "finite A candidate-color implementation scaffold",
        "allowed_claim_levels": ("candidate-experimental", "schema-test-safe"),
        "required_artifact_fields": REQUIRED_ARTIFACT_FIELDS,
        "source_status_required": True,
        "claim_boundary": (
            "implementation artifacts may compute exact candidate coefficients "
            "for supported finite A data, but must expose candidate status and "
            "must not certify a homologically twisted Kirby color"
        ),
    },
    {
        "node_id": "n35-twisted-decorated-core",
        "decision": "allowed-with-blocked-ordinary-gate",
        "allowed_activity": "decorated core experiments from diagram-backed data",
        "allowed_claim_levels": (
            "computed evidence scaffold",
            "provisional-low-confidence",
            "candidate-experimental",
        ),
        "required_artifact_fields": REQUIRED_ARTIFACT_FIELDS
        + ("ordinary_surgery_gate_status",),
        "source_status_required": True,
        "claim_boundary": (
            "decorated core outputs are computed evidence scaffolds only while "
            "n24 is blocked; they cannot be closed 4D invariant values or "
            "exotic-detection evidence"
        ),
    },
)


def claim_policy_decision(claim_type: str) -> dict[str, object]:
    """Return the deterministic n30 decision for one claim type."""

    if claim_type in REJECTED_CLAIM_TYPES:
        return {
            "claim_type": claim_type,
            "decision": "rejected",
            "allowed": False,
            "reason": (
                "n30 permits only provisional/candidate experiments while "
                "n24-ordinary-surgery-gate is blocked"
            ),
            "inherited_blocker": "n24-ordinary-surgery-gate:blocked",
        }

    if claim_type in ALLOWED_ARTIFACT_CLAIM_LEVELS:
        return {
            "claim_type": claim_type,
            "decision": "allowed",
            "allowed": True,
            "required_artifact_fields": list(REQUIRED_ARTIFACT_FIELDS),
            "claim_boundary": (
                "allowed only as non-theorem experimental or schema metadata"
            ),
        }

    return {
        "claim_type": claim_type,
        "decision": "unknown-claim-type",
        "allowed": False,
        "reason": "claim type is not explicitly allowed by n30 policy",
        "inherited_blocker": "n24-ordinary-surgery-gate:blocked",
    }


def provisional_formula_policy_certificate() -> dict[str, object]:
    """Return the deterministic n30 provisional formula policy certificate."""

    n24 = ordinary_surgery_gate_certificate()
    n24_reason_ids = [reason["reason_id"] for reason in n24["blocked_reasons"]]

    return {
        "schema": PROVISIONAL_FORMULA_POLICY_SCHEMA,
        "status": "policy-active",
        "node_id": "n30-provisional-formula-policy",
        "claim_level": "policy/gating certificate",
        "ordinary_surgery_gate_dependency": {
            "node_id": n24["node_id"],
            "schema": n24["schema"],
            "status": n24["status"],
            "blocked_source_slots": n24["blocked_source_slots"],
            "blocked_reason_ids": n24_reason_ids,
            "closed_4_manifold_claim_allowed": n24[
                "closed_4_manifold_claim_allowed"
            ],
            "claim_supporting_closed_invariant_allowed": n24[
                "claim_supporting_closed_invariant_allowed"
            ],
        },
        "allowed_artifact_claim_levels": list(ALLOWED_ARTIFACT_CLAIM_LEVELS),
        "required_artifact_fields": list(REQUIRED_ARTIFACT_FIELDS),
        "rejected_claim_types": list(REJECTED_CLAIM_TYPES),
        "claim_decisions": [
            claim_policy_decision(claim_type)
            for claim_type in REJECTED_CLAIM_TYPES
        ],
        "downstream_policy_decisions": [
            {
                **decision,
                "allowed_claim_levels": list(decision["allowed_claim_levels"]),
                "required_artifact_fields": list(
                    decision["required_artifact_fields"]
                ),
            }
            for decision in N30_DOWNSTREAM_DECISIONS
        ],
        "global_policy": {
            "may_run_many_examples": True,
            "passing_examples_are_proof": False,
            "failures_must_be_recorded": True,
            "must_not_implement_formula_here": True,
            "must_not_source_audit_external_references_here": True,
            "must_preserve_source_status_fields": True,
        },
        "unblocks": [
            "n31-yetter-z2-surgical-source-capture as source-capture work",
            "n32-general-a-candidate-contract as candidate contract work",
            "n33-omega-a-implementation as candidate implementation scaffold",
            "n35-twisted-decorated-core as computed evidence scaffold",
        ],
        "still_blocked": list(REJECTED_CLAIM_TYPES),
        "ledger_note": PROVISIONAL_FORMULA_POLICY_NOTE,
    }


def stable_provisional_formula_policy_json(
    certificate: Mapping[str, object],
) -> str:
    """Serialize an n30 policy certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


__all__ = [
    "ALLOWED_ARTIFACT_CLAIM_LEVELS",
    "N30_DOWNSTREAM_DECISIONS",
    "PROVISIONAL_FORMULA_POLICY_NOTE",
    "PROVISIONAL_FORMULA_POLICY_SCHEMA",
    "REJECTED_CLAIM_TYPES",
    "REQUIRED_ARTIFACT_FIELDS",
    "claim_policy_decision",
    "provisional_formula_policy_certificate",
    "stable_provisional_formula_policy_json",
]
