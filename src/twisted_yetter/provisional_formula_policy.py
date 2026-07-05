"""Policy gate for provisional twisted-formula experiments.

This module does not implement a twisted Yetter formula.  It records the n30
decision that downstream nodes may run candidate/provisional experiments while
the n24 ordinary surgery gate is still blocked, provided artifacts keep explicit
claim-level and source-status metadata and refuse theorem-level claims.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    git_metadata,
    hash_json,
    make_certificate,
)
from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate

PROVISIONAL_FORMULA_POLICY_SCHEMA: Final = (
    "twisted-yetter.provisional-formula-policy.v1"
)
PROVISIONAL_FORMULA_POLICY_NOTE: Final = (
    legacy_prose_member_ref("wiki/understandings/provisional-formula-policy.org")
)
PROVISIONAL_FORMULA_POLICY_ARTIFACT: Final = (
    "experiments/results/provisional-formula-policy/n30-policy-certificate.json"
)
NODE_ID: Final = "n30-provisional-formula-policy"
N24_ACCEPTED_COMMIT: Final = "bbc48b213409a5b034357ba91405f980006e6a05"
N24_ACCEPTED_COMMIT_SHORT: Final = "bbc48b2"
N24_ARTIFACT: Final = (
    "experiments/results/ordinary-surgery-gate/n24-blocker-certificate.json"
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
    "closed homologically twisted Yetter invariant value",
    "decorated/twisted formula theorem",
    "exotic detection claim",
    "Reutter escape/no-go conclusion",
)

FORMULA_STATUS_LEDGER: Final = (
    {
        "formula_id": "yetter-z2-surgical-formula",
        "status": "provisional-low-confidence",
        "policy": (
            "Yetter Z/2 surgical formula may be source-captured and checked, "
            "but cannot support theorem-level closed/decorated claims until "
            "source audit and independent checks pass"
        ),
        "allowed_next_node": "n31-yetter-z2-surgical-source-capture",
    },
    {
        "formula_id": "general-finite-a-omega-a",
        "display": "Omega_a = sum_i d_i lambda_i(a) X_i",
        "status": "candidate-experimental",
        "policy": (
            "general finite A Omega_a may be used only as a candidate/local "
            "experiment until proof/source and many-case validation are available"
        ),
        "allowed_next_node": "n32-general-a-candidate-contract",
    },
    {
        "formula_id": "ordinary-surgery-gate-blocker",
        "status": "blocked executable gate certificate",
        "policy": (
            "n24 must be cited in any closed-value, decorated/twisted, or "
            "exotic-related artifact while it remains blocked"
        ),
        "accepted_commit": N24_ACCEPTED_COMMIT,
        "artifact": N24_ARTIFACT,
    },
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
        "node_id": NODE_ID,
        "claim_level": "policy/gating certificate",
        "ordinary_surgery_gate_dependency": {
            "node_id": n24["node_id"],
            "schema": n24["schema"],
            "status": n24["status"],
            "accepted_as_blocker_at_commit": N24_ACCEPTED_COMMIT,
            "accepted_as_blocker_at_commit_short": N24_ACCEPTED_COMMIT_SHORT,
            "artifact": N24_ARTIFACT,
            "blocked_source_slots": n24["blocked_source_slots"],
            "blocked_reason_ids": n24_reason_ids,
            "closed_4_manifold_claim_allowed": n24[
                "closed_4_manifold_claim_allowed"
            ],
            "claim_supporting_closed_invariant_allowed": n24[
                "claim_supporting_closed_invariant_allowed"
            ],
        },
        "formula_status_ledger": [
            {
                **entry,
            }
            for entry in FORMULA_STATUS_LEDGER
        ],
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
            "downstream_twisted_outputs_must_be_provisional": True,
            "must_cite_n24_for_closed_or_exotic_artifacts": True,
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


def provisional_formula_policy_artifact_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a certificate envelope for the n30 policy ledger."""

    root = Path(repo_root)
    exact_output = provisional_formula_policy_certificate()
    return make_certificate(
        status="pass",
        command=(
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.provisional_formula_policy "
            f"--write {PROVISIONAL_FORMULA_POLICY_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.provisional_formula_policy",
            "--write",
            PROVISIONAL_FORMULA_POLICY_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "n24_artifact": N24_ARTIFACT,
                "n24_accepted_commit": N24_ACCEPTED_COMMIT,
                "formula_status_ledger": exact_output["formula_status_ledger"],
                "rejected_claim_types": exact_output["rejected_claim_types"],
                "downstream_policy_decisions": exact_output[
                    "downstream_policy_decisions"
                ],
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/provisional_formula_policy.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.provisional_formula_policy --write "
            "experiments/results/provisional-formula-policy/n30-policy-certificate.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n30 is a policy/guardrail ledger, not a formula implementation.",
            "n24 remains a blocked executable gate certificate and must be cited downstream.",
        ],
    )


def stable_provisional_formula_policy_json(
    certificate: Mapping[str, object],
) -> str:
    """Serialize an n30 policy certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Emit the n30 provisional formula policy certificate."
    )
    parser.add_argument("--write", type=Path, help="write the n30 certificate JSON")
    args = parser.parse_args()

    certificate = provisional_formula_policy_artifact_certificate()
    encoded = dumps_certificate(certificate)
    if args.write:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(encoded)
    else:
        print(encoded, end="")
    return 0


__all__ = [
    "ALLOWED_ARTIFACT_CLAIM_LEVELS",
    "FORMULA_STATUS_LEDGER",
    "N30_DOWNSTREAM_DECISIONS",
    "N24_ACCEPTED_COMMIT",
    "N24_ARTIFACT",
    "NODE_ID",
    "PROVISIONAL_FORMULA_POLICY_ARTIFACT",
    "PROVISIONAL_FORMULA_POLICY_NOTE",
    "PROVISIONAL_FORMULA_POLICY_SCHEMA",
    "REJECTED_CLAIM_TYPES",
    "REQUIRED_ARTIFACT_FIELDS",
    "claim_policy_decision",
    "provisional_formula_policy_artifact_certificate",
    "provisional_formula_policy_certificate",
    "stable_provisional_formula_policy_json",
]


if __name__ == "__main__":
    raise SystemExit(main())
