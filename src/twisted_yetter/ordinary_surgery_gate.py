"""Executable blocker for the n24 ordinary surgery gate.

This gate intentionally does not promote the n22/n23 ordinary scaffolds to a
closed 4-manifold invariant.  It collects the currently known blockers into a
deterministic certificate so downstream nodes can depend on an auditable
``blocked`` result instead of inferring status from exceptions or prose notes.
"""

from __future__ import annotations

import json
from typing import Final, Mapping

from twisted_yetter.ordinary_control_gate import known_ordinary_control_ledger
from twisted_yetter.ordinary_kirby_color import (
    CLAIM_LEVEL,
    HANDLE_SCOPE,
    NORMALIZATION_STATUS,
    SOURCE_STATUS_BY_SLOT,
)

ORDINARY_SURGERY_GATE_SCHEMA: Final = "twisted-yetter.ordinary-surgery-gate.v1"
ORDINARY_SURGERY_GATE_NOTE: Final = (
    "wiki/understandings/ordinary-surgery-gate.org"
)

SOURCE_BLOCKER_ID: Final = "n21-source-slots-unfilled"
N22_BLOCKER_ID: Final = "n22-local-convention-only"
N23_BLOCKER_ID: Final = "n23-s2xs2-crossing-blocked"
CLOSED_CLAIM_BLOCKER_ID: Final = "closed-claim-refused"

UNSUPPORTED_CLAIMS: Final = (
    "claim-supporting ordinary closed 4D invariant value",
    "decorated formula claim",
    "twisted formula claim",
    "exotic smooth-structure detection claim",
)


def ordinary_surgery_gate_certificate(
    *,
    claim_supporting_closed_invariant: bool = False,
) -> dict[str, object]:
    """Return the deterministic n24 ordinary surgery gate certificate.

    ``claim_supporting_closed_invariant=True`` is refused because this API is
    not a claim-promoter while n21 source slots remain unfilled and n23 still
    blocks the S2xS2 Hopf/crossing control.
    """

    if claim_supporting_closed_invariant:
        raise ValueError(
            "claim_supporting_closed_invariant=True is refused by "
            "n24-ordinary-surgery-gate while source slots, normalization, "
            "closed-scope, and S2xS2 crossing controls remain blocked"
        )

    n23 = known_ordinary_control_ledger()
    n23_cases = {case["case_id"]: case for case in n23["cases"]}
    s2xs2_case = n23_cases["S2xS2-hopf"]
    blocked_source_slots = [
        slot
        for slot, status in SOURCE_STATUS_BY_SLOT.items()
        if status == "SOURCE NEEDED"
    ]

    blocked_reasons = [
        {
            "reason_id": SOURCE_BLOCKER_ID,
            "source_node": "n21-ordinary-kirby-color-source-capture",
            "status": "blocked",
            "claim_boundary": (
                "ordinary surgery cannot support closed 4D claims while "
                "Kirby color, normalization, signature/framing, handle-move, "
                "cancellation, and closed-scope source slots remain SOURCE NEEDED"
            ),
            "blocked_source_slots": blocked_source_slots,
            "source_status_by_slot": dict(SOURCE_STATUS_BY_SLOT),
        },
        {
            "reason_id": N22_BLOCKER_ID,
            "source_node": "n22-ordinary-kirby-color-implementation",
            "status": "blocked",
            "claim_boundary": (
                "n22 is an experimental/local-convention no-dotted "
                "2-handle framed-link scaffold, not a sourced surgery formula"
            ),
            "n22_claim_level": CLAIM_LEVEL,
            "n22_handle_scope": HANDLE_SCOPE,
            "n22_normalization_status": NORMALIZATION_STATUS,
        },
        {
            "reason_id": N23_BLOCKER_ID,
            "source_node": "n23-known-ordinary-4d-controls",
            "status": "blocked",
            "claim_boundary": (
                "the first crossing ordinary 4D control, S2xS2 as a Hopf "
                "fixture, is blocked by the current n22 no-crossing scaffold"
            ),
            "case_id": s2xs2_case["case_id"],
            "fixture_path": s2xs2_case["fixture_path"],
            "crossing_count": s2xs2_case["crossing_count"],
            "linking_matrix": s2xs2_case["linking_matrix"],
            "ordinary_scaffold_status": s2xs2_case["ordinary_scaffold_status"],
            "blocked_reason": s2xs2_case["blocked_reason"],
        },
        {
            "reason_id": CLOSED_CLAIM_BLOCKER_ID,
            "source_node": "n24-ordinary-surgery-gate",
            "status": "blocked",
            "claim_boundary": (
                "the gate returns a blocker certificate and refuses "
                "claim_supporting_closed_invariant=True"
            ),
            "claim_supporting_closed_invariant_allowed": False,
        },
    ]

    return {
        "schema": ORDINARY_SURGERY_GATE_SCHEMA,
        "status": "blocked",
        "node_id": "n24-ordinary-surgery-gate",
        "claim_level": "executable blocker/certificate",
        "ordinary_surgery_claim_allowed": False,
        "claim_supporting_closed_invariant_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "source_status_by_slot": dict(SOURCE_STATUS_BY_SLOT),
        "blocked_source_slots": blocked_source_slots,
        "blocked_reasons": blocked_reasons,
        "upstream": {
            "n21": "wiki/understandings/ordinary-kirby-color-source-capture.org",
            "n22": {
                "claim_level": CLAIM_LEVEL,
                "handle_scope": HANDLE_SCOPE,
                "normalization_status": NORMALIZATION_STATUS,
            },
            "n23": {
                "schema": n23["schema"],
                "status": n23["status"],
                "closed_4_manifold_claim_allowed": n23[
                    "closed_4_manifold_claim_allowed"
                ],
                "s2xs2_status": s2xs2_case["status"],
            },
        },
        "does_not_unblock": list(UNSUPPORTED_CLAIMS),
        "unblocks": [
            "n30-provisional-formula-policy may cite an explicit ordinary-surgery blocker",
        ],
        "ledger_note": ORDINARY_SURGERY_GATE_NOTE,
    }


def stable_ordinary_surgery_gate_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n24 gate certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


__all__ = [
    "CLOSED_CLAIM_BLOCKER_ID",
    "N22_BLOCKER_ID",
    "N23_BLOCKER_ID",
    "ORDINARY_SURGERY_GATE_NOTE",
    "ORDINARY_SURGERY_GATE_SCHEMA",
    "SOURCE_BLOCKER_ID",
    "UNSUPPORTED_CLAIMS",
    "ordinary_surgery_gate_certificate",
    "stable_ordinary_surgery_gate_json",
]
