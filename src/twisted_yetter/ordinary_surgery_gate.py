"""Executable blocker for the n24 ordinary surgery gate.

This gate intentionally does not promote the n22/n23 ordinary scaffolds to a
closed 4-manifold invariant.  It collects the currently known blockers into a
deterministic certificate so downstream nodes can depend on an auditable
``blocked`` result instead of inferring status from exceptions or prose notes.
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
from twisted_yetter.ordinary_control_gate import known_ordinary_control_ledger
from twisted_yetter.ordinary_kirby_color import (
    CLAIM_LEVEL,
    HANDLE_SCOPE,
    NORMALIZATION_STATUS,
    SOURCE_STATUS_BY_SLOT,
)

ORDINARY_SURGERY_GATE_SCHEMA: Final = "twisted-yetter.ordinary-surgery-gate.v1"
ORDINARY_SURGERY_GATE_NOTE: Final = (
    legacy_prose_member_ref("wiki/understandings/ordinary-surgery-gate.org")
)
ORDINARY_SURGERY_GATE_ARTIFACT: Final = (
    "experiments/results/ordinary-surgery-gate/n24-blocker-certificate.json"
)
NODE_ID: Final = "n24-ordinary-surgery-gate"

SOURCE_BLOCKER_ID: Final = "n21-source-slots-unfilled"
N22_BLOCKER_ID: Final = "n22-local-convention-only"
N23_BLOCKER_ID: Final = "n23-ordinary-controls-local-only"
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
    not a claim-promoter while n21 source slots remain unfilled and n23
    ordinary controls remain local-convention regression data only.
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
                "known ordinary controls, including S2xS2 as a Hopf fixture, "
                "are local-convention regression data only until ordinary "
                "surgery source and normalization slots are filled"
            ),
            "case_id": s2xs2_case["case_id"],
            "fixture_path": s2xs2_case["fixture_path"],
            "crossing_count": s2xs2_case["crossing_count"],
            "linking_matrix": s2xs2_case["linking_matrix"],
            "ordinary_scaffold_status": s2xs2_case["ordinary_scaffold_status"],
            "n22_can_compute": s2xs2_case["n22_can_compute"],
            "n22_certificate_summary": s2xs2_case["n22_certificate_summary"],
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
        "node_id": NODE_ID,
        "claim_level": "executable blocker/certificate",
        "ordinary_surgery_claim_allowed": False,
        "claim_supporting_closed_invariant_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "source_status_by_slot": dict(SOURCE_STATUS_BY_SLOT),
        "blocked_source_slots": blocked_source_slots,
        "blocked_reasons": blocked_reasons,
        "upstream": {
            "n21": legacy_prose_member_ref(
                "wiki/understandings/ordinary-kirby-color-source-capture.org"
            ),
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


def ordinary_surgery_gate_artifact_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a certificate envelope for the current n24 blocker gate."""

    root = Path(repo_root)
    exact_output = ordinary_surgery_gate_certificate()
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.ordinary_surgery_gate "
            f"--write {ORDINARY_SURGERY_GATE_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.ordinary_surgery_gate",
            "--write",
            ORDINARY_SURGERY_GATE_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "blocked_source_slots": exact_output["blocked_source_slots"],
                "blocked_reason_ids": [
                    reason["reason_id"]
                    for reason in exact_output["blocked_reasons"]
                    if isinstance(reason, Mapping) and "reason_id" in reason
                ],
                "upstream": exact_output["upstream"],
                "closed_4_manifold_claim_allowed": exact_output[
                    "closed_4_manifold_claim_allowed"
                ],
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/ordinary_surgery_gate.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.ordinary_surgery_gate "
            "--write experiments/results/ordinary-surgery-gate/n24-blocker-certificate.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n24 is intentionally blocked; this certificate is the gate output.",
            "closed_4_manifold_claim and claim_supporting_closed_invariant remain refused.",
        ],
    )


def stable_ordinary_surgery_gate_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n24 gate certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the n24 certificate JSON")
    args = parser.parse_args()

    certificate = ordinary_surgery_gate_artifact_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is None:
        print(output, end="")
        return
    args.write.parent.mkdir(parents=True, exist_ok=True)
    args.write.write_text(output, encoding="utf-8")


if __name__ == "__main__":
    _main()


__all__ = [
    "CLOSED_CLAIM_BLOCKER_ID",
    "N22_BLOCKER_ID",
    "N23_BLOCKER_ID",
    "NODE_ID",
    "ORDINARY_SURGERY_GATE_ARTIFACT",
    "ORDINARY_SURGERY_GATE_NOTE",
    "ORDINARY_SURGERY_GATE_SCHEMA",
    "SOURCE_BLOCKER_ID",
    "UNSUPPORTED_CLAIMS",
    "ordinary_surgery_gate_artifact_certificate",
    "ordinary_surgery_gate_certificate",
    "stable_ordinary_surgery_gate_json",
]
