"""Source-aware ledger for known ordinary 4D control fixtures.

This n23 layer classifies the current S4, CP2, and S2xS2 toy controls against
the n22 ordinary Kirby-color scaffold.  It records what can be computed as a
local restricted-core experiment and what remains blocked before any closed
ordinary 4D invariant claim.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Final

from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.link_diagram import LINK_DIAGRAM_SCHEMA, LinkDiagram
from twisted_yetter.ordinary_kirby_color import (
    CLAIM_LEVEL,
    HANDLE_SCOPE,
    NORMALIZATION_STATUS,
    SOURCE_STATUS_BY_SLOT,
    load_fixture_certificate,
)

KNOWN_ORDINARY_CONTROL_SCHEMA: Final = (
    "twisted-yetter.known-ordinary-4d-controls-ledger.v1"
)
KNOWN_CONTROL_LEDGER_PATH: Final = (
    legacy_prose_member_ref("wiki/understandings/known-ordinary-4d-controls.org")
)
KNOWN_CONTROL_ARTIFACT_PATH: Final = (
    "experiments/results/known-ordinary-controls/su2-level2-local-convention.json"
)
TOY_FIXTURE_DIR: Final = Path("experiments/inputs/toy-diagrams")
SOURCE_NEEDED_SLOTS: Final = tuple(SOURCE_STATUS_BY_SLOT)
VALUE_STATUS: Final = "computed scaffold"
VALUE_CONVENTION_STATUS: Final = CLAIM_LEVEL
CLOSED_VALUE_SOURCE_STATUS: Final = "SOURCE NEEDED for closed claim"


@dataclass(frozen=True)
class KnownOrdinaryControl:
    case_id: str
    fixture_path: str
    ordinary_control_role: str
    source_needed_expectation: str


KNOWN_ORDINARY_CONTROLS: Final = (
    KnownOrdinaryControl(
        case_id="S4-empty",
        fixture_path="experiments/inputs/toy-diagrams/s4-empty.json",
        ordinary_control_role="empty Kirby diagram ordinary closed-control sanity target",
        source_needed_expectation=(
            "source audit must identify the empty-diagram normalization before "
            "this can be used as an S4 ordinary invariant value"
        ),
    ),
    KnownOrdinaryControl(
        case_id="CP2-plus-one-unknot",
        fixture_path="experiments/inputs/toy-diagrams/cp2-plus-one-framed-unknot.json",
        ordinary_control_role="+1-framed unknot ordinary closed-control sanity target",
        source_needed_expectation=(
            "source audit must identify the +1 framing, signature anomaly, and "
            "global normalization before this can be used as a CP2 value"
        ),
    ),
    KnownOrdinaryControl(
        case_id="S2xS2-hopf",
        fixture_path="experiments/inputs/toy-diagrams/s2x-s2-hopf-zero-framed.json",
        ordinary_control_role="0-framed Hopf-pair ordinary closed-control sanity target",
        source_needed_expectation=(
            "source audit must identify ordinary surgery normalization, "
            "signature/anomaly behavior, and closed-scope treatment before "
            "the local Hopf sector sum can be used as an S2xS2 value"
        ),
    ),
)


def known_ordinary_control_ledger(
    *,
    closed_4_manifold_claim: bool = False,
) -> dict[str, object]:
    """Return the n23 source-aware ordinary-control ledger.

    ``closed_4_manifold_claim`` is intentionally refused because every source
    slot inherited from n21 is still ``SOURCE NEEDED``.
    """

    if closed_4_manifold_claim:
        raise ValueError(
            "closed_4_manifold_claim=True is refused for n23 known ordinary "
            "controls while n21/n22 source slots remain SOURCE NEEDED"
        )

    cases = [_case_payload(control) for control in KNOWN_ORDINARY_CONTROLS]
    return {
        "schema": KNOWN_ORDINARY_CONTROL_SCHEMA,
        "status": "pass",
        "node_id": "n23-known-ordinary-4d-controls",
        "claim_level": "source-aware audit/gate ledger",
        "ordinary_scaffold_claim_level": CLAIM_LEVEL,
        "ordinary_scaffold_handle_scope": HANDLE_SCOPE,
        "ordinary_scaffold_normalization_status": NORMALIZATION_STATUS,
        "closed_4_manifold_claim_allowed": False,
        "source_status_by_slot": dict(SOURCE_STATUS_BY_SLOT),
        "value_status_labels": {
            "computed_scaffold": VALUE_STATUS,
            "local_convention": VALUE_CONVENTION_STATUS,
            "closed_claim_source_status": CLOSED_VALUE_SOURCE_STATUS,
        },
        "cases": cases,
        "n24_blocked_slots": list(SOURCE_NEEDED_SLOTS),
        "unblocks": [
            "n24-ordinary-surgery-gate source-audit planning",
            "deterministic regression checks for n22 no-crossing controls",
        ],
        "does_not_unblock": [
            "claim-supporting ordinary closed 4D invariant values",
            "decorated or twisted formula claims",
            "exotic-pair computation claims",
        ],
        "ledger_note": KNOWN_CONTROL_LEDGER_PATH,
    }


def _case_payload(control: KnownOrdinaryControl) -> dict[str, object]:
    diagram = _load_diagram(control.fixture_path)
    base_payload: dict[str, object] = {
        "case_id": control.case_id,
        "fixture_path": control.fixture_path,
        "diagram_id": diagram.diagram_id,
        "ordinary_control_role": control.ordinary_control_role,
        "component_ids": list(diagram.component_ids),
        "framings": list(diagram.framings),
        "crossing_count": len(diagram.crossings),
        "linking_matrix": [list(row) for row in diagram.linking_matrix()],
        "value_status": VALUE_STATUS,
        "value_convention_status": VALUE_CONVENTION_STATUS,
        "closed_claim_source_status": CLOSED_VALUE_SOURCE_STATUS,
        "source_audited_ordinary_value_status": CLOSED_VALUE_SOURCE_STATUS,
        "source_needed_expectation": control.source_needed_expectation,
        "closed_4_manifold_claim_allowed": False,
    }

    try:
        certificate = load_fixture_certificate(control.fixture_path)
    except NotImplementedError as error:
        return {
            **base_payload,
            "status": "blocked",
            "ordinary_scaffold_status": "blocked",
            "blocked_reason": str(error),
            "n22_can_compute": False,
            "n22_certificate_summary": None,
        }

    return {
        **base_payload,
        "status": VALUE_STATUS,
        "ordinary_scaffold_status": VALUE_STATUS,
        "n22_can_compute": True,
        "n22_certificate_summary": {
            "schema": certificate["schema"],
            "claim_level": certificate["claim_level"],
            "handle_scope": certificate["handle_scope"],
            "normalization_status": certificate["normalization_status"],
            "sector_count": certificate["sector_count"],
            "total_value": certificate["total_value"],
            "closed_4_manifold_claim_allowed": certificate[
                "closed_4_manifold_claim_allowed"
            ],
        },
    }


def _load_diagram(fixture_path: str) -> LinkDiagram:
    payload = json.loads(Path(fixture_path).read_text())
    if payload["schema"] != LINK_DIAGRAM_SCHEMA:
        raise ValueError(f"unsupported link diagram schema: {payload['schema']!r}")
    return LinkDiagram.from_json(payload)


__all__ = [
    "CLOSED_VALUE_SOURCE_STATUS",
    "KNOWN_CONTROL_ARTIFACT_PATH",
    "KNOWN_CONTROL_LEDGER_PATH",
    "KNOWN_ORDINARY_CONTROL_SCHEMA",
    "KNOWN_ORDINARY_CONTROLS",
    "SOURCE_NEEDED_SLOTS",
    "VALUE_CONVENTION_STATUS",
    "VALUE_STATUS",
    "known_ordinary_control_ledger",
]
