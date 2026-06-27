"""Executable blocked ledger for n70 exotic input certification.

This module certifies only the current repo-local input status for exotic
pairs.  It does not fetch sources, digitize diagrams, compute invariants, or
promote any exotic-detection claim.
"""

from __future__ import annotations

import json
from typing import Final, Mapping

from twisted_yetter.decorated_kirby_gate import (
    DECORATED_KIRBY_GATE_SCHEMA,
    decorated_kirby_gate_artifact,
    validate_decorated_kirby_gate_artifact,
)
from twisted_yetter.ordinary_surgery_gate import (
    ORDINARY_SURGERY_GATE_SCHEMA,
    ordinary_surgery_gate_certificate,
)
from twisted_yetter.toy_closed_suite import (
    TOY_CLOSED_SUITE_SCHEMA,
    toy_closed_suite_ledger_artifact,
    validate_toy_closed_suite_ledger_artifact,
)

EXOTIC_INPUT_CERTIFICATION_SCHEMA: Final = (
    "twisted-yetter.exotic-input-certification.v1"
)
EXOTIC_INPUT_CERTIFICATION_NOTE: Final = (
    "wiki/understandings/exotic-input-certification.org"
)
EXOTIC_INPUT_SCOUT_NOTE: Final = "wiki/roadmaps/exotic-input-scout.org"
EXOTIC_INPUT_REFERENCE_STUB: Final = (
    "wiki/references/exotic-input-candidates-2026-06-26.org"
)
EXOTIC_INPUT_CERTIFICATION_ARTIFACT: Final = (
    "experiments/inputs/exotic-pairs/n70-exotic-input-certification.json"
)

NODE_ID: Final = "n70-exotic-input-certification"
CLAIM_LEVEL: Final = "executable gate/blocked ledger"

MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID: Final = (
    "missing-machine-readable-exotic-kirby-diagrams"
)
MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID: Final = "missing-source-page-capture"
MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID: Final = (
    "missing-h2-homeomorphism-marking-certificate"
)
N55_TOY_CLOSED_SUITE_BLOCKER_ID: Final = "n55-toy-closed-suite-blocked"
N24_N50_UPSTREAM_BLOCKED_ID: Final = "n24-n50-upstream-blocked"

BLOCKED_ROUTE_ID: Final = "n80-exotic-computation"
RECOMMENDED_ROUTE_ID: Final = "n72-dolgachev-source-capture"

BLOCKED_CLAIMS: Final = (
    "n80 exotic computation route",
    "exotic smooth-structure detection claim",
    "marked distinction claim",
    "cork-canonical distinction claim",
    "unmarked total-function distinction claim",
    "closed 4-manifold invariant claim",
)

CANDIDATE_SCOUT_ROWS: Final = (
    {
        "candidate_id": "dolgachev-e1-23-vs-e1",
        "scout_rank": 1,
        "scout_status": "promising input path; SOURCE NEEDED",
        "certification_status": "not-certified",
        "comparison_level": "not-certified",
        "reference_stub_ids": ["akbulut-dolgachev-surface"],
        "missing_artifacts": [
            "captured source reference with hash or canonical locator",
            "exact source figure/page ids",
            "machine-readable Kirby or handle data for both sides",
            "component ids, framings, dotted status, orientation, and lineage",
            "integer linking matrices and intersection-form sanity checks",
            "explicit H2 comparison or cork-canonical marking matrix",
        ],
    },
    {
        "candidate_id": "r8-vs-cp2-8bar",
        "scout_rank": 2,
        "scout_status": "promising fallback; SOURCE NEEDED",
        "certification_status": "not-certified",
        "comparison_level": "not-certified",
        "reference_stub_ids": ["wakamaki-r8-cork"],
        "missing_artifacts": [
            "captured source reference with hash or canonical locator",
            "exact source figure/page ids",
            "machine-readable diagrams for exotic and standard sides",
            "cork-twist and stabilization source separation",
            "explicit H2 comparison data",
        ],
    },
    {
        "candidate_id": "akhmedov-park-cp2-2bar",
        "scout_rank": 3,
        "scout_status": "possible fallback; SOURCE NEEDED",
        "certification_status": "not-certified",
        "comparison_level": "not-certified",
        "reference_stub_ids": ["akbulut-akhmedov-park"],
        "missing_artifacts": [
            "captured source reference",
            "usable diagram references",
            "machine-readable input",
            "homeomorphism or marking comparison route",
        ],
    },
    {
        "candidate_id": "yasui-style-traces",
        "scout_rank": 4,
        "scout_status": "relative or boundary-sensitive fallback; SOURCE NEEDED",
        "certification_status": "not-certified-for-closed-pair-computation",
        "comparison_level": "not-selected",
        "reference_stub_ids": ["yasui-corks-knot-concordance"],
        "missing_artifacts": [
            "selected closed-pair construction or explicit relative-computation pivot",
            "machine-readable diagrams",
            "comparison-level declaration",
        ],
    },
)


def exotic_input_certification_ledger_artifact(
    *,
    ordinary_gate: Mapping[str, object] | None = None,
    decorated_gate: Mapping[str, object] | None = None,
    toy_closed_suite: Mapping[str, object] | None = None,
    claim_n80_route: bool = False,
    claim_exotic_detection: bool = False,
    claim_marked_distinction: bool = False,
    claim_closed_invariant: bool = False,
) -> dict[str, object]:
    """Return the deterministic n70 data-blocked ledger.

    Claim flags are explicit refusal checks.  n70 is an input-certification
    gate, not an exotic computation node.
    """

    if (
        claim_n80_route
        or claim_exotic_detection
        or claim_marked_distinction
        or claim_closed_invariant
    ):
        raise ValueError(
            "n70-exotic-input-certification is data-blocked and refuses n80 "
            "routing, exotic detection, marked distinction, and closed "
            "invariant claims"
        )

    n24 = (
        ordinary_surgery_gate_certificate()
        if ordinary_gate is None
        else dict(ordinary_gate)
    )
    n50 = (
        decorated_kirby_gate_artifact()
        if decorated_gate is None
        else dict(decorated_gate)
    )
    n55 = (
        toy_closed_suite_ledger_artifact()
        if toy_closed_suite is None
        else dict(toy_closed_suite)
    )

    candidate_results = [
        _candidate_result(candidate) for candidate in CANDIDATE_SCOUT_ROWS
    ]
    blocker_reason_ids = [
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
        N55_TOY_CLOSED_SUITE_BLOCKER_ID,
        N24_N50_UPSTREAM_BLOCKED_ID,
    ]

    artifact: dict[str, object] = {
        "schema": EXOTIC_INPUT_CERTIFICATION_SCHEMA,
        "status": "data-blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "Consumes existing n65 scout notes plus n24/n50/n55 blocked "
            "ledgers; no network search, source capture, diagram "
            "digitization, or exotic invariant computation is performed"
        ),
        "upstream_nodes": [
            "n24-ordinary-surgery-gate",
            "n50-decorated-kirby-move-gate",
            "n55-toy-closed-suite",
            "n65-exotic-input-scout",
        ],
        "input_notes": {
            "n65_exotic_input_scout": EXOTIC_INPUT_SCOUT_NOTE,
            "candidate_reference_stubs": EXOTIC_INPUT_REFERENCE_STUB,
        },
        "input_schemas": {
            "ordinary_surgery_gate": n24.get("schema"),
            "decorated_kirby_gate": n50.get("schema"),
            "toy_closed_suite": n55.get("schema"),
        },
        "input_statuses": {
            "ordinary_surgery_gate": n24.get("status"),
            "decorated_kirby_gate": n50.get("status"),
            "toy_closed_suite": n55.get("status"),
        },
        "input_validations": {
            "decorated_kirby_gate": validate_decorated_kirby_gate_artifact(n50),
            "toy_closed_suite": validate_toy_closed_suite_ledger_artifact(n55),
        },
        "candidate_count": len(candidate_results),
        "candidate_results": candidate_results,
        "any_candidate_certified": False,
        "selected_computation_target": None,
        "blocker_reason_ids": blocker_reason_ids,
        "blockers": _global_blockers(n24=n24, n50=n50, n55=n55),
        "route_decision": {
            "n80-exotic-computation": "blocked",
            "reason_id": "n70-data-blocked",
            "recommended_next_route": RECOMMENDED_ROUTE_ID,
            "claim_boundary": (
                "n70 has no certified exotic pair input, so n80 cannot be "
                "entered and no exotic calculation target is selected"
            ),
        },
        "n80_exotic_computation_route_allowed": False,
        "exotic_detection_claim_allowed": False,
        "marked_distinction_claim_allowed": False,
        "cork_canonical_distinction_claim_allowed": False,
        "unmarked_total_function_distinction_claim_allowed": False,
        "closed_4_manifold_invariant_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "required_unblock_artifacts": [
            "source reference records with canonical metadata, locator, capture time, and hash",
            "exact page, figure, theorem, or proposition ids for all selected input claims",
            "machine-readable Kirby or handle data for both sides of one selected exotic pair",
            "component ids, framings, dotted status, orientation, and lineage for both sides",
            "integer linking matrices and topological sanity checks for both sides",
            "H2/homeomorphism comparison or marking certificate with basis-change matrices",
            "n24 ordinary surgery gate pass certificate",
            "n50 decorated Kirby move gate pass certificate",
            "n55 toy closed suite pass certificate",
        ],
        "claim_boundary": (
            "this is an executable data-blocked ledger, not an exotic input "
            "pass and not a twisted Yetter computation"
        ),
        "ledger_note": EXOTIC_INPUT_CERTIFICATION_NOTE,
        "artifact_path": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_exotic_input_certification_ledger_artifact(
        artifact
    )
    return artifact


def validate_exotic_input_certification_ledger_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n70 ledger shape without certifying any exotic input."""

    required = {
        "schema",
        "status",
        "node_id",
        "claim_level",
        "input_schemas",
        "input_statuses",
        "candidate_results",
        "blocker_reason_ids",
        "blockers",
        "route_decision",
        "blocked_claims",
        "required_unblock_artifacts",
    }
    missing = sorted(field for field in required if field not in artifact)
    blockers = artifact.get("blocker_reason_ids", [])
    blockers_ok = (
        isinstance(blockers, list)
        and blockers
        and set(blockers)
        >= {
            MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
            MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
            N55_TOY_CLOSED_SUITE_BLOCKER_ID,
            N24_N50_UPSTREAM_BLOCKED_ID,
        }
    )
    input_schemas = artifact.get("input_schemas", {})
    input_schemas_ok = isinstance(input_schemas, Mapping) and input_schemas == {
        "ordinary_surgery_gate": ORDINARY_SURGERY_GATE_SCHEMA,
        "decorated_kirby_gate": DECORATED_KIRBY_GATE_SCHEMA,
        "toy_closed_suite": TOY_CLOSED_SUITE_SCHEMA,
    }
    candidates = artifact.get("candidate_results", [])
    candidates_ok = isinstance(candidates, list) and all(
        _candidate_result_is_valid(candidate) for candidate in candidates
    )
    route_decision = artifact.get("route_decision", {})
    route_ok = (
        isinstance(route_decision, Mapping)
        and route_decision.get(BLOCKED_ROUTE_ID) == "blocked"
        and artifact.get("n80_exotic_computation_route_allowed") is False
    )
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "n80_exotic_computation_route_allowed",
            "exotic_detection_claim_allowed",
            "marked_distinction_claim_allowed",
            "cork_canonical_distinction_claim_allowed",
            "unmarked_total_function_distinction_claim_allowed",
            "closed_4_manifold_invariant_claim_allowed",
        )
    )

    return {
        "valid": (
            not missing
            and artifact.get("schema") == EXOTIC_INPUT_CERTIFICATION_SCHEMA
            and artifact.get("status") == "data-blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("claim_level") == CLAIM_LEVEL
            and input_schemas_ok
            and candidates_ok
            and blockers_ok
            and route_ok
            and blocked_claims_ok
        ),
        "missing_required_fields": missing,
        "input_schemas_ok": input_schemas_ok,
        "candidate_list_ok": candidates_ok,
        "blockers_ok": blockers_ok,
        "route_ok": route_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "scope": "data-blocked exotic input ledger only; no n80 computation route",
    }


def stable_exotic_input_certification_ledger_json(
    artifact: Mapping[str, object],
) -> str:
    """Serialize an n70 ledger artifact deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def _candidate_result(candidate: Mapping[str, object]) -> dict[str, object]:
    missing_artifacts = [
        str(item) for item in candidate.get("missing_artifacts", [])
    ]
    blocked_reason_ids = []
    if any("machine-readable" in item for item in missing_artifacts):
        blocked_reason_ids.append(MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID)
    if any(
        "source" in item or "page" in item or "figure" in item
        for item in missing_artifacts
    ):
        blocked_reason_ids.append(MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID)
    if any(
        "H2" in item or "marking" in item or "homeomorphism" in item
        for item in missing_artifacts
    ):
        blocked_reason_ids.append(MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID)

    return {
        "candidate_id": candidate["candidate_id"],
        "scout_rank": candidate["scout_rank"],
        "scout_status": candidate["scout_status"],
        "status": "data-blocked",
        "certified_for_n80": False,
        "certification_status": candidate["certification_status"],
        "comparison_level": candidate["comparison_level"],
        "reference_stub_ids": candidate["reference_stub_ids"],
        "missing_artifacts": missing_artifacts,
        "blocked_reason_ids": blocked_reason_ids,
        "claim_boundary": (
            "candidate remains inventory/scout evidence only and cannot be "
            "used as machine-readable exotic input"
        ),
    }


def _global_blockers(
    *,
    n24: Mapping[str, object],
    n50: Mapping[str, object],
    n55: Mapping[str, object],
) -> list[dict[str, object]]:
    return [
        {
            "reason_id": MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n65-exotic-input-scout",
            "observed": "no certified exotic-pair machine-readable diagrams",
            "required": (
                "machine-readable PD code, braid word, or equivalent "
                "Kirby/handle data for both sides of one selected exotic pair"
            ),
            "claim_boundary": (
                "human-readable candidate notes cannot serve as n80 input"
            ),
        },
        {
            "reason_id": MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n65-exotic-input-scout",
            "observed": "reference stubs only",
            "required": (
                "captured source records with exact page/figure/theorem ids "
                "and content hash or canonical locator"
            ),
            "reference_stub": EXOTIC_INPUT_REFERENCE_STUB,
        },
        {
            "reason_id": MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n70-exotic-input-certification",
            "observed": "no H2/homeomorphism marking certificate",
            "required": (
                "explicit comparison level plus integer H2 identification or "
                "basis-change matrix"
            ),
            "claim_boundary": (
                "marked, cork-canonical, orbit, multiset, and unmarked "
                "distinction claims are all refused"
            ),
        },
        {
            "reason_id": N55_TOY_CLOSED_SUITE_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n55-toy-closed-suite",
            "observed": n55.get("status", "missing"),
            "required": "pass",
            "upstream_schema": n55.get("schema"),
            "upstream_blocker_reason_ids": n55.get(
                "global_blocker_reason_ids", []
            ),
            "claim_boundary": (
                "toy closed metadata cannot be promoted to exotic closed "
                "4-manifold invariant evidence"
            ),
        },
        {
            "reason_id": N24_N50_UPSTREAM_BLOCKED_ID,
            "status": "blocked",
            "source_node": "n24-ordinary-surgery-gate and n50-decorated-kirby-move-gate",
            "observed": {
                "n24": n24.get("status", "missing"),
                "n50": n50.get("status", "missing"),
            },
            "required": {"n24": "pass", "n50": "pass"},
            "upstream_schemas": {
                "n24": n24.get("schema"),
                "n50": n50.get("schema"),
            },
            "claim_boundary": (
                "n70 inherits the ordinary surgery and decorated Kirby move "
                "gate blockers before any closed exotic computation can run"
            ),
        },
    ]


def _candidate_result_is_valid(candidate: object) -> bool:
    if not isinstance(candidate, dict):
        return False
    required = {
        "candidate_id",
        "scout_rank",
        "status",
        "certified_for_n80",
        "certification_status",
        "comparison_level",
        "reference_stub_ids",
        "missing_artifacts",
        "blocked_reason_ids",
    }
    if any(field not in candidate for field in required):
        return False
    return (
        candidate.get("status") == "data-blocked"
        and candidate.get("certified_for_n80") is False
        and isinstance(candidate.get("blocked_reason_ids"), list)
        and bool(candidate.get("blocked_reason_ids"))
    )


__all__ = [
    "BLOCKED_CLAIMS",
    "CLAIM_LEVEL",
    "EXOTIC_INPUT_CERTIFICATION_ARTIFACT",
    "EXOTIC_INPUT_CERTIFICATION_NOTE",
    "EXOTIC_INPUT_CERTIFICATION_SCHEMA",
    "MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID",
    "MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID",
    "MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID",
    "N24_N50_UPSTREAM_BLOCKED_ID",
    "N55_TOY_CLOSED_SUITE_BLOCKER_ID",
    "NODE_ID",
    "exotic_input_certification_ledger_artifact",
    "stable_exotic_input_certification_ledger_json",
    "validate_exotic_input_certification_ledger_artifact",
]
