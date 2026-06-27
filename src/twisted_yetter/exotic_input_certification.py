"""Executable blocked ledger for n70 exotic input certification.

This module certifies only the current repo-local input status for exotic
pairs.  It does not fetch sources, digitize diagrams, compute invariants, or
promote any exotic-detection claim.
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
from twisted_yetter.decorated_kirby_gate import (
    DECORATED_KIRBY_GATE_SCHEMA,
    decorated_kirby_gate_artifact,
    validate_decorated_kirby_gate_artifact,
)
from twisted_yetter.exotic_input_scout import (
    EXOTIC_INPUT_SCOUT_ARTIFACT,
    EXOTIC_INPUT_SCOUT_SCHEMA,
    CANDIDATE_SCOUT_ROWS,
    EXOTIC_INPUT_REFERENCE_STUB,
    EXOTIC_INPUT_SCOUT_ROADMAP as EXOTIC_INPUT_SCOUT_NOTE,
    SOURCE_NEEDED_BLOCKER_ID,
    exotic_input_scout_ledger_artifact,
)
from twisted_yetter.dolgachev_source_capture import (
    DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
    DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
    EXACT_CITATION_BLOCKER_ID,
    SOURCE_CAPTURE_BLOCKER_ID,
    dolgachev_source_capture_ledger_artifact,
)
from twisted_yetter.exotic_diagram_digitization import (
    EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT,
    EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA,
    MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
    MISSING_PAGE_FIGURE_BLOCKER_ID,
    MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
    exotic_diagram_digitization_ledger_artifact,
)
from twisted_yetter.exotic_h2_marking_certification import (
    EXOTIC_H2_MARKING_CERTIFICATION_ARTIFACT,
    EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA,
    MISSING_H2_BASIS_BLOCKER_ID,
    MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
    MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
    MISSING_SOURCE_CITATION_BLOCKER_ID,
    exotic_h2_marking_certification_ledger_artifact,
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
SOURCE_SNAPSHOT_BLOCKER_ID: Final = "source-snapshot-needed"
EXACT_CITATIONS_BLOCKER_ID: Final = "exact-citations-needed"
SOURCE_CAPTURE_UPSTREAM_BLOCKED_ID: Final = "n72-source-capture-blocked"
DIAGRAM_DIGITIZATION_UPSTREAM_BLOCKED_ID: Final = (
    "n73-diagram-digitization-blocked"
)
H2_MARKING_UPSTREAM_BLOCKED_ID: Final = "n74-h2-marking-certification-blocked"
N55_TOY_CLOSED_SUITE_BLOCKER_ID: Final = "n55-toy-closed-suite-blocked"
N24_N50_UPSTREAM_BLOCKED_ID: Final = "n24-n50-upstream-blocked"

BLOCKED_ROUTE_ID: Final = "n80-exotic-computation"
RECOMMENDED_ROUTE_ID: Final = "manual/offline source acquisition, then rerun n72/n73/n74 before n70"

BLOCKED_CLAIMS: Final = (
    "n80 exotic computation route",
    "exotic smooth-structure detection claim",
    "marked distinction claim",
    "cork-canonical distinction claim",
    "unmarked total-function distinction claim",
    "closed 4-manifold invariant claim",
)

def exotic_input_certification_ledger_artifact(
    *,
    scout: Mapping[str, object] | None = None,
    source_capture: Mapping[str, object] | None = None,
    diagram_digitization: Mapping[str, object] | None = None,
    h2_marking: Mapping[str, object] | None = None,
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

    n65 = exotic_input_scout_ledger_artifact() if scout is None else dict(scout)
    n72 = (
        dolgachev_source_capture_ledger_artifact(scout=n65)
        if source_capture is None
        else dict(source_capture)
    )
    n73 = (
        exotic_diagram_digitization_ledger_artifact(source_capture=n72)
        if diagram_digitization is None
        else dict(diagram_digitization)
    )
    n74 = (
        exotic_h2_marking_certification_ledger_artifact(
            diagram_digitization=n73
        )
        if h2_marking is None
        else dict(h2_marking)
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
        SOURCE_SNAPSHOT_BLOCKER_ID,
        EXACT_CITATIONS_BLOCKER_ID,
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
        SOURCE_CAPTURE_UPSTREAM_BLOCKED_ID,
        DIAGRAM_DIGITIZATION_UPSTREAM_BLOCKED_ID,
        H2_MARKING_UPSTREAM_BLOCKED_ID,
        N55_TOY_CLOSED_SUITE_BLOCKER_ID,
        N24_N50_UPSTREAM_BLOCKED_ID,
    ]

    artifact: dict[str, object] = {
        "schema": EXOTIC_INPUT_CERTIFICATION_SCHEMA,
        "status": "blocked",
        "source_status": "source-needed",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "current_decision": (
            "Consumes n65 scout, n72 source capture, n73 diagram "
            "digitization, n74 H2 marking certification, and n24/n50/n55 "
            "control gates. All relevant upstream inputs are blocked or "
            "source-needed, so n70 certifies no exotic input."
        ),
        "upstream_nodes": [
            "n24-ordinary-surgery-gate",
            "n50-decorated-kirby-move-gate",
            "n55-toy-closed-suite",
            "n65-exotic-input-scout",
            "n72-dolgachev-source-capture",
            "n73-exotic-diagram-digitization",
            "n74-exotic-h2-marking-certification",
        ],
        "upstream_artifacts": {
            "n65_exotic_input_scout": EXOTIC_INPUT_SCOUT_ARTIFACT,
            "n72_dolgachev_source_capture": DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
            "n73_exotic_diagram_digitization": EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT,
            "n74_exotic_h2_marking_certification": EXOTIC_H2_MARKING_CERTIFICATION_ARTIFACT,
        },
        "input_notes": {
            "n65_exotic_input_scout": EXOTIC_INPUT_SCOUT_NOTE,
            "candidate_reference_stubs": EXOTIC_INPUT_REFERENCE_STUB,
        },
        "input_schemas": {
            "exotic_input_scout": n65.get("schema"),
            "dolgachev_source_capture": n72.get("schema"),
            "exotic_diagram_digitization": n73.get("schema"),
            "exotic_h2_marking_certification": n74.get("schema"),
            "ordinary_surgery_gate": n24.get("schema"),
            "decorated_kirby_gate": n50.get("schema"),
            "toy_closed_suite": n55.get("schema"),
        },
        "input_statuses": {
            "exotic_input_scout": n65.get("status"),
            "dolgachev_source_capture": n72.get("status"),
            "dolgachev_source_status": n72.get("source_status"),
            "exotic_diagram_digitization": n73.get("status"),
            "exotic_h2_marking_certification": n74.get("status"),
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
        "certified_input_count": 0,
        "certified_input_records": [],
        "selected_computation_target": None,
        "blocker_reason_ids": blocker_reason_ids,
        "dependency_statuses": _dependency_statuses(
            n65=n65, n72=n72, n73=n73, n74=n74, n24=n24, n50=n50, n55=n55
        ),
        "pass_conditions": _pass_conditions(),
        "blockers": _global_blockers(
            n65=n65, n72=n72, n73=n73, n74=n74, n24=n24, n50=n50, n55=n55
        ),
        "route_decision": {
            "n80-exotic-computation": "blocked",
            "reason_id": "n70-blocked-no-certified-input",
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
            "this is an executable blocked ledger, not an exotic input "
            "pass and not a twisted Yetter computation"
        ),
        "ledger_note": EXOTIC_INPUT_CERTIFICATION_NOTE,
        "artifact_path": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_exotic_input_certification_ledger_artifact(
        artifact
    )
    return artifact


def exotic_input_certification_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible certificate envelope for the n70 ledger."""

    root = Path(repo_root)
    n65 = exotic_input_scout_ledger_artifact()
    n72 = dolgachev_source_capture_ledger_artifact(scout=n65)
    n73 = exotic_diagram_digitization_ledger_artifact(source_capture=n72)
    n74 = exotic_h2_marking_certification_ledger_artifact(
        diagram_digitization=n73
    )
    exact_output = exotic_input_certification_ledger_artifact(
        scout=n65,
        source_capture=n72,
        diagram_digitization=n73,
        h2_marking=n74,
    )
    return make_certificate(
        status="fail",
        command=(
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.exotic_input_certification --write "
            f"{EXOTIC_INPUT_CERTIFICATION_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.exotic_input_certification",
            "--write",
            EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "upstream_schemas": exact_output.get("input_schemas"),
                "upstream_statuses": exact_output.get("input_statuses"),
                "certified_input_count": 0,
                "n80_route_allowed": False,
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/exotic_input_certification.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.exotic_input_certification --write "
            "experiments/inputs/exotic-pairs/n70-exotic-input-certification.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "No exotic pair input is certified.",
            "n65 is only a scout ledger; n72 is source-needed; n73 and n74 are blocked.",
            "n80 remains blocked and no invariant computation was run.",
        ],
    )


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
        "dependency_statuses",
        "pass_conditions",
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
            SOURCE_SNAPSHOT_BLOCKER_ID,
            EXACT_CITATIONS_BLOCKER_ID,
            MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
            MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
            SOURCE_CAPTURE_UPSTREAM_BLOCKED_ID,
            DIAGRAM_DIGITIZATION_UPSTREAM_BLOCKED_ID,
            H2_MARKING_UPSTREAM_BLOCKED_ID,
            N55_TOY_CLOSED_SUITE_BLOCKER_ID,
            N24_N50_UPSTREAM_BLOCKED_ID,
        }
    )
    input_schemas = artifact.get("input_schemas", {})
    input_schemas_ok = isinstance(input_schemas, Mapping) and input_schemas == {
        "exotic_input_scout": EXOTIC_INPUT_SCOUT_SCHEMA,
        "dolgachev_source_capture": DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
        "exotic_diagram_digitization": EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA,
        "exotic_h2_marking_certification": EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA,
        "ordinary_surgery_gate": ORDINARY_SURGERY_GATE_SCHEMA,
        "decorated_kirby_gate": DECORATED_KIRBY_GATE_SCHEMA,
        "toy_closed_suite": TOY_CLOSED_SUITE_SCHEMA,
    }
    dependency_statuses = artifact.get("dependency_statuses", [])
    dependency_statuses_ok = (
        isinstance(dependency_statuses, list)
        and {
            item.get("node_id")
            for item in dependency_statuses
            if isinstance(item, dict)
        }
        == {
            "n65-exotic-input-scout",
            "n72-dolgachev-source-capture",
            "n73-exotic-diagram-digitization",
            "n74-exotic-h2-marking-certification",
            "n24-ordinary-surgery-gate",
            "n50-decorated-kirby-move-gate",
            "n55-toy-closed-suite",
        }
    )
    pass_conditions = artifact.get("pass_conditions", [])
    pass_conditions_ok = (
        isinstance(pass_conditions, list)
        and len(pass_conditions) >= 9
        and all(
            isinstance(item, dict)
            and item.get("status") in {"missing", "blocked"}
            for item in pass_conditions
        )
    )
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
            and artifact.get("status") == "blocked"
            and artifact.get("source_status") == "source-needed"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("claim_level") == CLAIM_LEVEL
            and artifact.get("any_candidate_certified") is False
            and artifact.get("certified_input_count") == 0
            and artifact.get("selected_computation_target") is None
            and input_schemas_ok
            and dependency_statuses_ok
            and pass_conditions_ok
            and candidates_ok
            and blockers_ok
            and route_ok
            and blocked_claims_ok
        ),
        "missing_required_fields": missing,
        "input_schemas_ok": input_schemas_ok,
        "dependency_statuses_ok": dependency_statuses_ok,
        "pass_conditions_ok": pass_conditions_ok,
        "candidate_list_ok": candidates_ok,
        "blockers_ok": blockers_ok,
        "route_ok": route_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "scope": "blocked exotic input ledger only; no certified input and no n80 route",
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
        "status": "blocked",
        "source_status": candidate["source_status"],
        "certified_for_n70": False,
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
    n65: Mapping[str, object],
    n72: Mapping[str, object],
    n73: Mapping[str, object],
    n74: Mapping[str, object],
    n24: Mapping[str, object],
    n50: Mapping[str, object],
    n55: Mapping[str, object],
) -> list[dict[str, object]]:
    return [
        {
            "reason_id": SOURCE_SNAPSHOT_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n72-dolgachev-source-capture",
            "observed": n72.get("source_status", "missing"),
            "required": "local source/PDF/web snapshot with content hash or canonical locator",
            "upstream_blocker_reason_ids": [
                SOURCE_NEEDED_BLOCKER_ID,
                SOURCE_CAPTURE_BLOCKER_ID,
                MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
            ],
        },
        {
            "reason_id": EXACT_CITATIONS_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n72-dolgachev-source-capture",
            "observed": "no exact page, figure, theorem, proposition, or crop locators",
            "required": "exact citations for source claims, diagrams, handle moves, and comparison claims",
            "upstream_blocker_reason_ids": [
                EXACT_CITATION_BLOCKER_ID,
                MISSING_PAGE_FIGURE_BLOCKER_ID,
            ],
        },
        {
            "reason_id": MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n73-exotic-diagram-digitization",
            "observed": n73.get("machine_readable_diagrams", []),
            "required": (
                "machine-readable PD code, braid word, or equivalent "
                "Kirby/handle data for both sides of one selected exotic pair"
            ),
            "upstream_blocker_reason_ids": [
                MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
                MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
            ],
            "claim_boundary": (
                "human-readable candidate notes cannot serve as n80 input"
            ),
        },
        {
            "reason_id": MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n65-exotic-input-scout and n72-dolgachev-source-capture",
            "observed": {
                "n65_status": n65.get("status"),
                "n72_source_status": n72.get("source_status"),
            },
            "required": (
                "captured source records with exact page/figure/theorem ids "
                "and content hash or canonical locator"
            ),
            "reference_stub": EXOTIC_INPUT_REFERENCE_STUB,
        },
        {
            "reason_id": MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n74-exotic-h2-marking-certification",
            "observed": {
                "status": n74.get("status"),
                "comparison_level_status": n74.get("comparison_level_status"),
                "certified_h2_marking_claim_allowed": n74.get(
                    "certified_h2_marking_claim_allowed"
                ),
            },
            "required": (
                "explicit comparison level plus integer H2 identification or "
                "basis-change matrix"
            ),
            "upstream_blocker_reason_ids": [
                MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
                MISSING_SOURCE_CITATION_BLOCKER_ID,
                MISSING_H2_BASIS_BLOCKER_ID,
                MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
            ],
            "claim_boundary": (
                "marked, cork-canonical, orbit, multiset, and unmarked "
                "distinction claims are all refused"
            ),
        },
        {
            "reason_id": SOURCE_CAPTURE_UPSTREAM_BLOCKED_ID,
            "status": "blocked",
            "source_node": "n72-dolgachev-source-capture",
            "observed": {
                "status": n72.get("status"),
                "source_status": n72.get("source_status"),
                "n73_ready": n72.get("n73_ready"),
            },
            "required": "n72 source capture pass with exact source snapshot and citation slots filled",
        },
        {
            "reason_id": DIAGRAM_DIGITIZATION_UPSTREAM_BLOCKED_ID,
            "status": "blocked",
            "source_node": "n73-exotic-diagram-digitization",
            "observed": {
                "status": n73.get("status"),
                "n74_ready": n73.get("n74_marking_certification_ready"),
                "machine_readable_diagrams": n73.get(
                    "machine_readable_diagrams", []
                ),
            },
            "required": "n73 pass with both sides encoded and diagram sanity targets recorded",
        },
        {
            "reason_id": H2_MARKING_UPSTREAM_BLOCKED_ID,
            "status": "blocked",
            "source_node": "n74-exotic-h2-marking-certification",
            "observed": {
                "status": n74.get("status"),
                "n70_pass_allowed": n74.get(
                    "n70_exotic_input_certification_pass_allowed"
                ),
                "n80_route_allowed": n74.get(
                    "n80_exotic_computation_route_allowed"
                ),
            },
            "required": "n74 pass with source-backed H2 bases, matrices, lineage, comparison level, and sanity checks",
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


def _dependency_statuses(
    *,
    n65: Mapping[str, object],
    n72: Mapping[str, object],
    n73: Mapping[str, object],
    n74: Mapping[str, object],
    n24: Mapping[str, object],
    n50: Mapping[str, object],
    n55: Mapping[str, object],
) -> list[dict[str, object]]:
    return [
        {
            "node_id": "n65-exotic-input-scout",
            "status": n65.get("status"),
            "effect_on_n70": "candidate inventory only; no candidate certified",
        },
        {
            "node_id": "n72-dolgachev-source-capture",
            "status": n72.get("status"),
            "source_status": n72.get("source_status"),
            "effect_on_n70": "source snapshot and exact citations still missing",
        },
        {
            "node_id": "n73-exotic-diagram-digitization",
            "status": n73.get("status"),
            "n74_ready": n73.get("n74_marking_certification_ready"),
            "effect_on_n70": "machine-readable diagrams for both sides absent",
        },
        {
            "node_id": "n74-exotic-h2-marking-certification",
            "status": n74.get("status"),
            "n70_pass_allowed": n74.get(
                "n70_exotic_input_certification_pass_allowed"
            ),
            "effect_on_n70": "H2/homeomorphism comparison not certified",
        },
        {
            "node_id": "n24-ordinary-surgery-gate",
            "status": n24.get("status"),
            "effect_on_n70": "ordinary closed 4D surgery gate still blocked",
        },
        {
            "node_id": "n50-decorated-kirby-move-gate",
            "status": n50.get("status"),
            "effect_on_n70": "decorated Kirby move gate still blocked",
        },
        {
            "node_id": "n55-toy-closed-suite",
            "status": n55.get("status"),
            "effect_on_n70": "toy closed suite cannot substitute for certified exotic input",
        },
    ]


def _pass_conditions() -> list[dict[str, object]]:
    return [
        {
            "condition_id": "source-snapshot",
            "required": "source reference record with canonical metadata, capture time, locator, and hash",
            "status": "missing",
        },
        {
            "condition_id": "exact-citations",
            "required": "page/figure/theorem/proposition/crop ids for every selected claim and diagram feature",
            "status": "missing",
        },
        {
            "condition_id": "machine-readable-diagrams",
            "required": "both sides encoded as Kirby/link data with component ids, framings, dotted status, orientations, and crossings/PD/braid data",
            "status": "missing",
        },
        {
            "condition_id": "diagram-lineage",
            "required": "component lineage and GL(n,Z) basis changes through handle slides/cancellations",
            "status": "missing",
        },
        {
            "condition_id": "topological-sanity-targets",
            "required": "integer linking/intersection matrices, handle counts, Euler characteristic, signature, rank, determinant, and parity targets",
            "status": "missing",
        },
        {
            "condition_id": "h2-marking",
            "required": "source-backed H2 bases and homeomorphism or marking comparison matrix",
            "status": "missing",
        },
        {
            "condition_id": "claim-level",
            "required": "marked, cork-canonical, orbit, multiset, unmarked, or explicitly inconclusive comparison level",
            "status": "blocked",
        },
        {
            "condition_id": "n24-gate",
            "required": "ordinary surgery gate pass certificate",
            "status": "blocked",
        },
        {
            "condition_id": "n50-gate",
            "required": "decorated Kirby move gate pass certificate",
            "status": "blocked",
        },
        {
            "condition_id": "n55-gate",
            "required": "toy closed suite pass certificate",
            "status": "blocked",
        },
    ]


def _candidate_result_is_valid(candidate: object) -> bool:
    if not isinstance(candidate, dict):
        return False
    required = {
        "candidate_id",
        "scout_rank",
        "status",
        "certified_for_n70",
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
        candidate.get("status") == "blocked"
        and candidate.get("certified_for_n70") is False
        and candidate.get("certified_for_n80") is False
        and isinstance(candidate.get("blocked_reason_ids"), list)
        and bool(candidate.get("blocked_reason_ids"))
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate the n70 exotic input certification blocked ledger."
    )
    parser.add_argument(
        "--write",
        type=Path,
        help="write the certificate JSON to this path",
    )
    args = parser.parse_args()

    certificate = exotic_input_certification_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(output)
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "BLOCKED_CLAIMS",
    "CLAIM_LEVEL",
    "EXOTIC_INPUT_CERTIFICATION_ARTIFACT",
    "EXOTIC_INPUT_CERTIFICATION_NOTE",
    "EXOTIC_INPUT_CERTIFICATION_SCHEMA",
    "MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID",
    "MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID",
    "MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID",
    "SOURCE_SNAPSHOT_BLOCKER_ID",
    "EXACT_CITATIONS_BLOCKER_ID",
    "SOURCE_CAPTURE_UPSTREAM_BLOCKED_ID",
    "DIAGRAM_DIGITIZATION_UPSTREAM_BLOCKED_ID",
    "H2_MARKING_UPSTREAM_BLOCKED_ID",
    "N24_N50_UPSTREAM_BLOCKED_ID",
    "N55_TOY_CLOSED_SUITE_BLOCKER_ID",
    "NODE_ID",
    "exotic_input_certification_certificate",
    "exotic_input_certification_ledger_artifact",
    "stable_exotic_input_certification_ledger_json",
    "validate_exotic_input_certification_ledger_artifact",
]
