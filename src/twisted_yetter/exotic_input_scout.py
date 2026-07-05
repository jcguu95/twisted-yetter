"""Executable scouting ledger for n65 exotic input candidates.

This module records repo-local candidate metadata and data requirements only.
It does not fetch sources, digitize diagrams, certify an H2 marking, route to
n80, or promote any exotic-detection claim.
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
)
from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.ordinary_surgery_gate import (
    ORDINARY_SURGERY_GATE_SCHEMA,
    ordinary_surgery_gate_certificate,
)
from twisted_yetter.toy_closed_suite import (
    TOY_CLOSED_SUITE_SCHEMA,
    toy_closed_suite_ledger_artifact,
    validate_toy_closed_suite_ledger_artifact,
)

EXOTIC_INPUT_SCOUT_SCHEMA: Final = "twisted-yetter.exotic-input-scout.v1"
EXOTIC_INPUT_SCOUT_NOTE: Final = legacy_prose_member_ref(
    "wiki/understandings/exotic-input-scout.org"
)
EXOTIC_INPUT_SCOUT_ROADMAP: Final = legacy_prose_member_ref(
    "wiki/roadmaps/exotic-input-scout.org"
)
EXOTIC_INPUT_REFERENCE_STUB: Final = (
    legacy_prose_member_ref("wiki/references/exotic-input-candidates-2026-06-26.org")
)
EXOTIC_INPUT_SCOUT_ARTIFACT: Final = (
    "experiments/results/exotic-input-scout/n65-exotic-input-scout.json"
)

NODE_ID: Final = "n65-exotic-input-scout"
CLAIM_LEVEL: Final = "candidate inventory/scouting ledger"

SOURCE_NEEDED_BLOCKER_ID: Final = "source-needed-for-candidate-claims"
MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID: Final = (
    "missing-machine-readable-exotic-kirby-diagrams"
)
MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID: Final = (
    "missing-h2-homeomorphism-marking-certificate"
)
N24_N50_N55_UPSTREAM_BLOCKED_ID: Final = "n24-n50-n55-upstream-blocked"

RECOMMENDED_ROUTE_ID: Final = "n72-dolgachev-source-capture"

BLOCKED_CLAIMS: Final = (
    "certified exotic input claim",
    "n70 exotic input certification pass",
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
        "display_name": "Dolgachev E(1)_{2,3} vs E(1)",
        "scout_rank": 1,
        "candidate_family": "Dolgachev surface / rational elliptic surface",
        "scout_status": "promising input path; SOURCE NEEDED",
        "source_status": "source-needed",
        "certification_status": "not-certified",
        "comparison_level": "not-certified",
        "reference_stub_ids": ["akbulut-dolgachev-surface"],
        "source_capture_route": "n72-dolgachev-source-capture",
        "digitization_route": "n73-exotic-diagram-digitization",
        "marking_route": "n74-exotic-h2-marking-certification",
        "data_requirements": [
            "captured source reference with hash or canonical locator",
            "exact source page, figure, theorem, or proposition ids",
            "machine-readable Kirby or handle data for both sides",
            "component ids, framings, dotted status, orientation, and lineage",
            "integer linking matrices and intersection-form sanity checks",
            "explicit H2 comparison or cork-canonical marking matrix",
        ],
        "missing_artifacts": [
            "captured source reference with hash or canonical locator",
            "exact source figure/page ids",
            "machine-readable Kirby or handle data for both sides",
            "component ids, framings, dotted status, orientation, and lineage",
            "integer linking matrices and intersection-form sanity checks",
            "explicit H2 comparison or cork-canonical marking matrix",
        ],
        "scout_decision": (
            "first source-capture target, but not an n70-certified input"
        ),
    },
    {
        "candidate_id": "r8-vs-cp2-8bar",
        "display_name": "R8 vs CP2#8bar",
        "scout_rank": 2,
        "candidate_family": "rational surface cork route",
        "scout_status": "promising fallback; SOURCE NEEDED",
        "source_status": "source-needed",
        "certification_status": "not-certified",
        "comparison_level": "not-certified",
        "reference_stub_ids": ["wakamaki-r8-cork"],
        "source_capture_route": "future-source-capture",
        "digitization_route": "future-diagram-digitization",
        "marking_route": "future-h2-marking-certification",
        "data_requirements": [
            "captured source reference with hash or canonical locator",
            "exact source page, figure, theorem, or proposition ids",
            "machine-readable diagrams for exotic and standard sides",
            "cork-twist and stabilization source separation",
            "explicit H2 comparison data",
        ],
        "missing_artifacts": [
            "captured source reference with hash or canonical locator",
            "exact source figure/page ids",
            "machine-readable diagrams for exotic and standard sides",
            "cork-twist and stabilization source separation",
            "explicit H2 comparison data",
        ],
        "scout_decision": "fallback if Dolgachev source capture stalls",
    },
    {
        "candidate_id": "akhmedov-park-cp2-2bar",
        "display_name": "Akhmedov-Park exotic CP2#2bar",
        "scout_rank": 3,
        "candidate_family": "small-b2 rational surface",
        "scout_status": "possible fallback; SOURCE NEEDED",
        "source_status": "source-needed",
        "certification_status": "not-certified",
        "comparison_level": "not-certified",
        "reference_stub_ids": ["akbulut-akhmedov-park"],
        "source_capture_route": "future-source-capture",
        "digitization_route": "future-diagram-digitization",
        "marking_route": "future-h2-marking-certification",
        "data_requirements": [
            "captured source reference",
            "usable diagram references",
            "machine-readable input",
            "homeomorphism or marking comparison route",
        ],
        "missing_artifacts": [
            "captured source reference",
            "usable diagram references",
            "machine-readable input",
            "homeomorphism or marking comparison route",
        ],
        "scout_decision": (
            "keep as lower-rank fallback; do not assume lower b2 is easier"
        ),
    },
    {
        "candidate_id": "yasui-style-traces",
        "display_name": "Yasui-style traces and cork families",
        "scout_rank": 4,
        "candidate_family": "relative or boundary-sensitive cork route",
        "scout_status": "relative or boundary-sensitive fallback; SOURCE NEEDED",
        "source_status": "source-needed",
        "certification_status": "not-certified-for-closed-pair-computation",
        "comparison_level": "not-selected",
        "reference_stub_ids": ["yasui-corks-knot-concordance"],
        "source_capture_route": "future-source-capture",
        "digitization_route": "future-diagram-digitization",
        "marking_route": "future-h2-marking-certification-or-relative-computation-pivot",
        "data_requirements": [
            "selected closed-pair construction or explicit relative-computation pivot",
            "machine-readable diagrams",
            "comparison-level declaration",
        ],
        "missing_artifacts": [
            "selected closed-pair construction or explicit relative-computation pivot",
            "machine-readable diagrams",
            "comparison-level declaration",
        ],
        "scout_decision": (
            "use only after choosing a closed-pair or relative-computation scope"
        ),
    },
)


def exotic_input_scout_ledger_artifact(
    *,
    ordinary_gate: Mapping[str, object] | None = None,
    decorated_gate: Mapping[str, object] | None = None,
    toy_closed_suite: Mapping[str, object] | None = None,
    claim_certified_input: bool = False,
    claim_n70_pass: bool = False,
    claim_n80_route: bool = False,
    claim_exotic_detection: bool = False,
    claim_closed_invariant: bool = False,
) -> dict[str, object]:
    """Return the deterministic n65 candidate scouting ledger."""

    if (
        claim_certified_input
        or claim_n70_pass
        or claim_n80_route
        or claim_exotic_detection
        or claim_closed_invariant
    ):
        raise ValueError(
            "n65-exotic-input-scout is an inventory ledger and refuses "
            "certified exotic input, n70 pass, n80 routing, exotic detection, "
            "and closed invariant claims"
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
    candidates = [
        _candidate_inventory_row(candidate)
        for candidate in sorted(
            CANDIDATE_SCOUT_ROWS, key=lambda item: int(item["scout_rank"])
        )
    ]

    artifact: dict[str, object] = {
        "schema": EXOTIC_INPUT_SCOUT_SCHEMA,
        "status": "scout-data-blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "Repo-local candidate metadata and source-needed scaffolding only; "
            "no network search, source capture, diagram digitization, H2 "
            "marking certification, or exotic invariant computation is performed"
        ),
        "upstream_nodes": [
            "n24-ordinary-surgery-gate",
            "n50-decorated-kirby-move-gate",
            "n55-toy-closed-suite",
        ],
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
            "toy_closed_suite": validate_toy_closed_suite_ledger_artifact(n55),
        },
        "candidate_count": len(candidates),
        "candidate_inventory": candidates,
        "ranked_candidate_ids": [str(candidate["candidate_id"]) for candidate in candidates],
        "first_candidate_id": candidates[0]["candidate_id"] if candidates else None,
        "any_candidate_certified": False,
        "any_machine_readable_exotic_input": False,
        "selected_n70_target": None,
        "recommended_next_route": RECOMMENDED_ROUTE_ID,
        "blocker_reason_ids": [
            SOURCE_NEEDED_BLOCKER_ID,
            MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
            N24_N50_N55_UPSTREAM_BLOCKED_ID,
        ],
        "blockers": _global_blockers(n24=n24, n50=n50, n55=n55),
        "required_unblock_artifacts": [
            "source reference records with canonical metadata, locator, capture time, and hash",
            "exact page, figure, theorem, or proposition ids for the selected input claims",
            "machine-readable Kirby or handle data for both sides of one selected exotic pair",
            "component ids, framings, dotted status, orientation, and lineage for both sides",
            "integer linking matrices and topological sanity checks for both sides",
            "H2/homeomorphism comparison or marking certificate with basis-change matrices",
            "n24 ordinary surgery gate pass certificate",
            "n50 decorated Kirby move gate pass certificate",
            "n55 toy closed suite pass certificate",
        ],
        "n70_exotic_input_certification_pass_allowed": False,
        "n80_exotic_computation_route_allowed": False,
        "certified_exotic_input_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "marked_distinction_claim_allowed": False,
        "cork_canonical_distinction_claim_allowed": False,
        "unmarked_total_function_distinction_claim_allowed": False,
        "closed_4_manifold_invariant_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "claim_boundary": (
            "this is a scouting inventory, not source-audited exotic input "
            "certification and not a twisted Yetter computation"
        ),
        "ledger_note": EXOTIC_INPUT_SCOUT_NOTE,
        "roadmap_note": EXOTIC_INPUT_SCOUT_ROADMAP,
        "reference_stub": EXOTIC_INPUT_REFERENCE_STUB,
        "artifact_path": EXOTIC_INPUT_SCOUT_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_exotic_input_scout_ledger_artifact(
        artifact
    )
    return artifact


def exotic_input_scout_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible certificate envelope for the n65 scout ledger."""

    root = Path(repo_root)
    ordinary_gate = ordinary_surgery_gate_certificate()
    decorated_gate = decorated_kirby_gate_artifact()
    toy_closed_suite = toy_closed_suite_ledger_artifact(
        ordinary_gate=ordinary_gate,
        decorated_gate=decorated_gate,
    )
    exact_output = exotic_input_scout_ledger_artifact(
        ordinary_gate=ordinary_gate,
        decorated_gate=decorated_gate,
        toy_closed_suite=toy_closed_suite,
    )
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.exotic_input_scout "
            f"--write {EXOTIC_INPUT_SCOUT_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.exotic_input_scout",
            "--write",
            EXOTIC_INPUT_SCOUT_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "candidate_ids": [
                    candidate["candidate_id"] for candidate in CANDIDATE_SCOUT_ROWS
                ],
                "ordinary_surgery_gate_status": ordinary_gate.get("status"),
                "decorated_kirby_gate_status": decorated_gate.get("status"),
                "toy_closed_suite_status": toy_closed_suite.get("status"),
                "reference_stub": EXOTIC_INPUT_REFERENCE_STUB,
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/exotic_input_scout.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.exotic_input_scout "
            "--write experiments/results/exotic-input-scout/n65-exotic-input-scout.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n65 is a source-needed candidate inventory, not n70 certification.",
            "No candidate has machine-readable exotic Kirby input or H2 marking certification.",
            "n24, n50, and n55 blockers still prevent closed exotic computation claims.",
        ],
    )


def validate_exotic_input_scout_ledger_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n65 scout shape without certifying any exotic input."""

    required = {
        "schema",
        "status",
        "node_id",
        "claim_level",
        "input_schemas",
        "input_statuses",
        "candidate_inventory",
        "ranked_candidate_ids",
        "blocker_reason_ids",
        "blockers",
        "blocked_claims",
        "required_unblock_artifacts",
    }
    missing = sorted(field for field in required if field not in artifact)
    input_schemas = artifact.get("input_schemas", {})
    input_schemas_ok = isinstance(input_schemas, Mapping) and input_schemas == {
        "ordinary_surgery_gate": ORDINARY_SURGERY_GATE_SCHEMA,
        "decorated_kirby_gate": DECORATED_KIRBY_GATE_SCHEMA,
        "toy_closed_suite": TOY_CLOSED_SUITE_SCHEMA,
    }
    candidates = artifact.get("candidate_inventory", [])
    candidate_list_ok = isinstance(candidates, list) and all(
        _candidate_inventory_row_is_valid(candidate) for candidate in candidates
    )
    ranked_ids = artifact.get("ranked_candidate_ids", [])
    ranking_ok = (
        ranked_ids
        == [
            "dolgachev-e1-23-vs-e1",
            "r8-vs-cp2-8bar",
            "akhmedov-park-cp2-2bar",
            "yasui-style-traces",
        ]
    )
    blockers = artifact.get("blocker_reason_ids", [])
    blockers_ok = isinstance(blockers, list) and set(blockers) >= {
        SOURCE_NEEDED_BLOCKER_ID,
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
        N24_N50_N55_UPSTREAM_BLOCKED_ID,
    }
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "n70_exotic_input_certification_pass_allowed",
            "n80_exotic_computation_route_allowed",
            "certified_exotic_input_claim_allowed",
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
            and artifact.get("schema") == EXOTIC_INPUT_SCOUT_SCHEMA
            and artifact.get("status") == "scout-data-blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("claim_level") == CLAIM_LEVEL
            and input_schemas_ok
            and candidate_list_ok
            and ranking_ok
            and blockers_ok
            and blocked_claims_ok
            and artifact.get("any_candidate_certified") is False
            and artifact.get("any_machine_readable_exotic_input") is False
        ),
        "missing_required_fields": missing,
        "input_schemas_ok": input_schemas_ok,
        "candidate_list_ok": candidate_list_ok,
        "ranking_ok": ranking_ok,
        "blockers_ok": blockers_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "scope": "candidate scouting inventory only; no certified exotic input",
    }


def stable_exotic_input_scout_ledger_json(artifact: Mapping[str, object]) -> str:
    """Serialize an n65 scout artifact deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def _candidate_inventory_row(candidate: Mapping[str, object]) -> dict[str, object]:
    missing_artifacts = [str(item) for item in candidate.get("missing_artifacts", [])]
    blocked_reason_ids = [SOURCE_NEEDED_BLOCKER_ID]
    if any("machine-readable" in item for item in missing_artifacts):
        blocked_reason_ids.append(MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID)
    if any(
        "H2" in item or "marking" in item or "homeomorphism" in item
        for item in missing_artifacts
    ):
        blocked_reason_ids.append(MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID)

    return {
        "candidate_id": candidate["candidate_id"],
        "display_name": candidate["display_name"],
        "scout_rank": candidate["scout_rank"],
        "candidate_family": candidate["candidate_family"],
        "scout_status": candidate["scout_status"],
        "source_status": candidate["source_status"],
        "status": "scout-data-blocked",
        "certified_for_n70": False,
        "certified_for_n80": False,
        "certification_status": candidate["certification_status"],
        "comparison_level": candidate["comparison_level"],
        "reference_stub_ids": candidate["reference_stub_ids"],
        "source_capture_route": candidate["source_capture_route"],
        "digitization_route": candidate["digitization_route"],
        "marking_route": candidate["marking_route"],
        "data_requirements": [
            str(item) for item in candidate.get("data_requirements", [])
        ],
        "missing_artifacts": missing_artifacts,
        "blocked_reason_ids": blocked_reason_ids,
        "scout_decision": candidate["scout_decision"],
        "claim_boundary": (
            "candidate remains source-needed metadata only and cannot be used "
            "as certified machine-readable exotic input"
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
            "reason_id": SOURCE_NEEDED_BLOCKER_ID,
            "status": "blocked",
            "source_node": NODE_ID,
            "observed": "candidate source stubs only",
            "required": (
                "source records with canonical metadata, exact page/figure ids, "
                "capture time, locator, and content hash or git blob hash"
            ),
            "reference_stub": EXOTIC_INPUT_REFERENCE_STUB,
        },
        {
            "reason_id": MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            "status": "blocked",
            "source_node": NODE_ID,
            "observed": "no certified exotic-pair machine-readable diagrams",
            "required": (
                "machine-readable PD code, braid word, or equivalent "
                "Kirby/handle data for both sides of one selected exotic pair"
            ),
            "claim_boundary": "candidate inventory cannot serve as n70/n80 input",
        },
        {
            "reason_id": MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
            "status": "blocked",
            "source_node": NODE_ID,
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
            "reason_id": N24_N50_N55_UPSTREAM_BLOCKED_ID,
            "status": "blocked",
            "source_node": "n24, n50, and n55",
            "observed": {
                "n24": n24.get("status", "missing"),
                "n50": n50.get("status", "missing"),
                "n55": n55.get("status", "missing"),
            },
            "required": {"n24": "pass", "n50": "pass", "n55": "pass"},
            "upstream_schemas": {
                "n24": n24.get("schema"),
                "n50": n50.get("schema"),
                "n55": n55.get("schema"),
            },
            "claim_boundary": (
                "even a promising candidate inventory cannot route to exotic "
                "computation while ordinary surgery, decorated Kirby, and toy "
                "closed-suite gates are blocked"
            ),
        },
    ]


def _candidate_inventory_row_is_valid(candidate: object) -> bool:
    if not isinstance(candidate, dict):
        return False
    required = {
        "candidate_id",
        "scout_rank",
        "source_status",
        "status",
        "certified_for_n70",
        "certified_for_n80",
        "certification_status",
        "comparison_level",
        "reference_stub_ids",
        "data_requirements",
        "missing_artifacts",
        "blocked_reason_ids",
    }
    if any(field not in candidate for field in required):
        return False
    return (
        candidate.get("status") == "scout-data-blocked"
        and candidate.get("source_status") == "source-needed"
        and candidate.get("certified_for_n70") is False
        and candidate.get("certified_for_n80") is False
        and isinstance(candidate.get("blocked_reason_ids"), list)
        and SOURCE_NEEDED_BLOCKER_ID in candidate.get("blocked_reason_ids", [])
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate the n65 exotic input scout artifact."
    )
    parser.add_argument(
        "--write",
        type=Path,
        help="write the certificate JSON to this path",
    )
    args = parser.parse_args()

    certificate = exotic_input_scout_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(output)
    else:
        print(output, end="")
    return 0


__all__ = [
    "BLOCKED_CLAIMS",
    "CANDIDATE_SCOUT_ROWS",
    "CLAIM_LEVEL",
    "EXOTIC_INPUT_REFERENCE_STUB",
    "EXOTIC_INPUT_SCOUT_ARTIFACT",
    "EXOTIC_INPUT_SCOUT_NOTE",
    "EXOTIC_INPUT_SCOUT_ROADMAP",
    "EXOTIC_INPUT_SCOUT_SCHEMA",
    "MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID",
    "MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID",
    "N24_N50_N55_UPSTREAM_BLOCKED_ID",
    "NODE_ID",
    "RECOMMENDED_ROUTE_ID",
    "SOURCE_NEEDED_BLOCKER_ID",
    "exotic_input_scout_certificate",
    "exotic_input_scout_ledger_artifact",
    "stable_exotic_input_scout_ledger_json",
    "validate_exotic_input_scout_ledger_artifact",
]


if __name__ == "__main__":
    raise SystemExit(main())
