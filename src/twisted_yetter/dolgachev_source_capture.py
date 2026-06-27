"""Source-capture ledger for the n72 Dolgachev candidate.

This module records only repo-local source inventory and source-needed blockers
for the n65 first candidate.  It does not fetch network sources, digitize
Kirby diagrams, certify an H2 marking, or route to n70/n80.
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
from twisted_yetter.exotic_input_scout import (
    EXOTIC_INPUT_SCOUT_ARTIFACT,
    EXOTIC_INPUT_SCOUT_SCHEMA,
    EXOTIC_INPUT_REFERENCE_STUB,
    MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
    MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
    NODE_ID as N65_NODE_ID,
    SOURCE_NEEDED_BLOCKER_ID,
    exotic_input_scout_ledger_artifact,
)


DOLGACHEV_SOURCE_CAPTURE_SCHEMA: Final = (
    "twisted-yetter.dolgachev-source-capture.v1"
)
DOLGACHEV_SOURCE_CAPTURE_ARTIFACT: Final = (
    "experiments/results/source-capture/n72-dolgachev-source-capture.json"
)
DOLGACHEV_SOURCE_CAPTURE_NOTE: Final = (
    "wiki/understandings/dolgachev-source-capture.org"
)
DOLGACHEV_REFERENCE_STUB: Final = "wiki/references/akbulut-dolgachev-surface.org"
DOLGACHEV_SOURCE_CAPTURE_ROADMAP: Final = "wiki/roadmaps/dolgachev-source-capture.org"

NODE_ID: Final = "n72-dolgachev-source-capture"
CANDIDATE_ID: Final = "dolgachev-e1-23-vs-e1"
REFERENCE_ID: Final = "akbulut-dolgachev-surface"
CLAIM_LEVEL: Final = "source-capture checklist/source-needed blocker"

SOURCE_CAPTURE_BLOCKER_ID: Final = "dolgachev-source-artifact-needed"
EXACT_CITATION_BLOCKER_ID: Final = "dolgachev-exact-page-figure-theorem-needed"
DIGITIZATION_INPUT_BLOCKER_ID: Final = "dolgachev-digitization-input-needed"
MARKING_SOURCE_BLOCKER_ID: Final = "dolgachev-h2-marking-source-needed"

BLOCKED_CLAIMS: Final = (
    "Dolgachev source captured claim",
    "Dolgachev proved-in-source diagram claim",
    "machine-readable Dolgachev Kirby diagram exists",
    "Dolgachev H2/homeomorphism marking certified",
    "n70 exotic input certification pass",
    "n80 exotic computation route",
    "exotic smooth-structure detection claim",
)

REQUIRED_EXACT_SOURCE_SLOTS: Final = (
    {
        "slot_id": "bibliographic-metadata",
        "required": (
            "canonical title, author list, version/date, publication/arXiv "
            "identifier, and locator"
        ),
        "current_status": "source-needed",
        "current_repo_evidence": "only n65 candidate stub text",
    },
    {
        "slot_id": "source-snapshot-hash",
        "required": "local PDF/web snapshot path with sha256 or git blob hash",
        "current_status": "missing",
        "current_repo_evidence": "no local source/PDF/snapshot found",
    },
    {
        "slot_id": "diagram-page-figure-ids",
        "required": (
            "exact page and figure ids for diagrams of E(1)_{2,3} and the "
            "comparison E(1) side"
        ),
        "current_status": "missing",
        "current_repo_evidence": "no exact page or figure ids in repo-local records",
    },
    {
        "slot_id": "handle-claim-citations",
        "required": (
            "exact theorem/proposition/page ids for handle decomposition, "
            "no-1/no-3-handle claims if used, and any simplification sequence"
        ),
        "current_status": "missing",
        "current_repo_evidence": "no source-backed theorem/page ids captured",
    },
    {
        "slot_id": "comparison-claim-citations",
        "required": (
            "exact source ids for homeomorphic/non-diffeomorphic comparison "
            "and whether the comparison is marked, cork-canonical, or unmarked"
        ),
        "current_status": "missing",
        "current_repo_evidence": "comparison remains n65 scout metadata only",
    },
)

DIGITIZATION_INPUT_REQUIREMENTS: Final = (
    "component ids for both sides",
    "framings for each 2-handle component",
    "dotted status for 1-handle components",
    "orientation conventions for link components",
    "crossing or PD-code/braid-word equivalent input",
    "component lineage through every handle slide or cancellation",
    "integer linking matrix and intersection-form sanity targets",
    "handle count and Euler characteristic sanity targets",
    "signature sanity target",
    "basis-change matrices for simplification and H2 comparison",
)


def dolgachev_source_capture_ledger_artifact(
    *,
    scout: Mapping[str, object] | None = None,
    claim_source_captured: bool = False,
    claim_machine_readable_diagram: bool = False,
    claim_h2_marking_certified: bool = False,
    claim_n70_pass: bool = False,
    claim_n80_route: bool = False,
    claim_exotic_detection: bool = False,
) -> dict[str, object]:
    """Return the deterministic n72 source-capture checklist ledger."""

    if (
        claim_source_captured
        or claim_machine_readable_diagram
        or claim_h2_marking_certified
        or claim_n70_pass
        or claim_n80_route
        or claim_exotic_detection
    ):
        raise ValueError(
            "n72-dolgachev-source-capture is a source-needed checklist and "
            "refuses source-captured, machine-readable diagram, H2 marking, "
            "n70, n80, and exotic detection claims"
        )

    n65 = exotic_input_scout_ledger_artifact() if scout is None else dict(scout)
    selected = _selected_candidate_from_scout(n65)
    artifact: dict[str, object] = {
        "schema": DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
        "status": "blocked",
        "source_status": "source-needed",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "candidate_id": CANDIDATE_ID,
        "candidate_display_name": selected.get(
            "display_name", "Dolgachev E(1)_{2,3} vs E(1)"
        ),
        "upstream_node": N65_NODE_ID,
        "upstream_schema": n65.get("schema"),
        "upstream_artifact": EXOTIC_INPUT_SCOUT_ARTIFACT,
        "upstream_status": n65.get("status"),
        "upstream_selected_candidate_status": {
            "source_status": selected.get("source_status"),
            "certified_for_n70": selected.get("certified_for_n70"),
            "certified_for_n80": selected.get("certified_for_n80"),
            "comparison_level": selected.get("comparison_level"),
        },
        "reference_inventory": [
            {
                "reference_id": REFERENCE_ID,
                "record_path": DOLGACHEV_REFERENCE_STUB,
                "record_status": "stub/source-needed",
                "locator_status": "bibliographic pointer only; no local snapshot",
                "known_repo_locator": "wiki/references/exotic-input-candidates-2026-06-26.org",
                "parent_stub": EXOTIC_INPUT_REFERENCE_STUB,
                "content_hash_status": "missing",
                "capture_time_status": "missing",
                "proved_in_source_claims": [],
                "project_inference_only": [
                    "candidate was selected as n65 rank-1 source-capture target",
                    "Dolgachev route is promising only as source-needed metadata",
                ],
                "claim_boundary": (
                    "this record is not a captured paper/PDF and cannot support "
                    "diagram, marking, homeomorphism, or exotic computation claims"
                ),
            }
        ],
        "required_exact_source_slots": [
            dict(slot) for slot in REQUIRED_EXACT_SOURCE_SLOTS
        ],
        "needed_page_figure_theorem_ids": [
            "page/figure id for the E(1)_{2,3} Kirby or handle diagram",
            "page/figure id for the E(1) comparison diagram or construction",
            "theorem/proposition/page id for the homeomorphism claim",
            "theorem/proposition/page id for the non-diffeomorphism claim",
            "page/figure/proposition id for any cork decomposition or cork twist used",
            "page/proposition id for any no-1/no-3-handle or closed-manifold handle claim used",
            "page/figure ids for every handle-slide/simplification step used for digitization",
        ],
        "needed_snapshot_fields": [
            "canonical metadata payload",
            "capture time in UTC",
            "locator URL or local source path",
            "content sha256 or git blob hash",
            "license/access note if relevant",
        ],
        "needed_kirby_handle_diagram_fields": list(DIGITIZATION_INPUT_REQUIREMENTS),
        "digitization_input_requirements": list(DIGITIZATION_INPUT_REQUIREMENTS),
        "missing_fields": [
            "local source/PDF/web snapshot path",
            "content hash or git blob hash",
            "capture time",
            "exact diagram page/figure ids",
            "exact theorem/proposition/page ids for comparison claims",
            "machine-readable Kirby/handle data for both sides",
            "component ids, framings, dotted status, orientation, and lineage",
            "integer linking matrix, signature, Euler characteristic, and handle-count sanity targets",
            "H2/homeomorphism comparison or cork-canonical marking matrix",
        ],
        "n70_blocker_ids_addressed": [
            SOURCE_NEEDED_BLOCKER_ID,
            MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
            MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
        ],
        "blocker_reason_ids": [
            SOURCE_CAPTURE_BLOCKER_ID,
            EXACT_CITATION_BLOCKER_ID,
            DIGITIZATION_INPUT_BLOCKER_ID,
            MARKING_SOURCE_BLOCKER_ID,
        ],
        "blockers": _blockers(),
        "recommended_next_route": "manual/offline source acquisition before n73",
        "n73_ready": False,
        "n74_ready": False,
        "n70_exotic_input_certification_pass_allowed": False,
        "n80_exotic_computation_route_allowed": False,
        "source_captured_claim_allowed": False,
        "machine_readable_diagram_claim_allowed": False,
        "h2_marking_certified_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "claim_boundary": (
            "n72 found only repo-local stubs and source-needed slots; it is a "
            "blocked source-capture checklist, not a source audit, not diagram "
            "digitization, and not exotic input certification"
        ),
        "ledger_note": DOLGACHEV_SOURCE_CAPTURE_NOTE,
        "reference_stub": DOLGACHEV_REFERENCE_STUB,
        "roadmap_note": DOLGACHEV_SOURCE_CAPTURE_ROADMAP,
        "artifact_path": DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_dolgachev_source_capture_ledger_artifact(
        artifact
    )
    return artifact


def dolgachev_source_capture_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible certificate envelope for the n72 ledger."""

    root = Path(repo_root)
    scout = exotic_input_scout_ledger_artifact()
    exact_output = dolgachev_source_capture_ledger_artifact(scout=scout)
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.dolgachev_source_capture --write "
            f"{DOLGACHEV_SOURCE_CAPTURE_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.dolgachev_source_capture",
            "--write",
            DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "candidate_id": CANDIDATE_ID,
                "reference_id": REFERENCE_ID,
                "upstream_schema": EXOTIC_INPUT_SCOUT_SCHEMA,
                "upstream_status": scout.get("status"),
                "repo_local_reference_stub": EXOTIC_INPUT_REFERENCE_STUB,
                "network_used": False,
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/dolgachev_source_capture.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.dolgachev_source_capture --write "
            "experiments/results/source-capture/n72-dolgachev-source-capture.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "No network search or external source capture was performed.",
            "Repo-local records contain only an n65 bibliographic stub for the Dolgachev target.",
            "n72 remains blocked before n73 digitization, n74 marking certification, n70 input certification, and n80 computation.",
        ],
    )


def validate_dolgachev_source_capture_ledger_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n72 source-capture ledger shape without promoting claims."""

    required = {
        "schema",
        "status",
        "source_status",
        "node_id",
        "candidate_id",
        "upstream_schema",
        "reference_inventory",
        "required_exact_source_slots",
        "needed_page_figure_theorem_ids",
        "needed_kirby_handle_diagram_fields",
        "missing_fields",
        "n70_blocker_ids_addressed",
        "blocker_reason_ids",
        "blockers",
        "blocked_claims",
    }
    missing = sorted(field for field in required if field not in artifact)
    inventory = artifact.get("reference_inventory", [])
    inventory_ok = (
        isinstance(inventory, list)
        and len(inventory) == 1
        and isinstance(inventory[0], dict)
        and inventory[0].get("reference_id") == REFERENCE_ID
        and inventory[0].get("record_status") == "stub/source-needed"
        and inventory[0].get("content_hash_status") == "missing"
        and inventory[0].get("capture_time_status") == "missing"
        and inventory[0].get("proved_in_source_claims") == []
    )
    slots = artifact.get("required_exact_source_slots", [])
    slots_ok = (
        isinstance(slots, list)
        and {slot.get("slot_id") for slot in slots if isinstance(slot, dict)}
        == {
            "bibliographic-metadata",
            "source-snapshot-hash",
            "diagram-page-figure-ids",
            "handle-claim-citations",
            "comparison-claim-citations",
        }
    )
    blockers_ok = artifact.get("blocker_reason_ids") == [
        SOURCE_CAPTURE_BLOCKER_ID,
        EXACT_CITATION_BLOCKER_ID,
        DIGITIZATION_INPUT_BLOCKER_ID,
        MARKING_SOURCE_BLOCKER_ID,
    ]
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "n73_ready",
            "n74_ready",
            "n70_exotic_input_certification_pass_allowed",
            "n80_exotic_computation_route_allowed",
            "source_captured_claim_allowed",
            "machine_readable_diagram_claim_allowed",
            "h2_marking_certified_claim_allowed",
            "exotic_detection_claim_allowed",
        )
    )
    n70_blockers_ok = set(artifact.get("n70_blocker_ids_addressed", [])) == {
        SOURCE_NEEDED_BLOCKER_ID,
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
    }
    return {
        "valid": (
            not missing
            and artifact.get("schema") == DOLGACHEV_SOURCE_CAPTURE_SCHEMA
            and artifact.get("status") == "blocked"
            and artifact.get("source_status") == "source-needed"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("candidate_id") == CANDIDATE_ID
            and artifact.get("upstream_schema") == EXOTIC_INPUT_SCOUT_SCHEMA
            and inventory_ok
            and slots_ok
            and blockers_ok
            and blocked_claims_ok
            and n70_blockers_ok
        ),
        "missing_required_fields": missing,
        "reference_inventory_ok": inventory_ok,
        "required_slots_ok": slots_ok,
        "blockers_ok": blockers_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "n70_blockers_ok": n70_blockers_ok,
        "scope": "blocked source-capture checklist only; no Dolgachev source claims",
    }


def stable_dolgachev_source_capture_ledger_json(
    artifact: Mapping[str, object],
) -> str:
    """Serialize an n72 ledger deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def _selected_candidate_from_scout(scout: Mapping[str, object]) -> dict[str, object]:
    candidates = scout.get("candidate_inventory", [])
    if not isinstance(candidates, list):
        return {}
    for candidate in candidates:
        if isinstance(candidate, dict) and candidate.get("candidate_id") == CANDIDATE_ID:
            return dict(candidate)
    return {}


def _blockers() -> list[dict[str, object]]:
    return [
        {
            "reason_id": SOURCE_CAPTURE_BLOCKER_ID,
            "status": "blocked",
            "observed": "repo-local bibliographic stub only",
            "required": (
                "canonical source metadata, capture time, locator, and content "
                "sha256 or git blob hash"
            ),
        },
        {
            "reason_id": EXACT_CITATION_BLOCKER_ID,
            "status": "blocked",
            "observed": "no exact page, figure, theorem, or proposition ids",
            "required": (
                "exact source citations for diagrams, handle claims, and "
                "homeomorphic/non-diffeomorphic comparison claims"
            ),
        },
        {
            "reason_id": DIGITIZATION_INPUT_BLOCKER_ID,
            "status": "blocked",
            "observed": "no machine-readable Kirby/handle input",
            "required": (
                "component ids, framings, dotted status, orientations, crossings "
                "or PD/braid data, and lineage for both sides"
            ),
        },
        {
            "reason_id": MARKING_SOURCE_BLOCKER_ID,
            "status": "blocked",
            "observed": "no source-backed H2/homeomorphism marking data",
            "required": (
                "comparison level plus integer H2 identification, basis-change "
                "matrix, or cork-canonical marking source"
            ),
        },
    ]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate the n72 Dolgachev source-capture artifact."
    )
    parser.add_argument(
        "--write",
        type=Path,
        help="write the certificate JSON to this path",
    )
    args = parser.parse_args()

    certificate = dolgachev_source_capture_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(output)
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
