"""Blocked digitization ledger for the n73 exotic diagram gate.

This module fixes the schema and checklist for future exotic Kirby diagram
digitization.  Because n72 explicitly reports no captured PDF/snapshot and no
page/figure source, this module must not emit a machine-readable Dolgachev
diagram or route to n74/n70/n80.
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
from twisted_yetter.dolgachev_source_capture import (
    CANDIDATE_ID,
    DIGITIZATION_INPUT_BLOCKER_ID as N72_DIGITIZATION_INPUT_BLOCKER_ID,
    DOLGACHEV_REFERENCE_STUB,
    DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
    DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
    EXACT_CITATION_BLOCKER_ID,
    MARKING_SOURCE_BLOCKER_ID,
    NODE_ID as N72_NODE_ID,
    REFERENCE_ID,
    SOURCE_CAPTURE_BLOCKER_ID,
    dolgachev_source_capture_ledger_artifact,
)
from twisted_yetter.legacy_prose import legacy_prose_member_ref


EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA: Final = (
    "twisted-yetter.exotic-diagram-digitization.v1"
)
EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT: Final = (
    "experiments/results/diagram-digitization/"
    "n73-exotic-diagram-digitization.json"
)
EXOTIC_DIAGRAM_DIGITIZATION_NOTE: Final = (
    legacy_prose_member_ref("wiki/understandings/exotic-diagram-digitization.org")
)

NODE_ID: Final = "n73-exotic-diagram-digitization"
CLAIM_LEVEL: Final = "blocked digitization gate/schema checklist"

MISSING_SOURCE_SNAPSHOT_BLOCKER_ID: Final = "digitization-source-snapshot-needed"
MISSING_PAGE_FIGURE_BLOCKER_ID: Final = "digitization-page-figure-needed"
MISSING_DIAGRAM_ENCODING_BLOCKER_ID: Final = "digitization-diagram-encoding-needed"
MISSING_LINEAGE_BLOCKER_ID: Final = "digitization-component-lineage-needed"
MISSING_SANITY_TARGETS_BLOCKER_ID: Final = "digitization-sanity-targets-needed"

BLOCKED_CLAIMS: Final = (
    "machine-readable Dolgachev diagram exists",
    "Dolgachev Kirby components are digitized",
    "both exotic-pair sides validate under diagram schema",
    "derived matrix sanity checks match source expectations",
    "H2/homeomorphism marking certification can start",
    "n70 exotic input certification pass",
    "n80 exotic computation route",
    "exotic smooth-structure detection claim",
)

REQUIRED_COMPONENT_FIELDS: Final = (
    {
        "field": "side_id",
        "required": "stable id for each side of the candidate pair",
        "status": "blocked",
    },
    {
        "field": "component_id",
        "required": "stable component id matching the source figure",
        "status": "blocked",
    },
    {
        "field": "handle_role",
        "required": "1-handle/dotted component or 2-handle/framed component role",
        "status": "blocked",
    },
    {
        "field": "framing",
        "required": "integer framing for every 2-handle component",
        "status": "blocked",
    },
    {
        "field": "dotted_status",
        "required": "explicit dotted/undotted status for 1-handle components",
        "status": "blocked",
    },
    {
        "field": "orientation",
        "required": "component orientation convention or explicit unoriented justification",
        "status": "blocked",
    },
)

REQUIRED_ENCODING_FIELDS: Final = (
    {
        "field": "crossings",
        "required": "signed crossings with incident half-edge/component labels",
        "status": "blocked",
    },
    {
        "field": "pd_code",
        "required": "PD-code equivalent, if crossing list is not the primary encoding",
        "status": "blocked",
    },
    {
        "field": "braid_word",
        "required": "braid-word equivalent, if braid input is the primary encoding",
        "status": "blocked",
    },
    {
        "field": "source_locator",
        "required": "page/figure/crop locator for every encoded feature",
        "status": "blocked",
    },
)

REQUIRED_LINEAGE_FIELDS: Final = (
    {
        "field": "component_lineage",
        "required": "source component to final component lineage through slides/cancellations",
        "status": "blocked",
    },
    {
        "field": "handle_move_sequence",
        "required": "ordered move ids with source citation for each handle slide/cancellation",
        "status": "blocked",
    },
    {
        "field": "basis_change_matrices",
        "required": "integer matrices for every basis change and simplification",
        "status": "blocked",
    },
)

REQUIRED_SANITY_TARGETS: Final = (
    {
        "field": "linking_matrix",
        "required": "integer linking matrix target derived from the source diagram",
        "status": "blocked",
    },
    {
        "field": "intersection_form",
        "required": "intersection form target after dotted-handle elimination if used",
        "status": "blocked",
    },
    {
        "field": "handle_counts",
        "required": "0/1/2/3/4-handle counts or explicit source-backed unknowns",
        "status": "blocked",
    },
    {
        "field": "euler_characteristic",
        "required": "Euler characteristic target with handle-count convention",
        "status": "blocked",
    },
    {
        "field": "signature",
        "required": "signature target with orientation convention",
        "status": "blocked",
    },
    {
        "field": "h2_basis_comparison",
        "required": "basis labels needed by n74 marking certification",
        "status": "blocked",
    },
)


def exotic_diagram_digitization_ledger_artifact(
    *,
    source_capture: Mapping[str, object] | None = None,
    claim_machine_readable_diagram: bool = False,
    claim_digitized_components: bool = False,
    claim_schema_validated: bool = False,
    claim_matrix_sanity: bool = False,
    claim_n74_ready: bool = False,
    claim_n70_pass: bool = False,
    claim_n80_route: bool = False,
) -> dict[str, object]:
    """Return the deterministic n73 blocked digitization ledger."""

    if (
        claim_machine_readable_diagram
        or claim_digitized_components
        or claim_schema_validated
        or claim_matrix_sanity
        or claim_n74_ready
        or claim_n70_pass
        or claim_n80_route
    ):
        raise ValueError(
            "n73-exotic-diagram-digitization is blocked by n72 source gaps "
            "and refuses diagram, validation, n74, n70, and n80 claims"
        )

    n72 = (
        dolgachev_source_capture_ledger_artifact()
        if source_capture is None
        else dict(source_capture)
    )
    artifact: dict[str, object] = {
        "schema": EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA,
        "status": "blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "candidate_id": CANDIDATE_ID,
        "reference_id": REFERENCE_ID,
        "upstream_node": N72_NODE_ID,
        "upstream_schema": n72.get("schema"),
        "upstream_artifact": DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
        "upstream_status": n72.get("status"),
        "upstream_n73_ready": n72.get("n73_ready"),
        "source_snapshot_status": "missing",
        "page_figure_status": "missing",
        "diagram_payload_status": "not-produced",
        "machine_readable_diagrams": [],
        "blocked_by_n72_fields": [
            "local source/PDF/web snapshot path",
            "content hash or git blob hash",
            "exact diagram page/figure ids",
            "machine-readable Kirby/handle data for both sides",
            "component ids, framings, dotted status, orientation, and lineage",
        ],
        "source_inventory": {
            "reference_stub": DOLGACHEV_REFERENCE_STUB,
            "source_capture_artifact": DOLGACHEV_SOURCE_CAPTURE_ARTIFACT,
            "source_capture_schema": DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
            "source_capture_blockers": [
                SOURCE_CAPTURE_BLOCKER_ID,
                EXACT_CITATION_BLOCKER_ID,
                N72_DIGITIZATION_INPUT_BLOCKER_ID,
                MARKING_SOURCE_BLOCKER_ID,
            ],
            "proved_in_source_diagram_claims": [],
        },
        "required_schema_fields": {
            "component_fields": [dict(field) for field in REQUIRED_COMPONENT_FIELDS],
            "encoding_fields": [dict(field) for field in REQUIRED_ENCODING_FIELDS],
            "lineage_fields": [dict(field) for field in REQUIRED_LINEAGE_FIELDS],
            "sanity_targets": [dict(field) for field in REQUIRED_SANITY_TARGETS],
        },
        "required_side_records": [
            {
                "side_id": "dolgachev-e1-23",
                "display_name": "Dolgachev E(1)_{2,3}",
                "status": "blocked",
                "required": "source-backed Kirby/handle diagram before encoding",
            },
            {
                "side_id": "comparison-e1",
                "display_name": "E(1) comparison side",
                "status": "blocked",
                "required": "source-backed comparison diagram or construction before encoding",
            },
        ],
        "blocker_reason_ids": [
            MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
            MISSING_PAGE_FIGURE_BLOCKER_ID,
            MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
            MISSING_LINEAGE_BLOCKER_ID,
            MISSING_SANITY_TARGETS_BLOCKER_ID,
        ],
        "blockers": _blockers(),
        "claim_boundary": (
            "n73 fixes the future digitization schema and blocker inventory only. "
            "Because n72 has n73_ready=false and no captured source snapshot, "
            "page/figure ids, or diagram input, this artifact contains no "
            "machine-readable Dolgachev Kirby diagram."
        ),
        "diagram_exists_claim_allowed": False,
        "digitized_components_claim_allowed": False,
        "schema_validated_claim_allowed": False,
        "matrix_sanity_claim_allowed": False,
        "n74_marking_certification_ready": False,
        "n70_exotic_input_certification_pass_allowed": False,
        "n80_exotic_computation_route_allowed": False,
        "exotic_detection_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "recommended_next_route": "manual/offline source acquisition and exact page/figure capture",
        "ledger_note": EXOTIC_DIAGRAM_DIGITIZATION_NOTE,
        "artifact_path": EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_exotic_diagram_digitization_ledger_artifact(
        artifact
    )
    return artifact


def exotic_diagram_digitization_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible certificate envelope for the n73 ledger."""

    root = Path(repo_root)
    source_capture = dolgachev_source_capture_ledger_artifact()
    exact_output = exotic_diagram_digitization_ledger_artifact(
        source_capture=source_capture
    )
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.exotic_diagram_digitization --write "
            f"{EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.exotic_diagram_digitization",
            "--write",
            EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "candidate_id": CANDIDATE_ID,
                "reference_id": REFERENCE_ID,
                "upstream_schema": DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
                "upstream_status": source_capture.get("status"),
                "upstream_n73_ready": source_capture.get("n73_ready"),
                "network_used": False,
                "diagram_payload_produced": False,
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/exotic_diagram_digitization.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.exotic_diagram_digitization --write "
            "experiments/results/diagram-digitization/"
            "n73-exotic-diagram-digitization.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "No network search, PDF capture, visual digitization, or diagram encoding was performed.",
            "n72 reports n73_ready=false and no exact page/figure source for the Dolgachev target.",
            "This artifact is a blocked digitization schema/checklist, not an exotic-pair input.",
        ],
    )


def validate_exotic_diagram_digitization_ledger_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n73 digitization gate shape without promoting claims."""

    required = {
        "schema",
        "status",
        "node_id",
        "candidate_id",
        "upstream_schema",
        "upstream_status",
        "upstream_n73_ready",
        "machine_readable_diagrams",
        "required_schema_fields",
        "required_side_records",
        "blocker_reason_ids",
        "blockers",
        "blocked_claims",
    }
    missing = sorted(field for field in required if field not in artifact)
    schema_fields = artifact.get("required_schema_fields", {})
    schema_fields_ok = (
        isinstance(schema_fields, dict)
        and set(schema_fields) == {
            "component_fields",
            "encoding_fields",
            "lineage_fields",
            "sanity_targets",
        }
        and _field_names(schema_fields.get("component_fields")) == {
            "side_id",
            "component_id",
            "handle_role",
            "framing",
            "dotted_status",
            "orientation",
        }
        and _field_names(schema_fields.get("encoding_fields")) == {
            "crossings",
            "pd_code",
            "braid_word",
            "source_locator",
        }
        and _field_names(schema_fields.get("lineage_fields")) == {
            "component_lineage",
            "handle_move_sequence",
            "basis_change_matrices",
        }
        and _field_names(schema_fields.get("sanity_targets")) == {
            "linking_matrix",
            "intersection_form",
            "handle_counts",
            "euler_characteristic",
            "signature",
            "h2_basis_comparison",
        }
    )
    blockers_ok = artifact.get("blocker_reason_ids") == [
        MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
        MISSING_PAGE_FIGURE_BLOCKER_ID,
        MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
        MISSING_LINEAGE_BLOCKER_ID,
        MISSING_SANITY_TARGETS_BLOCKER_ID,
    ]
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "diagram_exists_claim_allowed",
            "digitized_components_claim_allowed",
            "schema_validated_claim_allowed",
            "matrix_sanity_claim_allowed",
            "n74_marking_certification_ready",
            "n70_exotic_input_certification_pass_allowed",
            "n80_exotic_computation_route_allowed",
            "exotic_detection_claim_allowed",
        )
    )
    side_records = artifact.get("required_side_records", [])
    side_records_ok = (
        isinstance(side_records, list)
        and {record.get("side_id") for record in side_records if isinstance(record, dict)}
        == {"dolgachev-e1-23", "comparison-e1"}
    )
    return {
        "valid": (
            not missing
            and artifact.get("schema") == EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA
            and artifact.get("status") == "blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("candidate_id") == CANDIDATE_ID
            and artifact.get("upstream_schema") == DOLGACHEV_SOURCE_CAPTURE_SCHEMA
            and artifact.get("upstream_status") == "blocked"
            and artifact.get("upstream_n73_ready") is False
            and artifact.get("machine_readable_diagrams") == []
            and schema_fields_ok
            and blockers_ok
            and blocked_claims_ok
            and side_records_ok
        ),
        "missing_required_fields": missing,
        "required_schema_fields_ok": schema_fields_ok,
        "blockers_ok": blockers_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "side_records_ok": side_records_ok,
        "scope": "blocked digitization checklist only; no machine-readable diagram",
    }


def stable_exotic_diagram_digitization_ledger_json(
    artifact: Mapping[str, object],
) -> str:
    """Serialize an n73 ledger deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def _field_names(value: object) -> set[str]:
    if not isinstance(value, list):
        return set()
    return {item.get("field") for item in value if isinstance(item, dict)}


def _blockers() -> list[dict[str, object]]:
    return [
        {
            "reason_id": MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
            "status": "blocked",
            "observed": "n72 source capture has no local PDF/web snapshot",
            "required": "captured source artifact with content sha256 or git blob hash",
        },
        {
            "reason_id": MISSING_PAGE_FIGURE_BLOCKER_ID,
            "status": "blocked",
            "observed": "n72 source capture has no exact page/figure ids",
            "required": "page/figure/crop ids for both sides before any visual transcription",
        },
        {
            "reason_id": MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
            "status": "blocked",
            "observed": "no crossing, PD-code, braid-word, or equivalent input exists",
            "required": "machine-readable link/handle encoding tied to source locators",
        },
        {
            "reason_id": MISSING_LINEAGE_BLOCKER_ID,
            "status": "blocked",
            "observed": "no source-backed handle slide, cancellation, or component lineage",
            "required": "component lineage and integer basis matrices for all simplifications",
        },
        {
            "reason_id": MISSING_SANITY_TARGETS_BLOCKER_ID,
            "status": "blocked",
            "observed": "no source-backed linking/intersection/signature/handle-count targets",
            "required": "integer sanity targets before n74 marking or n70 certification",
        },
    ]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate the n73 exotic diagram digitization blocked ledger."
    )
    parser.add_argument(
        "--write",
        type=Path,
        help="write the certificate JSON to this path",
    )
    args = parser.parse_args()

    certificate = exotic_diagram_digitization_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(output)
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
