"""Blocked H2/homeomorphism marking certification ledger for n74.

This module fixes the schema and checklist for future exotic-pair H2 marking
certification.  Because n73 emits no machine-readable diagrams, and n72 has no
source snapshot or exact page/figure locator, n74 must remain a blocked ledger:
it does not certify an H2 marking, a homeomorphism comparison, or an exotic
input gate.
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
from twisted_yetter.dolgachev_source_capture import CANDIDATE_ID, REFERENCE_ID
from twisted_yetter.exotic_diagram_digitization import (
    EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT,
    EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA,
    NODE_ID as N73_NODE_ID,
    exotic_diagram_digitization_ledger_artifact,
)
from twisted_yetter.h2_marking import H2_DECORATION_SCHEMA


EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA: Final = (
    "twisted-yetter.exotic-h2-marking-certification.v1"
)
EXOTIC_H2_MARKING_CERTIFICATION_ARTIFACT: Final = (
    "experiments/results/h2-marking/"
    "n74-exotic-h2-marking-certification.json"
)
EXOTIC_H2_MARKING_CERTIFICATION_NOTE: Final = (
    "wiki/understandings/exotic-h2-marking-certification.org"
)

NODE_ID: Final = "n74-exotic-h2-marking-certification"
CLAIM_LEVEL: Final = "blocked H2/homeomorphism marking certification checklist"
COMPARISON_LEVELS: Final = (
    "marked",
    "cork-canonical",
    "orbit",
    "multiset",
    "unmarked",
    "inconclusive",
)

MISSING_MACHINE_DIAGRAM_BLOCKER_ID: Final = "marking-machine-diagram-needed"
MISSING_SOURCE_CITATION_BLOCKER_ID: Final = "marking-source-citation-needed"
MISSING_H2_BASIS_BLOCKER_ID: Final = "marking-h2-basis-needed"
MISSING_INTERSECTION_MATRIX_BLOCKER_ID: Final = "marking-intersection-matrix-needed"
MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID: Final = (
    "marking-homeomorphism-identification-needed"
)
MISSING_COMPONENT_LINEAGE_BLOCKER_ID: Final = "marking-component-lineage-needed"
MISSING_CORK_TWIST_BLOCKER_ID: Final = "marking-cork-twist-data-needed"
MISSING_SANITY_CHECK_BLOCKER_ID: Final = "marking-sanity-checks-needed"

BLOCKED_CLAIMS: Final = (
    "H2 marking certified",
    "homeomorphism comparison certified",
    "marked distinction claim",
    "cork-canonical distinction claim",
    "orbit/multiset distinction claim",
    "unmarked total-function distinction claim",
    "n70 exotic input certification pass",
    "n80 exotic computation route",
    "exotic smooth-structure detection claim",
)

REQUIRED_MARKING_FIELDS: Final = (
    {
        "field": "comparison_level",
        "required": "one of marked, cork-canonical, orbit, multiset, unmarked, or inconclusive",
        "status": "blocked",
    },
    {
        "field": "side_h2_bases",
        "required": "source-backed H2 basis labels for both sides",
        "status": "blocked",
    },
    {
        "field": "intersection_matrices",
        "required": "exact integer intersection matrices in the recorded bases",
        "status": "blocked",
    },
    {
        "field": "homeomorphism_basis_identification_matrix",
        "required": "exact integer matrix identifying the two H2 bases, or a source-backed reason for absence",
        "status": "blocked",
    },
    {
        "field": "component_to_h2_lineage",
        "required": "Kirby component lineage to each H2 basis vector through slides/cancellations",
        "status": "blocked",
    },
    {
        "field": "cork_twist_marking",
        "required": "cork twist marking/action data when the comparison level is cork-canonical",
        "status": "blocked",
    },
    {
        "field": "source_citations",
        "required": "ref ids plus page/theorem/figure/crop locators for every marking and comparison claim",
        "status": "blocked",
    },
    {
        "field": "sanity_checks",
        "required": "rank, determinant, signature, Euler characteristic, form-preservation, and alpha=0 checks",
        "status": "blocked",
    },
)

REQUIRED_SIDE_FIELDS: Final = (
    {
        "field": "side_id",
        "required": "stable side id matching the digitized diagram side",
        "status": "blocked",
    },
    {
        "field": "h2_basis_id",
        "required": "stable id for the H2 basis used on that side",
        "status": "blocked",
    },
    {
        "field": "h2_basis_vectors",
        "required": "basis vectors with coordinate convention and source locator",
        "status": "blocked",
    },
    {
        "field": "component_lineage",
        "required": "component ids and integer basis changes producing each basis vector",
        "status": "blocked",
    },
    {
        "field": "intersection_matrix",
        "required": "exact integer symmetric matrix in this side basis",
        "status": "blocked",
    },
)

REQUIRED_SANITY_CHECKS: Final = (
    {
        "field": "rank_agreement",
        "required": "both side H2 ranks agree with diagrams and source claims",
        "status": "blocked",
    },
    {
        "field": "matrix_symmetry_integrality",
        "required": "intersection and identification matrices are exact integer data",
        "status": "blocked",
    },
    {
        "field": "form_preservation",
        "required": "P^T Q_left P = Q_right or the documented orientation convention equivalent",
        "status": "blocked",
    },
    {
        "field": "determinant_signature_euler",
        "required": "determinant, signature, and Euler characteristic match source and diagram targets",
        "status": "blocked",
    },
    {
        "field": "alpha_zero_route",
        "required": "zero decoration remains aligned with the ordinary route",
        "status": "blocked",
    },
    {
        "field": "basis_change_unimodularity",
        "required": "all basis-change and handle-slide matrices lie in GL(n,Z)",
        "status": "blocked",
    },
)


def exotic_h2_marking_certification_ledger_artifact(
    *,
    diagram_digitization: Mapping[str, object] | None = None,
    comparison_level: str = "inconclusive",
    claim_certified_h2_marking: bool = False,
    claim_homeomorphism_comparison: bool = False,
    claim_n70_pass: bool = False,
    claim_n80_route: bool = False,
) -> dict[str, object]:
    """Return the deterministic n74 blocked marking-certification ledger."""

    if comparison_level not in COMPARISON_LEVELS:
        raise ValueError(
            "comparison_level must be one of marked, cork-canonical, orbit, "
            "multiset, unmarked, or inconclusive"
        )
    if (
        claim_certified_h2_marking
        or claim_homeomorphism_comparison
        or claim_n70_pass
        or claim_n80_route
    ):
        raise ValueError(
            "n74-exotic-h2-marking-certification is blocked by missing n73 "
            "machine-readable diagrams and n72 source/page/figure data"
        )

    n73 = (
        exotic_diagram_digitization_ledger_artifact()
        if diagram_digitization is None
        else dict(diagram_digitization)
    )
    artifact: dict[str, object] = {
        "schema": EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA,
        "status": "blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "candidate_id": CANDIDATE_ID,
        "reference_id": REFERENCE_ID,
        "comparison_level": comparison_level,
        "comparison_level_status": "inconclusive-source-blocked",
        "allowed_comparison_levels": list(COMPARISON_LEVELS),
        "upstream_node": N73_NODE_ID,
        "upstream_schema": n73.get("schema"),
        "upstream_artifact": EXOTIC_DIAGRAM_DIGITIZATION_ARTIFACT,
        "upstream_status": n73.get("status"),
        "upstream_n74_ready": n73.get("n74_marking_certification_ready"),
        "upstream_machine_readable_diagrams": n73.get("machine_readable_diagrams", []),
        "h2_schema_dependency": H2_DECORATION_SCHEMA,
        "blocked_by_upstream_fields": [
            "no captured source/PDF/web snapshot",
            "no exact page/figure ids for the exotic-pair diagrams",
            "no machine-readable Kirby diagrams for both sides",
            "no source-backed component-to-H2 lineage",
            "no source-backed H2 bases or homeomorphism identification matrix",
        ],
        "required_fields": {
            "marking_fields": [dict(field) for field in REQUIRED_MARKING_FIELDS],
            "side_fields": [dict(field) for field in REQUIRED_SIDE_FIELDS],
            "sanity_checks": [dict(field) for field in REQUIRED_SANITY_CHECKS],
        },
        "required_side_records": [
            {
                "side_id": "dolgachev-e1-23",
                "display_name": "Dolgachev E(1)_{2,3}",
                "status": "blocked",
                "required": "source-backed diagram, H2 basis, intersection matrix, and component lineage",
            },
            {
                "side_id": "comparison-e1",
                "display_name": "E(1) comparison side",
                "status": "blocked",
                "required": "source-backed comparison basis and homeomorphism identification data",
            },
        ],
        "blocker_reason_ids": [
            MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
            MISSING_SOURCE_CITATION_BLOCKER_ID,
            MISSING_H2_BASIS_BLOCKER_ID,
            MISSING_INTERSECTION_MATRIX_BLOCKER_ID,
            MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
            MISSING_COMPONENT_LINEAGE_BLOCKER_ID,
            MISSING_CORK_TWIST_BLOCKER_ID,
            MISSING_SANITY_CHECK_BLOCKER_ID,
        ],
        "blockers": _blockers(),
        "claim_boundary": (
            "n74 fixes the future H2/homeomorphism marking certification schema "
            "only. Because n73 has no machine-readable diagrams and n72 has no "
            "source snapshot or exact page/figure locator, this artifact certifies "
            "no H2 marking, no homeomorphism comparison, no n70 input, and no n80 route."
        ),
        "certified_h2_marking_claim_allowed": False,
        "homeomorphism_comparison_claim_allowed": False,
        "marked_distinction_claim_allowed": False,
        "cork_canonical_distinction_claim_allowed": False,
        "orbit_multiset_distinction_claim_allowed": False,
        "unmarked_total_function_distinction_claim_allowed": False,
        "n70_exotic_input_certification_pass_allowed": False,
        "n80_exotic_computation_route_allowed": False,
        "exotic_detection_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "recommended_next_route": "manual/offline source acquisition, exact page/figure capture, then n73 diagram digitization",
        "ledger_note": EXOTIC_H2_MARKING_CERTIFICATION_NOTE,
        "artifact_path": EXOTIC_H2_MARKING_CERTIFICATION_ARTIFACT,
    }
    artifact["metadata_validation"] = (
        validate_exotic_h2_marking_certification_ledger_artifact(artifact)
    )
    return artifact


def exotic_h2_marking_certification_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a reproducible certificate envelope for the n74 ledger."""

    root = Path(repo_root)
    diagram_digitization = exotic_diagram_digitization_ledger_artifact()
    exact_output = exotic_h2_marking_certification_ledger_artifact(
        diagram_digitization=diagram_digitization
    )
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.exotic_h2_marking_certification --write "
            f"{EXOTIC_H2_MARKING_CERTIFICATION_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.exotic_h2_marking_certification",
            "--write",
            EXOTIC_H2_MARKING_CERTIFICATION_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "candidate_id": CANDIDATE_ID,
                "reference_id": REFERENCE_ID,
                "upstream_schema": EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA,
                "upstream_status": diagram_digitization.get("status"),
                "upstream_n74_ready": diagram_digitization.get(
                    "n74_marking_certification_ready"
                ),
                "comparison_level": "inconclusive",
                "marking_certified": False,
                "homeomorphism_comparison_certified": False,
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/exotic_h2_marking_certification.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m "
            "twisted_yetter.exotic_h2_marking_certification --write "
            "experiments/results/h2-marking/"
            "n74-exotic-h2-marking-certification.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "No H2 marking, homeomorphism matrix, cork action, or exotic input was certified.",
            "n73 reports n74_marking_certification_ready=false and no machine-readable diagrams.",
            "This artifact is a blocked certification schema/checklist, not a marking certificate.",
        ],
    )


def validate_exotic_h2_marking_certification_ledger_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n74 marking gate shape without promoting claims."""

    required = {
        "schema",
        "status",
        "node_id",
        "candidate_id",
        "comparison_level",
        "allowed_comparison_levels",
        "upstream_schema",
        "upstream_status",
        "upstream_n74_ready",
        "upstream_machine_readable_diagrams",
        "required_fields",
        "required_side_records",
        "blocker_reason_ids",
        "blockers",
        "blocked_claims",
    }
    missing = sorted(field for field in required if field not in artifact)
    required_fields = artifact.get("required_fields", {})
    required_fields_ok = (
        isinstance(required_fields, dict)
        and set(required_fields) == {"marking_fields", "side_fields", "sanity_checks"}
        and _field_names(required_fields.get("marking_fields"))
        == {
            "comparison_level",
            "side_h2_bases",
            "intersection_matrices",
            "homeomorphism_basis_identification_matrix",
            "component_to_h2_lineage",
            "cork_twist_marking",
            "source_citations",
            "sanity_checks",
        }
        and _field_names(required_fields.get("side_fields"))
        == {
            "side_id",
            "h2_basis_id",
            "h2_basis_vectors",
            "component_lineage",
            "intersection_matrix",
        }
        and _field_names(required_fields.get("sanity_checks"))
        == {
            "rank_agreement",
            "matrix_symmetry_integrality",
            "form_preservation",
            "determinant_signature_euler",
            "alpha_zero_route",
            "basis_change_unimodularity",
        }
    )
    blockers_ok = artifact.get("blocker_reason_ids") == [
        MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
        MISSING_SOURCE_CITATION_BLOCKER_ID,
        MISSING_H2_BASIS_BLOCKER_ID,
        MISSING_INTERSECTION_MATRIX_BLOCKER_ID,
        MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
        MISSING_COMPONENT_LINEAGE_BLOCKER_ID,
        MISSING_CORK_TWIST_BLOCKER_ID,
        MISSING_SANITY_CHECK_BLOCKER_ID,
    ]
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "certified_h2_marking_claim_allowed",
            "homeomorphism_comparison_claim_allowed",
            "marked_distinction_claim_allowed",
            "cork_canonical_distinction_claim_allowed",
            "orbit_multiset_distinction_claim_allowed",
            "unmarked_total_function_distinction_claim_allowed",
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
    comparison_level_ok = artifact.get("comparison_level") in COMPARISON_LEVELS
    return {
        "valid": (
            not missing
            and artifact.get("schema") == EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA
            and artifact.get("status") == "blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("candidate_id") == CANDIDATE_ID
            and artifact.get("upstream_schema") == EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA
            and artifact.get("upstream_status") == "blocked"
            and artifact.get("upstream_n74_ready") is False
            and artifact.get("upstream_machine_readable_diagrams") == []
            and comparison_level_ok
            and artifact.get("allowed_comparison_levels") == list(COMPARISON_LEVELS)
            and required_fields_ok
            and blockers_ok
            and blocked_claims_ok
            and side_records_ok
        ),
        "missing_required_fields": missing,
        "comparison_level_ok": comparison_level_ok,
        "required_fields_ok": required_fields_ok,
        "blockers_ok": blockers_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "side_records_ok": side_records_ok,
        "scope": "blocked H2/homeomorphism marking checklist only; no certification",
    }


def stable_exotic_h2_marking_certification_ledger_json(
    artifact: Mapping[str, object],
) -> str:
    """Serialize an n74 ledger deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def _field_names(value: object) -> set[str]:
    if not isinstance(value, list):
        return set()
    return {item.get("field") for item in value if isinstance(item, dict)}


def _blockers() -> list[dict[str, object]]:
    return [
        {
            "reason_id": MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
            "status": "blocked",
            "observed": "n73 has no machine-readable diagrams and n74_marking_certification_ready=false",
            "required": "both exotic-pair sides digitized with source locators before H2 lineage can be certified",
        },
        {
            "reason_id": MISSING_SOURCE_CITATION_BLOCKER_ID,
            "status": "blocked",
            "observed": "n72 has no source snapshot, content hash, or exact page/figure ids",
            "required": "ref ids plus page/theorem/figure/crop locators for every marking claim",
        },
        {
            "reason_id": MISSING_H2_BASIS_BLOCKER_ID,
            "status": "blocked",
            "observed": "no source-backed H2 basis exists for either side",
            "required": "explicit basis labels, coordinate convention, and source for both sides",
        },
        {
            "reason_id": MISSING_INTERSECTION_MATRIX_BLOCKER_ID,
            "status": "blocked",
            "observed": "no exact intersection matrices are certified in source-backed bases",
            "required": "integer symmetric matrices with rank/signature/determinant checks",
        },
        {
            "reason_id": MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
            "status": "blocked",
            "observed": "no homeomorphism or basis identification matrix is available",
            "required": "integer matrix preserving the intersection form, or a source-backed reason for absence",
        },
        {
            "reason_id": MISSING_COMPONENT_LINEAGE_BLOCKER_ID,
            "status": "blocked",
            "observed": "no component-to-H2 lineage through slides/cancellations exists",
            "required": "component lineage and GL(n,Z) basis-change matrices from diagram components to H2 bases",
        },
        {
            "reason_id": MISSING_CORK_TWIST_BLOCKER_ID,
            "status": "blocked",
            "observed": "no cork twist marking/action data has been captured",
            "required": "cork boundary/action data if the comparison level is cork-canonical",
        },
        {
            "reason_id": MISSING_SANITY_CHECK_BLOCKER_ID,
            "status": "blocked",
            "observed": "rank, form-preservation, alpha=0, and matrix sanity checks cannot be run",
            "required": "exact sanity checks after diagram, basis, lineage, and identification data exist",
        },
    ]


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate the n74 exotic H2 marking certification blocked ledger."
    )
    parser.add_argument(
        "--write",
        type=Path,
        help="write the certificate JSON to this path",
    )
    args = parser.parse_args()

    certificate = exotic_h2_marking_certification_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(output)
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
