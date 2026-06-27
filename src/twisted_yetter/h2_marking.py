"""H2/Kirby-component decoration metadata for finite-A toy scaffolds.

This n34 module is a schema layer only.  It aligns finite-group decoration
elements with machine-readable Kirby/link components and records basis
metadata, but it does not certify an H2 marking, prove basis invariance, run a
decorated link evaluator, or compute a closed 4-manifold invariant.
"""

from __future__ import annotations

import json
from numbers import Integral
from typing import Final, Mapping, Sequence

from twisted_yetter.finite_groups import (
    TRIVIAL_GROUP,
    Z2_GROUP,
    FiniteAbelianGroup,
    GroupElement,
    validate_character_table,
)
from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.linking_matrix import determinant
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate

H2_DECORATION_SCHEMA: Final = "twisted-yetter.h2-component-decoration.v1"
H2_DECORATION_NOTE: Final = "wiki/understandings/h2-label-and-basis-schema.org"
COMPARISON_LEVELS: Final = ("marked", "unmarked", "orbit/multiset", "not-in-scope")

CLAIM_LEVEL: Final = "schema-test-safe"
SOURCE_STATUS: Final = (
    "Kirby-basis/component-level metadata only; H2 marking and "
    "homeomorphism comparison are NOT CERTIFIED"
)

DOES_NOT_COMPUTE: Final = (
    "decorated core link evaluation",
    "handle-slide or basis-change proof",
    "certified H2 marking",
    "homeomorphism marking comparison",
    "closed 4-manifold invariant",
    "exotic smooth-structure detection evidence",
)

BLOCKED_HIGH_CLAIMS: Final = (
    "certified H2/homeomorphism marking claim",
    "decorated/twisted formula theorem",
    "claim-supporting closed 4D invariant",
    "exotic detection claim",
)


def h2_component_decoration_certificate(
    diagram: LinkDiagram,
    group: FiniteAbelianGroup,
    *,
    basis_id: str,
    basis_status: str,
    basis_source_status: str,
    decoration_by_component: Mapping[str, GroupElement] | None = None,
    decoration_vector: Sequence[GroupElement] | None = None,
    h2_basis_matrix: Sequence[Sequence[int]] | None = None,
    intersection_matrix: Sequence[Sequence[int]] | None = None,
    basis_change_matrix: Sequence[Sequence[int]] | None = None,
    lineage_source_status: str = "diagram component ids only; handle-slide lineage not certified",
    comparison_level: str = "not-in-scope",
    claim_boundary: str = (
        "schema-test-safe component/H2-basis metadata only; not a decorated "
        "calculation, closed invariant, homeomorphism comparison, or exotic claim"
    ),
    claim_certified_h2_marking: bool = False,
    claim_homeomorphism_marking: bool = False,
) -> dict[str, object]:
    """Return deterministic JSON-ready component decoration metadata.

    Decorations may be supplied either as a mapping keyed by component id or as
    a vector in ``diagram.component_ids`` order.  Values are finite-group
    elements from the currently supported exact groups: trivial and Z/2.
    """

    if claim_certified_h2_marking or claim_homeomorphism_marking:
        raise ValueError(
            "n34 refuses certified H2/homeomorphism marking claims; this API "
            "records only Kirby-basis/component-level decoration metadata"
        )

    _validate_supported_group(group)
    basis = _basis_payload(basis_id, basis_status, basis_source_status)
    comparison = _comparison_payload(comparison_level, claim_boundary)
    decorations = _normalize_decorations(
        diagram,
        group,
        decoration_by_component=decoration_by_component,
        decoration_vector=decoration_vector,
    )
    component_count = len(diagram.component_ids)
    h2_rank = component_count
    basis_matrix = _matrix_or_identity(
        h2_basis_matrix,
        "h2_basis_matrix",
        size=h2_rank,
    )
    intersection = _matrix_or_default(
        intersection_matrix,
        "intersection_matrix",
        default=diagram.linking_matrix(),
        size=h2_rank,
    )
    _check_symmetric(intersection, "intersection_matrix")
    basis_change = _matrix_or_identity(
        basis_change_matrix,
        "basis_change_matrix",
        size=h2_rank,
    )
    if abs(determinant(basis_change)) != 1:
        raise ValueError("basis_change_matrix must lie in GL(n,Z)")
    n24 = ordinary_surgery_gate_certificate()
    blockers = _certification_blockers(comparison["comparison_level"])

    artifact: dict[str, object] = {
        "schema": H2_DECORATION_SCHEMA,
        "status": "pass",
        "node_id": "n34-h2-label-and-basis-schema",
        "claim_level": CLAIM_LEVEL,
        "source_status": SOURCE_STATUS,
        "claim_boundary": claim_boundary,
        "comparison_level": comparison["comparison_level"],
        "comparison_language": comparison,
        "basis_id": basis["basis_id"],
        "basis_status": basis["basis_status"],
        "basis_source_status": basis["basis_source_status"],
        "basis": basis,
        "h2_basis": {
            "basis_id": basis["basis_id"],
            "rank": h2_rank,
            "basis_matrix": _json_matrix(basis_matrix),
            "matrix_convention": (
                "rows/columns follow diagram component order for no-1/no-3 "
                "toy schemas; not a certified closed H2 basis when blockers remain"
            ),
            "source_status": basis["basis_source_status"],
        },
        "intersection_form": {
            "matrix": _json_matrix(intersection),
            "matrix_status": "exact integer sanity metadata only",
            "source_status": "derived from LinkDiagram.linking_matrix unless explicitly supplied",
        },
        "basis_change": {
            "matrix": _json_matrix(basis_change),
            "matrix_status": "exact GL(n,Z) integer matrix",
            "coordinate_action": (
                "decoration coordinate transforms are recorded only as schema metadata; "
                "source-level handle-slide direction remains SOURCE NEEDED"
            ),
            "source_status": lineage_source_status,
        },
        "finite_group_id": _finite_group_id(group),
        "coefficient_group": {
            "group_id": _finite_group_id(group),
            "source_status": "exact finite group data from finite_groups.py",
        },
        "component_ids": list(diagram.component_ids),
        "component_lineage": [
            {
                "component_id": component_id,
                "source_status": lineage_source_status,
                "lineage_certified": False,
            }
            for component_id in diagram.component_ids
        ],
        "decoration_vector": [
            _component_decoration_payload(component_id, decorations[component_id])
            for component_id in diagram.component_ids
        ],
        "decoration_by_component": {
            component_id: _element_label(decorations[component_id])
            for component_id in diagram.component_ids
        },
        "zero_decoration": _is_zero_decoration(decorations),
        "all_trivial_decoration_explicit": True,
        "ordinary_surgery_gate_status": n24["status"],
        "ordinary_surgery_gate_status_explanation": (
            "n34 is schema metadata only and inherits the blocked n24 ordinary "
            "surgery gate; no closed ordinary or decorated invariant claim is allowed"
        ),
        "certified_h2_marking_claim_allowed": False,
        "homeomorphism_marking_claim_allowed": False,
        "closed_4_manifold_claim_allowed": False,
        "theorem_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "h2_marking_certification_status": "blocked",
        "certification_blockers": blockers,
        "does_not_compute": list(DOES_NOT_COMPUTE),
        "blocked_high_claims": list(BLOCKED_HIGH_CLAIMS),
        "ledger_note": H2_DECORATION_NOTE,
    }
    artifact["metadata_validation"] = validate_h2_decoration_artifact_metadata(artifact)
    return artifact


def zero_h2_component_decoration_certificate(
    diagram: LinkDiagram,
    group: FiniteAbelianGroup,
    *,
    basis_id: str,
    basis_status: str,
    basis_source_status: str,
) -> dict[str, object]:
    """Return an explicit all-identity component-decoration artifact."""

    return h2_component_decoration_certificate(
        diagram,
        group,
        basis_id=basis_id,
        basis_status=basis_status,
        basis_source_status=basis_source_status,
        decoration_vector=[_identity_element(group) for _ in diagram.component_ids],
    )


def validate_h2_decoration_artifact_metadata(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Check required n34 metadata fields without interpreting topology."""

    required = {
        "claim_level",
        "source_status",
        "claim_boundary",
        "comparison_level",
        "basis_status",
        "h2_basis",
        "intersection_form",
        "basis_change",
        "finite_group_id",
        "coefficient_group",
        "component_ids",
        "component_lineage",
        "decoration_vector",
        "decoration_by_component",
        "ordinary_surgery_gate_status",
        "h2_marking_certification_status",
        "certification_blockers",
    }
    missing = sorted(field for field in required if field not in artifact)
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "certified_h2_marking_claim_allowed",
            "homeomorphism_marking_claim_allowed",
            "closed_4_manifold_claim_allowed",
            "exotic_detection_claim_allowed",
        )
    )
    matrix_validation = _validate_artifact_matrices(artifact)
    return {
        "valid": not missing and blocked_claims_ok and matrix_validation["valid"],
        "missing_required_fields": missing,
        "blocked_claims_ok": blocked_claims_ok,
        "matrix_validation": matrix_validation,
        "scope": "metadata validation only; no H2 marking certification",
    }


def stable_h2_decoration_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n34 component-decoration certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _normalize_decorations(
    diagram: LinkDiagram,
    group: FiniteAbelianGroup,
    *,
    decoration_by_component: Mapping[str, GroupElement] | None,
    decoration_vector: Sequence[GroupElement] | None,
) -> dict[str, GroupElement]:
    if decoration_by_component is not None and decoration_vector is not None:
        raise ValueError("provide either decoration_by_component or decoration_vector, not both")

    component_ids = diagram.component_ids
    if decoration_by_component is None and decoration_vector is None:
        decoration_vector = [_identity_element(group) for _ in component_ids]

    if decoration_vector is not None:
        if len(decoration_vector) != len(component_ids):
            raise ValueError("decoration vector length must match diagram components")
        decorations = {
            component_id: tuple(element)
            for component_id, element in zip(component_ids, decoration_vector)
        }
    else:
        assert decoration_by_component is not None
        actual_ids = set(decoration_by_component)
        expected_ids = set(component_ids)
        if actual_ids != expected_ids:
            raise ValueError("decoration component ids must match diagram component ids")
        decorations = {
            component_id: tuple(decoration_by_component[component_id])
            for component_id in component_ids
        }

    for component_id, element in decorations.items():
        if element not in group.elements:
            raise ValueError(
                f"decoration for component {component_id!r} is not a group element"
            )
    return decorations


def _basis_payload(
    basis_id: str,
    basis_status: str,
    basis_source_status: str,
) -> dict[str, str]:
    if not basis_id:
        raise ValueError("basis_id must be present")
    if not basis_status:
        raise ValueError("basis_status must be present")
    if not basis_source_status:
        raise ValueError("basis_source_status must be present")
    return {
        "basis_id": basis_id,
        "basis_status": basis_status,
        "basis_source_status": basis_source_status,
        "scope": "Kirby component order only; not a certified H2/homeomorphism marking",
    }


def _comparison_payload(comparison_level: str, claim_boundary: str) -> dict[str, object]:
    if comparison_level not in COMPARISON_LEVELS:
        raise ValueError(
            "comparison_level must be one of marked, unmarked, orbit/multiset, not-in-scope"
        )
    if not claim_boundary:
        raise ValueError("claim_boundary must be present")
    descriptions = {
        "marked": (
            "marked language requires an explicit H2 identification matrix before "
            "it can support a comparison claim"
        ),
        "unmarked": (
            "unmarked total-function language requires the full allowed "
            "homeomorphism/isometry action before it can support a comparison claim"
        ),
        "orbit/multiset": (
            "orbit/multiset language requires an explicit automorphism action or "
            "recorded multiset construction before it can support a comparison claim"
        ),
        "not-in-scope": (
            "not-in-scope language records local schema metadata only and makes no "
            "comparison claim"
        ),
    }
    return {
        "comparison_level": comparison_level,
        "description": descriptions[comparison_level],
        "claim_boundary": claim_boundary,
        "comparison_claim_certified": False,
    }


def _certification_blockers(comparison_level: object) -> list[dict[str, object]]:
    blockers = [
        {
            "blocker_id": "uncertified-h2-marking",
            "status": "blocked",
            "required_evidence": (
                "machine-readable H2 marking or structured not-in-scope reason; "
                "no marking is inferred from component order"
            ),
        },
        {
            "blocker_id": "uncertified-component-lineage",
            "status": "blocked",
            "required_evidence": "integer handle-slide/basis-change lineage matrices",
        },
    ]
    if comparison_level != "not-in-scope":
        blockers.append(
            {
                "blocker_id": f"uncertified-{comparison_level}-comparison",
                "status": "blocked",
                "required_evidence": (
                    "comparison level is named for language discipline only; "
                    "no comparison claim is certified by n34"
                ),
            }
        )
    return blockers


def _matrix_or_identity(
    rows: Sequence[Sequence[int]] | None,
    field: str,
    *,
    size: int,
) -> tuple[tuple[int, ...], ...]:
    if rows is None:
        return tuple(tuple(1 if i == j else 0 for j in range(size)) for i in range(size))
    return _as_square_int_matrix(rows, field, size=size)


def _matrix_or_default(
    rows: Sequence[Sequence[int]] | None,
    field: str,
    *,
    default: Sequence[Sequence[int]],
    size: int,
) -> tuple[tuple[int, ...], ...]:
    if rows is None:
        return _as_square_int_matrix(default, field, size=size)
    return _as_square_int_matrix(rows, field, size=size)


def _as_square_int_matrix(
    rows: Sequence[Sequence[int]],
    field: str,
    *,
    size: int | None = None,
) -> tuple[tuple[int, ...], ...]:
    matrix = tuple(tuple(_as_exact_int(value, field) for value in row) for row in rows)
    matrix_size = len(matrix)
    if any(len(row) != matrix_size for row in matrix):
        raise ValueError(f"{field} must be square")
    if size is not None and matrix_size != size:
        raise ValueError(f"{field} size must match component/H2 rank")
    return matrix


def _as_exact_int(value: object, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError(f"{field} entries must be exact integers")
    return int(value)


def _check_symmetric(matrix: Sequence[Sequence[int]], field: str) -> None:
    size = len(matrix)
    for i in range(size):
        for j in range(size):
            if matrix[i][j] != matrix[j][i]:
                raise ValueError(f"{field} must be symmetric")


def _json_matrix(matrix: Sequence[Sequence[int]]) -> list[list[int]]:
    return [list(row) for row in matrix]


def _validate_artifact_matrices(artifact: Mapping[str, object]) -> dict[str, object]:
    errors: list[str] = []
    component_ids = artifact.get("component_ids", [])
    expected_size = len(component_ids) if isinstance(component_ids, list) else None
    for path in (
        ("h2_basis", "basis_matrix"),
        ("intersection_form", "matrix"),
        ("basis_change", "matrix"),
    ):
        section = artifact.get(path[0])
        if not isinstance(section, Mapping):
            errors.append(f"{path[0]} must be an object")
            continue
        try:
            matrix = _as_square_int_matrix(section[path[1]], ".".join(path), size=expected_size)
            if path == ("intersection_form", "matrix"):
                _check_symmetric(matrix, ".".join(path))
            if path == ("basis_change", "matrix") and abs(determinant(matrix)) != 1:
                errors.append("basis_change.matrix must lie in GL(n,Z)")
        except (KeyError, TypeError, ValueError) as exc:
            errors.append(str(exc))
    return {"valid": not errors, "errors": errors}


def _component_decoration_payload(
    component_id: str,
    element: GroupElement,
) -> dict[str, object]:
    return {
        "component_id": component_id,
        "element_id": _element_label(element),
        "element": list(element),
    }


def _validate_supported_group(group: FiniteAbelianGroup) -> None:
    validate_character_table(group)
    if group not in (TRIVIAL_GROUP, Z2_GROUP):
        raise ValueError(f"unsupported n34 finite group: {group.name}")


def _finite_group_id(group: FiniteAbelianGroup) -> str:
    if group == TRIVIAL_GROUP:
        return "trivial"
    if group == Z2_GROUP:
        return "Z/2"
    raise ValueError(f"unsupported n34 finite group: {group.name}")


def _identity_element(group: FiniteAbelianGroup) -> GroupElement:
    return group.elements[0]


def _is_zero_decoration(decorations: Mapping[str, GroupElement]) -> bool:
    return all(element == () or all(coordinate == 0 for coordinate in element) for element in decorations.values())


def _element_label(element: GroupElement) -> str:
    if element == ():
        return "e"
    return ",".join(str(coordinate) for coordinate in element)


__all__ = [
    "BLOCKED_HIGH_CLAIMS",
    "CLAIM_LEVEL",
    "COMPARISON_LEVELS",
    "DOES_NOT_COMPUTE",
    "H2_DECORATION_SCHEMA",
    "SOURCE_STATUS",
    "h2_component_decoration_certificate",
    "stable_h2_decoration_json",
    "validate_h2_decoration_artifact_metadata",
    "zero_h2_component_decoration_certificate",
]
