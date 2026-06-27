"""H2/Kirby-component decoration metadata for finite-A toy scaffolds.

This n34 module is a schema layer only.  It aligns finite-group decoration
elements with machine-readable Kirby/link components and records basis
metadata, but it does not certify an H2 marking, prove basis invariance, run a
decorated link evaluator, or compute a closed 4-manifold invariant.
"""

from __future__ import annotations

import json
from typing import Final, Mapping, Sequence

from twisted_yetter.finite_groups import (
    TRIVIAL_GROUP,
    Z2_GROUP,
    FiniteAbelianGroup,
    GroupElement,
    validate_character_table,
)
from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate

H2_DECORATION_SCHEMA: Final = "twisted-yetter.h2-component-decoration.v1"
H2_DECORATION_NOTE: Final = "wiki/understandings/h2-label-and-basis-schema.org"

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
    decorations = _normalize_decorations(
        diagram,
        group,
        decoration_by_component=decoration_by_component,
        decoration_vector=decoration_vector,
    )
    n24 = ordinary_surgery_gate_certificate()

    artifact: dict[str, object] = {
        "schema": H2_DECORATION_SCHEMA,
        "status": "pass",
        "node_id": "n34-h2-label-and-basis-schema",
        "claim_level": CLAIM_LEVEL,
        "source_status": SOURCE_STATUS,
        "basis_id": basis["basis_id"],
        "basis_status": basis["basis_status"],
        "basis_source_status": basis["basis_source_status"],
        "basis": basis,
        "finite_group_id": _finite_group_id(group),
        "component_ids": list(diagram.component_ids),
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
        "basis_status",
        "finite_group_id",
        "component_ids",
        "decoration_by_component",
        "ordinary_surgery_gate_status",
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
    return {
        "valid": not missing and blocked_claims_ok,
        "missing_required_fields": missing,
        "blocked_claims_ok": blocked_claims_ok,
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
    "DOES_NOT_COMPUTE",
    "H2_DECORATION_SCHEMA",
    "SOURCE_STATUS",
    "h2_component_decoration_certificate",
    "stable_h2_decoration_json",
    "validate_h2_decoration_artifact_metadata",
    "zero_h2_component_decoration_certificate",
]
