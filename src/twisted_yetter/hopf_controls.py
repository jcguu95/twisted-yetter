"""Hopf-specific exact controls for the colored framed link evaluator gate.

This module is deliberately narrower than a link evaluator.  It accepts only
the positive 0-framed two-component Hopf fixtures used by n17 and returns the
local-convention SU(2)_2 target S_ij / S_00.  General crossing diagrams,
Kirby colors, 4D normalizations, and twisted formulas are out of scope.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.su2_level2 import (
    LINK_DATA_CLAIM_LEVELS,
    RT_LINK_LEDGER_REFERENCE,
    RT_LINK_SOURCE_REFERENCE,
    SIMPLE_LABELS,
    QuadraticSurd,
    hopf_control_entry,
)

HOPF_CONTROL_CLAIM_LEVEL: Final = {
    "claim_level": "SOURCE NEEDED/local-convention/schema-test-safe",
    "ledger": RT_LINK_LEDGER_REFERENCE,
    "source_record": RT_LINK_SOURCE_REFERENCE,
    "working_target": "positive 0-framed Hopf value S_ij / S_00",
    "scope": "two-component positive 0-framed Hopf fixtures only",
    "not_scope": (
        "general crossing evaluator, Kirby color, 4D normalization, or twisted formula"
    ),
    "upstream_su2_claim": LINK_DATA_CLAIM_LEVELS["hopf_control"],
}


def positive_hopf_sanity(diagram: LinkDiagram) -> dict[str, object]:
    """Validate the positive 0-framed Hopf fixture shape and return metadata.

    The accepted shape is intentionally fixture-level: two undotted components,
    zero framings, exactly two positive inter-component crossings, and linking
    matrix ``[[0, 1], [1, 0]]``.  Anything else is refused so later nodes cannot
    mistake this for a general crossing-link evaluator.
    """

    if len(diagram.components) != 2:
        raise NotImplementedError("Hopf controls require exactly two components")
    if diagram.framings != (0, 0):
        raise NotImplementedError("Hopf controls only cover 0-framed fixtures")
    if any(component.dotted for component in diagram.components):
        raise NotImplementedError("Hopf controls do not cover dotted components")
    if len(diagram.crossings) != 2:
        raise NotImplementedError("Hopf controls require exactly two crossings")

    component_ids = diagram.component_ids
    crossing_signs = tuple(crossing.sign for crossing in diagram.crossings)
    if crossing_signs != (1, 1):
        raise NotImplementedError("Hopf controls only cover positive crossings")

    for crossing in diagram.crossings:
        over_id = crossing.over.component_id
        under_id = crossing.under.component_id
        if over_id == under_id:
            raise NotImplementedError("Hopf controls do not cover self-crossings")
        if {over_id, under_id} != set(component_ids):
            raise NotImplementedError("Hopf crossings must use both components")

    linking_matrix = diagram.linking_matrix()
    if linking_matrix != ((0, 1), (1, 0)):
        raise NotImplementedError("Hopf controls only cover linking number +1")

    return {
        "component_ids": list(component_ids),
        "framings": list(diagram.framings),
        "crossing_count": len(diagram.crossings),
        "crossing_signs": list(crossing_signs),
        "linking_matrix": [list(row) for row in linking_matrix],
    }


def hopf_expected_value(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> QuadraticSurd:
    """Return the exact local Hopf control value for a validated fixture."""

    positive_hopf_sanity(diagram)
    expected_ids = set(diagram.component_ids)
    supplied_ids = set(labels_by_component)
    if supplied_ids != expected_ids:
        missing = sorted(expected_ids.difference(supplied_ids))
        extra = sorted(supplied_ids.difference(expected_ids))
        raise ValueError(
            "label mapping must match Hopf components exactly; "
            f"missing={missing}, extra={extra}"
        )

    left_id, right_id = diagram.component_ids
    left_label = labels_by_component[left_id]
    right_label = labels_by_component[right_id]
    _check_label(left_label)
    _check_label(right_label)
    return hopf_control_entry(left_label, right_label)


def load_hopf_fixture_expected_value(
    fixture_path: str | Path,
    labels_by_component: Mapping[str, str],
) -> QuadraticSurd:
    """Load a machine-readable Hopf fixture and compute its local target."""

    payload = json.loads(Path(fixture_path).read_text())
    return hopf_expected_value(LinkDiagram.from_json(payload), labels_by_component)


def hopf_control_certificate(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> dict[str, object]:
    """Return deterministic JSON-ready metadata for an n17 Hopf control."""

    value = hopf_expected_value(diagram, labels_by_component)
    return {
        "schema": "twisted-yetter.hopf-link-control.v1",
        "status": "pass",
        "diagram_id": diagram.diagram_id,
        "labels_by_component": dict(sorted(labels_by_component.items())),
        "sanity": positive_hopf_sanity(diagram),
        "expected_value": value.to_jsonable(),
        "claim": HOPF_CONTROL_CLAIM_LEVEL,
    }


def _check_label(label: str) -> None:
    if label not in SIMPLE_LABELS:
        raise ValueError(f"unknown SU(2)_2 simple label: {label!r}")


__all__ = [
    "HOPF_CONTROL_CLAIM_LEVEL",
    "hopf_control_certificate",
    "hopf_expected_value",
    "load_hopf_fixture_expected_value",
    "positive_hopf_sanity",
]
