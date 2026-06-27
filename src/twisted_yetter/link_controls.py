"""Elementary exact framed-link controls for the evaluator gate.

This module only covers no-crossing local RT/Kauffman controls: the empty
link, colored framed unknots, and split unlinks.  It deliberately refuses
crossing data, Hopf controls, Kirby colors, and any 4D normalization.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.su2_level2 import (
    QUANTUM_DIMENSIONS,
    RT_LINK_LEDGER_REFERENCE,
    RT_LINK_SOURCE_REFERENCE,
    SIMPLE_LABELS,
    TWIST_VALUES,
    QuadraticSurd,
    RootOfUnityPower,
)

ELEMENTARY_LINK_CONTROLS_CLAIM_LEVEL: Final = {
    "claim_level": "SOURCE NEEDED/local-convention/schema-test-safe",
    "ledger": RT_LINK_LEDGER_REFERENCE,
    "source_record": RT_LINK_SOURCE_REFERENCE,
    "scope": "RT/Kauffman local controls for no-crossing colored framed links",
    "not_scope": "Hopf/crossing evaluator, Kirby formula, or closed 4D invariant",
}


@dataclass(frozen=True)
class ElementaryLinkValue:
    """Symbolic value ``dimension * twist`` for elementary link controls."""

    dimension: QuadraticSurd
    twist: RootOfUnityPower

    def __post_init__(self) -> None:
        if self.twist.order != 16:
            raise ValueError("current SU(2)_2 elementary controls use zeta_16 twists")

    def __mul__(self, other: object) -> "ElementaryLinkValue":
        if not isinstance(other, ElementaryLinkValue):
            return NotImplemented
        return ElementaryLinkValue(
            self.dimension * other.dimension,
            RootOfUnityPower(16, self.twist.exponent + other.twist.exponent),
        )

    def to_jsonable(self) -> dict[str, object]:
        return {
            "kind": "dimension_times_twist",
            "dimension": self.dimension.to_jsonable(),
            "twist": self.twist.to_jsonable(),
        }


EMPTY_LINK_VALUE: Final = ElementaryLinkValue(QuadraticSurd(1), RootOfUnityPower(16, 0))


def colored_framed_unknot_value(label: str, framing: int = 0) -> ElementaryLinkValue:
    """Return the local target ``theta_label^framing * d_label`` exactly."""

    _check_label(label)
    if isinstance(framing, bool) or not isinstance(framing, int):
        raise TypeError("framing must be an integer")
    return ElementaryLinkValue(
        QUANTUM_DIMENSIONS[label],
        RootOfUnityPower(16, TWIST_VALUES[label].exponent * framing),
    )


def elementary_expected_value(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> ElementaryLinkValue:
    """Return the split no-crossing expected value for a colored diagram.

    The label mapping must match diagram components exactly.  Any crossing is
    rejected here so that n17/n18 must make an explicit evaluator decision.
    """

    if diagram.crossings:
        raise NotImplementedError("elementary link controls do not evaluate crossings")

    expected_ids = set(diagram.component_ids)
    supplied_ids = set(labels_by_component)
    if supplied_ids != expected_ids:
        missing = sorted(expected_ids.difference(supplied_ids))
        extra = sorted(supplied_ids.difference(expected_ids))
        raise ValueError(
            "label mapping must match components exactly; "
            f"missing={missing}, extra={extra}"
        )

    value = EMPTY_LINK_VALUE
    for component in diagram.components:
        value *= colored_framed_unknot_value(
            labels_by_component[component.component_id],
            component.framing,
        )
    return value


def load_fixture_expected_value(
    fixture_path: str | Path,
    labels_by_component: Mapping[str, str],
) -> ElementaryLinkValue:
    """Load a machine-readable toy fixture and compute its elementary target."""

    payload = json.loads(Path(fixture_path).read_text())
    return elementary_expected_value(LinkDiagram.from_json(payload), labels_by_component)


def control_certificate(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> dict[str, object]:
    """Return deterministic JSON-ready metadata for an elementary control."""

    value = elementary_expected_value(diagram, labels_by_component)
    return {
        "schema": "twisted-yetter.elementary-link-control.v1",
        "status": "pass",
        "diagram_id": diagram.diagram_id,
        "component_ids": list(diagram.component_ids),
        "framings": list(diagram.framings),
        "labels_by_component": dict(sorted(labels_by_component.items())),
        "expected_value": value.to_jsonable(),
        "claim": ELEMENTARY_LINK_CONTROLS_CLAIM_LEVEL,
    }


def _check_label(label: str) -> None:
    if label not in SIMPLE_LABELS:
        raise ValueError(f"unknown SU(2)_2 simple label: {label!r}")


__all__ = [
    "ELEMENTARY_LINK_CONTROLS_CLAIM_LEVEL",
    "EMPTY_LINK_VALUE",
    "ElementaryLinkValue",
    "colored_framed_unknot_value",
    "control_certificate",
    "elementary_expected_value",
    "load_fixture_expected_value",
]
