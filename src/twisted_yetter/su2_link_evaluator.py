"""Restricted exact SU(2)_2 colored framed link evaluator core.

This module is the first bare link-evaluation entry point for n18b.  It
evaluates source-backed local controls from ``LinkDiagram`` input and returns
JSON-ready exact values.  It deliberately does not implement Kirby colors,
twisted colors, ordinary surgery normalization, or closed 4D invariants.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Final, Literal, Mapping

from twisted_yetter.hopf_controls import positive_hopf_sanity
from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.su2_level2 import (
    LINK_DATA_CLAIM_LEVELS,
    QUANTUM_DIMENSIONS,
    RT_LINK_LEDGER_REFERENCE,
    RT_LINK_SOURCE_REFERENCE,
    SIMPLE_LABELS,
    TWIST_VALUES,
    QuadraticSurd,
    RootOfUnityPower,
    hopf_control_entry,
)

SU2_LINK_EVALUATOR_SCHEMA: Final = "twisted-yetter.su2-level2-link-evaluator-core.v1"

EVALUATOR_CLAIM_LEVEL: Final = {
    "claim_level": "computed evidence/restricted-source-backed-core",
    "source_boundary": "SOURCE NEEDED/local-convention controls inherited from n14/n16/n17",
    "scope": (
        "bare SU(2)_2 colored framed link values for empty links, no-crossing "
        "split links, and positive Hopf-shaped crossing controls"
    ),
    "not_scope": (
        "Kirby color, twisted color, ordinary surgery normalization, closed 4D "
        "invariant, exotic-pair data, or general planar RT recoupling evaluator"
    ),
    "restriction_reason": (
        "LinkDiagram currently records signed over/under crossings but not full "
        "planar adjacency, F-symbol gauge, or R-symbol convention data."
    ),
    "ledgers": [
        RT_LINK_LEDGER_REFERENCE,
        "wiki/understandings/elementary-link-controls.org",
        "wiki/understandings/hopf-and-crossing-controls.org",
    ],
    "source_record": RT_LINK_SOURCE_REFERENCE,
}

FRAMING_TWIST_CONVENTION: Final = {
    "formula": "multiply by theta_label^framing for each component",
    "twist_table": {
        label: TWIST_VALUES[label].to_jsonable() for label in SIMPLE_LABELS
    },
    "positive_framing_sign": LINK_DATA_CLAIM_LEVELS["twists"]["positive_framing_sign"],
    "claim_level": LINK_DATA_CLAIM_LEVELS["twists"]["claim_level"],
    "root_symbol": LINK_DATA_CLAIM_LEVELS["twists"]["root_symbol"],
}

SupportedKind = Literal["empty", "split_no_crossing", "positive_hopf"]


@dataclass(frozen=True)
class SU2LinkValue:
    """Exact symbolic value ``coefficient * zeta_16^exponent``."""

    coefficient: QuadraticSurd
    twist: RootOfUnityPower

    def __post_init__(self) -> None:
        if self.twist.order != 16:
            raise ValueError("SU(2)_2 link evaluator uses zeta_16 twist powers")

    def to_jsonable(self) -> dict[str, object]:
        return {
            "kind": "coefficient_times_twist",
            "coefficient": self.coefficient.to_jsonable(),
            "twist": self.twist.to_jsonable(),
        }


def evaluate_su2_level2_link(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> dict[str, object]:
    """Evaluate a supported SU(2)_2 colored framed link diagram.

    Unsupported diagram features return a structured ``status = blocked``
    payload instead of being guessed.  Invalid label maps still raise
    ``ValueError`` because they are not mathematical feature blockers.
    """

    labels = _validated_labels(diagram, labels_by_component)
    base = _base_payload(diagram, labels)

    if any(component.dotted for component in diagram.components):
        return _blocked(
            base,
            reason_id="dotted-components-unsupported",
            message="bare link evaluator does not interpret dotted Kirby components",
            required="undotted framed link components only",
        )

    if not diagram.crossings:
        return _pass(base, _evaluate_split_no_crossing(diagram, labels))

    hopf_blocker = _hopf_blocker(diagram)
    if hopf_blocker is not None:
        return _blocked(base, **hopf_blocker)

    return _pass(base, _evaluate_positive_hopf(diagram, labels))


def load_and_evaluate_su2_level2_link(
    fixture_path: str | Path,
    labels_by_component: Mapping[str, str],
) -> dict[str, object]:
    """Load a ``LinkDiagram`` JSON fixture and evaluate it through the core."""

    payload = json.loads(Path(fixture_path).read_text())
    return evaluate_su2_level2_link(LinkDiagram.from_json(payload), labels_by_component)


def stable_evaluator_json(payload: Mapping[str, object]) -> str:
    """Serialize an evaluator payload deterministically."""

    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def _evaluate_split_no_crossing(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> tuple[SupportedKind, SU2LinkValue, dict[str, object]]:
    coefficient = QuadraticSurd(1)
    twist_exponent = 0
    component_factors = []

    for component in diagram.components:
        label = labels_by_component[component.component_id]
        component_twist = TWIST_VALUES[label].exponent * component.framing
        coefficient *= QUANTUM_DIMENSIONS[label]
        twist_exponent += component_twist
        component_factors.append(
            {
                "component_id": component.component_id,
                "label": label,
                "framing": component.framing,
                "quantum_dimension": QUANTUM_DIMENSIONS[label].to_jsonable(),
                "twist_exponent_mod_16": RootOfUnityPower(16, component_twist).exponent,
            }
        )

    kind: SupportedKind = "empty" if not diagram.components else "split_no_crossing"
    return (
        kind,
        SU2LinkValue(coefficient, RootOfUnityPower(16, twist_exponent)),
        {
            "component_factors": component_factors,
            "formula": "product_i d_label_i * theta_label_i^framing_i",
        },
    )


def _evaluate_positive_hopf(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> tuple[SupportedKind, SU2LinkValue, dict[str, object]]:
    left, right = diagram.components
    left_label = labels_by_component[left.component_id]
    right_label = labels_by_component[right.component_id]
    twist_exponent = (
        TWIST_VALUES[left_label].exponent * left.framing
        + TWIST_VALUES[right_label].exponent * right.framing
    )
    return (
        "positive_hopf",
        SU2LinkValue(
            hopf_control_entry(left_label, right_label),
            RootOfUnityPower(16, twist_exponent),
        ),
        {
            "sanity": positive_hopf_sanity(diagram),
            "formula": "(S_ij / S_00) * product_i theta_label_i^framing_i",
            "unframed_hopf_value": hopf_control_entry(left_label, right_label).to_jsonable(),
        },
    )


def _base_payload(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> dict[str, object]:
    return {
        "schema": SU2_LINK_EVALUATOR_SCHEMA,
        "diagram_id": diagram.diagram_id,
        "component_ids": list(diagram.component_ids),
        "framings": list(diagram.framings),
        "crossing_count": len(diagram.crossings),
        "labels_by_component": dict(sorted(labels_by_component.items())),
        "framing_twist_convention": FRAMING_TWIST_CONVENTION,
        "claim": EVALUATOR_CLAIM_LEVEL,
    }


def _pass(
    base: Mapping[str, object],
    evaluated: tuple[SupportedKind, SU2LinkValue, dict[str, object]],
) -> dict[str, object]:
    supported_kind, value, evaluation_details = evaluated
    return {
        **base,
        "status": "pass",
        "supported_kind": supported_kind,
        "value": value.to_jsonable(),
        "evaluation_details": evaluation_details,
    }


def _blocked(
    base: Mapping[str, object],
    *,
    reason_id: str,
    message: str,
    required: str,
) -> dict[str, object]:
    return {
        **base,
        "status": "blocked",
        "blocker": {
            "reason_id": reason_id,
            "message": message,
            "required": required,
            "status": "blocked",
        },
    }


def _hopf_blocker(diagram: LinkDiagram) -> dict[str, str] | None:
    try:
        positive_hopf_sanity(diagram)
    except NotImplementedError as error:
        return {
            "reason_id": "general-crossing-diagram-unsupported",
            "message": str(error),
            "required": (
                "positive Hopf-shaped crossing record or future planar adjacency "
                "plus F/R-symbol evaluator"
            ),
        }
    return None


def _validated_labels(
    diagram: LinkDiagram,
    labels_by_component: Mapping[str, str],
) -> dict[str, str]:
    expected_ids = set(diagram.component_ids)
    supplied_ids = set(labels_by_component)
    if supplied_ids != expected_ids:
        missing = sorted(expected_ids.difference(supplied_ids))
        extra = sorted(supplied_ids.difference(expected_ids))
        raise ValueError(
            "label mapping must match components exactly; "
            f"missing={missing}, extra={extra}"
        )

    labels = dict(labels_by_component)
    for component_id, label in labels.items():
        if label not in SIMPLE_LABELS:
            raise ValueError(
                f"unknown SU(2)_2 simple label for component {component_id!r}: {label!r}"
            )
    return labels


__all__ = [
    "EVALUATOR_CLAIM_LEVEL",
    "FRAMING_TWIST_CONVENTION",
    "SU2_LINK_EVALUATOR_SCHEMA",
    "SU2LinkValue",
    "evaluate_su2_level2_link",
    "load_and_evaluate_su2_level2_link",
    "stable_evaluator_json",
]
