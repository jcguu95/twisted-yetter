"""Experimental ordinary Kirby-color summation over restricted core sectors.

This module implements only the n22 local-convention scaffold:
``omega = sum_i d_i X_i`` for SU(2)_2 labels, evaluated through the existing
restricted colored framed link evaluator core.  It is not a closed 4-manifold
invariant, not a sourced surgery formula, and not a twisted/decorated formula.
"""

from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.exact import from_jsonable
from twisted_yetter.link_diagram import LinkDiagram
from twisted_yetter.su2_link_evaluator import evaluate_su2_level2_link
from twisted_yetter.su2_level2 import (
    QUANTUM_DIMENSIONS,
    RT_LINK_LEDGER_REFERENCE,
    SIMPLE_LABELS,
    QuadraticSurd,
)

ORDINARY_KIRBY_COLOR_SCHEMA: Final = (
    "twisted-yetter.experimental-ordinary-kirby-color.v1"
)
KIRBY_COLOR_CONVENTION: Final = "experimental-ordinary-omega-v0"
HANDLE_SCOPE: Final = "restricted-core-supported-no-dotted-2-handle-framed-link-only"
CLAIM_LEVEL: Final = "experimental/local-convention"
NORMALIZATION_STATUS: Final = "SOURCE NEEDED"

SOURCE_STATUS_BY_SLOT: Final[dict[str, str]] = {
    "kirby_color_coefficients": "SOURCE NEEDED",
    "global_dimension_and_normalization": "SOURCE NEEDED",
    "signature_anomaly_framing_convention": "SOURCE NEEDED",
    "handle_slide_invariance_proof_scope": "SOURCE NEEDED",
    "one_two_cancellation_treatment": "SOURCE NEEDED",
    "two_three_cancellation_treatment": "SOURCE NEEDED",
    "closed_4_manifold_vs_2_handlebody_distinction": "SOURCE NEEDED",
}

CLAIM_BOUNDARY: Final = {
    "claim_level": CLAIM_LEVEL,
    "handle_scope": HANDLE_SCOPE,
    "normalization_status": NORMALIZATION_STATUS,
    "source_status": "SOURCE NEEDED slots inherited from n21 source-capture ledger",
    "ledger": "wiki/understandings/ordinary-kirby-color-source-capture.org",
    "link_evaluator_gate": "wiki/understandings/colored-framed-link-evaluator-gate.org",
    "rt_link_ledger": RT_LINK_LEDGER_REFERENCE,
    "not_scope": (
        "ordinary Crane-Yetter/Yetter invariant, closed 4-manifold invariant, "
        "signature normalization, dotted handles, general planar RT evaluation, "
        "twisted formula, decorated formula, or exotic claim"
    ),
}


def omega_coefficients() -> dict[str, QuadraticSurd]:
    """Return local coefficients for ``omega = sum_i d_i X_i``."""

    return {label: QUANTUM_DIMENSIONS[label] for label in SIMPLE_LABELS}


def evaluate_su2_level2_ordinary_kirby_color(
    diagram: LinkDiagram,
    *,
    closed_4_manifold_claim: bool = False,
) -> dict[str, object]:
    """Return a deterministic exact n22 certificate for a restricted diagram.

    Every label sector is sent through
    :func:`evaluate_su2_level2_link`.  If the restricted core blocks any sector,
    this function returns a structured blocked certificate instead of guessing
    the Kirby-color sum.  The ``closed_4_manifold_claim`` flag is intentionally
    refused while source slots remain missing.
    """

    _refuse_closed_claim_if_needed(closed_4_manifold_claim)

    omega = omega_coefficients()
    sectors: list[dict[str, object]] = []
    total_by_exponent: dict[int, QuadraticSurd] = {}
    blocked_sectors: list[dict[str, object]] = []

    for labels in itertools.product(SIMPLE_LABELS, repeat=len(diagram.components)):
        labels_by_component = dict(zip(diagram.component_ids, labels))
        omega_coefficient = _omega_assignment_coefficient(labels, omega)
        core_result = evaluate_su2_level2_link(diagram, labels_by_component)

        if core_result["status"] == "blocked":
            sector = _blocked_sector_payload(
                labels_by_component=labels_by_component,
                omega_coefficient=omega_coefficient,
                core_result=core_result,
            )
            sectors.append(sector)
            blocked_sectors.append(sector)
            continue

        link_coefficient, exponent = _core_value_parts(core_result)
        term_coefficient = omega_coefficient * link_coefficient
        total_by_exponent[exponent] = (
            total_by_exponent.get(exponent, QuadraticSurd(0)) + term_coefficient
        )
        sectors.append(
            _sector_payload(
                labels_by_component=labels_by_component,
                omega_coefficient=omega_coefficient,
                core_result=core_result,
                term_coefficient=term_coefficient,
                exponent=exponent,
            )
        )

    payload = {
        "schema": ORDINARY_KIRBY_COLOR_SCHEMA,
        "status": "blocked" if blocked_sectors else "pass",
        "node_id": "n22-ordinary-kirby-color-implementation",
        "diagram_id": diagram.diagram_id,
        "component_ids": list(diagram.component_ids),
        "framings": list(diagram.framings),
        "crossing_count": len(diagram.crossings),
        "kirby_color_convention": KIRBY_COLOR_CONVENTION,
        "kirby_color_formula": "omega = sum_i d_i X_i",
        "kirby_color_coefficients": {
            label: omega[label].to_jsonable() for label in SIMPLE_LABELS
        },
        "simple_labels": list(SIMPLE_LABELS),
        "sector_count": len(sectors),
        "sectors": sectors,
        "total_value": _cyclotomic_sum_payload(total_by_exponent),
        "source_status_by_slot": dict(SOURCE_STATUS_BY_SLOT),
        "handle_scope": HANDLE_SCOPE,
        "normalization_status": NORMALIZATION_STATUS,
        "claim_level": CLAIM_LEVEL,
        "closed_4_manifold_claim_allowed": False,
        "claim_boundary": CLAIM_BOUNDARY,
    }
    if blocked_sectors:
        payload["blocker"] = {
            "status": "blocked",
            "reason_id": "restricted-core-sector-blocked",
            "message": (
                "ordinary Kirby-color sector summation is blocked because at "
                "least one colored sector is outside the accepted restricted "
                "SU(2)_2 link evaluator core"
            ),
            "blocked_sector_count": len(blocked_sectors),
            "blocked_sectors": [
                {
                    "labels_by_component": sector["labels_by_component"],
                    "core_blocker": sector["core_blocker"],
                }
                for sector in blocked_sectors
            ],
        }
    return payload


def evaluate_ordinary_kirby_color(
    diagram: LinkDiagram,
    *,
    closed_4_manifold_claim: bool = False,
) -> dict[str, object]:
    """Backward-compatible alias for the n22 public entry point."""

    return evaluate_su2_level2_ordinary_kirby_color(
        diagram,
        closed_4_manifold_claim=closed_4_manifold_claim,
    )


def load_fixture_certificate(
    fixture_path: str | Path,
    *,
    closed_4_manifold_claim: bool = False,
) -> dict[str, object]:
    """Load a link-diagram fixture and evaluate the n22 local convention."""

    diagram = LinkDiagram.from_json(json.loads(Path(fixture_path).read_text()))
    certificate = evaluate_su2_level2_ordinary_kirby_color(
        diagram,
        closed_4_manifold_claim=closed_4_manifold_claim,
    )
    certificate["fixture_path"] = Path(fixture_path).as_posix()
    return certificate


def stable_ordinary_kirby_color_json(certificate: Mapping[str, object]) -> str:
    """Serialize an n22 certificate deterministically."""

    return json.dumps(certificate, indent=2, sort_keys=True)


def _refuse_closed_claim_if_needed(closed_4_manifold_claim: bool) -> None:
    if closed_4_manifold_claim and any(
        status == "SOURCE NEEDED" for status in SOURCE_STATUS_BY_SLOT.values()
    ):
        raise ValueError(
            "closed_4_manifold_claim=True is refused while ordinary Kirby-color "
            "source slots remain SOURCE NEEDED"
        )


def _omega_assignment_coefficient(
    labels: tuple[str, ...],
    omega: Mapping[str, QuadraticSurd],
) -> QuadraticSurd:
    coefficient = QuadraticSurd(1)
    for label in labels:
        coefficient *= omega[label]
    return coefficient


def _core_value_parts(core_result: Mapping[str, object]) -> tuple[QuadraticSurd, int]:
    value = core_result["value"]  # type: ignore[index]
    if not isinstance(value, dict):
        raise TypeError("core evaluator pass result must contain value object")
    coefficient = _quadratic_surd_from_json(value["coefficient"])  # type: ignore[index]
    twist = value["twist"]  # type: ignore[index]
    if not isinstance(twist, dict) or twist.get("order") != 16:
        raise ValueError("ordinary Kirby-color scaffold expects zeta_16 core twists")
    exponent = twist["exponent"]
    if isinstance(exponent, bool) or not isinstance(exponent, int):
        raise TypeError("core twist exponent must be an integer")
    return coefficient, exponent


def _quadratic_surd_from_json(payload: object) -> QuadraticSurd:
    if not isinstance(payload, dict) or payload.get("kind") != "Q(sqrt2)":
        raise TypeError("expected Q(sqrt2) coefficient JSON")
    return QuadraticSurd(
        from_jsonable(payload["rational"]),
        from_jsonable(payload["sqrt2"]),
    )


def _sector_payload(
    *,
    labels_by_component: Mapping[str, str],
    omega_coefficient: QuadraticSurd,
    core_result: Mapping[str, object],
    term_coefficient: QuadraticSurd,
    exponent: int,
) -> dict[str, object]:
    return {
        "status": "pass",
        "labels_by_component": dict(sorted(labels_by_component.items())),
        "omega_coefficient": omega_coefficient.to_jsonable(),
        "core_evaluator_status": core_result["status"],
        "core_supported_kind": core_result["supported_kind"],
        "link_value": core_result["value"],
        "term": {
            "kind": "Q(sqrt2)_times_root_of_unity",
            "coefficient": term_coefficient.to_jsonable(),
            "root": {
                "kind": "root_of_unity_power",
                "symbol": "zeta_16",
                "order": 16,
                "exponent": exponent,
            },
        },
    }


def _blocked_sector_payload(
    *,
    labels_by_component: Mapping[str, str],
    omega_coefficient: QuadraticSurd,
    core_result: Mapping[str, object],
) -> dict[str, object]:
    return {
        "status": "blocked",
        "labels_by_component": dict(sorted(labels_by_component.items())),
        "omega_coefficient": omega_coefficient.to_jsonable(),
        "core_evaluator_status": core_result["status"],
        "core_blocker": core_result["blocker"],
        "term": None,
    }


def _cyclotomic_sum_payload(total_by_exponent: Mapping[int, QuadraticSurd]) -> dict[str, object]:
    nonzero_terms = {
        exponent: coefficient
        for exponent, coefficient in total_by_exponent.items()
        if coefficient != QuadraticSurd(0)
    }
    return {
        "kind": "Q(sqrt2)[zeta_16]_sparse_sum",
        "terms": [
            {
                "exponent": exponent,
                "coefficient": nonzero_terms[exponent].to_jsonable(),
            }
            for exponent in sorted(nonzero_terms)
        ],
    }


__all__ = [
    "CLAIM_BOUNDARY",
    "CLAIM_LEVEL",
    "HANDLE_SCOPE",
    "KIRBY_COLOR_CONVENTION",
    "NORMALIZATION_STATUS",
    "ORDINARY_KIRBY_COLOR_SCHEMA",
    "SOURCE_STATUS_BY_SLOT",
    "evaluate_ordinary_kirby_color",
    "evaluate_su2_level2_ordinary_kirby_color",
    "load_fixture_certificate",
    "omega_coefficients",
    "stable_ordinary_kirby_color_json",
]
