"""Yasui Figure 2 CP2(a=1) crossing-table sanity and Tham 5.11 context.

This module is deliberately small and data-facing.  It validates the corrected
hand PD/crossing table, derives the framed linking matrix, and records the
dual/upside-down Tham 5.11 handle-context metadata used by the first CP2
sanity check.  It does not claim a theorem-level Crane-Yetter formula.
"""

from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
from typing import Any, Final, Mapping, Sequence

from twisted_yetter.linking_matrix import determinant, rank, signature


FIGURE2_INPUT_SCHEMA: Final = "twisted-yetter.yasui-figure2-cp2-crossing-table.v1"
FIGURE2_SANITY_SCHEMA: Final = "twisted-yetter.yasui-figure2-cp2-pd-sanity.v1"
THAM511_CONTEXT_SCHEMA: Final = "twisted-yetter.tham511-handle-context.v1"

COMPONENT_ORDER: Final = ("A", "B", "C")
EXPECTED_MATRIX: Final = ((4, 2, 4), (2, 1, 2), (4, 2, 4))
EXPECTED_SIGNATURE: Final = (1, 0, 2)
EXPECTED_RELATIONS: Final = (
    {"id": "r1", "coefficients_by_component": {"A": 1, "B": -2, "C": 0}},
    {"id": "r2", "coefficients_by_component": {"A": 0, "B": -2, "C": 1}},
)
COMPONENT_PULLBACK_TO_H: Final = {"A": 2, "B": 1, "C": 2}
LEGAL_SU2_2_Z2_ASSIGNMENTS: Final = (
    {"h_label": 0, "component_omega_labels": {"A": 0, "B": 0, "C": 0}},
    {"h_label": 1, "component_omega_labels": {"A": 0, "B": 1, "C": 0}},
)


def load_crossing_table(path: str | Path) -> dict[str, Any]:
    payload = json.loads(Path(path).read_text())
    if payload.get("schema") != FIGURE2_INPUT_SCHEMA:
        raise ValueError(f"unsupported schema: {payload.get('schema')!r}")
    return payload


def arc_orders(payload: Mapping[str, Any]) -> dict[str, list[str]]:
    return {
        str(component["id"]): list(component["arc_order"])
        for component in payload["components"]
    }


def arc_next_map(payload: Mapping[str, Any]) -> dict[str, str]:
    result: dict[str, str] = {}
    for component_id, order in arc_orders(payload).items():
        if not order:
            raise ValueError(f"component {component_id} has no arcs")
        for index, label in enumerate(order):
            result[label] = order[(index + 1) % len(order)]
    return result


def arc_component_map(payload: Mapping[str, Any]) -> dict[str, str]:
    result: dict[str, str] = {}
    for component_id, order in arc_orders(payload).items():
        for label in order:
            result[label] = component_id
    return result


def source_order(payload: Mapping[str, Any]) -> list[str]:
    return [str(component["id"]) for component in payload["components"]]


def source_framings(payload: Mapping[str, Any]) -> list[int]:
    return [int(component["framing"]) for component in payload["components"]]


def source_target_matrix(payload: Mapping[str, Any]) -> list[list[int]]:
    return [[int(entry) for entry in row] for row in payload["target_intersection_matrix"]]


def source_oriented_gauss_code(
    payload: Mapping[str, Any],
) -> tuple[list[list[int]], list[int], list[dict[str, Any]]]:
    """Return Sage-style oriented Gauss code data from the crossing table.

    A positive entry means overpass and a negative entry means underpass.
    ``calibrated_sign`` supplies the crossing sign list.
    """

    next_arc = arc_next_map(payload)
    arc_components = arc_component_map(payload)
    crossings = list(payload["crossings"])
    crossing_signs: list[int] = []
    records: list[dict[str, Any]] = []
    over_arc_by_crossing_id: dict[str, tuple[str, str]] = {}

    for crossing in crossings:
        crossing_id = str(crossing["id"])
        x, y, z, w = [str(label) for label in crossing["tuple"]]
        if next_arc.get(x) != z:
            raise ValueError(f"{crossing_id} understrand is not oriented as X -> Z")
        if next_arc.get(y) == w:
            over_direction = "Y->W"
            over_arc = (y, w)
        elif next_arc.get(w) == y:
            over_direction = "W->Y"
            over_arc = (w, y)
        else:
            raise ValueError(f"{crossing_id} overstrand endpoints are not adjacent")
        sign = int(crossing["calibrated_sign"])
        if sign not in {-1, 1}:
            raise ValueError(f"{crossing_id} calibrated_sign must be +/-1")
        over_arc_by_crossing_id[crossing_id] = over_arc
        crossing_signs.append(sign)
        pair = tuple(sorted((arc_components[x], arc_components[y])))
        records.append(
            {
                "id": crossing_id,
                "tuple": [x, y, z, w],
                "under": f"{x}->{z}",
                "over_direction": over_direction,
                "crossing_sign": sign,
                "component_pair": list(pair),
            }
        )

    component_words: list[list[int]] = []
    for component in payload["components"]:
        entries: list[int] = []
        order = list(component["arc_order"])
        for index, arc in enumerate(order):
            next_label = order[(index + 1) % len(order)]
            matches: list[int] = []
            for crossing_index, crossing in enumerate(crossings, start=1):
                crossing_id = str(crossing["id"])
                x, _y, z, _w = [str(label) for label in crossing["tuple"]]
                if (x, z) == (arc, next_label):
                    matches.append(-crossing_index)
                if over_arc_by_crossing_id[crossing_id] == (arc, next_label):
                    matches.append(crossing_index)
            if len(matches) != 1:
                raise ValueError(
                    f"arc transition {arc}->{next_label} matched "
                    f"{len(matches)} crossings: {matches}"
                )
            entries.append(matches[0])
        component_words.append(entries)
    return component_words, crossing_signs, records


def analyze_crossing_table(payload: Mapping[str, Any]) -> dict[str, Any]:
    orders = arc_orders(payload)
    next_arc = arc_next_map(payload)
    arc_components = arc_component_map(payload)
    components = source_order(payload)
    component_by_id = {str(component["id"]): component for component in payload["components"]}

    rows = [list(crossing["tuple"]) for crossing in payload["crossings"]]
    occurrences: Counter[str] = Counter(label for row in rows for label in row)
    bad_arc_counts = [
        {"arc": label, "count": occurrences.get(label, 0)}
        for component in components
        for label in orders[component]
        if occurrences.get(label, 0) != 2
    ]
    extra_arc_counts = [
        {"arc": label, "count": count}
        for label, count in sorted(occurrences.items())
        if label not in arc_components
    ]

    transition_errors: list[dict[str, Any]] = []
    crossing_records: list[dict[str, Any]] = []
    crossing_sums: Counter[tuple[str, str]] = Counter()
    visible_self_writhe_sums: Counter[str] = Counter()
    sign_adjacency_rule_disagreements: list[dict[str, Any]] = []

    for index, crossing in enumerate(payload["crossings"], start=1):
        crossing_id = str(crossing["id"])
        x, y, z, w = [str(label) for label in crossing["tuple"]]
        errors = []
        if arc_components.get(x) != arc_components.get(z):
            errors.append("understrand-component-mismatch")
        if arc_components.get(y) != arc_components.get(w):
            errors.append("overstrand-component-mismatch")
        if next_arc.get(x) != z:
            errors.append(f"bad-under-transition expected {next_arc.get(x)}")
        if next_arc.get(w) == y:
            derived_sign = 1
            over_direction = "W->Y"
        elif next_arc.get(y) == w:
            derived_sign = -1
            over_direction = "Y->W"
        else:
            derived_sign = 0
            over_direction = "bad"
            errors.append(
                f"bad-over-transition next_y={next_arc.get(y)} next_w={next_arc.get(w)}"
            )
        if errors:
            transition_errors.append(
                {"id": crossing_id, "row": index, "tuple": [x, y, z, w], "errors": errors}
            )
            continue
        calibrated_sign = int(crossing["calibrated_sign"])
        if calibrated_sign != derived_sign:
            sign_adjacency_rule_disagreements.append(
                {
                    "id": crossing_id,
                    "tuple": [x, y, z, w],
                    "calibrated_sign": calibrated_sign,
                    "derived_sign": derived_sign,
                    "sign_source": crossing.get("sign_source"),
                }
            )
        left = arc_components[x]
        right = arc_components[y]
        pair = tuple(sorted((left, right)))
        crossing_sums[pair] += calibrated_sign
        if left == right:
            visible_self_writhe_sums[left] += calibrated_sign
        crossing_records.append(
            {
                "id": crossing_id,
                "tuple": [x, y, z, w],
                "under_component": left,
                "over_component": right,
                "component_pair": list(pair),
                "over_direction": over_direction,
                "crossing_sign": calibrated_sign,
            }
        )

    intercomponent_odd_sums = [
        {"component_pair": list(pair), "signed_crossing_sum": signed_sum}
        for pair, signed_sum in sorted(crossing_sums.items())
        if pair[0] != pair[1] and signed_sum % 2 != 0
    ]

    matrix: list[list[int]] = []
    for left in components:
        row: list[int] = []
        for right in components:
            if left == right:
                row.append(int(component_by_id[left]["framing"]))
            else:
                row.append(crossing_sums[tuple(sorted((left, right)))] // 2)
        matrix.append(row)

    matrix_tuple = tuple(tuple(row) for row in matrix)
    signature_triple = signature(matrix_tuple)
    failures: list[dict[str, Any]] = []
    failures.extend({"kind": "bad-arc-count", **item} for item in bad_arc_counts)
    failures.extend({"kind": "extra-arc-count", **item} for item in extra_arc_counts)
    failures.extend({"kind": "transition-error", **item} for item in transition_errors)
    failures.extend({"kind": "odd-intercomponent-sum", **item} for item in intercomponent_odd_sums)
    if matrix_tuple != EXPECTED_MATRIX:
        failures.append(
            {
                "kind": "matrix-mismatch",
                "actual": matrix,
                "expected": [list(row) for row in EXPECTED_MATRIX],
            }
        )
    if determinant(matrix_tuple) != 0:
        failures.append({"kind": "determinant-mismatch", "actual": determinant(matrix_tuple)})
    if rank(matrix_tuple) != 1:
        failures.append({"kind": "rank-mismatch", "actual": rank(matrix_tuple)})
    if signature_triple != EXPECTED_SIGNATURE:
        failures.append(
            {"kind": "signature-mismatch", "actual": list(signature_triple)}
        )

    return {
        "schema": FIGURE2_SANITY_SCHEMA,
        "status": "pass" if not failures else "needs-review",
        "component_order": components,
        "component_arc_counts": {component: len(orders[component]) for component in components},
        "crossing_count": len(rows),
        "arc_occurrence_status": "pass" if not bad_arc_counts and not extra_arc_counts else "fail",
        "bad_arc_counts": bad_arc_counts,
        "extra_arc_counts": extra_arc_counts,
        "transition_errors": transition_errors,
        "sign_adjacency_rule_disagreements": sign_adjacency_rule_disagreements,
        "sign_rule_note": (
            "The current Figure 2 signs are provisional XYZW/arc-order-derived "
            "signs, not independently hand-calibrated from the source image.  "
            "They are enough for matrix sanity bookkeeping but not yet enough "
            "for a theorem-level RT comparison claim."
        ),
        "intercomponent_odd_sums": intercomponent_odd_sums,
        "crossing_records": crossing_records,
        "pair_signed_crossing_sums": {
            "--".join(pair): signed_sum
            for pair, signed_sum in sorted(crossing_sums.items())
        },
        "pair_linking_numbers": {
            "--".join(pair): signed_sum // 2
            for pair, signed_sum in sorted(crossing_sums.items())
            if pair[0] != pair[1]
        },
        "visible_self_writhe_sums": dict(sorted(visible_self_writhe_sums.items())),
        "recorded_total_framings": {
            component: int(component_by_id[component]["framing"]) for component in components
        },
        "framing_corrections_from_visible_blackboard_writhe": {
            component: int(component_by_id[component]["framing"])
            - int(visible_self_writhe_sums.get(component, 0))
            for component in components
        },
        "framing_plus_intercomponent_linking_matrix": matrix,
        "expected_matrix": [list(row) for row in EXPECTED_MATRIX],
        "determinant": determinant(matrix_tuple),
        "rank": rank(matrix_tuple),
        "nullity": len(matrix_tuple) - rank(matrix_tuple),
        "signature_triple_positive_negative_zero": list(signature_triple),
        "signature": signature_triple[0] - signature_triple[1],
        "failures": failures,
    }


def relation_vector(relation: Mapping[str, Any], components: Sequence[str]) -> list[int]:
    coefficients = relation["coefficients_by_component"]
    return [int(coefficients.get(component, 0)) for component in components]


def matrix_vector_product(matrix: Sequence[Sequence[int]], vector: Sequence[int]) -> list[int]:
    return [sum(int(row[index]) * int(vector[index]) for index in range(len(vector))) for row in matrix]


def legal_z2_assignments() -> list[dict[str, Any]]:
    return [
        {
            "h_label": item["h_label"],
            "component_order": list(COMPONENT_ORDER),
            "component_omega_labels": [
                item["component_omega_labels"][component] for component in COMPONENT_ORDER
            ],
            "component_omega_labels_by_id": dict(item["component_omega_labels"]),
        }
        for item in LEGAL_SU2_2_Z2_ASSIGNMENTS
    ]


def tham511_context(payload: Mapping[str, Any], analysis: Mapping[str, Any]) -> dict[str, Any]:
    matrix = analysis["framing_plus_intercomponent_linking_matrix"]
    radical_relation_checks = []
    for relation in EXPECTED_RELATIONS:
        vector = relation_vector(relation, COMPONENT_ORDER)
        product = matrix_vector_product(matrix, vector)
        radical_relation_checks.append(
            {
                "relation_id": relation["id"],
                "component_order": list(COMPONENT_ORDER),
                "vector": vector,
                "matrix_times_vector": product,
                "is_in_radical": product == [0, 0, 0],
            }
        )

    relation_matrix_rows = [
        relation_vector(relation, COMPONENT_ORDER) for relation in EXPECTED_RELATIONS
    ]
    relation_rank = rank(relation_matrix_rows)
    quotient_rank = len(COMPONENT_ORDER) - relation_rank
    return {
        "schema": THAM511_CONTEXT_SCHEMA,
        "status": "WORKING_HYPOTHESIS_NOT_THEOREM",
        "input_schema": payload["schema"],
        "source_input_id": payload["diagram_id"],
        "mathematical_status": "WORKING_HYPOTHESIS_NOT_THEOREM",
        "claim_boundary": (
            "Records a Tham 5.11-compatible working context for a CP2 sanity "
            "check.  It is not a theorem, not a general Crane-Yetter formula, "
            "and not evidence for exotic smooth detection."
        ),
        "source_handle_counts": {"0": 1, "1": 0, "2": 3, "3": 2, "4": 1},
        "tham511_dual_upside_down_handle_counts": {
            "0": 1,
            "1": 2,
            "2": 3,
            "3": 0,
            "4": 1,
        },
        "dual_upside_down_interpretation": {
            "status": "WORKING_UNDERSTANDING_NOT_THEOREM",
            "original_three_handles": "interpreted as Tham 5.11 one-handle maps",
            "one_handle_scalar_factor": "GLOBAL_DIMENSION^-1 per original 3-handle",
            "special_dotted_projector_status": (
                "not present in this Yasui Figure 2 input; no cut-and-vacuum "
                "projection rule is applied"
            ),
        },
        "component_order": list(COMPONENT_ORDER),
        "framing_plus_intercomponent_linking_matrix": matrix,
        "dual_d2_constraints": [
            {
                "id": relation["id"],
                "coefficients_by_component": dict(relation["coefficients_by_component"]),
                "interpretation": (
                    "dual one-handle d2 constraint on 2-handle coefficients; "
                    "equivalently the corresponding vector is a radical vector "
                    "of the source degenerate linking matrix"
                ),
            }
            for relation in EXPECTED_RELATIONS
        ],
        "radical_relation_checks": radical_relation_checks,
        "dual_d2_rank": relation_rank,
        "h2_kernel": {
            "description": (
                "In the dual/upside-down Tham 5.11 direction, H2 is ker(d2) "
                "for the two 1-handles and three 2-handles."
            ),
            "rank": quotient_rank,
            "generator": "h",
            "component_pullback_to_h": dict(COMPONENT_PULLBACK_TO_H),
        },
        "legal_character_assignments": {
            "category": "SU(2)_2 / Z2 universal grading",
            "rule": "component label is h_label times component_pullback_to_h modulo 2",
            "assignments": legal_z2_assignments(),
        },
        "normalization_working_hypothesis": {
            "one_handle_factor": "GLOBAL_DIMENSION^-1 per dual Tham 5.11 one-handle",
            "source_three_handle_count": 2,
            "dual_one_handle_count": 2,
            "total_factor": "GLOBAL_DIMENSION^-2",
            "rt_framing_convention": (
                "The target total framings come from the classes 2h,h,2h. "
                "When evaluating the explicit planar PD/braid, use extra "
                "framing = target total framing - visible blackboard self-writhe."
            ),
            "sign_status": (
                "Figure 2 crossing signs are provisional XYZW-derived signs; "
                "source-image hand calibration remains required before treating "
                "the RT comparison as mathematical evidence."
            ),
            "status": "WORKING_HYPOTHESIS_NOT_THEOREM",
        },
    }


__all__ = [
    "COMPONENT_ORDER",
    "COMPONENT_PULLBACK_TO_H",
    "EXPECTED_MATRIX",
    "EXPECTED_RELATIONS",
    "EXPECTED_SIGNATURE",
    "FIGURE2_INPUT_SCHEMA",
    "FIGURE2_SANITY_SCHEMA",
    "THAM511_CONTEXT_SCHEMA",
    "analyze_crossing_table",
    "arc_next_map",
    "arc_orders",
    "legal_z2_assignments",
    "load_crossing_table",
    "relation_vector",
    "source_framings",
    "source_order",
    "source_oriented_gauss_code",
    "source_target_matrix",
    "tham511_context",
]
