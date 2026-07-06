"""Certify the Akbulut 0805.1524 Figure 38 PD transcription.

This script checks only repo-local, machine-readable claims:

* the hand-entered XYZW/PD rows are structurally valid;
* the Z-only self-crossing projection reduces to the empty Gauss word by
  explicit R1/R2 word moves;
* the reported Akbulut-style "slide red components off Z through Y, then
  cancel Y/Z" story matches the E(1) intersection-form invariants at a coarse
  algebraic level.

It deliberately does not decode Akbulut's special-dot/upside-down convention as
an ordinary Kirby diagram and does not route this input to an invariant
evaluator.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import json
from pathlib import Path
import re
import sys
import time
from typing import Any

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    file_sha256,
    git_metadata,
    make_certificate,
    utc_now_iso,
)
from twisted_yetter.linking_matrix import determinant, rank, signature


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "akbulut" / "figure38-pd-code.json"
PD_SANITY_OUTPUT = (
    REPO_ROOT / "experiments" / "results" / "akbulut" / "figure38-pd-sanity-v1.json"
)
Z_UNKNOT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut"
    / "figure38-z-unknot-certificate-v1.json"
)
ALGEBRAIC_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut"
    / "figure38-y-slide-cancel-algebraic-v1.json"
)
LAB_NOTE_OUTPUT = (
    REPO_ROOT
    / "ctl-dogfood"
    / "lab-notes"
    / "2026-07-05-akbulut-figure38-pd-certification.json"
)

INPUT_SCHEMA = "twisted-yetter.akbulut-figure38-pd-input.v1"
PD_SANITY_SCHEMA = "twisted-yetter.akbulut-figure38-pd-sanity.v1"
Z_UNKNOT_SCHEMA = "twisted-yetter.akbulut-figure38-z-unknot.v1"
ALGEBRAIC_SCHEMA = "twisted-yetter.akbulut-figure38-y-slide-cancel-algebraic.v1"
LAB_NOTE_SCHEMA = "twisted-yetter/objective-lab-note/1"

LABEL_RE = re.compile(r"^([A-Z]+)([1-9][0-9]*)$")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Certify Akbulut Figure 38 PD transcription artifacts."
    )
    parser.add_argument("--input", type=Path, default=INPUT)
    parser.add_argument("--pd-sanity-output", type=Path, default=PD_SANITY_OUTPUT)
    parser.add_argument("--z-unknot-output", type=Path, default=Z_UNKNOT_OUTPUT)
    parser.add_argument("--algebraic-output", type=Path, default=ALGEBRAIC_OUTPUT)
    parser.add_argument("--lab-note-output", type=Path, default=LAB_NOTE_OUTPUT)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()

    started = utc_now_iso()
    start_time = time.monotonic()
    payload = json.loads(args.input.read_text())
    command = " ".join(sys.argv)
    if Path(sys.argv[0]).is_absolute():
        command = " ".join([str(Path(sys.argv[0]).relative_to(REPO_ROOT)), *sys.argv[1:]])
    reproduce = (
        "PYTHONPATH=src python experiments/scripts/akbulut_figure38_certify.py --write"
    )

    analysis = analyze_input(payload)
    pd_exact = pd_sanity_exact_output(payload, analysis, args.input)
    z_exact = z_unknot_exact_output(payload, analysis, args.input)
    algebraic_exact = algebraic_exact_output(payload, analysis, args.input)

    input_hash = file_sha256(args.input)
    common = {
        "command": command,
        "argv": [str(item) for item in sys.argv],
        "git": git_metadata(REPO_ROOT),
        "tool_versions": default_tool_versions(),
        "input_hash": input_hash,
        "generator_script": str(Path(__file__).relative_to(REPO_ROOT)),
        "reproduce_command": reproduce,
        "started_at_utc": started,
        "finished_at_utc": utc_now_iso(),
        "elapsed_seconds": int(round(time.monotonic() - start_time)),
        "repo_root": str(REPO_ROOT),
    }
    pd_cert = make_certificate(
        status="pass" if pd_exact["status"] == "pass" else "fail",
        exact_output=pd_exact,
        notes=[
            "Structural PD/cyclic-order validation only; source-image transcription is not rechecked here."
        ],
        **common,
    )
    z_cert = make_certificate(
        status="pass" if z_exact["status"] == "pass" else "fail",
        exact_output=z_exact,
        notes=[
            "Z unknot claim is scoped to the Z-only self-crossing projection obtained by deleting non-Z components."
        ],
        **common,
    )
    algebraic_cert = make_certificate(
        status="pass" if algebraic_exact["status"] == "pass" else "fail",
        exact_output=algebraic_exact,
        notes=[
            "Coarse algebraic handle-slide shadow only; does not certify the Akbulut convention or an evaluator-ready Kirby diagram."
        ],
        **common,
    )

    if args.write:
        write_certificate(args.pd_sanity_output, pd_cert)
        write_certificate(args.z_unknot_output, z_cert)
        write_certificate(args.algebraic_output, algebraic_cert)
        lab_note = lab_note_payload(
            payload=payload,
            pd_cert=pd_cert,
            z_cert=z_cert,
            algebraic_cert=algebraic_cert,
            paths={
                "input": args.input,
                "pd_sanity": args.pd_sanity_output,
                "z_unknot": args.z_unknot_output,
                "algebraic": args.algebraic_output,
                "lab_note": args.lab_note_output,
                "script": Path(__file__),
            },
            reproduce=reproduce,
        )
        args.lab_note_output.parent.mkdir(parents=True, exist_ok=True)
        args.lab_note_output.write_text(json.dumps(lab_note, indent=2, sort_keys=True) + "\n")

    summary = {
        "pd_sanity": pd_exact["status"],
        "z_unknot": z_exact["status"],
        "algebraic_slide_cancel": algebraic_exact["status"],
        "outputs": {
            "pd_sanity": rel(args.pd_sanity_output),
            "z_unknot": rel(args.z_unknot_output),
            "algebraic": rel(args.algebraic_output),
            "lab_note": rel(args.lab_note_output),
        },
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if all(value == "pass" for value in summary.values() if isinstance(value, str)) else 1


def write_certificate(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(dumps_certificate(payload))


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def component_and_index(label: str) -> tuple[str, int]:
    match = LABEL_RE.match(label)
    if match is None:
        raise ValueError(f"bad arc label: {label!r}")
    return match.group(1), int(match.group(2))


def analyze_input(payload: dict[str, Any]) -> dict[str, Any]:
    if payload.get("schema") != INPUT_SCHEMA:
        raise ValueError(f"unsupported schema: {payload.get('schema')!r}")

    components = list(payload["components"])
    component_ids = [component["id"] for component in components]
    if len(set(component_ids)) != len(component_ids):
        raise ValueError("component ids must be unique")
    component_by_id = {component["id"]: component for component in components}
    arc_orders = {
        component["id"]: [
            f"{component['id']}{index}" for index in range(1, int(component["arc_count"]) + 1)
        ]
        for component in components
    }
    arc_to_component = {
        arc: component_id for component_id, arcs in arc_orders.items() for arc in arcs
    }
    next_arc = {
        arc: arcs[(index + 1) % len(arcs)]
        for arcs in arc_orders.values()
        for index, arc in enumerate(arcs)
    }

    rows = [list(row) for row in payload["pd_code_rows"]]
    arc_counts: Counter[str] = Counter()
    label_errors: list[dict[str, Any]] = []
    for row_index, row in enumerate(rows, start=1):
        if len(row) != 4:
            label_errors.append({"row": row_index, "kind": "row-length", "row_value": row})
            continue
        for label in row:
            try:
                component_id, arc_index = component_and_index(label)
            except ValueError as error:
                label_errors.append({"row": row_index, "kind": "bad-label", "label": label})
                continue
            component = component_by_id.get(component_id)
            if component is None:
                label_errors.append(
                    {"row": row_index, "kind": "unknown-component", "label": label}
                )
                continue
            if arc_index < 1 or arc_index > int(component["arc_count"]):
                label_errors.append(
                    {
                        "row": row_index,
                        "kind": "arc-index-out-of-range",
                        "label": label,
                        "arc_count": component["arc_count"],
                    }
                )
                continue
            arc_counts[label] += 1

    declared_arcs = sorted(arc_to_component)
    bad_arc_counts = [
        {"arc": arc, "count": arc_counts.get(arc, 0)}
        for arc in declared_arcs
        if arc_counts.get(arc, 0) != 2
    ]
    extra_arc_counts = [
        {"arc": arc, "count": count}
        for arc, count in sorted(arc_counts.items())
        if arc not in arc_to_component
    ]
    seen_rows = Counter(tuple(row) for row in rows)
    duplicate_crossings = [
        {"tuple": list(row), "count": count}
        for row, count in sorted(seen_rows.items())
        if count != 1
    ]

    transition_errors = []
    crossing_records = []
    crossing_sums: Counter[tuple[str, str]] = Counter()
    visible_self_writhe_sums: Counter[str] = Counter()
    for index, row in enumerate(rows, start=1):
        crossing_id = f"x{index:02d}"
        x, y, z, w = row
        x_component = arc_to_component.get(x)
        y_component = arc_to_component.get(y)
        z_component = arc_to_component.get(z)
        w_component = arc_to_component.get(w)
        if x_component != z_component:
            transition_errors.append(
                {
                    "id": crossing_id,
                    "kind": "understrand-component-mismatch",
                    "tuple": row,
                }
            )
            continue
        if y_component != w_component:
            transition_errors.append(
                {
                    "id": crossing_id,
                    "kind": "overstrand-component-mismatch",
                    "tuple": row,
                }
            )
            continue
        if next_arc.get(x) != z:
            transition_errors.append(
                {
                    "id": crossing_id,
                    "kind": "bad-under-transition",
                    "tuple": row,
                    "expected": next_arc.get(x),
                    "actual": z,
                }
            )
            continue
        if next_arc.get(w) == y:
            over_direction = "W->Y"
            over_boundary_arc = w
            sign = 1
        elif next_arc.get(y) == w:
            over_direction = "Y->W"
            over_boundary_arc = y
            sign = -1
        else:
            transition_errors.append(
                {
                    "id": crossing_id,
                    "kind": "bad-over-transition",
                    "tuple": row,
                    "next_y": next_arc.get(y),
                    "next_w": next_arc.get(w),
                }
            )
            continue
        pair = tuple(sorted((x_component, y_component)))
        crossing_sums[pair] += sign
        if x_component == y_component:
            visible_self_writhe_sums[x_component] += sign
        crossing_records.append(
            {
                "id": crossing_id,
                "tuple": row,
                "under_component": x_component,
                "over_component": y_component,
                "component_pair": list(pair),
                "under_boundary_arc": x,
                "over_boundary_arc": over_boundary_arc,
                "over_direction": over_direction,
                "cyclic_sign": sign,
            }
        )

    intercomponent_odd_sums = []
    for pair, signed_sum in sorted(crossing_sums.items()):
        if pair[0] != pair[1] and signed_sum % 2 != 0:
            intercomponent_odd_sums.append(
                {"component_pair": list(pair), "signed_crossing_sum": signed_sum}
            )

    linking_matrix = []
    for left in component_ids:
        row = []
        for right in component_ids:
            if left == right:
                row.append(int(component_by_id[left]["framing"]))
            else:
                pair = tuple(sorted((left, right)))
                row.append(crossing_sums[pair] // 2)
        linking_matrix.append(row)

    return {
        "component_ids": component_ids,
        "component_by_id": component_by_id,
        "arc_orders": arc_orders,
        "arc_to_component": arc_to_component,
        "next_arc": next_arc,
        "rows": rows,
        "label_errors": label_errors,
        "bad_arc_counts": bad_arc_counts,
        "extra_arc_counts": extra_arc_counts,
        "duplicate_crossings": duplicate_crossings,
        "transition_errors": transition_errors,
        "intercomponent_odd_sums": intercomponent_odd_sums,
        "crossing_records": crossing_records,
        "crossing_sums": crossing_sums,
        "visible_self_writhe_sums": visible_self_writhe_sums,
        "linking_matrix": linking_matrix,
    }


def pd_sanity_exact_output(
    payload: dict[str, Any], analysis: dict[str, Any], input_path: Path
) -> dict[str, Any]:
    failures = (
        analysis["label_errors"]
        + analysis["bad_arc_counts"]
        + analysis["extra_arc_counts"]
        + analysis["duplicate_crossings"]
        + analysis["transition_errors"]
        + analysis["intercomponent_odd_sums"]
    )
    return {
        "schema": PD_SANITY_SCHEMA,
        "status": "pass" if not failures else "needs-review",
        "source_input": rel(input_path),
        "source": payload["source"],
        "claim_boundary": payload["claim_boundary"],
        "component_order": analysis["component_ids"],
        "component_arc_counts": {
            component["id"]: int(component["arc_count"]) for component in payload["components"]
        },
        "component_framings": {
            component["id"]: int(component["framing"]) for component in payload["components"]
        },
        "akbulut_component_semantics": {
            component["id"]: {
                "akbulut_color": component["akbulut_color"],
                "akbulut_role": component["akbulut_role"],
                "special_dot": component["special_dot"],
                "ordinary_kirby_role_asserted": component["ordinary_kirby_role_asserted"],
            }
            for component in payload["components"]
        },
        "crossing_count": len(analysis["rows"]),
        "arc_occurrence_status": "pass" if not analysis["bad_arc_counts"] else "fail",
        "bad_arc_counts": analysis["bad_arc_counts"],
        "extra_arc_counts": analysis["extra_arc_counts"],
        "label_errors": analysis["label_errors"],
        "duplicate_crossings": analysis["duplicate_crossings"],
        "transition_errors": analysis["transition_errors"],
        "intercomponent_odd_sums": analysis["intercomponent_odd_sums"],
        "cyclic_sign_rule": payload["conventions"]["cyclic_sign_rule_under_test"],
        "crossing_records": analysis["crossing_records"],
        "pair_signed_crossing_sums": {
            "--".join(pair): value for pair, value in sorted(analysis["crossing_sums"].items())
        },
        "visible_self_writhe_sums": dict(sorted(analysis["visible_self_writhe_sums"].items())),
        "linking_matrix_order": analysis["component_ids"],
        "framing_plus_intercomponent_linking_matrix": analysis["linking_matrix"],
        "not_evaluator_ready_reasons": [
            "Akbulut special-dot/upside-down convention has not been decoded",
            "Z special dot is not asserted to be an ordinary dotted 1-handle",
            "This is one Figure 38 side, not a certified exotic-pair input with H2 marking",
        ],
    }


def z_unknot_exact_output(
    payload: dict[str, Any], analysis: dict[str, Any], input_path: Path
) -> dict[str, Any]:
    component_id = "Z"
    events = z_self_crossing_events(analysis, component_id)
    initial_word = [event["crossing_id"] for event in events]
    moves, final_events = reduce_reidemeister_word(events)
    return {
        "schema": Z_UNKNOT_SCHEMA,
        "status": "pass" if not final_events else "needs-review",
        "source_input": rel(input_path),
        "component_id": component_id,
        "scope": "Z-only self-crossing projection after deleting all non-Z components",
        "claim": "Z underlying component is certified as an unknot only within the Z-only projection scope",
        "source_crossing_count": len(analysis["rows"]),
        "z_self_crossing_count": len(set(initial_word)),
        "initial_gauss_word": initial_word,
        "initial_events": events,
        "reidemeister_reduction_moves": moves,
        "final_gauss_word": [event["crossing_id"] for event in final_events],
        "terminal_diagram": "crossing-free unknot" if not final_events else "not-reduced",
        "claim_boundary": [
            "Does not certify Akbulut special-dot semantics",
            "Does not certify a Y/Z handle cancellation",
            "Does not certify an evaluator-ready Kirby diagram",
        ],
    }


def z_self_crossing_events(
    analysis: dict[str, Any], component_id: str
) -> list[dict[str, Any]]:
    event_by_boundary: dict[str, dict[str, Any]] = {}
    for record in analysis["crossing_records"]:
        if (
            record["under_component"] != component_id
            or record["over_component"] != component_id
        ):
            continue
        under_arc = record["under_boundary_arc"]
        over_arc = record["over_boundary_arc"]
        event_by_boundary[under_arc] = {
            "event_id": f"{record['id']}@{under_arc}",
            "crossing_id": record["id"],
            "boundary_arc": under_arc,
            "role": "under",
            "cyclic_sign": record["cyclic_sign"],
        }
        event_by_boundary[over_arc] = {
            "event_id": f"{record['id']}@{over_arc}",
            "crossing_id": record["id"],
            "boundary_arc": over_arc,
            "role": "over",
            "cyclic_sign": record["cyclic_sign"],
        }
    ordered_events = []
    for arc in analysis["arc_orders"][component_id]:
        event = event_by_boundary.get(arc)
        if event is not None:
            ordered_events.append(event)
    return ordered_events


def reduce_reidemeister_word(
    initial_events: list[dict[str, Any]]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    events = [dict(event) for event in initial_events]
    moves = []
    step = 1
    while events:
        r1 = find_r1(events)
        if r1 is not None:
            before = word(events)
            first, second = r1
            removed = [events[first], events[second]]
            events = remove_indices(events, [first, second])
            moves.append(
                {
                    "move_id": f"z-r{step:02d}",
                    "move": "R1",
                    "crossings": [removed[0]["crossing_id"]],
                    "removed_events": [event["event_id"] for event in removed],
                    "role_check": sorted(event["role"] for event in removed),
                    "before_word": before,
                    "after_word": word(events),
                }
            )
            step += 1
            continue
        r2 = find_r2(events)
        if r2 is not None:
            before = word(events)
            first, second = r2
            removed = [events[index] for index in [first[0], first[1], second[0], second[1]]]
            events = remove_indices(events, [first[0], first[1], second[0], second[1]])
            moves.append(
                {
                    "move_id": f"z-r{step:02d}",
                    "move": "R2",
                    "crossings": [events_id["crossing_id"] for events_id in removed[:2]],
                    "removed_events": [event["event_id"] for event in removed],
                    "role_check": {
                        "first_pair_roles": [removed[0]["role"], removed[1]["role"]],
                        "second_pair_roles": [removed[2]["role"], removed[3]["role"]],
                    },
                    "before_word": before,
                    "after_word": word(events),
                }
            )
            step += 1
            continue
        break
    return moves, events


def word(events: list[dict[str, Any]]) -> list[str]:
    return [event["crossing_id"] for event in events]


def remove_indices(events: list[dict[str, Any]], indices: list[int]) -> list[dict[str, Any]]:
    remove = set(indices)
    return [event for index, event in enumerate(events) if index not in remove]


def find_r1(events: list[dict[str, Any]]) -> tuple[int, int] | None:
    size = len(events)
    if size < 2:
        return None
    for index in range(size):
        next_index = (index + 1) % size
        if index == next_index:
            continue
        left = events[index]
        right = events[next_index]
        if left["crossing_id"] == right["crossing_id"] and {
            left["role"],
            right["role"],
        } == {"over", "under"}:
            return tuple(sorted((index, next_index)))
    return None


def find_r2(events: list[dict[str, Any]]) -> tuple[tuple[int, int], tuple[int, int]] | None:
    size = len(events)
    if size < 4:
        return None
    adjacent_pairs = []
    for index in range(size):
        next_index = (index + 1) % size
        if index == size - 1:
            continue
        adjacent_pairs.append((index, next_index))
    for pair_index, first in enumerate(adjacent_pairs):
        first_events = [events[first[0]], events[first[1]]]
        first_ids = [event["crossing_id"] for event in first_events]
        if first_ids[0] == first_ids[1]:
            continue
        for second in adjacent_pairs[pair_index + 1 :]:
            if set(first).intersection(second):
                continue
            second_events = [events[second[0]], events[second[1]]]
            second_ids = [event["crossing_id"] for event in second_events]
            if first_ids != second_ids:
                continue
            if all(
                first_events[offset]["role"] != second_events[offset]["role"]
                for offset in (0, 1)
            ):
                return first, second
    return None


def algebraic_exact_output(
    payload: dict[str, Any], analysis: dict[str, Any], input_path: Path
) -> dict[str, Any]:
    component_order = analysis["component_ids"]
    red_components = [
        component["id"]
        for component in payload["components"]
        if component["akbulut_color"] == "red"
    ]
    matrix = [list(row) for row in analysis["linking_matrix"]]
    index_by_component = {component: index for index, component in enumerate(component_order)}
    y_index = index_by_component["Y"]
    z_index = index_by_component["Z"]
    yz_linking = matrix[y_index][z_index]
    if yz_linking == 0:
        raise ValueError("cannot build algebraic slide certificate with lk(Y,Z)=0")

    slide_coefficients = {}
    slide_sequence = []
    for component in red_components:
        component_index = index_by_component[component]
        linking_to_z = matrix[component_index][z_index]
        if linking_to_z == 0:
            continue
        if (-linking_to_z) % yz_linking != 0:
            raise ValueError(f"non-integral slide coefficient for {component}")
        coefficient = -linking_to_z // yz_linking
        slide_coefficients[component] = coefficient
        slide_sequence.append(
            {
                "move_id": f"alg-slide-{len(slide_sequence) + 1:02d}",
                "component": component,
                "slide_over": "Y",
                "coefficient": coefficient,
                "reason": "kill algebraic linking with Z before Y/Z cancellation",
                "lk_with_Z_before": linking_to_z,
                "lk_with_Z_after": 0,
            }
        )

    transform = identity(len(component_order))
    for component, coefficient in slide_coefficients.items():
        transform[y_index][index_by_component[component]] += coefficient
    after_slide = multiply(transpose(transform), multiply(matrix, transform))
    red_z_after = {
        component: after_slide[index_by_component[component]][z_index]
        for component in red_components
    }

    remaining_indices = [index_by_component[component] for component in red_components]
    pair_indices = [y_index, z_index]
    final_matrix = schur_complement(after_slide, remaining_indices, pair_indices)
    final_signature = signature(final_matrix)
    final_rank = rank(final_matrix)
    final_determinant = determinant(final_matrix)
    final_parity = "odd" if any(row[index] % 2 for index, row in enumerate(final_matrix)) else "even"
    e1_checks = {
        "rank_10": final_rank == 10,
        "determinant_abs_1": abs(final_determinant) == 1,
        "signature_1_9_0": list(final_signature) == [1, 9, 0],
        "signature_value_minus_8": final_signature[0] - final_signature[1] == -8,
        "odd_form": final_parity == "odd",
    }
    pass_status = (
        all(value == 0 for value in red_z_after.values())
        and all(e1_checks.values())
        and determinant([[after_slide[y_index][y_index], after_slide[y_index][z_index]], [after_slide[z_index][y_index], after_slide[z_index][z_index]]])
        in {1, -1}
    )

    return {
        "schema": ALGEBRAIC_SCHEMA,
        "status": "pass" if pass_status else "needs-review",
        "source_input": rel(input_path),
        "scope": "coarse algebraic matrix check for the reported Akbulut slide/cancel story",
        "claim": "After sliding red components with nonzero Z-linking over Y and algebraically cancelling the Y/Z block, the remaining red-component form has E(1)-type coarse invariants.",
        "claim_boundary": [
            "Does not decode Akbulut's special-dot convention",
            "Does not certify the geometric handle-slide sequence",
            "Does not certify pi1 or a full topological identification",
            "Does not make the diagram evaluator-ready",
        ],
        "component_order": component_order,
        "red_component_order": red_components,
        "initial_framing_plus_linking_matrix": matrix,
        "initial_nonzero_linking_with_Z": {
            component: matrix[index_by_component[component]][z_index]
            for component in red_components
            if matrix[index_by_component[component]][z_index] != 0
        },
        "lk_Y_Z": yz_linking,
        "slide_sequence": slide_sequence,
        "basis_transform_columns_new_basis_in_old_basis": transform,
        "after_slide_matrix_order": component_order,
        "after_slide_matrix": after_slide,
        "red_linking_with_Z_after_slides": red_z_after,
        "cancelled_pair": {
            "components": ["Y", "Z"],
            "matrix": [
                [after_slide[y_index][y_index], after_slide[y_index][z_index]],
                [after_slide[z_index][y_index], after_slide[z_index][z_index]],
            ],
            "determinant": determinant(
                [
                    [after_slide[y_index][y_index], after_slide[y_index][z_index]],
                    [after_slide[z_index][y_index], after_slide[z_index][z_index]],
                ]
            ),
            "method": "integral Schur complement of the unimodular Y/Z block",
        },
        "final_matrix_order": red_components,
        "final_matrix_after_algebraic_cancel": final_matrix,
        "final_matrix_invariants": {
            "rank": final_rank,
            "determinant": final_determinant,
            "signature_tuple_positive_negative_zero": list(final_signature),
            "signature": final_signature[0] - final_signature[1],
            "parity": final_parity,
        },
        "e1_intersection_form_sanity": e1_checks,
        "interpretation_status": "matches-E1-coarse-intersection-form-sanity-not-full-topological-proof",
    }


def identity(size: int) -> list[list[int]]:
    return [[1 if row == col else 0 for col in range(size)] for row in range(size)]


def transpose(matrix: list[list[int]]) -> list[list[int]]:
    return [list(row) for row in zip(*matrix)]


def multiply(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    return [
        [
            sum(left[row][inner] * right[inner][col] for inner in range(len(right)))
            for col in range(len(right[0]))
        ]
        for row in range(len(left))
    ]


def schur_complement(
    matrix: list[list[int]], remaining_indices: list[int], pair_indices: list[int]
) -> list[list[int]]:
    block = [[Fraction(matrix[row][col]) for col in pair_indices] for row in pair_indices]
    inverse = invert_2x2(block)
    result: list[list[int]] = []
    for left in remaining_indices:
        row = []
        for right in remaining_indices:
            correction = sum(
                Fraction(matrix[left][pair_indices[i]])
                * inverse[i][j]
                * Fraction(matrix[pair_indices[j]][right])
                for i in range(2)
                for j in range(2)
            )
            value = Fraction(matrix[left][right]) - correction
            if value.denominator != 1:
                raise ValueError("Schur complement produced non-integral entry")
            row.append(int(value))
        result.append(row)
    return result


def invert_2x2(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    determinant_value = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    if determinant_value == 0:
        raise ValueError("cannot invert singular 2x2 block")
    return [
        [matrix[1][1] / determinant_value, -matrix[0][1] / determinant_value],
        [-matrix[1][0] / determinant_value, matrix[0][0] / determinant_value],
    ]


def lab_note_payload(
    *,
    payload: dict[str, Any],
    pd_cert: dict[str, Any],
    z_cert: dict[str, Any],
    algebraic_cert: dict[str, Any],
    paths: dict[str, Path],
    reproduce: str,
) -> dict[str, Any]:
    output_paths = {
        "input": paths["input"],
        "pd_sanity": paths["pd_sanity"],
        "z_unknot": paths["z_unknot"],
        "algebraic": paths["algebraic"],
    }
    artifact_records = []
    for key, path in output_paths.items():
        artifact_records.append(
            {
                "artifact_id": key,
                "repo_path": rel(path),
                "sha256": file_sha256(path) if path.exists() else "pending-write",
            }
        )
    artifact_records.append(
        {
            "artifact_id": "generator_script",
            "repo_path": rel(paths["script"]),
            "sha256": file_sha256(paths["script"]),
        }
    )

    pd_output = pd_cert["exact_output"]
    z_output = z_cert["exact_output"]
    algebraic_output_value = algebraic_cert["exact_output"]
    return {
        "schema": LAB_NOTE_SCHEMA,
        "note_id": "objective-note-2026-07-05-akbulut-figure38-pd-certification",
        "title": "Akbulut Figure 38 PD transcription and coarse algebraic certification",
        "created_at": utc_now_iso(),
        "created_by": "actor:codex",
        "status": "objective-certification-with-claim-boundaries",
        "scope": {
            "question": "Record and certify the Akbulut arXiv 0805.1524 Figure 38 PD code, component framings, Z unknot check, and coarse Y-slide/Z-cancel algebraic check.",
            "normative_source_policy": "This objective note summarizes machine-readable JSON artifacts; it does not promote chat text or legacy prose to theorem evidence.",
            "claim_boundary": "The Figure 38 Akbulut convention is recorded but not decoded as an ordinary Kirby evaluator input.",
        },
        "source_reference": {
            "reference_id": "akbulut-dolgachev-surface",
            "paper": payload["source"]["paper"],
            "arxiv": payload["source"]["arxiv"],
            "arxiv_version": payload["source"]["arxiv_version"],
            "doi": payload["source"]["doi"],
            "figure": payload["source"]["figure"],
            "source_snapshot_status": payload["source"]["source_snapshot_status"],
            "canonical_locator": "https://arxiv.org/abs/0805.1524",
        },
        "repo_snapshot": git_metadata(REPO_ROOT),
        "generator_script": rel(paths["script"]),
        "reproduce_command": reproduce,
        "artifact_records": artifact_records,
        "claims": [
            {
                "claim_id": "figure38-pd-structural-validation",
                "status": "ESTABLISHED" if pd_output["status"] == "pass" else "FAIL",
                "artifact": rel(paths["pd_sanity"]),
                "summary": {
                    "crossing_count": pd_output["crossing_count"],
                    "component_order": pd_output["component_order"],
                    "arc_occurrence_status": pd_output["arc_occurrence_status"],
                    "transition_error_count": len(pd_output["transition_errors"]),
                    "intercomponent_odd_sum_count": len(pd_output["intercomponent_odd_sums"]),
                },
            },
            {
                "claim_id": "figure38-component-framing-and-akbulut-semantics-recorded",
                "status": "ESTABLISHED",
                "artifact": rel(paths["input"]),
                "component_framings": pd_output["component_framings"],
                "akbulut_semantics": pd_output["akbulut_component_semantics"],
                "boundary": "Akbulut colors and Z special dot are recorded semantics, not ordinary Kirby role assertions.",
            },
            {
                "claim_id": "figure38-z-component-unknot-projection",
                "status": "ESTABLISHED" if z_output["status"] == "pass" else "FAIL",
                "artifact": rel(paths["z_unknot"]),
                "scope": z_output["scope"],
                "z_self_crossing_count": z_output["z_self_crossing_count"],
                "move_count": len(z_output["reidemeister_reduction_moves"]),
                "terminal_diagram": z_output["terminal_diagram"],
            },
            {
                "claim_id": "figure38-y-slide-z-cancel-coarse-algebraic-shadow",
                "status": "ESTABLISHED" if algebraic_output_value["status"] == "pass" else "FAIL",
                "artifact": rel(paths["algebraic"]),
                "scope": algebraic_output_value["scope"],
                "slide_sequence": algebraic_output_value["slide_sequence"],
                "final_matrix_invariants": algebraic_output_value["final_matrix_invariants"],
                "e1_intersection_form_sanity": algebraic_output_value[
                    "e1_intersection_form_sanity"
                ],
                "boundary": algebraic_output_value["interpretation_status"],
            },
            {
                "claim_id": "figure38-evaluator-readiness",
                "status": "BLOCKED_FOR_EVALUATION",
                "blocked_reasons": pd_output["not_evaluator_ready_reasons"],
            },
        ],
        "downstream_policy": {
            "may_use_as": [
                "audited Figure 38 PD transcription candidate",
                "component-framing label record",
                "Z-only unknot projection certificate",
                "coarse algebraic consistency certificate for the reported Akbulut slide/cancel story",
            ],
            "must_not_use_as": [
                "ordinary Kirby diagram with decoded dotted-handle semantics",
                "complete E(1) topological proof",
                "exotic invariant computation input",
                "n70 pass certificate",
            ],
        },
    }


if __name__ == "__main__":
    raise SystemExit(main())
