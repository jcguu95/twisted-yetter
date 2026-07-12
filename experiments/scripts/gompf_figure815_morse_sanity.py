"""Link-level sanity checks for draft Gompf-Stipsicz Figure 8.15 Morse inputs.

This script does not verify that the draft transcription matches the printed
Kirby diagram.  It only derives a signed blackboard-style linking matrix from
the already expanded Morse forms and records determinant/signature checks.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict, deque
from pathlib import Path
from typing import Any

from twisted_yetter.linking_matrix import determinant, rank, signature


JsonObject = dict[str, Any]


class UnionFind:
    def __init__(self) -> None:
        self.parent: dict[str, str] = {}

    def add(self, item: str) -> None:
        self.parent.setdefault(item, item)

    def find(self, item: str) -> str:
        self.add(item)
        parent = self.parent[item]
        if parent != item:
            parent = self.find(parent)
            self.parent[item] = parent
        return parent

    def union(self, left: str, right: str) -> None:
        root_left = self.find(left)
        root_right = self.find(right)
        if root_left != root_right:
            self.parent[root_right] = root_left

    def groups(self) -> dict[str, list[str]]:
        grouped: dict[str, list[str]] = defaultdict(list)
        for item in self.parent:
            grouped[self.find(item)].append(item)
        return {root: sorted(items) for root, items in grouped.items()}


def piece_of(strand: str) -> str:
    return strand.rsplit(".", 1)[0]


def side_of(strand: str) -> str:
    return strand.rsplit(".", 1)[1]


def side_coefficient(strand: str) -> int:
    side = side_of(strand)
    if side == "left":
        return 1
    if side == "right":
        return -1
    raise ValueError(f"unknown strand side: {strand!r}")


def sign_symbol(value: int) -> str:
    if value == 1:
        return "+"
    if value == -1:
        return "-"
    raise ValueError(f"not a sign: {value!r}")


def sign_value(value: object) -> int:
    if value in {"+", 1, "+1"}:
        return 1
    if value in {"-", -1, "-1"}:
        return -1
    raise ValueError(f"not a sign: {value!r}")


def canonical_component_name(strands: list[str]) -> str:
    pieces = sorted({piece_of(strand) for strand in strands})
    if all(piece.startswith("A") for piece in pieces):
        return "A"
    if len(pieces) == 1:
        return pieces[0]
    return "+".join(pieces)


def add_orientation_constraint(
    graph: dict[str, list[tuple[str, int]]],
    left: str,
    right: str,
) -> None:
    left_piece = piece_of(left)
    right_piece = piece_of(right)
    # A cap should connect opposite oriented endpoints:
    # coeff(left) * v_left_piece = - coeff(right) * v_right_piece.
    relation = -side_coefficient(left) * side_coefficient(right)
    graph[left_piece].append((right_piece, relation))
    graph[right_piece].append((left_piece, relation))


def solve_piece_orientations(
    pieces: set[str],
    caps: list[tuple[str, str]],
) -> tuple[dict[str, int], list[JsonObject], list[JsonObject]]:
    graph: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for left, right in caps:
        add_orientation_constraint(graph, left, right)

    orientation: dict[str, int] = {}
    conflicts: list[JsonObject] = []
    for piece in sorted(pieces):
        if piece in orientation:
            continue
        orientation[piece] = 1
        queue: deque[str] = deque([piece])
        while queue:
            current = queue.popleft()
            for neighbor, relation in graph[current]:
                expected = orientation[current] * relation
                if neighbor not in orientation:
                    orientation[neighbor] = expected
                    queue.append(neighbor)
                elif orientation[neighbor] != expected:
                    conflicts.append(
                        {
                            "piece": current,
                            "neighbor": neighbor,
                            "expected_neighbor_orientation": expected,
                            "actual_neighbor_orientation": orientation[neighbor],
                        }
                    )

    fixed_left_up_conflicts = []
    for left, right in caps:
        if side_coefficient(left) != -side_coefficient(right):
            fixed_left_up_conflicts.append({"cap": [left, right]})

    return orientation, conflicts, fixed_left_up_conflicts


def strand_orientation(strand: str, piece_orientation: dict[str, int]) -> int:
    return side_coefficient(strand) * piece_orientation[piece_of(strand)]


def replay_and_analyze(
    payload: JsonObject,
    *,
    expected_component_count: int = 10,
    expected_signature: int = -8,
) -> JsonObject:
    forms = payload["forms"]
    order: list[str] = []
    pieces: set[str] = set()
    caps: list[tuple[str, str]] = []
    union_find = UnionFind()

    for form in forms:
        kind = form["kind"]
        if kind == "cup":
            piece = form["piece"]
            pieces.add(piece)
            left = f"{piece}.left"
            right = f"{piece}.right"
            union_find.add(left)
            union_find.add(right)
            union_find.union(left, right)
        elif kind == "cap":
            left, right = form["strands"]
            caps.append((left, right))
            union_find.union(left, right)

    piece_orientation, orientation_conflicts, fixed_left_up_conflicts = solve_piece_orientations(
        pieces, caps
    )

    component_by_strand: dict[str, str] = {}
    component_groups = union_find.groups()
    component_names_by_root: dict[str, str] = {}
    for root, strands in component_groups.items():
        component_names_by_root[root] = canonical_component_name(strands)
    for root, strands in component_groups.items():
        for strand in strands:
            component_by_strand[strand] = component_names_by_root[root]

    component_order = sorted(set(component_by_strand.values()), key=lambda name: (name != "A", name))
    index_by_component = {component: index for index, component in enumerate(component_order)}
    matrix = [[0 for _ in component_order] for _ in component_order]
    crossing_records: list[JsonObject] = []
    missing_explicit_sign = 0
    explicit_sign_mismatches = 0

    for form_index, form in enumerate(forms):
        kind = form["kind"]
        if kind == "cup":
            piece = form["piece"]
            left = f"{piece}.left"
            right = f"{piece}.right"
            if form.get("at") == "far-left":
                insert_at = 0
            elif form.get("at") == "far-right":
                insert_at = len(order)
            elif "between" in form:
                before, after = form["between"]
                if order.index(after) != order.index(before) + 1:
                    raise ValueError(f"cup endpoints are not adjacent in replay: {form!r}")
                insert_at = order.index(before) + 1
            elif "after" in form:
                insert_at = order.index(form["after"]) + 1
            else:
                raise ValueError(f"unsupported cup placement: {form!r}")
            order[insert_at:insert_at] = [left, right]
        elif kind == "cap":
            left, right = form["strands"]
            if abs(order.index(left) - order.index(right)) != 1:
                raise ValueError(f"cap endpoints are not adjacent in replay: {form!r}")
            order = [strand for strand in order if strand not in {left, right}]
        elif kind == "cross":
            over = form["over"]
            under = form["under"]
            over_index = order.index(over)
            under_index = order.index(under)
            if abs(over_index - under_index) != 1:
                raise ValueError(f"crossing endpoints are not adjacent in replay: {form!r}")
            motion = "right" if over_index < under_index else "left"
            motion_sign = 1 if motion == "right" else -1
            inferred = (
                motion_sign
                * strand_orientation(over, piece_orientation)
                * strand_orientation(under, piece_orientation)
            )
            if "sign" in form:
                explicit = sign_value(form["sign"])
                if explicit != inferred:
                    explicit_sign_mismatches += 1
            else:
                missing_explicit_sign += 1
            sign = inferred

            over_component = component_by_strand[over]
            under_component = component_by_strand[under]
            if over_component == under_component:
                idx = index_by_component[over_component]
                matrix[idx][idx] += sign
                contribution = "self-writhe"
            else:
                left_idx = index_by_component[over_component]
                right_idx = index_by_component[under_component]
                matrix[left_idx][right_idx] += sign
                matrix[right_idx][left_idx] += sign
                contribution = "intercomponent-crossing-sum"
            crossing_records.append(
                {
                    "form_index": form_index,
                    "over": over,
                    "under": under,
                    "motion": motion,
                    "over_orientation": sign_symbol(strand_orientation(over, piece_orientation)),
                    "under_orientation": sign_symbol(strand_orientation(under, piece_orientation)),
                    "inferred_sign": inferred,
                    "used_sign": sign,
                    "explicit_sign": form.get("sign"),
                    "over_component": over_component,
                    "under_component": under_component,
                    "contribution": contribution,
                }
            )
            order[over_index], order[under_index] = order[under_index], order[over_index]
        elif kind == "kink":
            component = component_by_strand[form["strand"]]
            idx = index_by_component[component]
            matrix[idx][idx] += sign_value(form["sign"]) * int(form.get("times", 1))
        else:
            raise ValueError(f"unknown form kind: {kind!r}")

    if order:
        raise ValueError(f"replay did not close all strands: {order!r}")

    odd_intercomponent_sums = []
    for i, left_component in enumerate(component_order):
        for j in range(i + 1, len(component_order)):
            signed_sum = matrix[i][j]
            if signed_sum % 2 != 0:
                odd_intercomponent_sums.append(
                    {
                        "components": [left_component, component_order[j]],
                        "signed_crossing_sum": signed_sum,
                    }
                )
            matrix[i][j] = signed_sum // 2
            matrix[j][i] = signed_sum // 2

    matrix_tuple = tuple(tuple(row) for row in matrix)
    sig = signature(matrix_tuple)
    det = determinant(matrix_tuple)
    matrix_rank = rank(matrix_tuple)
    checks = {
        "all_crossings_have_used_signs": len(crossing_records) == sum(
            1 for record in crossing_records if record["used_sign"] in {-1, 1}
        ),
        "cap_consistent_orientation_solved": not orientation_conflicts,
        "fixed_all_births_left_up_has_no_cap_conflicts": not fixed_left_up_conflicts,
        "intercomponent_sums_even": not odd_intercomponent_sums,
        "determinant_abs_1": abs(det) == 1,
        "signature_matches_expected": sig[0] - sig[1] == expected_signature,
        "component_count_matches_expected": len(component_order) == expected_component_count,
    }
    blocking_check_names = [
        "all_crossings_have_used_signs",
        "cap_consistent_orientation_solved",
        "intercomponent_sums_even",
        "determinant_abs_1",
        "signature_matches_expected",
        "component_count_matches_expected",
    ]
    status = "pass" if all(checks[name] for name in blocking_check_names) else "needs-review"

    return {
        "schema": "twisted-yetter.gompf-stipsicz.figure815-morse-link-sanity.v1",
        "status": status,
        "mathematical_status": "DRAFT_DERIVED_LINK_SANITY_NOT_PRINTED_DIAGRAM_VERIFICATION",
        "source_input": payload.get("source"),
        "input_status": payload.get("status"),
        "component_order": component_order,
        "component_count": len(component_order),
        "piece_orientation_solution": {
            piece: sign_symbol(value) for piece, value in sorted(piece_orientation.items())
        },
        "orientation_convention": {
            "piece_left_orientation": "piece sign",
            "piece_right_orientation": "negative piece sign",
            "piece_signs": "solved from cap constraints; each connected orientation component is normalized by first piece = +",
            "fixed_all_births_left_up_conflicts": fixed_left_up_conflicts,
            "cap_orientation_conflicts": orientation_conflicts,
        },
        "crossing_counts": {
            "total_crossings": len(crossing_records),
            "missing_explicit_signs_in_input": missing_explicit_sign,
            "explicit_sign_mismatches_with_inferred": explicit_sign_mismatches,
        },
        "odd_intercomponent_sums": odd_intercomponent_sums,
        "framing_plus_linking_matrix": [list(row) for row in matrix_tuple],
        "determinant": det,
        "rank": matrix_rank,
        "nullity": len(matrix_tuple) - matrix_rank,
        "signature_triple_positive_negative_zero": list(sig),
        "signature": sig[0] - sig[1],
        "expected": {
            "component_count": expected_component_count,
            "signature": expected_signature,
            "determinant_abs": 1,
        },
        "checks": checks,
        "blocking_check_names": blocking_check_names,
        "crossing_records": crossing_records,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--write", type=Path)
    parser.add_argument("--expected-component-count", type=int, default=10)
    parser.add_argument("--expected-signature", type=int, default=-8)
    args = parser.parse_args()

    payload = json.loads(args.input.read_text())
    result = replay_and_analyze(
        payload,
        expected_component_count=args.expected_component_count,
        expected_signature=args.expected_signature,
    )
    result["input_path"] = str(args.input)
    if args.write is not None:
        args.write.parent.mkdir(parents=True, exist_ok=True)
        args.write.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "crossing_records"}, indent=2))


if __name__ == "__main__":
    main()
