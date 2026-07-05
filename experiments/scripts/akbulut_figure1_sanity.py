"""Sanity checks for Akbulut 0805.1524 Figure 1 transcription."""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "akbulut" / "figure1-e1-crossing-table.json"
OUTPUT = REPO_ROOT / "experiments" / "results" / "akbulut" / "figure1-e1-sanity-v1.json"


def metric_pair(left, right):
    total = int(left.get("h", 0)) * int(right.get("h", 0))
    for index in range(1, 10):
        total -= int(left.get(f"e{index}", 0)) * int(right.get(f"e{index}", 0))
    return total


def main() -> int:
    payload = json.loads(INPUT.read_text())
    components = payload["components"]
    component_ids = [component["id"] for component in components]
    arc_to_component = {}
    next_arc = {}
    for component in components:
        arcs = component["arc_order"]
        for index, arc in enumerate(arcs):
            arc_to_component[arc] = component["id"]
            next_arc[arc] = arcs[(index + 1) % len(arcs)]

    arc_counts = Counter()
    duplicate_crossings = []
    seen_crossings = Counter()
    crossing_records = []
    crossing_sums = defaultdict(int)
    errors = []
    for crossing in payload["crossings"]:
        crossing_tuple = tuple(crossing["tuple"])
        seen_crossings[crossing_tuple] += 1
        for label in crossing_tuple:
            arc_counts[label] += 1
        x, y, z, w = crossing_tuple
        if next_arc.get(x) != z:
            errors.append(
                {
                    "id": crossing["id"],
                    "kind": "bad-under-transition",
                    "expected": next_arc.get(x),
                    "actual": z,
                }
            )
            continue
        if next_arc.get(w) == y:
            over_direction = "W->Y"
            sign = 1
        elif next_arc.get(y) == w:
            over_direction = "Y->W"
            sign = -1
        else:
            errors.append(
                {
                    "id": crossing["id"],
                    "kind": "bad-over-transition",
                    "next_y": next_arc.get(y),
                    "next_w": next_arc.get(w),
                }
            )
            continue
        pair = tuple(sorted((arc_to_component[x], arc_to_component[y])))
        crossing_sums[pair] += sign
        crossing_records.append(
            {
                "id": crossing["id"],
                "tuple": list(crossing_tuple),
                "component_pair": list(pair),
                "over_direction": over_direction,
                "cyclic_sign": sign,
            }
        )
    duplicate_crossings = [
        {"tuple": list(crossing_tuple), "count": count}
        for crossing_tuple, count in sorted(seen_crossings.items())
        if count != 1
    ]
    bad_arc_counts = [
        {"arc": arc, "count": count}
        for arc, count in sorted(arc_counts.items())
        if count != 2
    ]

    visible_matrix = []
    for left in component_ids:
        row = []
        for right in component_ids:
            if left == right:
                row.append(int(crossing_sums[(left, left)]))
            else:
                pair_sum = crossing_sums[tuple(sorted((left, right)))]
                row.append(pair_sum / 2 if pair_sum % 2 else pair_sum // 2)
        visible_matrix.append(row)

    total_framing_matrix = []
    for left_index, left in enumerate(component_ids):
        row = []
        for right_index, right in enumerate(component_ids):
            if left == right:
                row.append(int(components[left_index]["framing"]))
            else:
                pair_sum = crossing_sums[tuple(sorted((left, right)))]
                row.append(pair_sum / 2 if pair_sum % 2 else pair_sum // 2)
        total_framing_matrix.append(row)

    target_matrix = [
        [
            metric_pair(left["class_in_h_e_basis"], right["class_in_h_e_basis"])
            for right in components
        ]
        for left in components
    ]
    mismatches = []
    for row_index, left in enumerate(component_ids):
        for column_index, right in enumerate(component_ids):
            if total_framing_matrix[row_index][column_index] != target_matrix[row_index][column_index]:
                mismatches.append(
                    {
                        "entry": [left, right],
                        "cyclic_total_matrix": total_framing_matrix[row_index][column_index],
                        "homology_target_matrix": target_matrix[row_index][column_index],
                    }
                )

    result = {
        "schema": "twisted-yetter.akbulut-figure1-sanity.v1",
        "status": "pass" if not bad_arc_counts and not duplicate_crossings and not errors and not mismatches else "needs-review",
        "source_input": str(INPUT.relative_to(REPO_ROOT)),
        "component_order": component_ids,
        "arc_occurrence_status": "pass" if not bad_arc_counts else "fail",
        "bad_arc_counts": bad_arc_counts,
        "duplicate_crossings": duplicate_crossings,
        "conversion_errors": errors,
        "cyclic_sign_rule": payload["conventions"]["cyclic_sign_rule_under_test"],
        "crossing_records": crossing_records,
        "visible_self_writhe_matrix": visible_matrix,
        "cyclic_total_framing_matrix": total_framing_matrix,
        "homology_target_matrix": target_matrix,
        "matrix_mismatches": mismatches,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
