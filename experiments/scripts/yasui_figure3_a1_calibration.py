"""Calibration report for Yasui Figure 3, a=1.

This script is deliberately not an evaluator.  It separates three layers:

1. the raw X Y Z W crossing table;
2. explicit hand-calibrated visible crossing signs;
3. the clean-PD visible self-writhe/linking target and the homology-label matrix.

The report is meant to prevent accidental promotion of a hand-transcribed
diagram to evaluator input without recording the crossing signs.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a1-crossing-table.json"
OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a1-calibration-v1.json"


def arc_orders(payload: dict[str, Any]) -> dict[str, list[str]]:
    orders = {}
    for component in payload["components"]:
        component_id = component["id"]
        if "arc_order" in component:
            orders[component_id] = list(component["arc_order"])
        else:
            orders[component_id] = [
                f"{component_id}{index}" for index in range(1, component["arc_count"] + 1)
            ]
    return orders


def arc_next(label: str, orders: dict[str, list[str]]) -> str:
    component = label[0]
    order = orders[component]
    index = order.index(label)
    return order[(index + 1) % len(order)]


def pair_key(left: str, right: str) -> str:
    return "-".join(sorted((left, right)))


def provisional_crossing_record(crossing: dict[str, Any], orders: dict[str, list[str]]) -> dict[str, Any]:
    x, y, z, w = crossing["tuple"]
    if arc_next(x, orders) != z:
        raise ValueError(f"{crossing['id']} understrand is not oriented as X -> Z")
    if arc_next(y, orders) == w:
        over_direction = "Y->W"
    elif arc_next(w, orders) == y:
        over_direction = "W->Y"
    else:
        raise ValueError(f"{crossing['id']} overstrand endpoints are not adjacent")
    if "calibrated_sign" not in crossing:
        raise ValueError(f"{crossing['id']} has no calibrated_sign")
    sign = int(crossing["calibrated_sign"])
    if sign not in (-1, 1):
        raise ValueError(f"{crossing['id']} calibrated_sign must be +/-1")
    return {
        "id": crossing["id"],
        "tuple": crossing["tuple"],
        "under": f"{x}->{z}",
        "over_direction": over_direction,
        "provisional_sign": sign,
        "component_pair": pair_key(x[0], y[0]) if x[0] != y[0] else f"{x[0]}-{x[0]}",
    }


def main() -> int:
    payload = json.loads(INPUT.read_text())
    orders = arc_orders(payload)
    homology_matrix = payload["target_intersection_matrix"]
    target_matrix = payload.get("oriented_diagram_linking_matrix", homology_matrix)
    component_order = [component["id"] for component in payload["components"]]
    target_linking = {}
    for i, left in enumerate(component_order):
        for j, right in enumerate(component_order):
            if i < j:
                target_linking[pair_key(left, right)] = target_matrix[i][j]

    records = [provisional_crossing_record(crossing, orders) for crossing in payload["crossings"]]
    signed_sums: dict[str, int] = defaultdict(int)
    crossings_by_pair: dict[str, list[dict[str, Any]]] = defaultdict(list)
    self_writhe: dict[str, int] = {component: 0 for component in component_order}
    self_crossings: dict[str, list[dict[str, Any]]] = {component: [] for component in component_order}
    for record in records:
        pair = record["component_pair"]
        crossings_by_pair[pair].append(record)
        if pair in target_linking:
            signed_sums[pair] += record["provisional_sign"]
        left, right = pair.split("-")
        if left == right:
            self_writhe[left] += record["provisional_sign"]
            self_crossings[left].append(record)

    pair_reports = []
    for pair, target in sorted(target_linking.items()):
        provisional_sum = signed_sums[pair]
        target_sum = 2 * target
        pair_records = crossings_by_pair[pair]
        pair_reports.append(
            {
                "pair": pair,
                "crossing_ids": [record["id"] for record in pair_records],
                "provisional_signs": [record["provisional_sign"] for record in pair_records],
                "provisional_signed_sum": provisional_sum,
                "target_signed_sum": target_sum,
                "status": "pass" if provisional_sum == target_sum else "needs-calibration",
                "note": (
                    "A global flip of all signs for this pair would match the target."
                    if -provisional_sum == target_sum
                    else "Not fixed by a simple all-crossings sign flip for this pair."
                ),
            }
        )

    framing_reports = [
        {
            "component": component["id"],
            "recorded_framing": component["framing"],
            "visible_self_writhe": self_writhe[component["id"]],
            "effective_framing_correction": component["framing"] - self_writhe[component["id"]],
            "self_crossing_ids": [
                record["id"] for record in self_crossings[component["id"]]
            ],
            "status": (
                "pass-clean-pd-carries-framing"
                if self_writhe[component["id"]] == component["framing"]
                else "needs-framing-review"
            ),
        }
        for component in payload["components"]
    ]

    overall_status = (
        "pass"
        if all(report["status"] == "pass" for report in pair_reports)
        and all(report["status"] == "pass-clean-pd-carries-framing" for report in framing_reports)
        else "needs-sign-or-framing-review"
    )
    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-calibration.v1",
        "status": overall_status,
        "input": str(INPUT.relative_to(REPO_ROOT)),
        "raw_crossing_table_status": payload["status"],
        "oriented_diagram_target_linking": target_linking,
        "homology_label_intersection_matrix": homology_matrix,
        "pair_reports": pair_reports,
        "framing_reports": framing_reports,
        "self_twist_blockers": payload.get("self_twists", []),
        "interpretation": [
            "The raw arc bookkeeping is consistent.",
            "The A15, B1, and C1 positive self-twist blocks have been expanded into explicit subarcs and self-crossings.",
            "The tuple convention supplies incidence and over/under data, but not enough absolute page-position data to infer every sign from one quadrant convention.",
            "The hand-calibrated visible crossing signs are treated as first-class data, not inferred from a linear label order.",
            "With the current signs, every pair report must explicitly match the target before evaluator promotion.",
            "For components A, B, and C, the visible self-writhe agrees with the recorded component framing.",
            "The oriented source component C is opposite to the paper label direction, so evaluator markings use C=-(2h+e1).",
            "The clean PD now carries the component framings directly; the homology-label matrix remains the target intersection check.",
        ],
        "next_actions": [
            "Produce an evaluator-ready LinkDiagram/PD artifact with explicit component framings and a documented Kirby/oriented sign conversion.",
            "Then compare the nonstandard Yasui Figure 3 presentation against the standard (+1,-1,-1) unlink presentation.",
        ],
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
