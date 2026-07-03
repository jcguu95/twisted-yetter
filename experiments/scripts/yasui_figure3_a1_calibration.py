"""Calibration report for Yasui Figure 3, a=1.

This script is deliberately not an evaluator.  It separates three layers:

1. the raw X Y Z W crossing table;
2. the provisional sign rule inferred from the local tuple convention;
3. the homology-target linking matrix from the component labels.

The report is meant to prevent accidental promotion of an uncalibrated
hand-transcribed diagram to evaluator input.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a1-crossing-table.json"
OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a1-calibration-v1.json"


def arc_next(label: str, arc_counts: dict[str, int]) -> str:
    component = label[0]
    index = int(label[1:])
    return f"{component}{index % arc_counts[component] + 1}"


def pair_key(left: str, right: str) -> str:
    return "-".join(sorted((left, right)))


def provisional_crossing_record(crossing: dict[str, Any], arc_counts: dict[str, int]) -> dict[str, Any]:
    x, y, z, w = crossing["tuple"]
    if arc_next(x, arc_counts) != z:
        raise ValueError(f"{crossing['id']} understrand is not oriented as X -> Z")
    if arc_next(y, arc_counts) == w:
        over_direction = "Y->W"
        sign = 1
    elif arc_next(w, arc_counts) == y:
        over_direction = "W->Y"
        sign = -1
    else:
        raise ValueError(f"{crossing['id']} overstrand endpoints are not adjacent")
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
    arc_counts = {component["id"]: component["arc_count"] for component in payload["components"]}
    target_matrix = payload["target_intersection_matrix"]
    component_order = [component["id"] for component in payload["components"]]
    target_linking = {}
    for i, left in enumerate(component_order):
        for j, right in enumerate(component_order):
            if i < j:
                target_linking[pair_key(left, right)] = target_matrix[i][j]

    records = [provisional_crossing_record(crossing, arc_counts) for crossing in payload["crossings"]]
    signed_sums: dict[str, int] = defaultdict(int)
    crossings_by_pair: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        pair = record["component_pair"]
        crossings_by_pair[pair].append(record)
        if pair in target_linking:
            signed_sums[pair] += record["provisional_sign"]

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

    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-calibration.v1",
        "status": "blocked-before-evaluator",
        "input": str(INPUT.relative_to(REPO_ROOT)),
        "raw_crossing_table_status": payload["status"],
        "target_linking": target_linking,
        "pair_reports": pair_reports,
        "self_twist_blockers": payload.get("self_twists", []),
        "interpretation": [
            "The raw arc bookkeeping is consistent.",
            "The A15 +1 twist is still a coupon-level notation, not explicit PD/local-piece crossings.",
            "The provisional sign rule agrees with A-C and B-C but not A-B.",
            "Because the A-B provisional signed sum is the negative of the target signed sum, the issue is consistent with a local sign-convention calibration problem rather than a raw crossing-table failure.",
        ],
        "next_actions": [
            "Expand the A15 +1 full twist using an explicit local convention.",
            "Calibrate the X Y Z W sign rule against a known positive crossing drawn in the same convention.",
            "Only after calibration produce an evaluator-ready LinkDiagram/PD artifact.",
        ],
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
