"""Sanity checks for the hand-entered Yasui Figure 3, a=1 crossing table."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a1-crossing-table.json"


def arc_next(label: str, arc_counts: dict[str, int]) -> str:
    component = label[0]
    index = int(label[1:])
    return f"{component}{index % arc_counts[component] + 1}"


def component_pair(left: str, right: str) -> tuple[str, str]:
    return tuple(sorted((left, right)))  # type: ignore[return-value]


def main() -> int:
    payload = json.loads(INPUT.read_text())
    arc_counts = {component["id"]: component["arc_count"] for component in payload["components"]}
    counter: Counter[str] = Counter()
    for crossing in payload["crossings"]:
        counter.update(crossing["tuple"])

    bad_occurrences = {
        label: count
        for label, count in sorted(counter.items(), key=lambda item: (item[0][0], int(item[0][1:])))
        if count != 2
    }

    missing = []
    for component, count in arc_counts.items():
        for index in range(1, count + 1):
            label = f"{component}{index}"
            if label not in counter:
                missing.append(label)

    signed_sums = {("A", "B"): 0, ("A", "C"): 0, ("B", "C"): 0}
    crossing_details = []
    for crossing in payload["crossings"]:
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
        if x[0] != y[0]:
            signed_sums[component_pair(x[0], y[0])] += sign
        crossing_details.append(
            {
                "id": crossing["id"],
                "tuple": crossing["tuple"],
                "under": f"{x}->{z}",
                "over_direction": over_direction,
                "derived_sign": sign,
            }
        )

    derived_linking = {
        "-".join(pair): signed_sum // 2 for pair, signed_sum in signed_sums.items()
    }
    result = {
        "status": "needs-ab-crossing-review",
        "arc_occurrences": "pass" if not bad_occurrences and not missing else "fail",
        "bad_occurrences": bad_occurrences,
        "missing": missing,
        "signed_sums": {"-".join(pair): value for pair, value in signed_sums.items()},
        "derived_linking": derived_linking,
        "target_linking": {"A-B": 2, "A-C": 4, "B-C": 2},
        "mismatch": ["A-B"] if derived_linking["A-B"] != 2 else [],
        "crossing_details": crossing_details,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["arc_occurrences"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
