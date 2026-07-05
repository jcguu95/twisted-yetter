"""Create Yasui Figure 3 (a=3) clean crossing-table input from hand PD data."""

from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a3-crossing-table.json"


RAW_CROSSINGS = """
C16 B13 C17 B12
C17 A28 C18 A27
C18 A37 C19 A36
C19 A46 C20 A45
C20 A1 C1 A54

B11 C16 B12 C15
A26 C15 A27 C14
A35 C14 A36 C13
A44 C13 A45 C12
A53 C12 A54 C11

A1 C2 A2 C1
A6 C3 A7 C2
A11 C4 A12 C3
A16 C5 A17 C4
B1 C6 B2 C5

C6 B3 C7 B2
C7 A18 C8 A17
C8 A13 C9 A12
C9 A8 C10 A7
C10 A3 C11 A2

A33 B11 A34 B10
A34 A26 A35 A25
A42 B10 A43 B9
A43 A25 A44 A24
A51 B9 A52 B8
A52 A24 A53 A23

A22 B8 A23 B7
B6 A22 B7 A21

B3 A15 B4 A14
B4 A10 B5 A9
B5 A5 B6 A4
A18 A14 A19 A13
A19 A9 A20 A8
A20 A4 A21 A3

A29 A39 A30 A38
A30 A48 A31 A47
A39 A49 A40 A48
A40 A32 A41 A31
A49 A33 A50 A32
A50 A42 A51 A41

B13 A29 B14 A28
B14 A38 B15 A37
B15 A47 B16 A46
B16 A5 B17 A6
B17 A10 B18 A11
B18 A15 B1 A16
"""


def arc_order(component: str, count: int) -> list[str]:
    return [f"{component}{index}" for index in range(1, count + 1)]


def next_map(orders: dict[str, list[str]]) -> dict[str, str]:
    result = {}
    for order in orders.values():
        for index, label in enumerate(order):
            result[label] = order[(index + 1) % len(order)]
    return result


def crossing_sign(tuple_: list[str], next_arc: dict[str, str]) -> int:
    _x, y, _z, w = tuple_
    if next_arc[y] == w:
        return -1
    if next_arc[w] == y:
        return 1
    raise ValueError(f"overstrand endpoints are not adjacent: {tuple_}")


def cyclic_distance(start: str, end: str, orders: dict[str, list[str]]) -> int:
    order = orders[start[0]]
    if end[0] != start[0]:
        raise ValueError(f"labels are on different components: {start}, {end}")
    left = order.index(start)
    right = order.index(end)
    return (right - left) % len(order)


def compressed_crossing_sign(tuple_: list[str], orders: dict[str, list[str]], next_arc: dict[str, str]) -> tuple[int, str]:
    """Return sign for compressed PD-like rows.

    The a=1 source used fully adjacent PD arcs.  The a=3 transcription is more
    compressed: the overpass endpoints may skip labels that belong to other
    crossings along the same overpass.  We orient the overpass by the shorter
    cyclic direction between Y and W.  This reduces to the a=1 rule in the
    adjacent case.
    """

    _x, y, _z, w = tuple_
    if next_arc[y] == w:
        return -1, "Y->W-adjacent"
    if next_arc[w] == y:
        return 1, "W->Y-adjacent"
    y_to_w = cyclic_distance(y, w, orders)
    w_to_y = cyclic_distance(w, y, orders)
    if y_to_w == w_to_y:
        raise ValueError(f"ambiguous compressed overpass direction: {tuple_}")
    if y_to_w < w_to_y:
        return -1, f"Y->W-compressed-distance-{y_to_w}"
    return 1, f"W->Y-compressed-distance-{w_to_y}"


def parse_crossings() -> list[list[str]]:
    rows = []
    for line in RAW_CROSSINGS.splitlines():
        line = line.strip()
        if not line:
            continue
        items = line.split()
        if len(items) != 4:
            raise ValueError(f"bad crossing line: {line!r}")
        rows.append(items)
    return rows


def main() -> int:
    orders = {
        "A": arc_order("A", 54),
        "B": arc_order("B", 18),
        "C": arc_order("C", 20),
    }
    next_arc = next_map(orders)
    crossings = []
    for index, tuple_ in enumerate(parse_crossings(), start=1):
        x, _y, z, _w = tuple_
        if next_arc[x] != z:
            raise ValueError(f"x{index:02d} understrand is not oriented X->Z: {tuple_}")
        sign, sign_source = compressed_crossing_sign(tuple_, orders, next_arc)
        crossings.append(
            {
                "id": f"x{index:02d}",
                "tuple": tuple_,
                "calibrated_sign": sign,
                "sign_source": sign_source,
            }
        )

    payload = {
        "schema": "twisted-yetter.yasui-figure-crossing-table.v1",
        "status": "needs-evaluator-artifact",
        "source": {
            "paper": "Kouichi Yasui, Small exotic rational surfaces without 1- and 3-handles",
            "arxiv": "0807.0373v2",
            "figure": "Figure 3",
            "case": "a=3",
            "topological_target": "CP2 # 2 CPbar2",
            "hand_transcription": "provided by user in Codex thread on 2026-07-04",
        },
        "components": [
            {
                "id": "A",
                "class_in_h_e_basis": {"h": 4, "e1": 0, "e2": 1},
                "framing": 15,
                "arc_count": 54,
                "arc_order": orders["A"],
            },
            {
                "id": "B",
                "class_in_h_e_basis": {"h": 1, "e1": 0, "e2": 0},
                "framing": 1,
                "arc_count": 18,
                "arc_order": orders["B"],
            },
            {
                "id": "C",
                "class_in_h_e_basis": {"h": 2, "e1": 1, "e2": 0},
                "framing": 3,
                "arc_count": 20,
                "arc_order": orders["C"],
            },
        ],
        "target_intersection_matrix": [
            [15, 4, 8],
            [4, 1, 2],
            [8, 2, 3],
        ],
        "oriented_diagram_linking_matrix": [
            [15, 4, 8],
            [4, 1, 2],
            [8, 2, 3],
        ],
        "conventions": {
            "component_orientation": "arc labels increase cyclically, e.g. A1 -> A2 -> ... -> A54 -> A1",
            "crossing_tuple": "X Y Z W",
            "understrand": "X -> Z",
            "overstrand": "the strand through Y and W, oriented by the component arc order",
            "cyclic_order": "X, Y, Z, W listed counterclockwise around the crossing",
            "sign_rule": "validated against the admitted a=1 input: Y->W gives -1 and W->Y gives +1; for compressed a=3 overpasses, choose the shorter cyclic direction between Y and W",
            "framing_rule": "component framing is the homology class square; self-curls are not drawn explicitly in this R1-normalized input",
        },
        "crossings": crossings,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"output": str(OUTPUT.relative_to(REPO_ROOT)), "crossing_count": len(crossings)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
