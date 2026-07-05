"""Convert Yasui Figure 3 (a=1) crossing input to braid evaluator payloads.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_to_braid.sage.py

The hand transcription records ``X Y Z W`` crossings, where ``X -> Z`` is the
understrand and the overstrand direction is recovered from component arc order.
The tuple data records incidence and over/under information.  It does not
record enough absolute page-position data to infer every crossing sign from a
single local quadrant convention.  Therefore the admitted input carries
explicit hand-calibrated crossing signs.  In the clean PD, the A, B, and C
self-twist blocks are all expanded into actual self-crossings, giving
``AA=3, BB=1, CC=3, AB=2, AC=-4, BC=-2``.  Equivalently, the source-oriented
component ``C`` represents ``-(2h+e1)``.
"""

from __future__ import annotations

import json
from itertools import permutations, product
from pathlib import Path
import sys

from sage.all import ZZ
from sage.env import SAGE_VERSION
from sage.knots.link import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a1-crossing-table.json"
OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a1-braid-payload-v1.json"
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.local_piece import (  # noqa: E402
    braid_closure_data,
    braid_closure_linking_matrix,
    braid_program,
)


def source_payload():
    return json.loads(INPUT.read_text())


def source_order(payload):
    return [component["id"] for component in payload["components"]]


def source_framings(payload):
    return [int(component["framing"]) for component in payload["components"]]


def source_linking_matrix(payload):
    return [[int(entry) for entry in row] for row in payload["target_intersection_matrix"]]


def arc_component_map(payload):
    result = {}
    for component in payload["components"]:
        for arc in component["arc_order"]:
            result[arc] = component["id"]
    return result


def arc_next_map(payload):
    result = {}
    for component in payload["components"]:
        arcs = list(component["arc_order"])
        for index, arc in enumerate(arcs):
            result[arc] = arcs[(index + 1) % len(arcs)]
    return result


def source_oriented_gauss_code(payload, switched_pairs=None):
    """Return ``(component_words, crossing_signs, records)`` for Sage ``Link``.

    In Sage's oriented Gauss code, a positive entry means the component passes
    over the crossing and a negative entry means it passes under.  The separate
    crossing-sign list uses the explicit ``calibrated_sign`` field in the
    source crossing table.  The tuple still supplies the oriented Gauss-code
    incidence and over/under data.
    """

    # ``switched_pairs`` belongs to the derived evaluator-calibration layer.  It
    # must not be confused with the source crossing table.
    switched_pairs = {tuple(sorted(pair)) for pair in (switched_pairs or [])}
    next_arc = arc_next_map(payload)
    arc_components = arc_component_map(payload)
    crossings = payload["crossings"]
    crossing_signs = []
    records = []
    over_arc_by_crossing_id = {}
    for crossing in crossings:
        x, y, z, w = crossing["tuple"]
        if next_arc[x] != z:
            raise ValueError(f"{crossing['id']} understrand is not oriented as X -> Z")
        if next_arc[y] == w:
            over_direction = "Y->W"
            over_arc = (y, w)
        elif next_arc[w] == y:
            over_direction = "W->Y"
            over_arc = (w, y)
        else:
            raise ValueError(f"{crossing['id']} overstrand endpoints are not adjacent")
        over_arc_by_crossing_id[crossing["id"]] = over_arc
        if "calibrated_sign" not in crossing:
            raise ValueError(f"{crossing['id']} has no calibrated_sign")
        sign = int(crossing["calibrated_sign"])
        if sign not in (-1, 1):
            raise ValueError(f"{crossing['id']} calibrated_sign must be +/-1")
        pair = tuple(sorted((arc_components[x], arc_components[y])))
        switched = pair in switched_pairs and pair[0] != pair[1]
        if switched:
            sign = -sign
        crossing_signs.append(sign)
        records.append(
            {
                "id": crossing["id"],
                "tuple": crossing["tuple"],
                "under": f"{x}->{z}",
                "over_direction": over_direction,
                "crossing_sign": sign,
                "component_pair": list(pair),
                "crossing_switched_for_kirby_calibration": switched,
            }
        )

    component_words = []
    for component in payload["components"]:
        entries = []
        arcs = component["arc_order"]
        for index, arc in enumerate(arcs):
            next_label = arcs[(index + 1) % len(arcs)]
            matches = []
            for crossing_index, crossing in enumerate(crossings, start=1):
                x, y, z, w = crossing["tuple"]
                entry_sign = 1
                pair = tuple(sorted((arc_components[x], arc_components[y])))
                if pair in switched_pairs and pair[0] != pair[1]:
                    entry_sign = -1
                if (x, z) == (arc, next_label):
                    matches.append(-crossing_index * entry_sign)
                if over_arc_by_crossing_id[crossing["id"]] == (arc, next_label):
                    matches.append(crossing_index * entry_sign)
            if len(matches) != 1:
                raise ValueError(
                    f"arc transition {arc}->{next_label} matched {len(matches)} crossings: {matches}"
                )
            entries.append(matches[0])
        component_words.append(entries)
    return component_words, crossing_signs, records


def component_permutation(source_matrix, braid_linking):
    size = len(source_matrix)
    candidates = []
    source_offdiag = [
        [source_matrix[i][j] if i != j else 0 for j in range(size)]
        for i in range(size)
    ]
    for perm in permutations(range(size)):
        permuted = [
            [source_offdiag[perm[i]][perm[j]] for j in range(size)]
            for i in range(size)
        ]
        if permuted == braid_linking:
            candidates.append(list(perm))
    return candidates


def choose_component_permutation(source_components, candidates):
    if not candidates:
        return None
    return min(candidates, key=lambda perm: [source_components[index] for index in perm])


def source_ordered_matrix(braid_linking, source_index_per_braid_component):
    size = len(source_index_per_braid_component)
    braid_index_for_source = [0 for _ in range(size)]
    for braid_index, source_index in enumerate(source_index_per_braid_component):
        braid_index_for_source[source_index] = braid_index
    return [
        [
            int(braid_linking[braid_index_for_source[left]][braid_index_for_source[right]])
            for right in range(size)
        ]
        for left in range(size)
    ]


def main():
    payload = source_payload()
    switched_pairs = []
    component_words, crossing_signs, crossing_records = source_oriented_gauss_code(
        payload,
        switched_pairs=switched_pairs,
    )
    link = Link([component_words, crossing_signs])
    braid = link.braid()
    n_strands = int(braid.parent().strands())
    braid_word = [int(generator) for generator in braid.Tietze()]
    braid_linking = [
        [int(entry) for entry in row]
        for row in braid_closure_linking_matrix(n_strands, tuple(braid_word))
    ]
    source_matrix = source_linking_matrix(payload)
    permutations_to_source = component_permutation(source_matrix, braid_linking)
    selected_permutation = choose_component_permutation(source_order(payload), permutations_to_source)
    status = "pass" if selected_permutation is not None else "needs-component-order-review"
    if selected_permutation is not None:
        perm = selected_permutation
        source_components = source_order(payload)
        component_order_in_braid = [source_components[source_index] for source_index in perm]
        framings_in_braid_order = [source_framings(payload)[source_index] for source_index in perm]
    else:
        component_order_in_braid = []
        framings_in_braid_order = []

    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-braid-payload.v1",
        "status": status,
        "source_input": str(INPUT.relative_to(REPO_ROOT)),
        "conversion": "source-oriented-gauss-code -> Sage Link(...).braid()",
        "kirby_calibration": {
            "reason": (
                "The source crossing table is kept as transcribed.  The local "
                "tuple convention records incidence and over/under data, while "
                "the source table's calibrated_sign fields record the hand-checked "
                "visible crossing signs.  These signs give AA=3, BB=1, CC=3, "
                "AB=2, AC=-4, BC=-2 and match the oriented Yasui homology-label "
                "matrix, so no component-pair crossing switch or separate B/C "
                "self-twist correction is applied."
            ),
            "switched_component_pairs": [list(pair) for pair in switched_pairs],
            "switched_crossing_ids": [
                record["id"]
                for record in crossing_records
                if record["crossing_switched_for_kirby_calibration"]
            ],
        },
        "sage_version": SAGE_VERSION,
        "source_oriented_gauss_code": {
            "component_order": source_order(payload),
            "component_words": component_words,
            "crossing_signs": crossing_signs,
            "crossing_records": crossing_records,
        },
        "n_strands": n_strands,
        "braid_word": braid_word,
        "braid_closure_data": braid_closure_data(n_strands, tuple(braid_word)).to_json(),
        "braid_closure_linking_matrix": braid_linking,
        "source_ordered_braid_linking_matrix": (
            source_ordered_matrix(braid_linking, selected_permutation)
            if selected_permutation is not None
            else None
        ),
        "source_target_intersection_matrix": source_matrix,
        "source_oriented_diagram_linking_matrix": [
            [int(entry) for entry in row]
            for row in payload["oriented_diagram_linking_matrix"]
        ],
        "component_order_in_source": source_order(payload),
        "component_order_in_braid": component_order_in_braid,
        "source_index_per_braid_component": list(selected_permutation)
        if selected_permutation is not None
        else None,
        "component_order_candidates": permutations_to_source,
        "framings_in_braid_order": framings_in_braid_order,
        "omega_label_order": component_order_in_braid,
        "su2_2_omega_evaluations": [],
        "su2_2_omega_evaluations_status": (
            "skipped-legacy-jones-diagnostic; clean PD braid conversion is a "
            "payload step and should not be blocked by the older SU(2)_2 "
            "Jones-polynomial oracle"
        ),
        "local_piece_programs": [
            braid_program(
                program_id=f"yasui-figure3-a1-su2-2-omega-{''.join(map(str, omega_labels))}",
                category_id="SU(2)_2",
                strand_count=n_strands,
                braid_word=tuple(ZZ(g) for g in braid_word),
                framings=framings_in_braid_order,
                omega_labels=omega_labels,
                description=(
                    "Evaluator-ready braid-closure local-piece program for "
                    "Yasui Figure 3 a=1, with component order matching omega_label_order."
                ),
            ).to_json()
            for omega_labels in product((0, 1), repeat=len(framings_in_braid_order))
        ]
        if status == "pass"
        else [],
        "claim_boundary": (
            "This is a converted braid payload for the Yasui Figure 3 a=1 presentation. "
            "It is not yet a comparison with the standard CP2#2CPbar presentation."
        ),
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if status == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
