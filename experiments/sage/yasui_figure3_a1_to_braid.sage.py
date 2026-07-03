"""Convert Yasui Figure 3 (a=1) crossing input to braid evaluator payloads.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_to_braid.sage.py

The hand transcription records ``X Y Z W`` crossings, where ``X -> Z`` is the
understrand and the overstrand direction is recovered from component arc order.
We first turn this into an oriented Gauss code with the same provisional crossing
sign rule used by the calibration report.  Sage then converts that oriented link
to a braid.  Finally we match the braid-closure component order back to the
source components A,B,C by comparing inter-component linking matrices.
"""

from __future__ import annotations

import importlib.util
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
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.local_piece import (  # noqa: E402
    braid_closure_data,
    braid_closure_linking_matrix,
    braid_program,
)


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def source_payload():
    return json.loads(INPUT.read_text())


def source_order(payload):
    return [component["id"] for component in payload["components"]]


def source_framings(payload):
    return [int(component["framing"]) for component in payload["components"]]


def source_linking_matrix(payload):
    return [[int(entry) for entry in row] for row in payload["oriented_diagram_linking_matrix"]]


def arc_next_map(payload):
    result = {}
    for component in payload["components"]:
        arcs = list(component["arc_order"])
        for index, arc in enumerate(arcs):
            result[arc] = arcs[(index + 1) % len(arcs)]
    return result


def source_oriented_gauss_code(payload):
    """Return ``(component_words, crossing_signs, records)`` for Sage ``Link``.

    In Sage's oriented Gauss code, a positive entry means the component passes
    over the crossing and a negative entry means it passes under.  The separate
    crossing-sign list uses the calibration sign convention:

    * overstrand oriented as ``Y -> W`` gives ``+1``;
    * overstrand oriented as ``W -> Y`` gives ``-1``.
    """

    next_arc = arc_next_map(payload)
    crossings = payload["crossings"]
    crossing_signs = []
    records = []
    for crossing in crossings:
        x, y, z, w = crossing["tuple"]
        if next_arc[x] != z:
            raise ValueError(f"{crossing['id']} understrand is not oriented as X -> Z")
        if next_arc[y] == w:
            sign = 1
            over_direction = "Y->W"
        elif next_arc[w] == y:
            sign = -1
            over_direction = "W->Y"
        else:
            raise ValueError(f"{crossing['id']} overstrand endpoints are not adjacent")
        crossing_signs.append(sign)
        records.append(
            {
                "id": crossing["id"],
                "tuple": crossing["tuple"],
                "under": f"{x}->{z}",
                "over_direction": over_direction,
                "crossing_sign": sign,
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
                if (x, z) == (arc, next_label):
                    matches.append(-crossing_index)
                if (y, w) == (arc, next_label) or (w, y) == (arc, next_label):
                    matches.append(crossing_index)
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


def omega_evaluations(oracle, n_strands, braid_word, framings):
    output = []
    for omega_labels in product((0, 1), repeat=len(framings)):
        output.append(
            {
                "omega_labels": list(omega_labels),
                "omega_value": oracle.cyclotomic_json(
                    oracle.omega_value(n_strands, braid_word, tuple(framings), omega_labels)
                ),
            }
        )
    return output


def main():
    payload = source_payload()
    component_words, crossing_signs, crossing_records = source_oriented_gauss_code(payload)
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
    status = "pass" if len(permutations_to_source) == 1 else "needs-component-order-review"
    if permutations_to_source:
        perm = permutations_to_source[0]
        source_components = source_order(payload)
        component_order_in_braid = [source_components[source_index] for source_index in perm]
        framings_in_braid_order = [source_framings(payload)[source_index] for source_index in perm]
    else:
        component_order_in_braid = []
        framings_in_braid_order = []

    oracle = load_module(ORACLE_PATH, "su2_2_braid_oracle_for_yasui_figure3")
    evaluations = []
    if status == "pass":
        evaluations = omega_evaluations(oracle, n_strands, tuple(ZZ(g) for g in braid_word), framings_in_braid_order)

    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-braid-payload.v1",
        "status": status,
        "source_input": str(INPUT.relative_to(REPO_ROOT)),
        "conversion": "source-oriented-gauss-code -> Sage Link(...).braid()",
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
            source_ordered_matrix(braid_linking, permutations_to_source[0])
            if permutations_to_source
            else None
        ),
        "source_oriented_linking_matrix": source_matrix,
        "component_order_in_source": source_order(payload),
        "component_order_in_braid": component_order_in_braid,
        "source_index_per_braid_component": permutations_to_source[0] if permutations_to_source else None,
        "component_order_candidates": permutations_to_source,
        "framings_in_braid_order": framings_in_braid_order,
        "omega_label_order": component_order_in_braid,
        "su2_2_omega_evaluations": evaluations,
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
