"""Compare Akbulut 0805.1524 Figure 1 with standard E(1), SU(2)_2 untwisted.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/akbulut_figure1_e1_su2_2_untwisted_comparison.sage.py

This is the first ordinary untwisted test for the Akbulut Figure 1
transcription.  It compares the 10-component Figure 1 Kirby link against the
standard unlink presentation of CP2#9CPbar with framings (+1,-1,...,-1).
"""

from __future__ import annotations

import importlib.util
import json
from itertools import product
from pathlib import Path
import sys
import time

from sage.all import ComplexField
from sage.env import SAGE_VERSION
from sage.knots.link import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "akbulut" / "figure1-e1-crossing-table.json"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "akbulut"
    / "figure1-e1-su2-2-untwisted-comparison-v1.json"
)
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))
from twisted_yetter.local_piece import braid_closure_linking_matrix  # noqa: E402


CF = ComplexField(120)
TOLERANCE = CF("1e-10")


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def complex_json(value):
    value = CF(value)
    return {
        "field": "ComplexField(120)",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
        "abs": str(abs(value)),
    }


def component_order(payload):
    return [component["id"] for component in payload["components"]]


def component_framings(payload):
    return [int(component["framing"]) for component in payload["components"]]


def next_arc_map(payload):
    result = {}
    for component in payload["components"]:
        arcs = component["arc_order"]
        for index, arc in enumerate(arcs):
            result[arc] = arcs[(index + 1) % len(arcs)]
    return result


def arc_component_map(payload):
    result = {}
    for component in payload["components"]:
        for arc in component["arc_order"]:
            result[arc] = component["id"]
    return result


def cyclic_sign(next_arc, y, w):
    if next_arc[w] == y:
        return 1
    if next_arc[y] == w:
        return -1
    raise ValueError(f"bad overstrand endpoints: {y}, {w}")


def source_oriented_gauss_code(payload):
    next_arc = next_arc_map(payload)
    arc_component = arc_component_map(payload)
    component_words = []
    crossing_signs = []
    records = []
    crossings = payload["crossings"]
    crossing_over_arcs = {}
    for crossing in crossings:
        x, y, z, w = crossing["tuple"]
        if next_arc[x] != z:
            raise ValueError(f"{crossing['id']} understrand is not oriented as X -> Z")
        sign = cyclic_sign(next_arc, y, w)
        over_arc = (w, y) if sign == 1 else (y, w)
        crossing_over_arcs[crossing["id"]] = over_arc
        crossing_signs.append(sign)
        records.append(
            {
                "id": crossing["id"],
                "tuple": crossing["tuple"],
                "crossing_sign": sign,
                "over_arc": list(over_arc),
                "component_pair": sorted([arc_component[x], arc_component[y]]),
            }
        )
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
                if tuple(crossing_over_arcs[crossing["id"]]) == (arc, next_label):
                    matches.append(crossing_index)
            if len(matches) != 1:
                raise ValueError(
                    f"arc transition {arc}->{next_label} matched {len(matches)} crossings: {matches}"
                )
            entries.append(matches[0])
        component_words.append(entries)
    return component_words, crossing_signs, records


def metric_pair(left, right):
    total = int(left.get("h", 0)) * int(right.get("h", 0))
    for index in range(1, 10):
        total -= int(left.get(f"e{index}", 0)) * int(right.get(f"e{index}", 0))
    return total


def target_matrix(payload):
    components = payload["components"]
    return [
        [
            metric_pair(left["class_in_h_e_basis"], right["class_in_h_e_basis"])
            for right in components
        ]
        for left in components
    ]


def component_permutations(source_matrix, braid_linking):
    from itertools import permutations

    size = len(source_matrix)
    source_offdiag = [
        [source_matrix[i][j] if i != j else 0 for j in range(size)]
        for i in range(size)
    ]
    candidates = []
    for perm in permutations(range(size)):
        permuted = [
            [source_offdiag[perm[i]][perm[j]] for j in range(size)]
            for i in range(size)
        ]
        if permuted == braid_linking:
            candidates.append(list(perm))
    return candidates


def choose_permutation(source_components, candidates):
    if not candidates:
        return None
    return min(candidates, key=lambda perm: [source_components[index] for index in perm])


def omega_from_cache(evaluator, cache):
    total = evaluator.zero()
    for fixed_labels, amplitude in cache.items():
        coefficient = evaluator.one()
        for simple_label in fixed_labels:
            coefficient *= evaluator.dimension(simple_label)
        total += coefficient * amplitude
    return total


def main():
    started = time.time()
    payload = json.loads(INPUT.read_text())
    su2k = load_module(SU2K_PATH, "su2k_for_akbulut_figure1_su2_2")
    evaluator = su2k.SU2KBraidEvaluator(2, exact=False, precision=120)

    component_words, crossing_signs, crossing_records = source_oriented_gauss_code(payload)
    braid = Link([component_words, crossing_signs]).braid()
    n_strands = int(braid.parent().strands())
    braid_word = tuple(int(generator) for generator in braid.Tietze())
    braid_linking = [
        [int(entry) for entry in row]
        for row in braid_closure_linking_matrix(n_strands, braid_word)
    ]
    source_components = component_order(payload)
    source_target_matrix = target_matrix(payload)
    candidates = component_permutations(source_target_matrix, braid_linking)
    selected = choose_permutation(source_components, candidates)
    if selected is None:
        raise ValueError("could not match braid components to source components by linking matrix")
    component_order_in_braid = [source_components[source_index] for source_index in selected]
    framings_in_braid_order = [component_framings(payload)[source_index] for source_index in selected]

    print(
        json.dumps(
            {
                "phase": "braid-built",
                "n_strands": n_strands,
                "braid_word_length": len(braid_word),
                "component_order_in_braid": component_order_in_braid,
                "framings_in_braid_order": framings_in_braid_order,
                "elapsed_seconds": time.time() - started,
            },
            sort_keys=True,
        ),
        flush=True,
    )
    akbulut_cache = evaluator.sector_amplitudes(n_strands, braid_word, tuple(framings_in_braid_order))
    print(
        json.dumps(
            {
                "phase": "akbulut-cache-built",
                "sector_count": len(akbulut_cache),
                "elapsed_seconds": time.time() - started,
            },
            sort_keys=True,
        ),
        flush=True,
    )
    standard_framings = (1,) + (-1,) * 9
    standard_cache = evaluator.sector_amplitudes(10, (), standard_framings)
    akbulut_value = omega_from_cache(evaluator, akbulut_cache)
    standard_value = omega_from_cache(evaluator, standard_cache)
    difference = CF(akbulut_value - standard_value)
    result = {
        "schema": "twisted-yetter.akbulut-figure1-e1-su2-2-untwisted-comparison.v1",
        "status": "pass" if abs(difference) < TOLERANCE else "mismatch",
        "sage_version": SAGE_VERSION,
        "category_id": "SU(2)_2",
        "claim_level": "ordinary untwisted Kirby color comparison against standard CP2#9CPbar",
        "source_input": str(INPUT.relative_to(REPO_ROOT)),
        "algorithm": "source XYZW -> Sage oriented Gauss code -> Sage braid -> SU2KBraidEvaluator",
        "akbulut_complexity": {
            "n_strands": n_strands,
            "braid_word_length": len(braid_word),
            "component_count": len(component_order_in_braid),
            "component_order_in_braid": component_order_in_braid,
            "framings_in_braid_order": framings_in_braid_order,
            "fixed_sector_count": len(akbulut_cache),
        },
        "standard_complexity": {
            "n_strands": 10,
            "braid_word_length": 0,
            "component_count": 10,
            "framings": list(standard_framings),
            "fixed_sector_count": len(standard_cache),
        },
        "akbulut_value": complex_json(akbulut_value),
        "standard_value": complex_json(standard_value),
        "difference": complex_json(difference),
        "abs_difference": str(abs(difference)),
        "tolerance": str(TOLERANCE),
        "elapsed_seconds": time.time() - started,
        "source_oriented_gauss_code": {
            "component_words": component_words,
            "crossing_signs": crossing_signs,
            "crossing_records": crossing_records,
        },
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(OUTPUT.relative_to(REPO_ROOT)),
                "akbulut_value": result["akbulut_value"]["display"],
                "standard_value": result["standard_value"]["display"],
                "abs_difference": result["abs_difference"],
                "elapsed_seconds": result["elapsed_seconds"],
            },
            indent=2,
            sort_keys=True,
        ),
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
