"""Yasui Figure 3 (a=3) SU(2)_2 untwisted comparison.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a3_su2_2_untwisted_comparison.sage.py

The a=3 hand transcription is a compressed PD-like code: understrands are
adjacent X->Z arcs, but some overpasses skip labels along a longer visible
overpass.  The input generator records crossing signs using the a=1-validated
cyclic rule.  This script expands the compressed rows into Sage oriented Gauss
code by putting each compressed over-crossing on the final adjacent transition
of the overpass.
"""

from __future__ import annotations

import importlib.util
import json
import argparse
from itertools import product
from pathlib import Path
import sys
import time

from sage.all import ComplexField
from sage.env import SAGE_VERSION
from sage.knots.link import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a3-crossing-table.json"
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
PRECISION = 120
CF = ComplexField(PRECISION)
TOLERANCE = CF("1e-10")

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.local_piece import braid_closure_data, braid_closure_linking_matrix  # noqa: E402


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def complex_json(value):
    value = CF(value)
    return {
        "field": f"ComplexField({PRECISION})",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
        "abs": str(abs(value)),
    }


def source_order(payload):
    return [component["id"] for component in payload["components"]]


def source_framings(payload):
    return [int(component["framing"]) for component in payload["components"]]


def source_matrix(payload):
    return [[int(entry) for entry in row] for row in payload["target_intersection_matrix"]]


def arc_maps(payload):
    next_arc = {}
    prev_arc = {}
    arc_component = {}
    for component in payload["components"]:
        arcs = list(component["arc_order"])
        for index, arc in enumerate(arcs):
            next_arc[arc] = arcs[(index + 1) % len(arcs)]
            prev_arc[arc] = arcs[(index - 1) % len(arcs)]
            arc_component[arc] = component["id"]
    return next_arc, prev_arc, arc_component


def over_transition(crossing, next_arc, prev_arc):
    x, y, z, w = crossing["tuple"]
    if next_arc[x] != z:
        raise ValueError(f"{crossing['id']} understrand is not X->Z")
    source = crossing["sign_source"]
    if source.startswith("Y->W"):
        return (y, w) if next_arc[y] == w else (prev_arc[w], w)
    if source.startswith("W->Y"):
        return (w, y) if next_arc[w] == y else (prev_arc[y], y)
    raise ValueError(f"unknown sign source: {source}")


def source_oriented_gauss_code(payload):
    next_arc, prev_arc, arc_component = arc_maps(payload)
    crossing_signs = []
    records = []
    under_transition_by_id = {}
    over_transition_by_id = {}
    for crossing_index, crossing in enumerate(payload["crossings"], start=1):
        x, y, z, _w = crossing["tuple"]
        under_transition_by_id[crossing["id"]] = (x, z)
        over_transition_by_id[crossing["id"]] = over_transition(crossing, next_arc, prev_arc)
        sign = int(crossing["calibrated_sign"])
        crossing_signs.append(sign)
        records.append(
            {
                "id": crossing["id"],
                "tuple": crossing["tuple"],
                "under": f"{x}->{z}",
                "over_transition": "->".join(over_transition_by_id[crossing["id"]]),
                "crossing_sign": sign,
                "component_pair": sorted([arc_component[x], arc_component[y]]),
                "sign_source": crossing["sign_source"],
                "gauss_index": crossing_index,
            }
        )

    component_words = []
    for component in payload["components"]:
        entries = []
        arcs = list(component["arc_order"])
        for index, arc in enumerate(arcs):
            transition = (arc, arcs[(index + 1) % len(arcs)])
            matches = []
            for crossing_index, crossing in enumerate(payload["crossings"], start=1):
                crossing_id = crossing["id"]
                if under_transition_by_id[crossing_id] == transition:
                    matches.append(-crossing_index)
                if over_transition_by_id[crossing_id] == transition:
                    matches.append(crossing_index)
            if len(matches) != 1:
                raise ValueError(
                    f"arc transition {transition[0]}->{transition[1]} matched {len(matches)} crossings: {matches}"
                )
            entries.append(matches[0])
        component_words.append(entries)
    return component_words, crossing_signs, records


def component_permutation(source, braid_linking):
    from itertools import permutations

    size = len(source)
    source_offdiag = [
        [source[i][j] if i != j else 0 for j in range(size)]
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


def omega_from_sector_cache(evaluator, sector_cache, omega_labels):
    total = evaluator.zero()
    for fixed_labels, amplitude in sector_cache.items():
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(omega_labels, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * amplitude
    return total


def output_path(level, all_alpha):
    mode = "all-alpha" if all_alpha else "untwisted"
    return RESULT_DIR / f"figure3-a3-su2-{level}-{mode}-comparison-v1.json"


def yasui_labels_for_alpha(alpha):
    alpha_h, alpha_e1, alpha_e2 = alpha
    return {
        "A": alpha_e2,
        "B": alpha_h,
        "C": alpha_e1,
    }


def compare(level, all_alpha=False):
    started = time.time()
    payload = json.loads(INPUT.read_text())
    component_words, crossing_signs, crossing_records = source_oriented_gauss_code(payload)
    link = Link([component_words, crossing_signs])
    braid = link.braid()
    n_strands = int(braid.parent().strands())
    braid_word = [int(generator) for generator in braid.Tietze()]
    braid_linking = [
        [int(entry) for entry in row]
        for row in braid_closure_linking_matrix(n_strands, tuple(braid_word))
    ]
    candidates = component_permutation(source_matrix(payload), braid_linking)
    selected = min(candidates) if candidates else None
    if selected is None:
        status = "needs-component-order-review"
        component_order_in_braid = []
        framings_in_braid_order = []
    else:
        status = "converted"
        components = source_order(payload)
        component_order_in_braid = [components[source_index] for source_index in selected]
        framings = source_framings(payload)
        framings_in_braid_order = [framings[source_index] for source_index in selected]

    su2k = load_module(SU2K_PATH, f"su2k_yasui_a3_su2_{level}")
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=PRECISION)
    comparison = None
    rows = []
    if status == "converted":
        yasui_cache = evaluator.sector_amplitudes(
            n_strands,
            tuple(braid_word),
            tuple(framings_in_braid_order),
        )
        standard_cache = evaluator.sector_amplitudes(3, (), (1, -1, -1))
        alphas = list(product((0, 1), repeat=3)) if all_alpha else [(0, 0, 0)]
        all_close = True
        max_abs_difference = CF(0)
        for alpha in alphas:
            labels_by_component = yasui_labels_for_alpha(alpha)
            yasui_omega_labels = tuple(labels_by_component[name] for name in component_order_in_braid)
            standard_omega_labels = alpha
            yasui_value = omega_from_sector_cache(evaluator, yasui_cache, yasui_omega_labels)
            standard_value = omega_from_sector_cache(evaluator, standard_cache, standard_omega_labels)
            difference = CF(yasui_value - standard_value)
            abs_difference = abs(difference)
            close = bool(abs_difference < TOLERANCE)
            all_close = all_close and close
            max_abs_difference = max(max_abs_difference, abs_difference)
            rows.append(
                {
                    "alpha_basis_order": ["h", "e1", "e2"],
                    "alpha": [int(item) for item in alpha],
                    "standard_omega_labels": [int(item) for item in standard_omega_labels],
                    "yasui_omega_label_order": component_order_in_braid,
                    "yasui_omega_labels": [int(item) for item in yasui_omega_labels],
                    "yasui_value": complex_json(yasui_value),
                    "standard_value": complex_json(standard_value),
                    "difference": complex_json(difference),
                    "abs_difference": str(abs_difference),
                    "close_under_tolerance": close,
                }
            )
        comparison = {
            "category_id": f"SU(2)_{level}",
            "alpha_mode": "all-alpha" if all_alpha else "untwisted",
            "max_abs_difference": str(max_abs_difference),
            "rows": rows,
            "yasui_fixed_sector_count": len(yasui_cache),
            "standard_fixed_sector_count": len(standard_cache),
        }
        status = "pass" if all_close else "mismatch"

    matrix = source_matrix(payload)
    result = {
        "schema": "twisted-yetter.yasui-figure3-a3-su2-comparison.v1",
        "status": status,
        "sage_version": SAGE_VERSION,
        "source_input": str(INPUT.relative_to(REPO_ROOT)),
        "conversion": "compressed source-oriented-gauss-code -> Sage Link(...).braid()",
        "component_order_in_source": source_order(payload),
        "target_intersection_matrix": matrix,
        "determinant": 1,
        "signature": -1,
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
        "source_index_per_braid_component": selected,
        "source_ordered_braid_linking_matrix": (
            source_ordered_matrix(braid_linking, selected)
            if selected is not None
            else None
        ),
        "component_order_in_braid": component_order_in_braid,
        "framings_in_braid_order": framings_in_braid_order,
        "comparison": comparison,
        "elapsed_seconds": time.time() - started,
    }
    out = output_path(level, all_alpha)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(out.relative_to(REPO_ROOT)),
                "n_strands": n_strands,
                "braid_word_length": len(braid_word),
                "component_order_in_braid": component_order_in_braid,
                "framings_in_braid_order": framings_in_braid_order,
                "category_id": f"SU(2)_{level}",
                "alpha_mode": "all-alpha" if all_alpha else "untwisted",
                "max_abs_difference": comparison["max_abs_difference"] if comparison else None,
                "row_count": len(rows),
                "elapsed_seconds": result["elapsed_seconds"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if status == "pass" else 1


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--level", type=int, default=2)
    parser.add_argument("--all-alpha", action="store_true")
    args = parser.parse_args(argv)
    return compare(args.level, all_alpha=args.all_alpha)


if __name__ == "__main__":
    raise SystemExit(main())
