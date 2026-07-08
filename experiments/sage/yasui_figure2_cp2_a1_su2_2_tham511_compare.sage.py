"""Compare corrected Yasui Figure 2 CP2(a=1) with standard CP2 in SU(2)_2.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure2_cp2_a1_su2_2_tham511_compare.sage.py --write

This is a working Tham 5.11 upside-down context sanity check.  The source
Figure 2 has two 3-handles; in the dual/upside-down Tham 5.11 direction these
are treated as two 1-handle maps, each contributing GLOBAL_DIMENSION^-1.  The
source input has no special dotted unknot, so no cut-and-vacuum projector rule
is applied here.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys
import time

from sage.all import CyclotomicField, ZZ
from sage.env import SAGE_VERSION
from sage.knots.link import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure2-cp2-a1-crossing-table.json"
CONTEXT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure2-cp2-a1-tham511-context-v1.json"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure2-cp2-a1-su2-2-tham511-comparison-v1.json"
)
R1_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure2-cp2-a1-su2-2-tham511-r1-a15-curl-comparison-v1.json"
)
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.local_piece import braid_closure_data, braid_closure_linking_matrix  # noqa: E402
from twisted_yetter.artifacts import (  # noqa: E402
    default_tool_versions,
    file_sha256,
    git_metadata,
    hash_json,
    utc_now_iso,
)
from twisted_yetter.yasui_figure2_cp2 import (  # noqa: E402
    analyze_crossing_table,
    load_crossing_table,
    source_framings,
    source_order,
    source_oriented_gauss_code,
    source_target_matrix,
)


K = CyclotomicField(16)
GLOBAL_DIMENSION = K(4)
NORMALIZATION_DENOMINATOR = GLOBAL_DIMENSION**2


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def cyclotomic_json(value):
    value = K(value)
    return {
        "field": "CyclotomicField(16)",
        "display": display_cyclotomic(value),
        "coefficients_in_power_basis": [str(value[i]) for i in range(K.degree())],
    }


def display_cyclotomic(value):
    value = K(value)
    if value == 0:
        return "0"
    terms = []
    for exponent in range(K.degree()):
        coefficient = value[exponent]
        if coefficient == 0:
            continue
        if exponent == 0:
            monomial = "1"
        else:
            monomial = f"zeta16^{exponent}"
        terms.append(f"{coefficient}*{monomial}")
    return " + ".join(terms).replace("+ -", "- ")


def component_permutation(source_matrix, braid_linking):
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


def choose_component_permutation(source_components, candidates):
    if not candidates:
        return None
    return min(candidates, key=lambda perm: [source_components[index] for index in perm])


def r1_remove_a15_curl(payload):
    """Return an in-memory payload with the explicit positive A15 curl removed."""

    result = json.loads(json.dumps(payload))
    removed = []
    remaining = []
    for crossing in result["crossings"]:
        if crossing["id"] == "x20":
            removed.append(crossing)
        else:
            remaining.append(crossing)
    if len(removed) != 1:
        raise ValueError("expected exactly one x20 crossing to remove")
    if removed[0]["tuple"] != ["A15", "A17", "A16", "A16"]:
        raise ValueError(f"unexpected x20 tuple: {removed[0]['tuple']!r}")
    if int(removed[0]["calibrated_sign"]) != 1:
        raise ValueError("x20 removal currently assumes a positive R1 curl")

    for crossing in remaining:
        crossing["tuple"] = [
            "A15" if label == "A17" else label
            for label in crossing["tuple"]
        ]
    result["crossings"] = remaining

    for component in result["components"]:
        if component["id"] != "A":
            continue
        component["arc_order"] = [
            label
            for label in component["arc_order"]
            if label not in {"A16", "A17"}
        ]
        component["arc_count"] = len(component["arc_order"])
        component["visible_self_writhe"] = int(component.get("visible_self_writhe", 0)) - 1
        component["framing_correction_after_visible_writhe"] = (
            int(component["framing"]) - int(component["visible_self_writhe"])
        )
        break
    else:
        raise ValueError("component A not found")

    result["r1_normalization"] = {
        "status": "in_memory_only",
        "removed_crossing_id": "x20",
        "removed_tuple": removed[0]["tuple"],
        "removed_self_writhe": 1,
        "collapsed_arc_block": ["A15", "A16", "A17"],
        "surviving_arc": "A15",
        "label_replacements_after_removal": {"A17": "A15"},
        "target_total_framing_A": 4,
        "expected_visible_self_writhe_A_after_removal": 2,
        "expected_extra_framing_A_after_removal": 2,
    }
    return result


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


def compare(*, r1_remove_a15=False):
    started_at_utc = utc_now_iso()
    started = time.time()
    oracle = load_module(ORACLE_PATH, "su2_2_braid_oracle_for_yasui_figure2")
    payload = load_crossing_table(INPUT)
    if r1_remove_a15:
        payload = r1_remove_a15_curl(payload)
    context = json.loads(CONTEXT.read_text())
    analysis = analyze_crossing_table(payload)
    if analysis["status"] != "pass":
        raise ValueError("Figure 2 sanity analysis is not pass")

    component_words, crossing_signs, crossing_records = source_oriented_gauss_code(payload)
    link = Link([component_words, crossing_signs])
    braid = link.braid()
    n_strands = int(braid.parent().strands())
    braid_word = [int(generator) for generator in braid.Tietze()]
    braid_linking = [
        [int(entry) for entry in row]
        for row in braid_closure_linking_matrix(n_strands, tuple(braid_word))
    ]
    source_matrix = source_target_matrix(payload)
    permutations_to_source = component_permutation(source_matrix, braid_linking)
    selected_permutation = choose_component_permutation(source_order(payload), permutations_to_source)
    if selected_permutation is None:
        raise ValueError("could not identify braid component order from linking matrix")

    components = source_order(payload)
    component_order_in_braid = [
        components[source_index] for source_index in selected_permutation
    ]
    source_framing_by_component = dict(zip(components, source_framings(payload), strict=True))
    visible_writhe_by_component = {
        component["id"]: int(component.get("visible_self_writhe", 0))
        for component in payload["components"]
    }
    extra_framing_by_component = {
        component: source_framing_by_component[component]
        - visible_writhe_by_component.get(component, 0)
        for component in components
    }
    framings_in_braid_order = [
        extra_framing_by_component[component] for component in component_order_in_braid
    ]
    assignments = context["legal_character_assignments"]["assignments"]

    rows = []
    all_match = True
    for assignment in assignments:
        source_labels = assignment["component_omega_labels_by_id"]
        yasui_omega_labels = [
            int(source_labels[component]) for component in component_order_in_braid
        ]
        standard_omega_labels = [int(assignment["h_label"])]
        raw_value = oracle.omega_value(
            ZZ(n_strands),
            tuple(ZZ(generator) for generator in braid_word),
            tuple(ZZ(framing) for framing in framings_in_braid_order),
            tuple(ZZ(label) for label in yasui_omega_labels),
        )
        normalized_value = K(raw_value) / NORMALIZATION_DENOMINATOR
        standard_value = oracle.omega_value(ZZ(1), (), (ZZ(1),), tuple(ZZ(x) for x in standard_omega_labels))
        difference = K(normalized_value - standard_value)
        match = difference == 0
        all_match = bool(all_match and match)
        rows.append(
            {
                "h_label": int(assignment["h_label"]),
                "source_component_order": components,
                "component_order_in_braid": component_order_in_braid,
                "yasui_omega_labels_in_braid_order": yasui_omega_labels,
                "standard_omega_labels": standard_omega_labels,
                "raw_yasui_value": cyclotomic_json(raw_value),
                "normalization_denominator": cyclotomic_json(NORMALIZATION_DENOMINATOR),
                "normalized_yasui_value": cyclotomic_json(normalized_value),
                "standard_cp2_value": cyclotomic_json(standard_value),
                "difference": cyclotomic_json(difference),
                "normalized_matches_standard": match,
            }
        )

    return {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-su2-2-tham511.v1",
        "status": "pass" if all_match else "needs-review",
        "generator_script": str(Path(__file__).relative_to(REPO_ROOT)),
        "command": " ".join(sys.argv),
        "argv": [str(item) for item in sys.argv],
        "reproduce_command": (
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/'
            "yasui_figure2_cp2_a1_su2_2_tham511_compare.sage.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_metadata(REPO_ROOT),
        "tool_versions": {
            **default_tool_versions(),
            "sage": SAGE_VERSION,
        },
        "input_hash": hash_json(
            {
                "input": str(INPUT.relative_to(REPO_ROOT)),
                "input_sha256": file_sha256(INPUT),
                "context": str(CONTEXT.relative_to(REPO_ROOT)),
                "context_sha256": file_sha256(CONTEXT),
            }
        ),
        "started_at_utc": started_at_utc,
        "finished_at_utc": utc_now_iso(),
        "mathematical_status": "WORKING_HYPOTHESIS_NOT_THEOREM",
        "variant": "r1-remove-a15-curl" if r1_remove_a15 else "source-pd",
        "r1_normalization": payload.get("r1_normalization"),
        "comparison_interpretation": (
            "PD blackboard RT evaluation with extra framing correction, divided "
            "by the two dual one-handle global-dimension factors, matches "
            "standard CP2"
            if all_match
            else (
                "PD blackboard RT evaluation with extra framing correction, "
                "divided by D^2, does not match standard CP2 in this "
                "implementation; review PD-to-braid conversion, framing "
                "convention, and SU(2)_2 oracle convention before drawing a "
                "mathematical conclusion"
            )
        ),
        "halt_downstream_twisted_work": not all_match,
        "category_id": "SU(2)_2",
        "sage_version": SAGE_VERSION,
        "source": {
            "input": str(INPUT.relative_to(REPO_ROOT)),
            "context": str(CONTEXT.relative_to(REPO_ROOT)),
            "oracle": str(ORACLE_PATH.relative_to(REPO_ROOT)),
            "standard_presentation": "one +1 framed unknot for CP2",
        },
        "normalization_working_hypothesis": {
            "source_three_handle_count": 2,
            "dual_tham511_one_handle_count": 2,
            "global_dimension": cyclotomic_json(GLOBAL_DIMENSION),
            "factor": "GLOBAL_DIMENSION^-2",
            "special_dotted_projector_status": (
                "not present in this Figure 2 input; no cut-and-vacuum "
                "projection rule applied"
            ),
        },
        "conversion": {
            "component_words": component_words,
            "crossing_signs": crossing_signs,
            "crossing_records": crossing_records,
            "n_strands": n_strands,
            "braid_word": braid_word,
            "braid_closure_data": braid_closure_data(n_strands, tuple(braid_word)).to_json(),
            "braid_closure_linking_matrix": braid_linking,
            "source_ordered_braid_linking_matrix": source_ordered_matrix(
                braid_linking,
                selected_permutation,
            ),
            "source_target_intersection_matrix": source_matrix,
            "target_total_framing_by_source_component": source_framing_by_component,
            "visible_blackboard_self_writhe_by_source_component": visible_writhe_by_component,
            "extra_framing_by_source_component": extra_framing_by_component,
            "framings_in_braid_order": framings_in_braid_order,
        },
        "rows": rows,
        "elapsed_seconds": str(time.time() - started),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument(
        "--r1-remove-a15-curl",
        action="store_true",
        help="remove the explicit positive A15 self curl in memory before braid conversion",
    )
    args = parser.parse_args(argv)

    output_path = R1_OUTPUT if args.r1_remove_a15_curl else OUTPUT
    result = compare(r1_remove_a15=args.r1_remove_a15_curl)
    if args.write:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(output_path.relative_to(REPO_ROOT)),
                "halt_downstream_twisted_work": result["halt_downstream_twisted_work"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
