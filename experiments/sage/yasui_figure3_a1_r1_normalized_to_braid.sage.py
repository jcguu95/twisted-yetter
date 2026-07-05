"""Build an R1-normalized evaluator payload for Yasui Figure 3 (a=1).

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_r1_normalized_to_braid.sage.py

The canonical audited source is the clean PD crossing table
``figure3-a1-crossing-table.json``.  That clean PD explicitly draws the local
positive self-curl blocks for A15, B1, and C1, so its visible matrix already is

    [[ 3,  2, -4],
     [ 2,  1, -2],
     [-4, -2,  3]].

For evaluator efficiency, this script removes only those explicitly identified
local R1 curl crossings and records their writhe contribution as framing
metadata.  It does not remove other same-component crossings.
"""

from __future__ import annotations

import copy
import importlib.util
import json
from collections import defaultdict
from itertools import product
from pathlib import Path
import sys

from sage.all import ZZ
from sage.env import SAGE_VERSION
from sage.knots.link import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE_INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure3-a1-crossing-table.json"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-braid-payload-v1.json"
)
CONVERTER_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure3_a1_to_braid.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.local_piece import (  # noqa: E402
    braid_closure_data,
    braid_closure_linking_matrix,
    braid_program,
)


R1_NORMALIZATIONS = [
    {
        "component_id": "A",
        "reason": "A15 +1 coupon/local curl",
        "removed_crossing_ids": ["x18"],
        "replace_arc_block": ["A15a", "A15b", "A15c"],
        "replacement_arc": "A15",
        "label_replacements": {"A15a": "A15", "A15c": "A15"},
        "removed_writhe": 1,
    },
    {
        "component_id": "B",
        "reason": "B1 +1 local curl inserted to carry B^2=1 in the clean PD",
        "removed_crossing_ids": ["x09"],
        "replace_arc_block": ["B1a", "B1b", "B1c"],
        "replacement_arc": "B1",
        "label_replacements": {"B1a": "B1", "B1c": "B1"},
        "removed_writhe": 1,
    },
    {
        "component_id": "C",
        "reason": "three C1 +1 local curls inserted to carry C^2=3 in the clean PD",
        "removed_crossing_ids": ["x02", "x03", "x04"],
        "replace_arc_block": ["C1a", "C1b", "C1c", "C1d", "C1e", "C1f", "C1g"],
        "replacement_arc": "C1",
        "label_replacements": {"C1a": "C1", "C1g": "C1"},
        "removed_writhe": 3,
    },
]


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def replace_block(sequence, old_block, replacement):
    for index in range(len(sequence) - len(old_block) + 1):
        if sequence[index : index + len(old_block)] == old_block:
            return sequence[:index] + [replacement] + sequence[index + len(old_block) :]
    raise ValueError(f"arc block not found: {old_block}")


def source_component_order(payload):
    return [component["id"] for component in payload["components"]]


def normalize_payload(clean_payload):
    payload = copy.deepcopy(clean_payload)
    removed_ids = {
        crossing_id
        for item in R1_NORMALIZATIONS
        for crossing_id in item["removed_crossing_ids"]
    }
    label_replacements = {}
    for item in R1_NORMALIZATIONS:
        label_replacements.update(item["label_replacements"])

    crossings_by_id = {crossing["id"]: crossing for crossing in clean_payload["crossings"]}
    missing = sorted(removed_ids.difference(crossings_by_id))
    if missing:
        raise ValueError(f"missing R1 crossing ids: {missing}")
    for item in R1_NORMALIZATIONS:
        component = item["component_id"]
        for crossing_id in item["removed_crossing_ids"]:
            crossing = crossings_by_id[crossing_id]
            labels = crossing["tuple"]
            if any(label[0] != component for label in labels):
                raise ValueError(f"{crossing_id} is not a pure {component} self-curl")
            if int(crossing["calibrated_sign"]) != 1:
                raise ValueError(f"{crossing_id} is not a positive local curl")

    for component in payload["components"]:
        for item in R1_NORMALIZATIONS:
            if component["id"] == item["component_id"]:
                component["arc_order"] = replace_block(
                    list(component["arc_order"]),
                    item["replace_arc_block"],
                    item["replacement_arc"],
                )
                component["arc_count"] = len(component["arc_order"])

    normalized_crossings = []
    for crossing in payload["crossings"]:
        if crossing["id"] in removed_ids:
            continue
        normalized = copy.deepcopy(crossing)
        normalized["tuple"] = [
            label_replacements.get(label, label)
            for label in crossing["tuple"]
        ]
        normalized_crossings.append(normalized)
    payload["crossings"] = normalized_crossings
    payload["status"] = "r1-normalized-evaluator-payload"
    payload["r1_normalization"] = {
        "source_clean_pd": str(SOURCE_INPUT.relative_to(REPO_ROOT)),
        "removed_crossing_ids": sorted(removed_ids),
        "removed_local_curls": R1_NORMALIZATIONS,
        "scope": (
            "Only explicitly recorded local R1 curl/coupon crossings are removed. "
            "Other same-component crossings are retained as projection complexity."
        ),
    }
    return payload


def self_writhe_by_component(records, components):
    result = {component: 0 for component in components}
    for record in records:
        pair = record["component_pair"]
        if len(pair) == 2 and pair[0] == pair[1]:
            result[pair[0]] += int(record["crossing_sign"])
    return result


def removed_writhe_by_component():
    result = defaultdict(int)
    for item in R1_NORMALIZATIONS:
        result[item["component_id"]] += int(item["removed_writhe"])
    return dict(result)


def main():
    converter = load_module(CONVERTER_PATH, "yasui_figure3_a1_converter_for_r1_normalized")
    clean_payload = json.loads(SOURCE_INPUT.read_text())
    payload = normalize_payload(clean_payload)
    component_words, crossing_signs, crossing_records = converter.source_oriented_gauss_code(payload)

    link = Link([component_words, crossing_signs])
    braid = link.braid()
    n_strands = int(braid.parent().strands())
    braid_word = [int(generator) for generator in braid.Tietze()]
    braid_linking = [
        [int(entry) for entry in row]
        for row in braid_closure_linking_matrix(n_strands, tuple(braid_word))
    ]
    source_matrix = converter.source_linking_matrix(payload)
    permutations_to_source = converter.component_permutation(source_matrix, braid_linking)
    selected_permutation = converter.choose_component_permutation(
        converter.source_order(payload),
        permutations_to_source,
    )
    status = "pass" if selected_permutation is not None else "needs-component-order-review"
    if selected_permutation is not None:
        source_components = converter.source_order(payload)
        component_order_in_braid = [
            source_components[source_index]
            for source_index in selected_permutation
        ]
        framings_in_braid_order = [
            converter.source_framings(payload)[source_index]
            for source_index in selected_permutation
        ]
    else:
        component_order_in_braid = []
        framings_in_braid_order = []

    normalized_self_writhe = self_writhe_by_component(
        crossing_records,
        source_component_order(payload),
    )
    removed_self_writhe = removed_writhe_by_component()
    recorded_framings = {
        component["id"]: int(component["framing"])
        for component in payload["components"]
    }
    expected_clean_self_writhe = {
        component: normalized_self_writhe[component] + removed_self_writhe.get(component, 0)
        for component in recorded_framings
    }

    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-braid-payload.v1",
        "status": status,
        "source_clean_pd_input": str(SOURCE_INPUT.relative_to(REPO_ROOT)),
        "conversion": "clean-PD -> explicit R1 curl removal -> source-oriented-gauss-code -> Sage Link(...).braid()",
        "sage_version": SAGE_VERSION,
        "r1_normalization": {
            **payload["r1_normalization"],
            "recorded_total_framing_by_source_component": recorded_framings,
            "normalized_visible_self_writhe_by_source_component": normalized_self_writhe,
            "removed_writhe_by_source_component": removed_self_writhe,
            "expected_clean_visible_self_writhe_by_source_component": expected_clean_self_writhe,
            "framing_identity_status": (
                "pass"
                if expected_clean_self_writhe == recorded_framings
                else "needs-review"
            ),
        },
        "source_oriented_gauss_code": {
            "component_order": converter.source_order(payload),
            "component_words": component_words,
            "crossing_signs": crossing_signs,
            "crossing_records": crossing_records,
        },
        "n_strands": n_strands,
        "braid_word": braid_word,
        "braid_closure_data": braid_closure_data(n_strands, tuple(braid_word)).to_json(),
        "braid_closure_linking_matrix": braid_linking,
        "source_ordered_braid_linking_matrix": (
            converter.source_ordered_matrix(braid_linking, selected_permutation)
            if selected_permutation is not None
            else None
        ),
        "source_target_intersection_matrix": source_matrix,
        "source_oriented_diagram_linking_matrix": [
            [int(entry) for entry in row]
            for row in payload["oriented_diagram_linking_matrix"]
        ],
        "component_order_in_source": converter.source_order(payload),
        "component_order_in_braid": component_order_in_braid,
        "source_index_per_braid_component": (
            list(selected_permutation)
            if selected_permutation is not None
            else None
        ),
        "component_order_candidates": permutations_to_source,
        "framings_in_braid_order": framings_in_braid_order,
        "omega_label_order": component_order_in_braid,
        "local_piece_programs": [
            braid_program(
                program_id=f"yasui-figure3-a1-r1-normalized-su2-2-omega-{''.join(map(str, omega_labels))}",
                category_id="SU(2)_2",
                strand_count=n_strands,
                braid_word=tuple(ZZ(g) for g in braid_word),
                framings=framings_in_braid_order,
                omega_labels=omega_labels,
                description=(
                    "Evaluator-ready R1-normalized braid-closure local-piece "
                    "program for Yasui Figure 3 a=1."
                ),
            ).to_json()
            for omega_labels in product((0, 1), repeat=len(framings_in_braid_order))
        ]
        if status == "pass"
        else [],
        "claim_boundary": (
            "This is an evaluator payload derived from the clean PD by explicit "
            "R1 curl removal.  The clean PD remains the canonical audited input."
        ),
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if status == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
