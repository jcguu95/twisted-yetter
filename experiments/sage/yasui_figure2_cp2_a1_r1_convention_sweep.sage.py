"""Small convention sweep for the R1-normalized Yasui Figure 2 CP2(a=1) test."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

from sage.all import CyclotomicField, ZZ
from sage.knots.link import Link


REPO_ROOT = Path(__file__).resolve().parents[2]
INPUT = REPO_ROOT / "experiments" / "inputs" / "yasui" / "figure2-cp2-a1-crossing-table.json"
CONTEXT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure2-cp2-a1-tham511-context-v1.json"
COMPARE_PATH = REPO_ROOT / "experiments" / "sage" / "yasui_figure2_cp2_a1_su2_2_tham511_compare.sage.py"
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.local_piece import braid_closure_linking_matrix  # noqa: E402
from twisted_yetter.yasui_figure2_cp2 import (  # noqa: E402
    load_crossing_table,
    source_framings,
    source_order,
    source_oriented_gauss_code,
    source_target_matrix,
)


K = CyclotomicField(16)
GLOBAL_DIMENSION = K(4)


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main():
    compare = load_module(COMPARE_PATH, "yasui_cp2_compare_for_convention_sweep")
    oracle = load_module(ORACLE_PATH, "su2_2_braid_oracle_for_convention_sweep")
    payload = compare.r1_remove_a15_curl(load_crossing_table(INPUT))
    context = json.loads(CONTEXT.read_text())

    component_words, crossing_signs, _records = source_oriented_gauss_code(payload)
    components = source_order(payload)
    source_matrix = source_target_matrix(payload)
    visible_writhe = {
        component["id"]: int(component.get("visible_self_writhe", 0))
        for component in payload["components"]
    }
    total_framing = dict(zip(components, source_framings(payload), strict=True))
    extra_framing = {
        component: total_framing[component] - visible_writhe.get(component, 0)
        for component in components
    }
    assignments = context["legal_character_assignments"]["assignments"]
    standard = [
        oracle.omega_value(ZZ(1), (), (ZZ(1),), (ZZ(0),)),
        oracle.omega_value(ZZ(1), (), (ZZ(1),), (ZZ(1),)),
    ]

    for flip_words in (False, True):
        for flip_signs in (False, True):
            words = (
                [[-entry for entry in component] for component in component_words]
                if flip_words
                else component_words
            )
            signs = [-sign for sign in crossing_signs] if flip_signs else crossing_signs
            try:
                braid = Link([words, signs]).braid()
                n_strands = int(braid.parent().strands())
                braid_word = [int(generator) for generator in braid.Tietze()]
                braid_linking = [
                    [int(entry) for entry in row]
                    for row in braid_closure_linking_matrix(n_strands, tuple(braid_word))
                ]
                permutations = compare.component_permutation(source_matrix, braid_linking)
                selected = compare.choose_component_permutation(components, permutations)
                if selected is None:
                    print(
                        json.dumps(
                            {
                                "flip_words": flip_words,
                                "flip_signs": flip_signs,
                                "status": "no-component-permutation",
                                "braid_linking_matrix": braid_linking,
                                "n_strands": n_strands,
                                "braid_word_length": len(braid_word),
                            },
                            sort_keys=True,
                        )
                    )
                    continue
                component_order = [components[index] for index in selected]
                framings = [extra_framing[component] for component in component_order]
                rows = []
                all_match = True
                for assignment, standard_value in zip(assignments, standard, strict=True):
                    source_labels = assignment["component_omega_labels_by_id"]
                    labels = [int(source_labels[component]) for component in component_order]
                    value = (
                        K(
                            oracle.omega_value(
                                ZZ(n_strands),
                                tuple(ZZ(generator) for generator in braid_word),
                                tuple(ZZ(framing) for framing in framings),
                                tuple(ZZ(label) for label in labels),
                            )
                        )
                        / GLOBAL_DIMENSION**2
                    )
                    match = value == standard_value
                    all_match = all_match and match
                    rows.append(
                        {
                            "h_label": int(assignment["h_label"]),
                            "labels": labels,
                            "normalized_value": str(value),
                            "standard_value": str(standard_value),
                            "match": match,
                        }
                    )
                print(
                    json.dumps(
                        {
                            "flip_words": flip_words,
                            "flip_signs": flip_signs,
                            "status": "pass" if all_match else "needs-review",
                            "component_order": component_order,
                            "framings": framings,
                            "braid_linking_matrix": braid_linking,
                            "n_strands": n_strands,
                            "braid_word_length": len(braid_word),
                            "rows": rows,
                        },
                        sort_keys=True,
                    )
                )
            except Exception as error:
                print(
                    json.dumps(
                        {
                            "flip_words": flip_words,
                            "flip_signs": flip_signs,
                            "status": "error",
                            "error_type": type(error).__name__,
                            "error": str(error),
                        },
                        sort_keys=True,
                    )
                )


if __name__ == "__main__":
    main()
