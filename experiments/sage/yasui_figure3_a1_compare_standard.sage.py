"""Compare Yasui Figure 3 (a=1) with the standard CP2#2CPbar unlink.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_compare_standard.sage.py

This is a first exact SU(2)_2 comparison.  It compares the raw unnormalized
braid-oracle values as functions of an alpha in Hom(H2, Z/2), using the basis
labels (h,e1,e2).  The Yasui source classes are:

    A = 2h + e2, B = h, C = 2h + e1.

The calibrated braid payload records its own component order.  The comparison
uses the mod-2 reductions:
    A -> e2, B -> h, C -> e1.
"""

from __future__ import annotations

import importlib.util
import json
from itertools import product
from pathlib import Path
import sys

from sage.all import ZZ


REPO_ROOT = Path(__file__).resolve().parents[2]
YASUI_PAYLOAD = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a1-braid-payload-v1.json"
OUTPUT = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a1-standard-comparison-su2-2-v1.json"
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CLASS_MOD_2 = {
    "A": "e2",
    "B": "h",
    "C": "e1",
}


def labels_for_yasui_order(component_order, alpha):
    alpha_by_basis = {"h": alpha[0], "e1": alpha[1], "e2": alpha[2]}
    return tuple(alpha_by_basis[CLASS_MOD_2[component]] for component in component_order)


def main():
    oracle = load_module(ORACLE_PATH, "su2_2_braid_oracle_for_yasui_compare")
    yasui = json.loads(YASUI_PAYLOAD.read_text())
    if yasui["status"] != "pass":
        raise ValueError("Yasui braid payload is not pass")
    yasui_order = list(yasui["omega_label_order"])
    for component in yasui_order:
        if component not in CLASS_MOD_2:
            raise ValueError(f"unexpected Yasui component in omega label order: {component}")

    rows = []
    all_equal = True
    for alpha_h, alpha_e1, alpha_e2 in product((0, 1), repeat=3):
        standard_labels = (alpha_h, alpha_e1, alpha_e2)
        alpha = (alpha_h, alpha_e1, alpha_e2)
        standard_value = oracle.omega_value(
            3,
            (),
            (ZZ(1), ZZ(-1), ZZ(-1)),
            tuple(ZZ(label) for label in standard_labels),
        )
        yasui_labels = labels_for_yasui_order(yasui_order, alpha)
        yasui_recomputed = oracle.omega_value(
            int(yasui["n_strands"]),
            tuple(ZZ(g) for g in yasui["braid_word"]),
            tuple(ZZ(f) for f in yasui["framings_in_braid_order"]),
            tuple(ZZ(label) for label in yasui_labels),
        )
        equal = standard_value == yasui_recomputed
        all_equal = all_equal and bool(equal)
        rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(alpha_h), int(alpha_e1), int(alpha_e2)],
                "standard_omega_label_order": ["h", "e1", "e2"],
                "standard_omega_labels": list(standard_labels),
                "yasui_omega_label_order": yasui_order,
                "yasui_omega_labels": list(yasui_labels),
                "standard_raw_value": oracle.cyclotomic_json(standard_value),
                "yasui_raw_value": oracle.cyclotomic_json(yasui_recomputed),
                "equal_raw_value": bool(equal),
            }
        )

    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-standard-comparison-su2-2.v1",
        "status": "pass" if all_equal else "mismatch",
        "comparison_level": (
            "raw unnormalized SU(2)_2 braid-oracle values as functions of "
            "alpha in Hom(H2,Z/2); no closed-4-manifold global normalization "
            "has been applied"
        ),
        "standard_presentation": {
            "description": "split unlink for CP2#2CPbar",
            "component_order": ["h", "e1", "e2"],
            "framings": [1, -1, -1],
            "n_strands": 3,
            "braid_word": [],
        },
        "yasui_presentation": {
            "source": str(YASUI_PAYLOAD.relative_to(REPO_ROOT)),
            "component_order_in_braid": yasui["omega_label_order"],
            "framings_in_braid_order": yasui["framings_in_braid_order"],
            "class_map_mod_2": {
                key: value for key, value in sorted(CLASS_MOD_2.items())
            },
            "kirby_calibration": yasui.get("kirby_calibration"),
        },
        "rows": rows,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if all_equal else 1


if __name__ == "__main__":
    raise SystemExit(main())
