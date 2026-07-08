"""Untwisted SU(2)_k check for Yasui Figure 2 CP2(a=1), R1-normalized.

This uses the generic SU2KBraidEvaluator.  Its framing argument is the total
component framing; the evaluator subtracts braid blackboard self-writhe
internally.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys
import time

from sage.all import ComplexField
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure2-cp2-a1-r1-su2k-untwisted-check-v1.json"
)

N_STRANDS = 5
BRAID_WORD = (
    1,
    1,
    2,
    3,
    3,
    2,
    1,
    2,
    3,
    2,
    2,
    -4,
    3,
    2,
    1,
    2,
    3,
    3,
    2,
    3,
    4,
    -3,
)
COMPONENT_ORDER_IN_BRAID = ("A", "C", "B")
TOTAL_FRAMINGS_IN_BRAID_ORDER = (4, 4, 1)
OMEGA_LABELS_UNTWISTED = (0, 0, 0)
PRECISION = 160
TOLERANCE = ComplexField(PRECISION)("1e-10")


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def value_json(value):
    approx = ComplexField(PRECISION)(value)
    return {
        "display": str(value),
        "complex_approx": str(approx),
        "real": str(approx.real()),
        "imag": str(approx.imag()),
        "abs": str(abs(approx)),
    }


def level_row(su2k, level, *, exact):
    evaluator = su2k.SU2KBraidEvaluator(level, exact=exact, precision=PRECISION)
    dimensions = [evaluator.dimension(label) for label in evaluator.labels]
    twists = [evaluator.twist(label) for label in evaluator.labels]
    global_dimension = sum(dimension * dimension for dimension in dimensions)
    unknot_plus_one = sum(
        dimensions[index] * dimensions[index] * twists[index]
        for index in range(len(dimensions))
    )
    raw_yasui = evaluator.omega_value(
        N_STRANDS,
        BRAID_WORD,
        TOTAL_FRAMINGS_IN_BRAID_ORDER,
        OMEGA_LABELS_UNTWISTED,
    )
    normalized_yasui = raw_yasui / (global_dimension * global_dimension)
    difference = normalized_yasui - unknot_plus_one
    abs_difference = abs(ComplexField(PRECISION)(difference))
    blackboard_self_writhe = evaluator.blackboard_self_writhe(N_STRANDS, BRAID_WORD)
    return {
        "level": int(level),
        "category_id": f"SU(2)_{level}",
        "labels": [int(label) for label in evaluator.labels],
        "dimensions": [value_json(value) for value in dimensions],
        "twists": [value_json(value) for value in twists],
        "global_dimension_D": value_json(global_dimension),
        "global_dimension_D_squared": value_json(global_dimension * global_dimension),
        "unknot_plus_one_omega0": value_json(unknot_plus_one),
        "yasui_r1_raw": value_json(raw_yasui),
        "yasui_r1_normalized_by_D_squared": value_json(normalized_yasui),
        "difference_normalized_minus_unknot": value_json(difference),
        "abs_difference": str(abs_difference),
        "normalized_matches_unknot_plus_one": bool(
            normalized_yasui == unknot_plus_one if exact else abs_difference < TOLERANCE
        ),
        "blackboard_self_writhe": [int(value) for value in blackboard_self_writhe],
        "total_framings_in_braid_order": list(TOTAL_FRAMINGS_IN_BRAID_ORDER),
        "effective_extra_framing": [
            int(total - writhe)
            for total, writhe in zip(TOTAL_FRAMINGS_IN_BRAID_ORDER, blackboard_self_writhe, strict=True)
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--levels", nargs="+", type=int, default=[2, 4])
    parser.add_argument("--floating", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args(argv)

    started = time.time()
    su2k = load_module(SU2K_PATH, "su2k_for_yasui_figure2_r1_check")
    exact = not args.floating
    rows = [level_row(su2k, level, exact=exact) for level in args.levels]
    result = {
        "schema": "twisted-yetter.yasui-figure2-cp2-a1-r1-su2k-untwisted-check.v1",
        "status": "pass" if all(row["normalized_matches_unknot_plus_one"] for row in rows) else "needs-review",
        "mathematical_status": "COMPUTATIONAL_CHECK_NOT_THEOREM",
        "sage_version": SAGE_VERSION,
        "numeric_mode": "exact" if exact else f"floating ComplexField({PRECISION})",
        "tolerance": str(TOLERANCE),
        "source": {
            "description": "R1-normalized Yasui Figure 2 CP2(a=1) braid from the SU(2)_2 Tham 5.11 comparison artifact",
            "component_order_in_braid": list(COMPONENT_ORDER_IN_BRAID),
            "n_strands": N_STRANDS,
            "braid_word": list(BRAID_WORD),
            "omega_labels_untwisted": list(OMEGA_LABELS_UNTWISTED),
        },
        "normalization": {
            "handle_factor": "divide by D^2 for the two original 3-handles read as dual Tham 5.11 one-handles",
            "framing_convention": "generic SU2KBraidEvaluator takes total framings and subtracts braid blackboard self-writhe internally",
        },
        "rows": rows,
        "elapsed_seconds": time.time() - started,
    }
    if args.write:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
