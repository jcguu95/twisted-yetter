"""Raw R1-normalized Yasui Figure 3 (a=1) SU(2)_k comparison.

This is the post-R-symbol-fix R1-normalized comparison.  Unlike the older
diagnostic sweep, this script does not apply a basis-orientation phase when
deciding acceptance: after the evaluator fix, the expected check is raw equality
against the standard split presentation.

Run examples:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_r1_normalized_su2_raw_comparison.sage.py --level 6
    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_r1_normalized_su2_raw_comparison.sage.py --level 6 --untwisted-only
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from itertools import product
from pathlib import Path
import sys
import time

from sage.all import ComplexField
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
YASUI_PAYLOAD = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-braid-payload-v1.json"
)
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
RESULT_DIR = REPO_ROOT / "experiments" / "results" / "yasui"
PRECISION = 120
CF = ComplexField(PRECISION)
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
        "field": f"ComplexField({PRECISION})",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
        "abs": str(abs(value)),
    }


def omega_from_sector_cache(evaluator, sector_cache, omega_labels):
    total = evaluator.zero()
    for fixed_labels, amplitude in sector_cache.items():
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(omega_labels, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * amplitude
    return total


def yasui_labels_for_alpha(yasui, alpha):
    alpha_h, alpha_e1, alpha_e2 = alpha
    by_source = {
        "A": alpha_e2,
        "B": alpha_h,
        "C": alpha_e1,
    }
    return tuple(by_source[name] for name in yasui["omega_label_order"])


def output_path(level, untwisted_only):
    mode = "untwisted" if untwisted_only else "all-alpha"
    return RESULT_DIR / f"figure3-a1-r1-normalized-su2-{level}-{mode}-raw-comparison-v2.json"


def compare_level(level, untwisted_only=False):
    su2k = load_module(SU2K_PATH, f"su2k_for_yasui_r1_raw_su2_{level}")
    yasui = json.loads(YASUI_PAYLOAD.read_text())
    if yasui["status"] != "pass":
        raise ValueError("R1-normalized Yasui braid payload is not pass")
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=PRECISION)
    started = time.time()
    yasui_cache = evaluator.sector_amplitudes(
        int(yasui["n_strands"]),
        tuple(int(generator) for generator in yasui["braid_word"]),
        tuple(int(framing) for framing in yasui["framings_in_braid_order"]),
    )
    standard_cache = evaluator.sector_amplitudes(3, (), (1, -1, -1))
    alphas = [(0, 0, 0)] if untwisted_only else list(product((0, 1), repeat=3))
    rows = []
    all_close = True
    max_abs_difference = CF(0)
    for alpha in alphas:
        standard_labels = alpha
        yasui_labels = yasui_labels_for_alpha(yasui, alpha)
        standard_value = omega_from_sector_cache(evaluator, standard_cache, standard_labels)
        yasui_value = omega_from_sector_cache(evaluator, yasui_cache, yasui_labels)
        difference = CF(yasui_value - standard_value)
        abs_difference = abs(difference)
        close = bool(abs_difference < TOLERANCE)
        all_close = all_close and close
        max_abs_difference = max(max_abs_difference, abs_difference)
        rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(item) for item in alpha],
                "standard_omega_labels": [int(item) for item in standard_labels],
                "yasui_omega_label_order": yasui["omega_label_order"],
                "yasui_omega_labels": [int(item) for item in yasui_labels],
                "standard_value": complex_json(standard_value),
                "yasui_value": complex_json(yasui_value),
                "difference": complex_json(difference),
                "abs_difference": str(abs_difference),
                "close_under_tolerance": close,
            }
        )
    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-su2-raw-comparison.v2",
        "status": "pass" if all_close else "mismatch",
        "sage_version": SAGE_VERSION,
        "category_id": f"SU(2)_{level}",
        "alpha_mode": "untwisted" if untwisted_only else "all-alpha",
        "source": {
            "r1_normalized_payload": str(YASUI_PAYLOAD.relative_to(REPO_ROOT)),
            "standard_presentation": "split unlink with framings (+1,-1,-1)",
        },
        "complexity": {
            "yasui_n_strands": int(yasui["n_strands"]),
            "yasui_braid_word_length": len(yasui["braid_word"]),
            "yasui_framings_in_braid_order": yasui["framings_in_braid_order"],
            "yasui_omega_label_order": yasui["omega_label_order"],
            "yasui_fixed_sector_count": len(yasui_cache),
            "standard_fixed_sector_count": len(standard_cache),
        },
        "tolerance": str(TOLERANCE),
        "max_abs_difference": str(max_abs_difference),
        "rows": rows,
        "elapsed_seconds": time.time() - started,
    }
    path = output_path(level, untwisted_only)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": result["status"],
                "artifact": str(path.relative_to(REPO_ROOT)),
                "category_id": result["category_id"],
                "alpha_mode": result["alpha_mode"],
                "max_abs_difference": result["max_abs_difference"],
                "elapsed_seconds": result["elapsed_seconds"],
                "yasui_fixed_sector_count": len(yasui_cache),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if result["status"] == "pass" else 1


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--level", type=int, required=True)
    parser.add_argument("--untwisted-only", action="store_true")
    args = parser.parse_args(argv)
    return compare_level(args.level, untwisted_only=args.untwisted_only)


if __name__ == "__main__":
    raise SystemExit(main())
