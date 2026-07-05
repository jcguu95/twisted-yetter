"""Compare R1-normalized Yasui Figure 3 (a=1) against standard CP2#2CPbar for SU(2)_k.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_r1_normalized_su2_levels_comparison.sage.py

This is a diagnostic level sweep.  It asks whether the mismatch seen for
SU(2)_6 is already present at smaller even levels under the same fusion-braid
evaluator.  It records both raw comparison values and the current
source-basis-orientation phase correction det(P)=-1 used by the SU(2)_2 audit.
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


REPO_ROOT = Path(__file__).resolve().parents[2]
YASUI_PAYLOAD = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-braid-payload-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-r1-normalized-su2-levels-comparison-v1.json"
)
SU2K_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"


CF = ComplexField(120)
BASIS_ORIENTATION_PHASE = -1


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


def omega_from_sector_cache(evaluator, sector_cache, omega_labels):
    total = evaluator.zero()
    for fixed_labels, amplitude in sector_cache.items():
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(omega_labels, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * amplitude
    return total


def yasui_labels_for_level(yasui, alpha, modulus):
    alpha_h, alpha_e1, alpha_e2 = alpha
    by_source = {
        "A": alpha_e2 % modulus,
        "B": alpha_h % modulus,
        "C": alpha_e1 % modulus,
    }
    return tuple(by_source[name] for name in yasui["omega_label_order"])


def compare_level(su2k, yasui, level):
    evaluator = su2k.SU2KBraidEvaluator(level, exact=False, precision=120)
    started = time.time()
    yasui_cache = evaluator.sector_amplitudes(
        int(yasui["n_strands"]),
        tuple(int(generator) for generator in yasui["braid_word"]),
        tuple(int(framing) for framing in yasui["framings_in_braid_order"]),
    )
    standard_cache = evaluator.sector_amplitudes(3, (), (1, -1, -1))
    modulus = 2
    tolerance = CF("1e-10")
    rows = []
    all_close = True
    all_phase_corrected_close = True
    max_abs_difference = CF(0)
    max_phase_corrected_abs_difference = CF(0)
    raw_constant_ratio = None
    raw_ratio_constant = True
    for alpha in product(range(modulus), repeat=3):
        standard_labels = alpha
        yasui_labels = yasui_labels_for_level(yasui, alpha, modulus)
        standard_value = omega_from_sector_cache(evaluator, standard_cache, standard_labels)
        yasui_value = omega_from_sector_cache(evaluator, yasui_cache, yasui_labels)
        difference = CF(yasui_value - standard_value)
        phase_corrected_standard_value = BASIS_ORIENTATION_PHASE * standard_value
        phase_corrected_difference = CF(yasui_value - phase_corrected_standard_value)
        abs_difference = abs(difference)
        phase_corrected_abs_difference = abs(phase_corrected_difference)
        max_abs_difference = max(max_abs_difference, abs_difference)
        max_phase_corrected_abs_difference = max(
            max_phase_corrected_abs_difference,
            phase_corrected_abs_difference,
        )
        close = bool(abs_difference < tolerance)
        phase_corrected_close = bool(phase_corrected_abs_difference < tolerance)
        all_close = all_close and close
        all_phase_corrected_close = all_phase_corrected_close and phase_corrected_close
        ratio = CF(yasui_value / standard_value) if standard_value != 0 else None
        if raw_constant_ratio is None:
            raw_constant_ratio = ratio
        elif ratio is not None and abs(CF(ratio - raw_constant_ratio)) >= tolerance:
            raw_ratio_constant = False
        rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(item) for item in alpha],
                "standard_omega_labels": list(standard_labels),
                "yasui_omega_label_order": yasui["omega_label_order"],
                "yasui_omega_labels": list(yasui_labels),
                "standard_raw_value": complex_json(standard_value),
                "yasui_raw_value": complex_json(yasui_value),
                "raw_yasui_over_standard_ratio": complex_json(ratio) if ratio is not None else None,
                "difference": complex_json(difference),
                "abs_difference": str(abs_difference),
                "close_under_tolerance": close,
                "basis_orientation_phase": BASIS_ORIENTATION_PHASE,
                "phase_corrected_standard_value": complex_json(phase_corrected_standard_value),
                "phase_corrected_difference": complex_json(phase_corrected_difference),
                "phase_corrected_abs_difference": str(phase_corrected_abs_difference),
                "phase_corrected_close_under_tolerance": phase_corrected_close,
            }
        )
    if all_close:
        status = "raw-numerical-pass"
    elif all_phase_corrected_close:
        status = "phase-corrected-numerical-pass"
    else:
        status = "numerical-mismatch"
    return {
        "category_id": f"SU(2)_{level}",
        "status": status,
        "elapsed_seconds": time.time() - started,
        "tolerance": str(tolerance),
        "max_abs_difference": str(max_abs_difference),
        "basis_orientation_phase": BASIS_ORIENTATION_PHASE,
        "raw_ratio_constant": raw_ratio_constant,
        "raw_yasui_over_standard_ratio": complex_json(raw_constant_ratio) if raw_constant_ratio is not None else None,
        "max_phase_corrected_abs_difference": str(max_phase_corrected_abs_difference),
        "yasui_fixed_sector_count": len(yasui_cache),
        "standard_fixed_sector_count": len(standard_cache),
        "framing_convention": {
            "yasui_component_order": yasui["omega_label_order"],
            "yasui_total_framings": yasui["framings_in_braid_order"],
            "yasui_blackboard_self_writhe": list(
                evaluator.blackboard_self_writhe(
                    int(yasui["n_strands"]),
                    tuple(int(generator) for generator in yasui["braid_word"]),
                )
            ),
        },
        "rows": rows,
    }


def main():
    su2k = load_module(SU2K_PATH, "su2k_for_yasui_r1_su2_levels")
    yasui = json.loads(YASUI_PAYLOAD.read_text())
    if yasui["status"] != "pass":
        raise ValueError("R1-normalized Yasui braid payload is not pass")

    levels = (2, 4, 6)
    results = [compare_level(su2k, yasui, level) for level in levels]
    status = (
        "phase-corrected-pass"
        if all(result["status"].endswith("numerical-pass") for result in results)
        else "diagnostic-mismatch"
    )
    output = {
        "schema": "twisted-yetter.yasui-figure3-a1-r1-normalized-su2-levels-comparison.v1",
        "status": status,
        "sage_version": SAGE_VERSION,
        "levels": list(levels),
        "comparison_policy": {
            "raw_values_recorded": True,
            "basis_orientation_phase": BASIS_ORIENTATION_PHASE,
            "phase_status": "diagnostic-convention",
        },
        "source": {
            "r1_normalized_payload": str(YASUI_PAYLOAD.relative_to(REPO_ROOT)),
            "standard_presentation": "split unlink with framings (+1,-1,-1)",
        },
        "results": results,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "status": output["status"],
                "artifact": str(OUTPUT.relative_to(REPO_ROOT)),
                "levels": list(levels),
                "summary": [
                    {
                        "category_id": result["category_id"],
                        "status": result["status"],
                        "max_abs_difference": result["max_abs_difference"],
                        "max_phase_corrected_abs_difference": result[
                            "max_phase_corrected_abs_difference"
                        ],
                        "raw_ratio_constant": result["raw_ratio_constant"],
                    }
                    for result in results
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
