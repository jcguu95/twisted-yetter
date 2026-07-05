"""Compare Yasui Figure 3 (a=1) with available non-SU(2)_2 MTC evaluators.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/yasui_figure3_a1_other_mtc_comparison.sage.py

This script is intentionally strict about evaluator scope.  It computes the
comparison for Vec_{Z/3}^q because that pointed category reduces framed-link
evaluation to the integer linking matrix.  It records SU(2)_6 and SU(3)_3 as
blocked here because the current repo artifacts explicitly do not implement an
arbitrary colored-link evaluator for the Yasui braid/link.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path
import sys
import time
import importlib.util

from sage.all import ComplexField, CyclotomicField, Matrix, ZZ
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
YASUI_PAYLOAD = REPO_ROOT / "experiments" / "results" / "yasui" / "figure3-a1-braid-payload-v1.json"
OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "yasui"
    / "figure3-a1-other-mtc-comparison-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))


FIELD_Z3 = CyclotomicField(3)
ZETA3 = FIELD_Z3.gen()
CF = ComplexField(120)
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"


def quadratic_exponent_mod3(entries, simple_labels):
    size = len(simple_labels)
    exponent = 0
    for index, simple in enumerate(simple_labels):
        exponent += simple * simple * entries[index][index]
    for left in range(size):
        for right in range(left + 1, size):
            exponent += 2 * simple_labels[left] * simple_labels[right] * entries[left][right]
    return exponent % 3


def vec_z3_omega_value(linking_matrix, omega_labels):
    size = len(linking_matrix)
    label_vectors = tuple(product(range(3), repeat=size))
    counts = [0, 0, 0]
    for simple_labels in label_vectors:
        quadratic_exponent = quadratic_exponent_mod3(linking_matrix, simple_labels)
        character_exponent = sum(
            omega_label * simple_label
            for omega_label, simple_label in zip(omega_labels, simple_labels, strict=True)
        )
        counts[(quadratic_exponent + character_exponent) % 3] += 1
    return FIELD_Z3(counts[0]) + FIELD_Z3(counts[1]) * ZETA3 + FIELD_Z3(counts[2]) * ZETA3**2


def cyclotomic_z3_json(value):
    value = FIELD_Z3(value)
    return {
        "field": "CyclotomicField(3)",
        "zeta_symbol": "zeta3",
        "display": str(value),
        "coefficients": [str(coefficient) for coefficient in value.list()],
    }


def complex_json(value):
    value = CF(value)
    return {
        "field": "ComplexField(120)",
        "display": str(value),
        "real": str(value.real()),
        "imag": str(value.imag()),
        "abs": str(abs(value)),
    }


def matrix_without_diagonal(matrix):
    return [[0 if row == column else int(entry) for column, entry in enumerate(line)] for row, line in enumerate(matrix)]


def expected_yasui_source_matrix_from_standard_form():
    return [
        [3, 2, 4],
        [2, 1, 2],
        [4, 2, 3],
    ]


def blocked_vec_z3_comparison(yasui, reason):
    return {
        "category_id": "Vec_Z3_q",
        "status": "blocked-yasui-braid-payload-not-admitted",
        "scope": "pointed linking-matrix evaluator; exact comparison for Hom(H2,Z/3) is blocked before evaluation",
        "reason": reason,
        "standard_matrix": [[1, 0, 0], [0, -1, 0], [0, 0, -1]],
        "observed_yasui_matrix_source_order": yasui["source_target_intersection_matrix"],
        "expected_yasui_matrix_source_order": expected_yasui_source_matrix_from_standard_form(),
        "class_map_mod_3": {
            "A": "2h+e2",
            "B": "h",
            "C": "2h+e1",
        },
        "rows": [],
    }


def vec_z3_comparison(yasui):
    standard_matrix = [[1, 0, 0], [0, -1, 0], [0, 0, -1]]
    yasui_matrix_source_order = yasui["source_target_intersection_matrix"]
    expected_matrix = expected_yasui_source_matrix_from_standard_form()
    if yasui_matrix_source_order != expected_matrix:
        return blocked_vec_z3_comparison(
            yasui,
            (
                "Current Yasui payload source matrix does not match the matrix "
                "induced from the standard CP2#2CPbar form by the recorded class "
                "map A=2h+e2, B=h, C=2h+e1.  Treat this as payload admission "
                "failure, not as an invariant comparison."
            ),
        )
    if yasui["source_ordered_braid_linking_matrix"] != matrix_without_diagonal(yasui_matrix_source_order):
        raise ValueError("Yasui braid payload does not match target off-diagonal matrix")

    rows = []
    all_equal = True
    for alpha_h, alpha_e1, alpha_e2 in product(range(3), repeat=3):
        standard_labels = (alpha_h, alpha_e1, alpha_e2)
        yasui_labels_source_order = (
            (2 * alpha_h + alpha_e2) % 3,
            alpha_h,
            (2 * alpha_h + alpha_e1) % 3,
        )
        standard_value = vec_z3_omega_value(standard_matrix, standard_labels)
        yasui_value = vec_z3_omega_value(yasui_matrix_source_order, yasui_labels_source_order)
        equal = standard_value == yasui_value
        all_equal = all_equal and bool(equal)
        rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(alpha_h), int(alpha_e1), int(alpha_e2)],
                "standard_component_order": ["h", "e1", "e2"],
                "standard_omega_labels": list(standard_labels),
                "yasui_component_order": ["A", "B", "C"],
                "yasui_omega_labels": list(yasui_labels_source_order),
                "standard_raw_value": cyclotomic_z3_json(standard_value),
                "yasui_raw_value": cyclotomic_z3_json(yasui_value),
                "equal_raw_value": bool(equal),
            }
        )

    return {
        "category_id": "Vec_Z3_q",
        "status": "pass" if all_equal else "mismatch",
        "scope": "pointed linking-matrix evaluator; exact comparison for all 27 alpha in Hom(H2,Z/3)",
        "standard_matrix": standard_matrix,
        "yasui_matrix_source_order": yasui_matrix_source_order,
        "class_map_mod_3": {
            "A": "2h+e2",
            "B": "h",
            "C": "2h+e1",
        },
        "rows": rows,
    }


def load_su2k_evaluator_module():
    spec = importlib.util.spec_from_file_location("su2k_fusion_braid_evaluator", SU2K_EVALUATOR)
    module = importlib.util.module_from_spec(spec)
    sys.modules["su2k_fusion_braid_evaluator"] = module
    spec.loader.exec_module(module)
    return module


def omega_from_sector_cache(evaluator, sector_cache, omega_labels):
    total = evaluator.zero()
    for fixed_labels, amplitude in sector_cache.items():
        coefficient = evaluator.one()
        for omega_label, simple_label in zip(omega_labels, fixed_labels, strict=True):
            coefficient *= evaluator.dimension(simple_label) * evaluator.character(omega_label, simple_label)
        total += coefficient * amplitude
    return total


def su2_6_numerical_comparison(yasui):
    module = load_su2k_evaluator_module()
    evaluator = module.SU2KBraidEvaluator(6, exact=False, precision=120)
    started = time.time()

    yasui_braid_word = tuple(int(generator) for generator in yasui["braid_word"])
    yasui_framings = tuple(int(framing) for framing in yasui["framings_in_braid_order"])
    yasui_sector_cache = evaluator.sector_amplitudes(
        int(yasui["n_strands"]),
        yasui_braid_word,
        yasui_framings,
    )

    standard_sector_cache = evaluator.sector_amplitudes(
        3,
        (),
        (1, -1, -1),
    )

    rows = []
    max_abs_difference = CF(0)
    tolerance = CF("1e-70")
    all_close = True
    for alpha_h, alpha_e1, alpha_e2 in product((0, 1), repeat=3):
        standard_labels = (alpha_h, alpha_e1, alpha_e2)
        yasui_by_source = {
            "A": alpha_e2,
            "B": alpha_h,
            "C": alpha_e1,
        }
        yasui_labels = tuple(yasui_by_source[name] for name in yasui["omega_label_order"])
        standard_value = omega_from_sector_cache(evaluator, standard_sector_cache, standard_labels)
        yasui_value = omega_from_sector_cache(evaluator, yasui_sector_cache, yasui_labels)
        difference = CF(yasui_value - standard_value)
        abs_difference = abs(difference)
        max_abs_difference = max(max_abs_difference, abs_difference)
        close = bool(abs_difference < tolerance)
        all_close = all_close and close
        rows.append(
            {
                "alpha_basis_order": ["h", "e1", "e2"],
                "alpha": [int(alpha_h), int(alpha_e1), int(alpha_e2)],
                "standard_component_order": ["h", "e1", "e2"],
                "standard_omega_labels": list(standard_labels),
                "yasui_component_order": list(yasui["omega_label_order"]),
                "yasui_omega_labels": list(yasui_labels),
                "standard_raw_value": complex_json(standard_value),
                "yasui_raw_value": complex_json(yasui_value),
                "difference": complex_json(difference),
                "abs_difference": str(abs_difference),
                "close_under_tolerance": close,
            }
        )

    return {
        "category_id": "SU(2)_6",
        "status": "numerical-pass" if all_close else "numerical-mismatch",
        "claim_level": "high-precision numerical evidence from mixed-color fusion-braid evaluator",
        "scope": "all 8 alpha in Hom(H2,Z/2) for Yasui Figure 3 a=1 versus standard CP2#2CPbar presentation",
        "not_scope": "exact certificate, arbitrary MTC evaluator, SU(3)_3 evaluator, dotted/special-link evaluator",
        "precision_bits": 120,
        "tolerance": str(tolerance),
        "elapsed_seconds": time.time() - started,
        "yasui_fixed_sector_count": len(yasui_sector_cache),
        "standard_fixed_sector_count": len(standard_sector_cache),
        "max_abs_difference": str(max_abs_difference),
        "rows": rows,
    }


def blocked_nonpointed_categories():
    return [
        {
            "category_id": "SU(2)_6",
            "status": "blocked-yasui-braid-payload-not-admitted",
            "reason": (
                "The mixed-color SU(2)_k fusion-braid evaluator now passes the "
                "Yasui Figure 3 a=1 SU(2)_2 fixed-sector calibration against the "
                "existing braid oracle and can compute the full SU(2)_6 sector "
                "cache numerically.  However, applying it to the current Yasui "
                "braid payload gives a large mismatch against the split standard "
                "CP2#2CPbar presentation.  Since SU(2)_6 sees link type beyond "
                "the linking matrix, this is treated as an admission failure of "
                "the current digitized Yasui braid payload, not as an exotic or "
                "invariant claim."
            ),
            "latest_checks": [
                "SU(2)_2 fixed-sector Yasui calibration: pass, max difference < 1e-12",
                "SU(2)_6 fusion-braid calibration gate: pass on unknots, split unlinks, Hopf links, one-component braid knots, and Omega expansions",
                "SU(2)_6 Yasui sector cache: completes numerically in about 32-37 seconds on this machine",
                "SU(2)_6 standard-vs-Yasui comparison: numerical mismatch, max absolute difference about 2.4e3",
                "Existing SU(2)_6 Kirby-slide stress suite: pass, 1088 exact comparisons",
            ],
            "blocking_artifacts": [
                "experiments/sage/su2k_fusion_braid_evaluator.sage.py",
                "experiments/results/yasui/figure3-a1-braid-payload-v1.json",
            ],
        },
        {
            "category_id": "SU(3)_3",
            "status": "blocked-no-arbitrary-link-evaluator",
            "reason": (
                "Current SU(3)_3 artifact proves category-level coefficient identities for "
                "the stress-suite move classes, but explicitly says there is no arbitrary "
                "SU(3)_3 link-polynomial or F/R tensor-network backend."
            ),
            "blocking_artifacts": [
                "experiments/results/mtc-candidates/su3-3-multiplicity-stress-v1.json",
            ],
        },
    ]


def main():
    yasui = json.loads(YASUI_PAYLOAD.read_text())
    if yasui["status"] != "pass":
        raise ValueError("Yasui braid payload is not pass")

    vec_z3 = vec_z3_comparison(yasui)
    blocked = blocked_nonpointed_categories()
    status = (
        "pass-with-blocked-nonpointed"
        if vec_z3["status"] == "pass"
        else "blocked-yasui-braid-payload-not-admitted"
    )
    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-other-mtc-comparison.v1",
        "status": status,
        "sage_version": SAGE_VERSION,
        "source": {
            "yasui_payload": str(YASUI_PAYLOAD.relative_to(REPO_ROOT)),
            "standard_presentation": "split unlink with framings (+1,-1,-1)",
        },
        "computed_categories": [vec_z3],
        "blocked_categories": blocked,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
