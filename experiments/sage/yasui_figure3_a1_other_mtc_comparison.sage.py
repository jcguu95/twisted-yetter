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

from sage.all import CyclotomicField, Matrix, ZZ
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


def matrix_without_diagonal(matrix):
    return [[0 if row == column else int(entry) for column, entry in enumerate(line)] for row, line in enumerate(matrix)]


def vec_z3_comparison(yasui):
    standard_matrix = [[1, 0, 0], [0, -1, 0], [0, 0, -1]]
    yasui_matrix_source_order = yasui["source_target_intersection_matrix"]
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


def blocked_nonpointed_categories():
    return [
        {
            "category_id": "SU(2)_6",
            "status": "blocked-no-arbitrary-link-evaluator",
            "reason": (
                "Current SU(2)_6 artifacts cover modular data, split unlinks, Hopf pairs, "
                "and specific Kirby-slide stress classes.  They explicitly reject arbitrary "
                "colored-link evaluation for a Yasui 8-strand braid closure."
            ),
            "blocking_artifacts": [
                "experiments/results/mtc-candidates/su2-6-modular-supported-v1.json",
                "experiments/results/sage-stress/su2-6-kirby-slide-stress-v1.json",
                "experiments/results/sage-stress/su2-6-nontrivial-slide-stress-v1.json",
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
    result = {
        "schema": "twisted-yetter.yasui-figure3-a1-other-mtc-comparison.v1",
        "status": "pass-with-blocked-nonpointed" if vec_z3["status"] == "pass" else "mismatch",
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
    return 0 if vec_z3["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
