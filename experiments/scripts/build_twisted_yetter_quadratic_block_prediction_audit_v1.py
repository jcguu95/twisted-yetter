#!/usr/bin/env python3
"""Audit all eligible saved data against the modular quadratic-block prediction."""

from __future__ import annotations

import cmath
from datetime import UTC, datetime
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import platform
import subprocess
import sys
import time
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    REPO_ROOT
    / "experiments/results/theory/"
    "twisted-yetter-quadratic-block-prediction-audit-v1.json"
)
TOLERANCE = 1e-8

SU2_A1_PATHS = {
    2: "experiments/results/yasui/figure3-a1-r1-normalized-su2-2-all-alpha-raw-comparison-v3.json",
    3: "experiments/results/yasui/figure3-a1-r1-normalized-su2-3-all-alpha-raw-comparison-v2.json",
    4: "experiments/results/yasui/figure3-a1-r1-normalized-su2-4-all-alpha-raw-comparison-v3.json",
    6: "experiments/results/yasui/figure3-a1-r1-normalized-su2-6-all-alpha-raw-comparison-v2.json",
    8: "experiments/results/yasui/figure3-a1-r1-normalized-su2-8-all-alpha-raw-comparison-v3.json",
}
SU2_A3_PATHS = {
    2: "experiments/results/yasui/figure3-a3-su2-2-all-alpha-chunked-comparison-v1.json",
    3: "experiments/results/yasui/figure3-a3-su2-3-all-alpha-chunked-comparison-v1.json",
    4: "experiments/results/yasui/figure3-a3-su2-4-all-alpha-chunked-comparison-v1.json",
    6: "experiments/results/yasui/figure3-a3-su2-6-all-alpha-chunked-comparison-v1.json",
}
PATHS = {
    "su3_figure2": (
        "experiments/results/yasui/"
        "figure2-cp2-a1-r1-su3-2-anyonwiki-h2-character-check-v1.json"
    ),
    "su3_figure3": (
        "experiments/results/yasui/"
        "figure3-a1-su3-2-yasui-vs-split-coordinate-comparison-v1.json"
    ),
    "su3_small_handles": (
        "experiments/results/small-handle-examples/"
        "su3-2-standard-form-character-controls-v1.json"
    ),
    "da4_split": (
        "experiments/results/yasui/"
        "figure3-a1-standard-split-unlink-da4-c3w1-character-scan-v1.json"
    ),
    "figure21_compatibility": (
        "experiments/results/theory/"
        "twisted-yetter-stable-no-go-computational-audit-v1.json"
    ),
}


class AuditError(ValueError):
    """Raised when a pinned input no longer supports the prediction audit."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return f"sha256:{digest.hexdigest()}"


def _content_hash(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _relative(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path.resolve())


def _complex(value: Mapping[str, Any]) -> complex:
    return complex(float(value["real"]), float(value["imag"]))


def _complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def _close(left: complex, right: complex, tolerance: float = TOLERANCE) -> bool:
    return abs(left - right) <= tolerance


def _resolve(
    key: str,
    default: str,
    overrides: Mapping[str, Path] | None,
) -> Path:
    if overrides and key in overrides:
        return overrides[key]
    return REPO_ROOT / default


def _load(
    key: str,
    default: str,
    overrides: Mapping[str, Path] | None,
) -> tuple[Path, dict[str, Any]]:
    path = _resolve(key, default, overrides)
    _require(path.is_file(), f"missing audit input: {path}")
    return path, json.loads(path.read_text())


def _artifact_ref(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "path": _relative(path),
        "sha256": _sha256(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def _invert_integer_matrix(matrix: list[list[int]]) -> list[list[int]]:
    size = len(matrix)
    _require(size > 0, "intersection matrix must be nonempty")
    _require(all(len(row) == size for row in matrix), "intersection matrix must be square")
    augmented = [
        [Fraction(value) for value in row]
        + [Fraction(int(index == column)) for column in range(size)]
        for index, row in enumerate(matrix)
    ]
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if augmented[row][column]),
            None,
        )
        _require(pivot is not None, "intersection matrix is singular")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [entry / scale for entry in augmented[column]]
        for row in range(size):
            if row == column:
                continue
            scale = augmented[row][column]
            augmented[row] = [
                left - scale * right
                for left, right in zip(
                    augmented[row], augmented[column], strict=True
                )
            ]
    inverse_fraction = [row[size:] for row in augmented]
    _require(
        all(entry.denominator == 1 for row in inverse_fraction for entry in row),
        "intersection matrix is not integrally unimodular",
    )
    return [[int(entry) for entry in row] for row in inverse_fraction]


def _quadratic_exponent(vector: list[int], matrix: list[list[int]]) -> int:
    return sum(
        int(vector[left]) * int(matrix[left][right]) * int(vector[right])
        for left in range(len(vector))
        for right in range(len(vector))
    )


def _su2_dimension(level: int, label: int) -> float:
    angle = math.pi / (level + 2)
    return math.sin((label + 1) * angle) / math.sin(angle)


def _su2_twist(level: int, label: int) -> complex:
    return cmath.exp(1j * math.pi * label * (label + 2) / (2 * (level + 2)))


def _su2_gauss_sum(level: int, framing: int, character: int) -> complex:
    return sum(
        _su2_dimension(level, label) ** 2
        * _su2_twist(level, label) ** framing
        * (-1) ** (character * label)
        for label in range(level + 1)
    )


def _su2_q(level: int, character: int) -> complex:
    return cmath.exp(-1j * math.pi * level * character * character / 2)


def _audit_su2_table(
    path: Path,
    payload: dict[str, Any],
    *,
    level: int,
    presentation_id: str,
) -> dict[str, Any]:
    _require(payload.get("status") == "pass", f"{path.name}: status is not pass")
    _require(payload.get("alpha_mode") == "all-alpha", f"{path.name}: not all-alpha")
    _require(
        payload.get("category_id") == f"SU(2)_{level}",
        f"{path.name}: category id changed",
    )
    rows = payload.get("rows", [])
    _require(len(rows) == 8, f"{path.name}: expected 8 all-alpha rows")
    expected_alphas = {
        (left, middle, right)
        for left in range(2)
        for middle in range(2)
        for right in range(2)
    }
    actual_alphas = {tuple(int(value) for value in row["alpha"]) for row in rows}
    _require(actual_alphas == expected_alphas, f"{path.name}: alpha denominator changed")

    positive = {alpha: _su2_gauss_sum(level, 1, alpha) for alpha in range(2)}
    negative = {alpha: _su2_gauss_sum(level, -1, alpha) for alpha in range(2)}
    q_values = {alpha: _su2_q(level, alpha) for alpha in range(2)}
    for alpha in range(2):
        _require(
            _close(positive[alpha] / positive[0], q_values[alpha]),
            f"{path.name}: positive Gauss ratio is not inverse simple-current twist",
        )
        _require(
            _close(negative[alpha] / negative[0], q_values[alpha] ** -1),
            f"{path.name}: negative Gauss ratio is not inverse quadratic phase",
        )

    max_block_standard_error = 0.0
    max_quadratic_standard_error = 0.0
    max_block_target_error = 0.0
    max_factorization_error = 0.0
    standard_values: dict[tuple[int, int, int], complex] = {}
    for row in rows:
        alpha = tuple(int(value) for value in row["alpha"])
        _require(
            row.get("alpha_basis_order") == ["h", "e1", "e2"],
            f"{path.name}: alpha basis order changed",
        )
        standard = _complex(row["standard_value"])
        target = _complex(row["yasui_value"])
        block_prediction = (
            positive[alpha[0]] * negative[alpha[1]] * negative[alpha[2]]
        )
        phase = q_values[alpha[0]] * q_values[alpha[1]] ** -1 * q_values[
            alpha[2]
        ] ** -1
        quadratic_prediction = (
            positive[0] * negative[0] * negative[0] * phase
        )
        max_block_standard_error = max(
            max_block_standard_error, abs(standard - block_prediction)
        )
        max_quadratic_standard_error = max(
            max_quadratic_standard_error, abs(standard - quadratic_prediction)
        )
        max_block_target_error = max(
            max_block_target_error, abs(target - block_prediction)
        )
        standard_values[alpha] = standard

    baseline = standard_values[(0, 0, 0)]
    for alpha, value in standard_values.items():
        factorized = (
            standard_values[(alpha[0], 0, 0)]
            * standard_values[(0, alpha[1], 0)]
            * standard_values[(0, 0, alpha[2])]
            / baseline**2
        )
        max_factorization_error = max(
            max_factorization_error, abs(value - factorized)
        )

    for label, error in {
        "block-to-standard": max_block_standard_error,
        "quadratic-to-standard": max_quadratic_standard_error,
        "block-to-target": max_block_target_error,
        "table-factorization": max_factorization_error,
    }.items():
        _require(error <= TOLERANCE, f"{path.name}: {label} error {error} exceeds tolerance")

    return {
        "presentation_id": presentation_id,
        "category_id": f"SU(2)_{level}",
        "coefficient_group": "Z/2",
        "intersection_form": [[1, 0, 0], [0, -1, 0], [0, 0, -1]],
        "alpha_basis_order": ["h", "e1", "e2"],
        "row_count": len(rows),
        "status": "PASS_ABSOLUTE_BLOCK_AND_QUADRATIC_PREDICTION",
        "category_quadratic_function": {
            "formula": "q_eval(a)=exp(-pi*i*k*a^2/2)",
            "simple_current_twist_formula": "theta_k=exp(pi*i*k/2)",
            "orientation_convention": "q_eval=theta_k^(-1) on the +1 block",
            "values": {
                str(alpha): _complex_json(value)
                for alpha, value in q_values.items()
            },
        },
        "one_component_gauss_sums": {
            "+1": {
                str(alpha): _complex_json(value)
                for alpha, value in positive.items()
            },
            "-1": {
                str(alpha): _complex_json(value)
                for alpha, value in negative.items()
            },
        },
        "max_errors": {
            "block_prediction_vs_standard": repr(max_block_standard_error),
            "quadratic_prediction_vs_standard": repr(max_quadratic_standard_error),
            "block_prediction_vs_target": repr(max_block_target_error),
            "direct_table_factorization": repr(max_factorization_error),
        },
        "source": _artifact_ref(path, payload),
    }


def _selected_su3_category(payload: dict[str, Any]) -> dict[str, Any]:
    _require(
        payload.get("status") == "pass_with_convention_warning",
        "SU(3)_2 Figure 2 convention artifact status changed",
    )
    selected = payload.get("selected_convention", {})
    parameter = selected.get("category_parameter")
    convention = selected.get("braiding_convention")
    rows = [
        row
        for row in payload.get("rows", [])
        if row.get("category", {}).get("anyonwiki_category_parameter") == parameter
        and row.get("category", {}).get("braiding_convention") == convention
    ]
    _require(len(rows) == 1, "SU(3)_2 selected convention is not unique")
    row = rows[0]
    _require(row.get("all_character_rows_match") is True, "selected SU(3)_2 CP2 row fails")
    _require(len(row.get("character_rows", [])) == 3, "selected SU(3)_2 CP2 row is incomplete")
    return row["category"]


def _su3_gauss_sum(
    category: dict[str, Any],
    framing: int,
    character: int,
) -> complex:
    zeta = cmath.exp(2j * math.pi / 3)
    total = 0.0 + 0.0j
    for label in category["simple_labels"]:
        dimension = float(category["quantum_dimensions"][label])
        twist = _complex(category["twists"][label])
        triality = int(category["triality"][label])
        total += (
            dimension**2
            * twist**framing
            * zeta ** (int(character) * triality)
        )
    return total


def _audit_su3_figure2(
    path: Path,
    payload: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    category = _selected_su3_category(payload)
    selected_row = next(
        row
        for row in payload["rows"]
        if row["category"]["anyonwiki_category_parameter"]
        == payload["selected_convention"]["category_parameter"]
        and row["category"]["braiding_convention"]
        == payload["selected_convention"]["braiding_convention"]
    )
    positive = {alpha: _su3_gauss_sum(category, 1, alpha) for alpha in range(3)}
    negative = {alpha: _su3_gauss_sum(category, -1, alpha) for alpha in range(3)}
    zeta = cmath.exp(2j * math.pi / 3)
    q_values = {alpha: zeta ** (alpha * alpha) for alpha in range(3)}
    max_gauss_ratio_error = 0.0
    max_figure2_error = 0.0
    for alpha in range(3):
        max_gauss_ratio_error = max(
            max_gauss_ratio_error,
            abs(positive[alpha] / positive[0] - q_values[alpha]),
            abs(negative[alpha] / negative[0] - q_values[alpha] ** -1),
        )
        char_row = next(
            row
            for row in selected_row["character_rows"]
            if int(row["standard_cp2_character_power"]) == alpha
        )
        max_figure2_error = max(
            max_figure2_error,
            abs(_complex(char_row["standard_unknot_plus_one_value"]) - positive[alpha]),
            abs(_complex(char_row["yasui_r1_normalized_by_D_squared"]) - positive[alpha]),
        )
    _require(
        max_gauss_ratio_error <= TOLERANCE,
        "SU(3)_2 Gauss ratios do not define q(a)=zeta3^(a^2)",
    )
    _require(
        max_figure2_error <= TOLERANCE,
        "SU(3)_2 Figure 2 values do not match the +1 block prediction",
    )

    invertible_labels = [
        label
        for label in category["simple_labels"]
        if abs(float(category["quantum_dimensions"][label]) - 1.0) <= TOLERANCE
    ]
    nonunit_invertibles = [label for label in invertible_labels if label != "(0,0)"]
    _require(
        set(nonunit_invertibles) == {"(2,0)", "(0,2)"},
        "SU(3)_2 invertible labels changed",
    )
    for label in nonunit_invertibles:
        _require(
            _close(_complex(category["twists"][label]), zeta**-1),
            "SU(3)_2 simple-current twist no longer equals zeta3^(-1)",
        )

    result = {
        "status": "PASS_CP2_BLOCK_CALIBRATION_AND_SIMPLE_CURRENT_SIGN",
        "row_count": 3,
        "selected_category_parameter": category["anyonwiki_category_parameter"],
        "selected_braiding_convention": category["braiding_convention"],
        "coefficient_group": "Z/3",
        "category_quadratic_function": {
            "formula": "q_eval(a)=zeta3^(a^2)",
            "invertible_object_twist": "theta=zeta3^(-1)",
            "orientation_convention": "q_eval=theta^(-1) on the +1 block",
            "values": {
                str(alpha): _complex_json(value)
                for alpha, value in q_values.items()
            },
        },
        "one_component_gauss_sums": {
            "+1": {
                str(alpha): _complex_json(value)
                for alpha, value in positive.items()
            },
            "-1": {
                str(alpha): _complex_json(value)
                for alpha, value in negative.items()
            },
        },
        "max_gauss_ratio_error": repr(max_gauss_ratio_error),
        "max_figure2_absolute_error": repr(max_figure2_error),
        "source": _artifact_ref(path, payload),
    }
    return result, {
        "category": category,
        "positive": positive,
        "negative": negative,
        "q_values": q_values,
    }


def _audit_su3_figure3(
    path: Path,
    payload: dict[str, Any],
    calibration: dict[str, Any],
) -> dict[str, Any]:
    _require(payload.get("status") == "pass", "SU(3)_2 coordinate comparison is not pass")
    _require(
        payload.get("coordinate_map", {}).get("standard_alpha_order")
        == ["h", "e1", "e2"],
        "SU(3)_2 standard alpha order changed",
    )
    rows = payload.get("mapped_rows", [])
    _require(len(rows) == 27, "SU(3)_2 mapped all-alpha denominator is not 27")
    expected_alphas = {
        (left, middle, right)
        for left in range(3)
        for middle in range(3)
        for right in range(3)
    }
    actual_alphas = {
        tuple(int(value) for value in row["standard_alpha_he1e2_mapped"])
        for row in rows
    }
    _require(actual_alphas == expected_alphas, "SU(3)_2 mapped alpha denominator changed")

    positive = calibration["positive"]
    negative = calibration["negative"]
    q_values = calibration["q_values"]
    max_block_standard_error = 0.0
    max_quadratic_standard_error = 0.0
    max_block_target_error = 0.0
    max_factorization_error = 0.0
    standard_values: dict[tuple[int, int, int], complex] = {}
    for row in rows:
        alpha = tuple(int(value) for value in row["standard_alpha_he1e2_mapped"])
        standard = _complex(row["split_raw_mapped"])
        target = _complex(row["yasui_raw"])
        block_prediction = (
            positive[alpha[0]] * negative[alpha[1]] * negative[alpha[2]]
        )
        phase = q_values[alpha[0]] * q_values[alpha[1]] ** -1 * q_values[
            alpha[2]
        ] ** -1
        quadratic_prediction = (
            positive[0] * negative[0] * negative[0] * phase
        )
        max_block_standard_error = max(
            max_block_standard_error, abs(standard - block_prediction)
        )
        max_quadratic_standard_error = max(
            max_quadratic_standard_error, abs(standard - quadratic_prediction)
        )
        max_block_target_error = max(
            max_block_target_error, abs(target - block_prediction)
        )
        standard_values[alpha] = standard

    baseline = standard_values[(0, 0, 0)]
    for alpha, value in standard_values.items():
        factorized = (
            standard_values[(alpha[0], 0, 0)]
            * standard_values[(0, alpha[1], 0)]
            * standard_values[(0, 0, alpha[2])]
            / baseline**2
        )
        max_factorization_error = max(
            max_factorization_error, abs(value - factorized)
        )
    for label, error in {
        "block-to-standard": max_block_standard_error,
        "quadratic-to-standard": max_quadratic_standard_error,
        "block-to-target": max_block_target_error,
        "table-factorization": max_factorization_error,
    }.items():
        _require(error <= TOLERANCE, f"SU(3)_2 Figure 3 {label} error exceeds tolerance")

    return {
        "status": "PASS_ABSOLUTE_BLOCK_AND_QUADRATIC_PREDICTION_AFTER_COORDINATE_MAP",
        "category_id": "SU(3)_2",
        "coefficient_group": "Z/3",
        "intersection_form": [[1, 0, 0], [0, -1, 0], [0, 0, -1]],
        "alpha_basis_order": ["h", "e1", "e2"],
        "row_count": len(rows),
        "coordinate_map": payload["coordinate_map"],
        "direct_same_tuple_nonmatching_count": payload["summary"][
            "direct_same_tuple_nonmatching_count"
        ],
        "max_errors": {
            "block_prediction_vs_standard": repr(max_block_standard_error),
            "quadratic_prediction_vs_standard": repr(max_quadratic_standard_error),
            "block_prediction_vs_target": repr(max_block_target_error),
            "direct_table_factorization": repr(max_factorization_error),
        },
        "source": _artifact_ref(path, payload),
    }


def _audit_small_handles(
    path: Path,
    payload: dict[str, Any],
) -> dict[str, Any]:
    _require(payload.get("status") == "pass", "small-handle SU(3)_2 controls are not pass")
    _require(payload.get("example_count") == 16, "small-handle example denominator changed")
    zeta = cmath.exp(2j * math.pi / 3)
    row_count = 0
    off_diagonal_row_count = 0
    off_diagonal_witness_count = 0
    wrong_direct_form_mismatch_count = 0
    max_phase_error = 0.0
    max_absolute_error = 0.0
    example_results = []
    for example in payload["examples"]:
        matrix = [[int(value) for value in row] for row in example["h2_intersection_form"]]
        inverse = _invert_integer_matrix(matrix)
        baseline = _complex(example["untwisted_value"])
        example_max_error = 0.0
        has_off_diagonal = any(
            matrix[left][right] != 0
            for left in range(len(matrix))
            for right in range(len(matrix))
            if left != right
        )
        for row in example["rows"]:
            vector = [int(value) for value in row["values_on_h2_quotient_basis"]]
            _require(len(vector) == len(matrix), "small-handle character rank mismatch")
            exponent = _quadratic_exponent(vector, inverse) % 3
            expected_phase = zeta**exponent
            expected_value = baseline * expected_phase
            observed_phase = _complex(row["baseline_ratio"])
            observed_value = _complex(row["standard_form_value"])
            phase_error = abs(observed_phase - expected_phase)
            absolute_error = abs(observed_value - expected_value)
            example_max_error = max(example_max_error, phase_error, absolute_error)
            max_phase_error = max(max_phase_error, phase_error)
            max_absolute_error = max(max_absolute_error, absolute_error)
            row_count += 1
            if has_off_diagonal:
                off_diagonal_row_count += 1
                diagonal_exponent = sum(
                    vector[index] * matrix[index][index] * vector[index]
                    for index in range(len(vector))
                ) % 3
                if exponent != diagonal_exponent:
                    off_diagonal_witness_count += 1
            direct_exponent = _quadratic_exponent(vector, matrix) % 3
            if direct_exponent != exponent:
                wrong_direct_form_mismatch_count += 1
        _require(
            example_max_error <= TOLERANCE,
            f"small-handle quadratic prediction fails for {example['id']}",
        )
        example_results.append(
            {
                "id": example["id"],
                "intersection_form": matrix,
                "inverse_intersection_form": inverse,
                "row_count": len(example["rows"]),
                "max_error": repr(example_max_error),
                "status": "PASS",
            }
        )
    _require(row_count == 72, "small-handle all-character row denominator changed")
    _require(
        off_diagonal_witness_count > 0,
        "small-handle controls no longer witness mutual-intersection terms",
    )
    _require(
        wrong_direct_form_mismatch_count > 0,
        "small-handle controls no longer distinguish Q from Q inverse coordinates",
    )
    return {
        "status": "PASS_GENERAL_UNIMODULAR_FORM_QUADRATIC_PREDICTION",
        "category_id": "SU(3)_2",
        "coefficient_group": "Z/3",
        "coordinate_convention": (
            "Stored character values are covector coordinates lambda. "
            "The homology coordinates are Q^(-1) lambda, so the scalar exponent "
            "is lambda^T Q^(-1) lambda mod 3."
        ),
        "formula": "phase(lambda)=zeta3^(lambda^T Q^(-1) lambda)",
        "example_count": len(example_results),
        "row_count": row_count,
        "off_diagonal_row_count": off_diagonal_row_count,
        "off_diagonal_mutual_intersection_witness_count": off_diagonal_witness_count,
        "wrong_direct_Q_model_mismatch_count": wrong_direct_form_mismatch_count,
        "max_phase_error": repr(max_phase_error),
        "max_absolute_error": repr(max_absolute_error),
        "examples": example_results,
        "source": _artifact_ref(path, payload),
    }


def _audit_da4_split(
    path: Path,
    payload: dict[str, Any],
) -> dict[str, Any]:
    _require(
        payload.get("status") == "no-nonbaseline-character-found",
        "D(A4) split scan status changed",
    )
    rows = payload.get("rows", [])
    _require(len(rows) == 27, "D(A4) split all-character denominator is not 27")
    expected_alphas = {
        (left, middle, right)
        for left in range(3)
        for middle in range(3)
        for right in range(3)
    }
    actual_alphas = {tuple(int(value) for value in row["standard_alpha"]) for row in rows}
    _require(actual_alphas == expected_alphas, "D(A4) alpha denominator changed")
    baseline = _complex(next(row["raw_value"] for row in rows if row["standard_alpha"] == [0, 0, 0]))
    max_constant_error = 0.0
    max_component_product_error = 0.0
    for row in rows:
        value = _complex(row["raw_value"])
        product_value = math.prod(
            (_complex(factor) for factor in row["component_factors"]),
            start=1.0 + 0.0j,
        )
        max_constant_error = max(max_constant_error, abs(value - baseline))
        max_component_product_error = max(
            max_component_product_error, abs(value - product_value)
        )
    _require(max_constant_error <= TOLERANCE, "D(A4) q=1 prediction fails")
    _require(
        max_component_product_error <= TOLERANCE,
        "D(A4) split block product fails",
    )
    return {
        "status": "PASS_TRIVIAL_QUADRATIC_RESPONSE_AND_BLOCK_FACTORIZATION",
        "category_id": "D(A4)-c3w1",
        "coefficient_group": "Z/3",
        "intersection_form": [[1, 0, 0], [0, -1, 0], [0, 0, -1]],
        "category_quadratic_function_observed": "q_eval(a)=1 for all a in Z/3",
        "row_count": len(rows),
        "max_constant_error": repr(max_constant_error),
        "max_component_product_error": repr(max_component_product_error),
        "source": _artifact_ref(path, payload),
    }


def _audit_figure21(
    path: Path,
    payload: dict[str, Any],
) -> dict[str, Any]:
    _require(
        payload.get("status")
        == "PASS_COMPATIBLE_WITH_EXPLICIT_FIGURE21_NORMALIZATION_DISCREPANCY",
        "Figure 21 compatibility audit status changed",
    )
    counts = payload["established_computational_theorem"]["machine_checked_counts"]
    _require(counts["figure21_pointed_realization_count"] == 15, "Figure 21 denominator changed")
    _require(counts["figure21_raw_exact_pointed_rows"] == 13, "Figure 21 raw count changed")
    _require(counts["figure21_phase_only_pointed_rows"] == 2, "Figure 21 phase count changed")
    _require(
        counts["figure21_certified_h2_marked_pointwise_rows"] == 0,
        "Figure 21 unexpectedly claims an H2-marked pointwise row",
    )
    return {
        "status": "DISTRIBUTION_LEVEL_COMPATIBLE_BLOCKED_FOR_POINTWISE_QUADRATIC_AUDIT",
        "target": "Akbulut-Yasui 2008 Figure 21 / E3prime",
        "standard_topological_model": "CP2#9(-CP2)",
        "standard_intersection_form": {
            "diagonal": [1] + [-1] * 9,
            "rank": 10,
            "signature": -8,
        },
        "pointed_modular_realization_count": 15,
        "raw_distribution_match_count": 13,
        "global_minus_one_phase_aligned_count": 2,
        "certified_h2_marked_pointwise_row_count": 0,
        "why_not_all_alpha_verified": (
            "The saved Figure 21 computation records fixed-label distributions, "
            "not a certified H2 coordinate map from each alpha to the standard "
            "diagonal basis. Distribution equality cannot be promoted to the "
            "pointwise Pontryagin-square formula."
        ),
        "source": _artifact_ref(path, payload),
    }


def even_block_analysis(e8_pair_count: int, hyperbolic_count: int) -> dict[str, Any]:
    """Return the arithmetic role of 11/8 for Q = +/-2kE8 + nH."""

    k = abs(int(e8_pair_count))
    n = int(hyperbolic_count)
    if n < 0:
        raise AuditError("hyperbolic count must be nonnegative")
    direct_standard_h_count = n - 3 * k
    stabilization_needed = max(0, -direct_standard_h_count)
    return {
        "e8_pair_count_abs": k,
        "hyperbolic_count": n,
        "signature_abs": 16 * k,
        "b2": 16 * k + 2 * n,
        "eleven_eighths_inequality_holds": n >= 3 * k,
        "equivalent_inequality": f"{n} >= {3 * k}",
        "unstabilized_standard_model": (
            {
                "signed_K3_count": k,
                "S2xS2_count": direct_standard_h_count,
            }
            if direct_standard_h_count >= 0
            else None
        ),
        "minimum_algebraic_H_stabilizations_for_standard_block_form": stabilization_needed,
        "stabilized_standard_model": {
            "signed_K3_count": k,
            "S2xS2_count_after_stabilizing_source": (
                n + stabilization_needed - 3 * k
            ),
        },
    }


def _mathematical_scope() -> dict[str, Any]:
    return {
        "status": "CONDITIONAL_FORMULA_AND_TOPOLOGICAL_SCOPE_ANALYSIS_NOT_A_PROOF",
        "terminology_correction": {
            "relevant_operation": "Pontryagin square / induced quadratic refinement",
            "not_the_operation": "the tangent-bundle Pontryagin class p1(TM)",
            "reason": (
                "The proposed phase evaluates a finite-coefficient H2 background "
                "against the manifold intersection pairing. It is not a pairing "
                "of p1(TM) with that background."
            ),
        },
        "candidate_modular_formula": {
            "coefficient_group": "A=Aut_tensor(Id_C), identified with invertible objects when C is modular",
            "normalization_safe_definition": (
                "q_C(a)=Z_C(CP2,a)/Z_C(CP2,0) in the pinned orientation convention"
            ),
            "bilinearization": "b_C(a,b)=q_C(a+b)/(q_C(a)q_C(b))",
            "homology_coordinate_formula": (
                "Phi_Q(a_1,...,a_r)=product_i q_C(a_i)^(Q_ii) "
                "product_{i<j} b_C(a_i,a_j)^(Q_ij)"
            ),
            "dual_coordinate_formula_for_cyclic_examples": (
                "If stored coordinates are lambda=<alpha,basis>, first use "
                "a=Q^(-1)lambda. For q(a)=zeta^(c a^2), "
                "Phi=zeta^(c lambda^T Q^(-1) lambda)."
            ),
            "full_value_prediction": "Z_C(M,alpha)=Z_C(M,0)*Phi_Q(alpha)",
            "epistemic_status": "THEOREM_CANDIDATE_NUMERICALLY_SUPPORTED_NOT_PROVED_HERE",
        },
        "simply_connected_topological_models": {
            "scope": "closed connected oriented smooth simply connected 4-manifolds",
            "odd_intersection_form": (
                "Unconditionally, the unimodular odd form is diagonal in the "
                "indefinite case; Donaldson handles the smooth definite case. "
                "Freedman then identifies the topological model with connected "
                "sums of CP2 and -CP2, with the smooth Kirby-Siebenmann branch."
            ),
            "even_intersection_form": (
                "After orienting, write Q=-2kE8+nH. Rokhlin makes k integral. "
                "The still-open 11/8 conjecture is exactly n>=3k, which would "
                "give the unstabilized topological model #k K3 #(n-3k)(S2xS2)."
            ),
            "stable_even_form_without_11_8": (
                "Even without 11/8, adding max(0,3k-n) hyperbolic summands "
                "makes the lattice a K3/S2xS2 block sum. Turning this algebra "
                "into an invariant identity still uses marked stable realization, "
                "connected-sum normalization, and nonzero stabilization."
            ),
            "why_11_8_is_not_needed_for_an_existing_exotic_pair": (
                "For a specified homeomorphic exotic pair, the shared "
                "intersection form is already known. Neither the pairwise no-go "
                "claim nor the direct quadratic formula needs 11/8."
            ),
            "why_11_8_is_not_needed_for_direct_prediction": (
                "Once the quadratic formula is proved, Q and alpha themselves "
                "already determine the phase. Named connected-sum blocks are a "
                "convenient presentation, not a logical prerequisite."
            ),
        },
        "proof_obligations_not_discharged_by_data": [
            "Prove the twisted Kirby-color/simple-current identification with the exact orientation convention.",
            "Prove the surface-defect evaluation and all normalization factors for arbitrary MTCs.",
            "Prove basis independence and the torsion/Pontryagin-square extension in the claimed generality.",
            "Keep the separate marked-stable no-go proof obligations under expert review.",
        ],
        "reference_locators": [
            {
                "reference_id": "ref:freedman-topology-four-dimensional-manifolds-1982",
                "locator": "Theorem 1.5, journal pages 368-370",
                "role": "classification by unimodular intersection form and Kirby-Siebenmann branch",
            },
            {
                "reference_id": "ref:furuta-monopole-11-8-2001",
                "locator": "Introduction, journal page 279",
                "role": "11/8 statement, K3 equality, Donaldson definite case, and Rokhlin divisibility",
            },
            {
                "reference_id": "ref:yetter-homologically-twisted-hepth-9311082",
                "locator": "Definition 9 and surrounding construction",
                "role": "homologically twisted invariant and total invariant",
            },
            {
                "reference_id": "ref:cky-state-sum-hepth-9409167",
                "locator": "discussion of Yetter/Roberts 2-dimensional (co)homology refinements",
                "role": "historical surface-refinement and intersection-form context",
            },
        ],
    }


def build_audit(
    overrides: Mapping[str, Path] | None = None,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    dirty_before = bool(_git("status", "--short"))

    loaded_inputs: list[tuple[Path, dict[str, Any]]] = []
    su2_results = []
    for family, paths in (("yasui-figure3-a1", SU2_A1_PATHS), ("yasui-figure3-a3", SU2_A3_PATHS)):
        for level, default in paths.items():
            key = f"{family}-su2-{level}"
            path, payload = _load(key, default, overrides)
            loaded_inputs.append((path, payload))
            su2_results.append(
                _audit_su2_table(
                    path,
                    payload,
                    level=level,
                    presentation_id=family,
                )
            )

    su3_figure2_path, su3_figure2_payload = _load(
        "su3_figure2", PATHS["su3_figure2"], overrides
    )
    loaded_inputs.append((su3_figure2_path, su3_figure2_payload))
    su3_calibration_result, su3_calibration = _audit_su3_figure2(
        su3_figure2_path, su3_figure2_payload
    )

    su3_figure3_path, su3_figure3_payload = _load(
        "su3_figure3", PATHS["su3_figure3"], overrides
    )
    loaded_inputs.append((su3_figure3_path, su3_figure3_payload))
    su3_figure3_result = _audit_su3_figure3(
        su3_figure3_path, su3_figure3_payload, su3_calibration
    )

    small_path, small_payload = _load(
        "su3_small_handles", PATHS["su3_small_handles"], overrides
    )
    loaded_inputs.append((small_path, small_payload))
    small_result = _audit_small_handles(small_path, small_payload)

    da4_path, da4_payload = _load("da4_split", PATHS["da4_split"], overrides)
    loaded_inputs.append((da4_path, da4_payload))
    da4_result = _audit_da4_split(da4_path, da4_payload)

    figure21_path, figure21_payload = _load(
        "figure21_compatibility", PATHS["figure21_compatibility"], overrides
    )
    loaded_inputs.append((figure21_path, figure21_payload))
    figure21_result = _audit_figure21(figure21_path, figure21_payload)

    h2_marked_rows = (
        sum(result["row_count"] for result in su2_results)
        + su3_calibration_result["row_count"]
        + su3_figure3_result["row_count"]
        + small_result["row_count"]
        + da4_result["row_count"]
    )
    _require(h2_marked_rows == 201, "eligible H2-marked row denominator changed")

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.quadratic-block-prediction-audit.v1",
        "status": (
            "PASS_ALL_ELIGIBLE_H2_MARKED_DATA_MATCH_QUADRATIC_BLOCK_PREDICTION_"
            "FIGURE21_POINTWISE_BLOCKED"
        ),
        "mathematical_status": (
            "ESTABLISHED_COMPUTATIONAL_PATTERN_THEOREM_CANDIDATE_NOT_PROVED"
        ),
        "top_notice": (
            "This artifact machine-checks a closed-form modular prediction against "
            "all pinned eligible H2-marked data. It does not prove the formula for "
            "arbitrary MTCs. Figure 21 remains only distribution-level evidence "
            "because no certified H2 marking exists."
        ),
        "generator_script": _relative(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": (
            "python experiments/scripts/"
            "build_twisted_yetter_quadratic_block_prediction_audit_v1.py"
        ),
        "utc_start": started.isoformat(),
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "tolerance": TOLERANCE,
        "repo": {
            "root": str(REPO_ROOT),
            "git_commit": _git("rev-parse", "HEAD"),
            "dirty_before_output_write": dirty_before,
            "status_short_before_output_write": _git("status", "--short"),
        },
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
        },
        "input_artifacts": [
            _artifact_ref(path, source_payload)
            for path, source_payload in loaded_inputs
        ],
        "mathematical_scope": _mathematical_scope(),
        "machine_checked_result": {
            "status": "PASS_NO_COUNTEREXAMPLE_IN_ELIGIBLE_MARKED_DATA",
            "eligible_h2_marked_artifact_row_count": h2_marked_rows,
            "su2_all_alpha_table_count": len(su2_results),
            "su2_all_alpha_row_count": sum(
                result["row_count"] for result in su2_results
            ),
            "su3_figure2_calibration_row_count": su3_calibration_result["row_count"],
            "su3_figure3_all_alpha_row_count": su3_figure3_result["row_count"],
            "su3_general_form_control_row_count": small_result["row_count"],
            "da4_split_all_alpha_row_count": da4_result["row_count"],
            "off_diagonal_mutual_intersection_witness_count": small_result[
                "off_diagonal_mutual_intersection_witness_count"
            ],
            "wrong_direct_Q_model_mismatch_count": small_result[
                "wrong_direct_Q_model_mismatch_count"
            ],
            "certified_counterexample_count": 0,
            "figure21_h2_marked_pointwise_row_count": 0,
        },
        "evidence_groups": {
            "su2_figure3_all_alpha": su2_results,
            "su3_figure2_cp2_calibration": su3_calibration_result,
            "su3_figure3_all_alpha": su3_figure3_result,
            "su3_general_intersection_forms": small_result,
            "da4_standard_split_all_alpha": da4_result,
            "figure21_exotic_target": figure21_result,
        },
        "conclusions": {
            "established_about_saved_data": (
                "All 201 pinned eligible H2-marked rows agree with the absolute "
                "basic-block prediction and/or its induced quadratic-refinement "
                "formula within tolerance. The general-form SU(3)_2 controls "
                "include genuine off-diagonal witnesses and distinguish the "
                "correct Q^(-1) covector formula from the wrong direct-Q formula."
            ),
            "supported_but_not_proved": (
                "For modular input, the full twisted Yetter function appears to "
                "be the untwisted value multiplied by the quadratic phase induced "
                "from the invertible-object sector and the intersection form."
            ),
            "figure21_scope": (
                "Figure 21 remains compatible at distribution level for 15 pointed "
                "MTC realizations, but contributes zero H2-marked pointwise checks "
                "of the quadratic formula."
            ),
        },
        "explicit_non_claims": [
            "This artifact is not a proof of the modular quadratic formula.",
            "This artifact does not turn the still-open 11/8 conjecture into a theorem.",
            "This artifact does not use the tangent-bundle Pontryagin class p1(TM).",
            "This artifact does not certify a Figure 21 H2 coordinate map.",
            "This artifact does not remove the two Figure 21 semion global-phase discrepancies.",
            "This artifact does not establish a premodular formula.",
            "This artifact does not cover torsion H2, non-simply-connected manifolds, or manifolds with boundary.",
            "Presentation-control agreement is not independent experimental proof of a universal theorem.",
        ],
        "even_form_arithmetic_examples": {
            "K3": even_block_analysis(1, 3),
            "two_K3_boundary_case": even_block_analysis(2, 6),
            "hypothetical_11_8_violating_form": even_block_analysis(2, 5),
        },
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> int:
    payload = build_audit()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "artifact": _relative(OUTPUT),
                "status": payload["status"],
                "marked_rows": payload["machine_checked_result"][
                    "eligible_h2_marked_artifact_row_count"
                ],
                "figure21_marked_rows": payload["machine_checked_result"][
                    "figure21_h2_marked_pointwise_row_count"
                ],
                "content_hash": payload["content_hash"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
