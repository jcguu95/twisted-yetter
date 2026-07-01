"""SU(2)_2 B3 generic fusion-path backend for sigma sublinks.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_rf_generic_backend.sage.py

This is the next evaluator-track slice after the B2 Omega backend.  It replaces
the previous n<=3 all-sigma R/F evaluator with a generic left-associated
fusion-path implementation for arbitrary-length all-sigma SU(2)_2 strand
sequences.  Mixed fixed labels and Omega expansion are then evaluated using the
same SU(2)_2 reduction as B2: unit components are transparent, psi components
contribute the invertible psi-sigma linking scalar, and the sigma sublink is
evaluated by the generic fusion-path backend.

This is still not a fully generic mixed-label F/R local tensor graph evaluator.
"""

from __future__ import annotations

import argparse
import importlib.util
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.all import CyclotomicField, ZZ, matrix
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "local-piece"
    / "su2-2-rf-generic-backend-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402
from twisted_yetter.local_piece import braid_closure_data, braid_closure_linking_matrix, braid_program  # noqa: E402


K = CyclotomicField(16)
ZETA = K.gen()
SQRT2 = ZETA**2 + ZETA**(-2)

LABEL_UNIT = 0
LABEL_SIGMA = 1
LABEL_PSI = 2
SIMPLE_LABELS = (LABEL_UNIT, LABEL_SIGMA, LABEL_PSI)
OMEGA_LABELS = (0, 1)
DEGREES = {LABEL_UNIT: 0, LABEL_SIGMA: 1, LABEL_PSI: 0}
INVERTIBLE_LABELS = (LABEL_UNIT, LABEL_PSI)

SIGMA_TWIST = ZETA**3
TWISTS = {
    LABEL_UNIT: K(1),
    LABEL_SIGMA: SIGMA_TWIST,
    LABEL_PSI: ZETA**8,
}
R_SIGMA_SIGMA = {
    LABEL_UNIT: ZETA**2,
    LABEL_PSI: ZETA**14,
}
F_SIGMA_SIGMA_SIGMA_SIGMA = matrix(
    K,
    [
        [1 / SQRT2, 1 / SQRT2],
        [1 / SQRT2, -1 / SQRT2],
    ],
)


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_suite(oracle):
    fusion_controls = fusion_path_controls()
    braid_relation_controls = all_sigma_braid_relation_controls()
    evaluations = [evaluate_case(oracle, case) for case in example_cases()]
    move_regressions = move_regression_cases(oracle)
    status = "pass"
    if any(item["status"] != "pass" for item in fusion_controls):
        status = "fail"
    if any(item["status"] != "pass" for item in braid_relation_controls):
        status = "fail"
    if any(item["status"] != "pass" for item in evaluations):
        status = "fail"
    if any(item["status"] != "pass" for item in move_regressions):
        status = "fail"
    return {
        "schema": "twisted-yetter.su2_2-rf-generic-backend.v1",
        "status": status,
        "category_id": "SU(2)_2",
        "claim_level": "B3 generic fusion-path backend / sigma sublinks plus Omega expansion",
        "scope": (
            "generic left-associated fusion-path basis for arbitrary-length all-sigma "
            "SU(2)_2 braid sequences; fixed mixed labels via unit transparency and "
            "psi-sigma linking scalar; Omega_0/Omega_1 expansion for supported braid closures"
        ),
        "not_scope": (
            "full mixed-label F/R generator matrices, arbitrary planar tensor graph, "
            "cup/cap/eval/coeval programs, special/dotted links, closed 4-manifold "
            "normalization, or exotic-pair computation"
        ),
        "backend": {
            "oracle_comparison_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
            "field": "CyclotomicField(16)",
            "zeta_symbol": "zeta16",
            "sigma_backend": (
                "left-associated fusion-path matrices for all-sigma selected subbraids; "
                "no hard-coded n<=3 selected-strand cap in this B3 implementation"
            ),
            "mixed_label_method": (
                "evaluate sigma-selected subbraid by the generic sigma backend; multiply "
                "by (-1)^lk for psi-sigma linking and by component twists"
            ),
            "omega_formula": "Omega_a = sum_i d_i (-1)^(a deg(i)) X_i",
        },
        "fusion_path_controls": fusion_controls,
        "braid_relation_controls": braid_relation_controls,
        "case_count": len(evaluations),
        "move_regression_count": len(move_regressions),
        "max_sigma_selected_strands_checked": max(
            max(item["sigma_selected_strand_count"] for item in case["fixed_label_checks"])
            for case in evaluations
        ),
        "evaluations": evaluations,
        "move_regressions": move_regressions,
        "upstream_backend_artifacts": [
            "experiments/results/local-piece/su2-2-rf-omega-backend-v1.json",
            "experiments/results/local-piece/su2-2-rf-local-backend-v1.json",
            "experiments/results/sage-stress/su2-2-braid-auto-stress-v1.json",
        ],
    }


def fusion_path_controls():
    expected = {
        1: {LABEL_SIGMA: 1},
        2: {LABEL_UNIT: 1, LABEL_PSI: 1},
        3: {LABEL_SIGMA: 2},
        4: {LABEL_UNIT: 2, LABEL_PSI: 2},
        5: {LABEL_SIGMA: 4},
        6: {LABEL_UNIT: 4, LABEL_PSI: 4},
    }
    controls = []
    for n_strands, expected_counts in expected.items():
        labels = (LABEL_SIGMA,) * n_strands
        actual_counts = {
            total_label: len(fusion_path_basis(labels, total_label))
            for total_label in possible_total_labels(labels)
        }
        controls.append(
            {
                "name": f"all_sigma_fusion_path_counts_n{n_strands}",
                "n_strands": n_strands,
                "actual_counts": {str(label): count for label, count in actual_counts.items()},
                "expected_counts": {str(label): count for label, count in expected_counts.items()},
                "status": "pass" if actual_counts == expected_counts else "fail",
            }
        )
    f_square = F_SIGMA_SIGMA_SIGMA_SIGMA * F_SIGMA_SIGMA_SIGMA_SIGMA
    controls.append(
        {
            "name": "f_sigma_sigma_sigma_sigma_is_involutive",
            "actual": matrix_json(f_square),
            "expected": matrix_json(matrix.identity(K, 2)),
            "status": "pass" if f_square == matrix.identity(K, 2) else "fail",
        }
    )
    return controls


def all_sigma_braid_relation_controls():
    controls = []
    for n_strands in (4, 5):
        labels = (LABEL_SIGMA,) * n_strands
        for total_label in possible_total_labels(labels):
            for left_index in range(1, n_strands - 1):
                left = (
                    all_sigma_generator_matrix(n_strands, total_label, left_index)
                    * all_sigma_generator_matrix(n_strands, total_label, left_index + 1)
                    * all_sigma_generator_matrix(n_strands, total_label, left_index)
                )
                right = (
                    all_sigma_generator_matrix(n_strands, total_label, left_index + 1)
                    * all_sigma_generator_matrix(n_strands, total_label, left_index)
                    * all_sigma_generator_matrix(n_strands, total_label, left_index + 1)
                )
                controls.append(
                    {
                        "name": "all_sigma_braid_relation",
                        "n_strands": n_strands,
                        "left_index": left_index,
                        "total_label": int(total_label),
                        "matrix_size": left.nrows(),
                        "difference": matrix_json(left - right),
                        "status": "pass" if left == right else "fail",
                    }
                )
    return controls


def example_cases():
    return [
        {
            "case_id": "generic-sigma-four-strand-identity",
            "n_strands": 4,
            "braid_word": (),
            "framings": (0, 0, 0, 0),
            "fixed_labels_to_check": [(LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA)],
            "omega_labels_to_check": [(0, 0, 0, 0), (1, 1, 1, 1)],
        },
        {
            "case_id": "generic-sigma-four-strand-two-component",
            "n_strands": 4,
            "braid_word": (1, 2, 3, 1, 2, 1),
            "framings": (0, 0),
            "fixed_labels_to_check": list(product(SIMPLE_LABELS, repeat=2)),
            "omega_labels_to_check": list(product(OMEGA_LABELS, repeat=2)),
        },
        {
            "case_id": "generic-mixed-four-sigma-plus-psi",
            "n_strands": 5,
            "braid_word": (1, 2, 3, 1, 2, 1, 4, 4),
            "framings": (0, 0, 0),
            "fixed_labels_to_check": list(product(SIMPLE_LABELS, repeat=3)),
            "omega_labels_to_check": list(product(OMEGA_LABELS, repeat=3)),
        },
        {
            "case_id": "generic-sigma-five-strand-one-component",
            "n_strands": 5,
            "braid_word": (1, 2, 3, 4),
            "framings": (0,),
            "fixed_labels_to_check": [(LABEL_UNIT,), (LABEL_SIGMA,), (LABEL_PSI,)],
            "omega_labels_to_check": [(0,), (1,)],
        },
        {
            "case_id": "generic-five-component-chain",
            "n_strands": 5,
            "braid_word": (1, 1, 2, 2, 3, 3, 4, 4),
            "framings": (0, 0, 0, 0, 0),
            "fixed_labels_to_check": [
                (LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA),
                (LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA, LABEL_SIGMA, LABEL_PSI),
                (LABEL_SIGMA, LABEL_PSI, LABEL_SIGMA, LABEL_PSI, LABEL_SIGMA),
                (LABEL_PSI, LABEL_SIGMA, LABEL_UNIT, LABEL_SIGMA, LABEL_PSI),
            ],
            "omega_labels_to_check": [
                (0, 0, 0, 0, 0),
                (1, 0, 1, 0, 1),
                (1, 1, 1, 1, 1),
            ],
        },
    ]


def move_regression_cases(oracle):
    return [
        compare_case_pair(
            oracle,
            name="generic-r-r-inverse-cancellation-middle-strands",
            reason="local R followed by R^{-1} cancels with four visible strands",
            left={"n_strands": 4, "braid_word": (), "framings": (0, 0, 0, 0)},
            right={"n_strands": 4, "braid_word": (2, -2), "framings": (0, 0, 0, 0)},
            omega_labels_to_check=list(product(OMEGA_LABELS, repeat=4)),
        ),
        compare_case_pair(
            oracle,
            name="generic-four-strand-positive-markov",
            reason="closure(beta) equals closure(beta sigma_n) beyond the B2 n<=3 sigma path",
            left={"n_strands": 4, "braid_word": (1, 2, 3, 1, 2, 1), "framings": (0, 0)},
            right={"n_strands": 5, "braid_word": (1, 2, 3, 1, 2, 1, 4), "framings": (0, 0)},
            omega_labels_to_check=list(product(OMEGA_LABELS, repeat=2)),
        ),
        compare_case_pair(
            oracle,
            name="generic-four-strand-negative-markov",
            reason="closure(beta) equals closure(beta sigma_n^-1) beyond the B2 n<=3 sigma path",
            left={"n_strands": 4, "braid_word": (1, 2, 3, 1, 2, 1), "framings": (0, 0)},
            right={"n_strands": 5, "braid_word": (1, 2, 3, 1, 2, 1, -4), "framings": (0, 0)},
            omega_labels_to_check=list(product(OMEGA_LABELS, repeat=2)),
        ),
        compare_case_pair(
            oracle,
            name="generic-four-strand-conjugation",
            reason="closure(beta) equals closure(alpha beta alpha^-1) with a four-strand beta",
            left={"n_strands": 4, "braid_word": (1, 2, 3, 1, 2, 1), "framings": (0, 0)},
            right={"n_strands": 4, "braid_word": (1, 1, 2, 3, 1, 2, 1, -1), "framings": (0, 0)},
            omega_labels_to_check=list(product(OMEGA_LABELS, repeat=2)),
        ),
    ]


def evaluate_case(oracle, case):
    fixed_label_checks = [
        fixed_label_comparison(oracle, case, labels)
        for labels in case["fixed_labels_to_check"]
    ]
    omega_checks = [
        omega_comparison(oracle, case, omega_labels)
        for omega_labels in case["omega_labels_to_check"]
    ]
    return {
        "case_id": case["case_id"],
        "status": "pass"
        if all(item["status"] == "pass" for item in fixed_label_checks + omega_checks)
        else "fail",
        "local_piece_program": program_payload(case),
        "component_count": component_count(case["n_strands"], case["braid_word"]),
        "fixed_label_check_count": len(fixed_label_checks),
        "omega_check_count": len(omega_checks),
        "fixed_label_checks": fixed_label_checks,
        "omega_checks": omega_checks,
    }


def fixed_label_comparison(oracle, case, labels):
    rf_value = explicit_fixed_value(
        case["n_strands"],
        case["braid_word"],
        labels,
        case["framings"],
    )
    oracle_value = oracle.fixed_label_rt_value(
        case["n_strands"],
        case["braid_word"],
        labels,
        case["framings"],
    )
    return {
        "labels": [int(label) for label in labels],
        "sigma_selected_strand_count": sigma_selected_strand_count(
            case["n_strands"],
            case["braid_word"],
            labels,
        ),
        "rf_value": cyclotomic_json(rf_value),
        "oracle_value": oracle.cyclotomic_json(oracle_value),
        "difference": cyclotomic_json(rf_value - oracle_value),
        "status": "pass" if rf_value == oracle_value else "fail",
    }


def omega_comparison(oracle, case, omega_labels):
    rf_value = explicit_omega_value(
        case["n_strands"],
        case["braid_word"],
        case["framings"],
        omega_labels,
    )
    oracle_value = oracle.omega_value(
        case["n_strands"],
        case["braid_word"],
        case["framings"],
        omega_labels,
    )
    return {
        "omega_labels": [int(label) for label in omega_labels],
        "rf_value": cyclotomic_json(rf_value),
        "oracle_value": oracle.cyclotomic_json(oracle_value),
        "difference": cyclotomic_json(rf_value - oracle_value),
        "status": "pass" if rf_value == oracle_value else "fail",
    }


def compare_case_pair(oracle, *, name, reason, left, right, omega_labels_to_check):
    comparisons = []
    for omega_labels in omega_labels_to_check:
        left_rf = explicit_omega_value(
            left["n_strands"],
            left["braid_word"],
            left["framings"],
            omega_labels,
        )
        right_rf = explicit_omega_value(
            right["n_strands"],
            right["braid_word"],
            right["framings"],
            omega_labels,
        )
        left_oracle = oracle.omega_value(
            left["n_strands"],
            left["braid_word"],
            left["framings"],
            omega_labels,
        )
        right_oracle = oracle.omega_value(
            right["n_strands"],
            right["braid_word"],
            right["framings"],
            omega_labels,
        )
        comparisons.append(
            {
                "omega_labels": [int(label) for label in omega_labels],
                "left_rf_value": cyclotomic_json(left_rf),
                "right_rf_value": cyclotomic_json(right_rf),
                "left_oracle_value": oracle.cyclotomic_json(left_oracle),
                "right_oracle_value": oracle.cyclotomic_json(right_oracle),
                "rf_difference": cyclotomic_json(left_rf - right_rf),
                "oracle_difference": oracle.cyclotomic_json(left_oracle - right_oracle),
                "status": "pass" if left_rf == right_rf == left_oracle == right_oracle else "fail",
            }
        )
    return {
        "name": name,
        "reason": reason,
        "status": "pass" if all(item["status"] == "pass" for item in comparisons) else "fail",
        "left": program_payload(left),
        "right": program_payload(right),
        "comparison_count": len(comparisons),
        "comparisons": comparisons,
    }


def explicit_omega_value(n_strands, braid_word, framings, omega_labels):
    count = component_count(n_strands, braid_word)
    if len(omega_labels) != count:
        raise ValueError("Omega label count must match component count")
    total = K(0)
    for labels in product(SIMPLE_LABELS, repeat=count):
        coefficient = K(1)
        for omega_label, simple_label in zip(omega_labels, labels, strict=True):
            coefficient *= quantum_dimension(simple_label) * character(omega_label, simple_label)
        total += coefficient * explicit_fixed_value(n_strands, braid_word, labels, framings)
    return K(total)


def explicit_fixed_value(n_strands, braid_word, labels, framings):
    components = closure_components(n_strands, braid_word)
    if len(labels) != len(components):
        raise ValueError("label count must match component count")
    if len(framings) != len(components):
        raise ValueError("framing count must match component count")
    for label in labels:
        if label not in SIMPLE_LABELS:
            raise ValueError(f"unknown SU(2)_2 simple label: {label!r}")

    sigma_components = {index for index, label in enumerate(labels) if label == LABEL_SIGMA}
    strand_component_lookup = strand_to_component(components, n_strands)
    sigma_strands = {
        strand
        for strand, component_index in enumerate(strand_component_lookup)
        if component_index in sigma_components
    }
    sigma_value = sigma_sublink_value(n_strands, braid_word, sigma_strands)
    psi_sigma_factor = psi_sigma_linking_factor(n_strands, braid_word, labels)
    framing_factor = K(1)
    for label, framing in zip(labels, framings, strict=True):
        framing_factor *= TWISTS[label] ** ZZ(framing)
    return K(sigma_value * psi_sigma_factor * framing_factor)


def sigma_sublink_value(n_strands, braid_word, sigma_strands):
    if not sigma_strands:
        return K(1)
    subword, selected_count = selected_subbraid_word(n_strands, braid_word, sigma_strands)
    return all_sigma_unframed_value(selected_count, subword)


def all_sigma_unframed_value(n_strands, braid_word):
    if n_strands < 1:
        raise ValueError("all-sigma backend needs at least one selected strand")
    labels = (LABEL_SIGMA,) * n_strands
    total = K(0)
    for total_label in possible_total_labels(labels):
        representation = all_sigma_braid_matrix(n_strands, braid_word, total_label)
        total += quantum_dimension(total_label) * representation.trace()
    return K(total)


def all_sigma_braid_matrix(n_strands, braid_word, total_label):
    basis = all_sigma_fusion_path_basis(n_strands, total_label)
    if not basis:
        raise ValueError("empty all-sigma fusion basis")
    output = matrix.identity(K, len(basis))
    for generator in braid_word:
        output = all_sigma_generator_matrix(n_strands, total_label, generator) * output
    return output


def all_sigma_generator_matrix(n_strands, total_label, generator):
    if generator == 0 or abs(generator) >= n_strands:
        raise ValueError("bad braid generator")
    labels = (LABEL_SIGMA,) * n_strands
    basis = all_sigma_fusion_path_basis(n_strands, total_label)
    basis_index = {path: index for index, path in enumerate(basis)}
    output = matrix(K, len(basis), len(basis), 0)
    sign = 1 if generator > 0 else -1
    left_index = abs(generator)

    if left_index == 1:
        for path, column in basis_index.items():
            channel = path[1]
            output[column, column] = r_sigma_sigma(channel, sign)
        return output

    for input_path, column in basis_index.items():
        before_pair = input_path[left_index - 2]
        after_pair = input_path[left_index]
        if before_pair == LABEL_SIGMA:
            for output_path, row in basis_index.items():
                if (
                    output_path[: left_index - 1] != input_path[: left_index - 1]
                    or output_path[left_index:] != input_path[left_index:]
                ):
                    continue
                output[row, column] = sigma_sigma_recoupled_entry(
                    output_path[left_index - 1],
                    input_path[left_index - 1],
                    sign,
                )
        else:
            if before_pair not in INVERTIBLE_LABELS or after_pair not in INVERTIBLE_LABELS:
                raise ValueError("unexpected all-sigma path parity")
            channel = invertible_product(before_pair, after_pair)
            output[column, column] = r_sigma_sigma(channel, sign)
    return output


def sigma_sigma_recoupled_entry(output_middle, input_middle, sign):
    row = invertible_index(output_middle)
    column = invertible_index(input_middle)
    total = K(0)
    for channel in INVERTIBLE_LABELS:
        channel_index = invertible_index(channel)
        total += (
            F_SIGMA_SIGMA_SIGMA_SIGMA[row, channel_index]
            * r_sigma_sigma(channel, sign)
            * F_SIGMA_SIGMA_SIGMA_SIGMA[channel_index, column]
        )
    return K(total)


def r_sigma_sigma(channel, sign):
    if channel not in R_SIGMA_SIGMA:
        raise ValueError("sigma-sigma R channel must be 0 or psi")
    value = R_SIGMA_SIGMA[channel]
    return value if sign > 0 else value**-1


def fusion_product(left, right):
    if left == LABEL_UNIT:
        return (right,)
    if right == LABEL_UNIT:
        return (left,)
    if left == LABEL_PSI and right == LABEL_PSI:
        return (LABEL_UNIT,)
    if (left, right) in ((LABEL_PSI, LABEL_SIGMA), (LABEL_SIGMA, LABEL_PSI)):
        return (LABEL_SIGMA,)
    if left == LABEL_SIGMA and right == LABEL_SIGMA:
        return (LABEL_UNIT, LABEL_PSI)
    raise ValueError(f"unknown SU(2)_2 labels: {left!r}, {right!r}")


def fusion_path_basis(labels, total_label):
    if not labels:
        return ()
    paths = [(labels[0],)]
    for label in labels[1:]:
        next_paths = []
        for path in paths:
            for fused in fusion_product(path[-1], label):
                next_paths.append(path + (fused,))
        paths = next_paths
    return tuple(path for path in paths if path[-1] == total_label)


def all_sigma_fusion_path_basis(n_strands, total_label):
    return fusion_path_basis((LABEL_SIGMA,) * n_strands, total_label)


def possible_total_labels(labels):
    if not labels:
        return ()
    totals = {labels[0]}
    for label in labels[1:]:
        next_totals = set()
        for current in totals:
            next_totals.update(fusion_product(current, label))
        totals = next_totals
    return tuple(label for label in SIMPLE_LABELS if label in totals)


def invertible_product(left, right):
    if left not in INVERTIBLE_LABELS or right not in INVERTIBLE_LABELS:
        raise ValueError("invertible product expects labels 0 or psi")
    return LABEL_UNIT if left == right else LABEL_PSI


def invertible_index(label):
    if label == LABEL_UNIT:
        return 0
    if label == LABEL_PSI:
        return 1
    raise ValueError("expected invertible label 0 or psi")


def psi_sigma_linking_factor(n_strands, braid_word, labels):
    linking = braid_closure_linking_matrix(n_strands, braid_word)
    exponent = ZZ(0)
    for left, left_label in enumerate(labels):
        if left_label != LABEL_PSI:
            continue
        for right, right_label in enumerate(labels):
            if right_label == LABEL_SIGMA:
                exponent += ZZ(linking[left][right])
    return K(-1) ** exponent


def selected_subbraid_word(n_strands, braid_word, selected_strands):
    positions = list(range(n_strands))
    subword = []
    for generator in braid_word:
        sign = 1 if generator > 0 else -1
        index = abs(generator) - 1
        left = positions[index]
        right = positions[index + 1]
        if left in selected_strands and right in selected_strands:
            selected_positions_before = [
                position for position, strand in enumerate(positions) if strand in selected_strands
            ]
            sub_index = selected_positions_before.index(index) + 1
            subword.append(sign * sub_index)
        positions[index], positions[index + 1] = positions[index + 1], positions[index]
    return tuple(subword), len(selected_strands)


def closure_components(n_strands, braid_word):
    return braid_closure_data(n_strands, braid_word).components


def strand_to_component(components, n_strands):
    lookup = [0] * n_strands
    for component_index, component in enumerate(components):
        for strand in component:
            lookup[strand] = component_index
    return tuple(lookup)


def component_count(n_strands, braid_word):
    return len(closure_components(n_strands, braid_word))


def sigma_selected_strand_count(n_strands, braid_word, labels):
    components = closure_components(n_strands, braid_word)
    sigma_components = {index for index, label in enumerate(labels) if label == LABEL_SIGMA}
    lookup = strand_to_component(components, n_strands)
    return sum(1 for component_index in lookup if component_index in sigma_components)


def quantum_dimension(label):
    if label == LABEL_SIGMA:
        return SQRT2
    if label in INVERTIBLE_LABELS:
        return K(1)
    raise ValueError(f"unknown SU(2)_2 label: {label!r}")


def character(omega_label, simple_label):
    if omega_label not in OMEGA_LABELS:
        raise ValueError("SU(2)_2 Omega label must be 0 or 1")
    return K(-1) if omega_label == 1 and DEGREES[simple_label] == 1 else K(1)


def program_payload(case):
    count = component_count(case["n_strands"], case["braid_word"])
    program = braid_program(
        program_id=case.get("case_id", "rf-generic-case"),
        category_id="SU(2)_2",
        strand_count=case["n_strands"],
        braid_word=case["braid_word"],
        framings=case["framings"],
        omega_labels=(0,) * count,
    )
    return {
        "program": program.to_json(),
        "diagnostics": program.diagnostics(),
    }


def matrix_json(value):
    return [
        [cyclotomic_json(entry) for entry in row]
        for row in value.rows()
    ]


def cyclotomic_json(value):
    value = K(value)
    return {
        "field": "CyclotomicField(16)",
        "zeta_symbol": "zeta16",
        "display": str(value),
        "coefficients": [str(coefficient) for coefficient in value.list()],
    }


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "su2-2-rf-generic-backend-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "oracle_comparison_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "case_count": exact_output["case_count"],
        "move_regression_count": exact_output["move_regression_count"],
        "max_sigma_selected_strands_checked": exact_output["max_sigma_selected_strands_checked"],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_rf_generic_backend.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_rf_generic_backend.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is B3: arbitrary-length all-sigma fusion-path matrices feed the fixed-label and Omega evaluator.",
            "The SU(2)_2 braid oracle is used only as an independent exact comparison backend.",
            "Full mixed-label F/R generator matrices remain an explicit next step.",
        ],
    )


def git_metadata():
    return {
        "commit": _run(["git", "rev-parse", "HEAD"]),
        "dirty": bool(_run(["git", "status", "--porcelain"])),
    }


def utc_now_iso():
    return _run(["date", "-u", "+%Y-%m-%dT%H:%M:%SZ"])


def _run(command):
    return subprocess.run(
        command,
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args(argv)

    output_path = args.output
    if not output_path.is_absolute():
        output_path = REPO_ROOT / output_path
    output_path.parent.mkdir(parents=True, exist_ok=True)

    started_at = utc_now_iso()
    start = time.time()
    oracle = load_module(ORACLE_PATH, "su2_2_braid_oracle_for_rf_generic")
    exact_output = run_suite(oracle)
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(f"cases: {exact_output['case_count']}")
    print(f"move regressions: {exact_output['move_regression_count']}")
    print(f"max sigma selected strands checked: {exact_output['max_sigma_selected_strands_checked']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
