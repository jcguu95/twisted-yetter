"""SU(2)_2 B1' explicit R/F local backend for sigma-colored braid closures.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_rf_local_backend.sage.py

This is the next evaluator-track slice after the B0 braid-closure plumbing.
It evaluates fixed-label all-sigma braid closures by explicit local categorical
data:

* R_{sigma,sigma}^{0} and R_{sigma,sigma}^{psi}, calibrated against the
  repo's SU(2)_2 braid oracle conventions;
* the nontrivial Ising F^{sigma,sigma,sigma}_{sigma} matrix;
* categorical trace over fusion-path spaces.

It is not an Omega evaluator, not a full label-mixed evaluator, and not a
general planar F/R/eval/coeval tensor graph yet.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import subprocess
import sys
import time

from sage.all import CyclotomicField, matrix
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
ORACLE_PATH = REPO_ROOT / "experiments" / "sage" / "su2_2_braid_oracle.sage.py"
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "local-piece"
    / "su2-2-rf-local-backend-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402
from twisted_yetter.local_piece import braid_program  # noqa: E402


K = CyclotomicField(16)
ZETA = K.gen()
SQRT2 = ZETA**2 + ZETA**(-2)
LABEL_UNIT = 0
LABEL_SIGMA = 1
LABEL_PSI = 2
SIGMA_TWIST = ZETA**3
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


def load_oracle():
    spec = importlib.util.spec_from_file_location("su2_2_braid_oracle_runtime", ORACLE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def run_suite(oracle):
    rf_controls = rf_symbol_controls()
    examples = [evaluate_case(oracle, case) for case in example_cases()]
    move_regressions = move_regression_cases(oracle)
    status = "pass"
    if any(control["status"] != "pass" for control in rf_controls):
        status = "fail"
    if any(example["status"] != "pass" for example in examples):
        status = "fail"
    if any(regression["status"] != "pass" for regression in move_regressions):
        status = "fail"
    return {
        "schema": "twisted-yetter.su2_2-rf-local-backend.v1",
        "status": status,
        "category_id": "SU(2)_2",
        "claim_level": "B1-prime explicit R/F backend / fixed all-sigma braid closures",
        "scope": (
            "fixed-label all-sigma braid closures with at most three strands, "
            "evaluated by explicit R/F fusion-path matrices and categorical trace"
        ),
        "not_scope": (
            "Omega expansion, mixed simple labels, arbitrary component colorings, "
            "n>3 fusion-path implementation, cup/cap boundary programs, special/dotted "
            "links, closed 4-manifold normalization, or exotic-pair computation"
        ),
        "convention": {
            "field": "CyclotomicField(16)",
            "zeta_symbol": "zeta16",
            "sigma_label": 1,
            "psi_label": 2,
            "theta_sigma": cyclotomic_json(SIGMA_TWIST),
            "r_sigma_sigma": {
                "0": cyclotomic_json(R_SIGMA_SIGMA[LABEL_UNIT]),
                "2": cyclotomic_json(R_SIGMA_SIGMA[LABEL_PSI]),
            },
            "f_sigma_sigma_sigma_sigma": matrix_json(F_SIGMA_SIGMA_SIGMA_SIGMA),
            "calibration_note": (
                "R eigenvalues are oracle-calibrated to the repository's "
                "SU(2)_2 braid/Jones convention: sigma_1 closure gives sqrt(2), "
                "sigma_1^2 Hopf with sigma labels gives 0, and sigma_1^3 trefoil "
                "gives -sqrt(2)."
            ),
        },
        "rf_controls": rf_controls,
        "example_count": len(examples),
        "move_regression_count": len(move_regressions),
        "examples": examples,
        "move_regressions": move_regressions,
        "upstream_backend_artifacts": [
            "experiments/results/local-piece/su2-2-local-piece-evaluator-v1.json",
            "experiments/results/sage-stress/su2-2-braid-auto-stress-v1.json",
        ],
    }


def rf_symbol_controls():
    b3_left, b3_right = b3_braid_relation_matrices()
    controls = [
        {
            "name": "f_matrix_is_involutive",
            "actual": matrix_json(F_SIGMA_SIGMA_SIGMA_SIGMA * F_SIGMA_SIGMA_SIGMA_SIGMA),
            "expected": matrix_json(matrix.identity(K, 2)),
            "status": "pass"
            if F_SIGMA_SIGMA_SIGMA_SIGMA * F_SIGMA_SIGMA_SIGMA_SIGMA == matrix.identity(K, 2)
            else "fail",
        },
        {
            "name": "two_strand_sigma_unknot_calibration",
            "actual": cyclotomic_json(two_strand_trace(1)),
            "expected": cyclotomic_json(SQRT2),
            "status": "pass" if two_strand_trace(1) == SQRT2 else "fail",
        },
        {
            "name": "two_strand_sigma_hopf_calibration",
            "actual": cyclotomic_json(two_strand_trace(2)),
            "expected": cyclotomic_json(K(0)),
            "status": "pass" if two_strand_trace(2) == K(0) else "fail",
        },
        {
            "name": "two_strand_sigma_trefoil_calibration",
            "actual": cyclotomic_json(two_strand_trace(3)),
            "expected": cyclotomic_json(-SQRT2),
            "status": "pass" if two_strand_trace(3) == -SQRT2 else "fail",
        },
        {
            "name": "b3_braid_relation",
            "left": matrix_json(b3_left),
            "right": matrix_json(b3_right),
            "status": "pass" if b3_left == b3_right else "fail",
        },
    ]
    return controls


def example_cases():
    return [
        {
            "case_id": "sigma-unknot-one-strand",
            "n_strands": 1,
            "braid_word": (),
            "framings": (0,),
            "expected_description": "0-framed sigma-colored unknot",
        },
        {
            "case_id": "sigma-unlink-two-strand-identity",
            "n_strands": 2,
            "braid_word": (),
            "framings": (0, 0),
            "expected_description": "two split sigma-colored unknots",
        },
        {
            "case_id": "sigma-unknot-two-strand-sigma1",
            "n_strands": 2,
            "braid_word": (1,),
            "framings": (0,),
            "expected_description": "sigma_1 closure, isotopic to sigma-colored unknot",
        },
        {
            "case_id": "sigma-hopf",
            "n_strands": 2,
            "braid_word": (1, 1),
            "framings": (0, 0),
            "expected_description": "positive Hopf with both components sigma-colored",
        },
        {
            "case_id": "sigma-right-trefoil",
            "n_strands": 2,
            "braid_word": (1, 1, 1),
            "framings": (0,),
            "expected_description": "right trefoil with sigma color",
        },
        {
            "case_id": "sigma-figure-eight",
            "n_strands": 3,
            "braid_word": (-1, 2, -1, 2),
            "framings": (0,),
            "expected_description": "figure-eight with sigma color",
        },
        {
            "case_id": "sigma-figure-eight-plus-one-framed",
            "n_strands": 3,
            "braid_word": (-1, 2, -1, 2),
            "framings": (1,),
            "expected_description": "figure-eight with sigma color and +1 external framing",
        },
    ]


def move_regression_cases(oracle):
    comparisons = [
        compare_cases(
            oracle,
            "rf-r-r-inverse-cancellation",
            "local R followed by R^{-1} cancels",
            {"n_strands": 2, "braid_word": (), "framings": (0, 0)},
            {"n_strands": 2, "braid_word": (1, -1), "framings": (0, 0)},
        ),
        compare_cases(
            oracle,
            "rf-trefoil-positive-markov",
            "closure(beta) equals closure(beta sigma_n)",
            {"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)},
            {"n_strands": 3, "braid_word": (1, 1, 1, 2), "framings": (0,)},
        ),
        compare_cases(
            oracle,
            "rf-trefoil-negative-markov",
            "closure(beta) equals closure(beta sigma_n^-1)",
            {"n_strands": 2, "braid_word": (1, 1, 1), "framings": (0,)},
            {"n_strands": 3, "braid_word": (1, 1, 1, -2), "framings": (0,)},
        ),
        compare_cases(
            oracle,
            "rf-figure-eight-conjugation",
            "closure(beta) equals closure(alpha beta alpha^-1)",
            {"n_strands": 3, "braid_word": (-1, 2, -1, 2), "framings": (0,)},
            {"n_strands": 3, "braid_word": (1, -1, 2, -1, 2, -1), "framings": (0,)},
        ),
    ]
    return comparisons


def evaluate_case(oracle, case):
    rf_value = rf_framed_value(case["n_strands"], case["braid_word"], case["framings"])
    oracle_value = oracle.fixed_label_rt_value(
        case["n_strands"],
        case["braid_word"],
        (LABEL_SIGMA,) * component_count(case["n_strands"], case["braid_word"]),
        case["framings"],
    )
    return {
        "case_id": case["case_id"],
        "status": "pass" if rf_value == oracle_value else "fail",
        "description": case["expected_description"],
        "local_piece_program": program_payload(case),
        "diagnostics": {
            "component_count": component_count(case["n_strands"], case["braid_word"]),
            "fusion_trace_terms": fusion_trace_terms(case["n_strands"], case["braid_word"]),
        },
        "rf_value": cyclotomic_json(rf_value),
        "oracle_fixed_sigma_value": cyclotomic_json(oracle_value),
        "difference": cyclotomic_json(rf_value - oracle_value),
    }


def compare_cases(oracle, name, reason, left, right):
    left_rf = rf_framed_value(left["n_strands"], left["braid_word"], left["framings"])
    right_rf = rf_framed_value(right["n_strands"], right["braid_word"], right["framings"])
    left_oracle = oracle.fixed_label_rt_value(
        left["n_strands"],
        left["braid_word"],
        (LABEL_SIGMA,) * component_count(left["n_strands"], left["braid_word"]),
        left["framings"],
    )
    right_oracle = oracle.fixed_label_rt_value(
        right["n_strands"],
        right["braid_word"],
        (LABEL_SIGMA,) * component_count(right["n_strands"], right["braid_word"]),
        right["framings"],
    )
    return {
        "name": name,
        "reason": reason,
        "status": "pass" if left_rf == right_rf == left_oracle == right_oracle else "fail",
        "left": {
            "local_piece_program": program_payload(left),
            "rf_value": cyclotomic_json(left_rf),
            "oracle_value": cyclotomic_json(left_oracle),
        },
        "right": {
            "local_piece_program": program_payload(right),
            "rf_value": cyclotomic_json(right_rf),
            "oracle_value": cyclotomic_json(right_oracle),
        },
        "rf_difference": cyclotomic_json(left_rf - right_rf),
        "oracle_difference": cyclotomic_json(left_oracle - right_oracle),
    }


def rf_framed_value(n_strands, braid_word, framings):
    if len(framings) != component_count(n_strands, braid_word):
        raise ValueError("framing count must match braid closure component count")
    return rf_unframed_value(n_strands, braid_word) * SIGMA_TWIST ** sum(framings)


def rf_unframed_value(n_strands, braid_word):
    if n_strands < 1 or n_strands > 3:
        raise ValueError("B1-prime RF backend supports one to three strands")
    total = K(0)
    for total_label in possible_total_labels(n_strands):
        basis = fusion_path_basis(n_strands, total_label)
        representation = braid_matrix(n_strands, braid_word, total_label)
        total += quantum_dimension(total_label) * representation.trace()
    return K(total)


def braid_matrix(n_strands, braid_word, total_label):
    basis = fusion_path_basis(n_strands, total_label)
    if not basis:
        raise ValueError("empty fusion basis")
    output = matrix.identity(K, len(basis))
    for generator in braid_word:
        output = generator_matrix(n_strands, total_label, generator) * output
    return output


def generator_matrix(n_strands, total_label, generator):
    if generator == 0 or abs(generator) >= n_strands:
        raise ValueError("bad braid generator")
    sign = 1 if generator > 0 else -1
    index = abs(generator)
    if index == 1:
        return sigma_one_matrix(n_strands, total_label, sign)
    if n_strands == 3 and index == 2:
        return sigma_two_matrix(total_label, sign)
    raise ValueError("B1-prime RF backend only supports braid generators on up to three strands")


def sigma_one_matrix(n_strands, total_label, sign):
    basis = fusion_path_basis(n_strands, total_label)
    diagonal = []
    for path in basis:
        pair_channel = path[1] if n_strands >= 2 else None
        if pair_channel not in R_SIGMA_SIGMA:
            raise ValueError("sigma_1 requires sigma-sigma pair channel 0 or psi")
        eigenvalue = R_SIGMA_SIGMA[pair_channel]
        diagonal.append(eigenvalue if sign > 0 else eigenvalue**-1)
    return matrix.diagonal(K, diagonal)


def sigma_two_matrix(total_label, sign):
    if total_label != LABEL_SIGMA:
        raise ValueError("three sigma strands only have total sigma in this B1-prime backend")
    diagonal = matrix.diagonal(
        K,
        [
            R_SIGMA_SIGMA[LABEL_UNIT],
            R_SIGMA_SIGMA[LABEL_PSI],
        ],
    )
    if sign < 0:
        diagonal = diagonal**-1
    return F_SIGMA_SIGMA_SIGMA_SIGMA * diagonal * F_SIGMA_SIGMA_SIGMA_SIGMA


def b3_braid_relation_matrices():
    left = (
        generator_matrix(3, LABEL_SIGMA, 1)
        * generator_matrix(3, LABEL_SIGMA, 2)
        * generator_matrix(3, LABEL_SIGMA, 1)
    )
    right = (
        generator_matrix(3, LABEL_SIGMA, 2)
        * generator_matrix(3, LABEL_SIGMA, 1)
        * generator_matrix(3, LABEL_SIGMA, 2)
    )
    return left, right


def fusion_path_basis(n_strands, total_label):
    if n_strands == 1:
        return ((LABEL_SIGMA,),) if total_label == LABEL_SIGMA else ()
    if n_strands == 2:
        return ((LABEL_SIGMA, total_label),) if total_label in (LABEL_UNIT, LABEL_PSI) else ()
    if n_strands == 3:
        if total_label != LABEL_SIGMA:
            return ()
        return (
            (LABEL_SIGMA, LABEL_UNIT, LABEL_SIGMA),
            (LABEL_SIGMA, LABEL_PSI, LABEL_SIGMA),
        )
    raise ValueError("B1-prime RF backend supports one to three strands")


def possible_total_labels(n_strands):
    if n_strands % 2 == 1:
        return (LABEL_SIGMA,)
    return (LABEL_UNIT, LABEL_PSI)


def two_strand_trace(power):
    return sum(R_SIGMA_SIGMA[label] ** power for label in (LABEL_UNIT, LABEL_PSI))


def fusion_trace_terms(n_strands, braid_word):
    terms = []
    for total_label in possible_total_labels(n_strands):
        basis = fusion_path_basis(n_strands, total_label)
        representation = braid_matrix(n_strands, braid_word, total_label)
        trace = representation.trace()
        weighted = quantum_dimension(total_label) * trace
        terms.append(
            {
                "total_label": int(total_label),
                "basis": [list(path) for path in basis],
                "matrix_trace": cyclotomic_json(trace),
                "quantum_dimension": cyclotomic_json(quantum_dimension(total_label)),
                "weighted_trace": cyclotomic_json(weighted),
            }
        )
    return terms


def quantum_dimension(label):
    if label == LABEL_SIGMA:
        return SQRT2
    if label in (LABEL_UNIT, LABEL_PSI):
        return K(1)
    raise ValueError(f"unknown SU(2)_2 label: {label!r}")


def component_count(n_strands, braid_word):
    return len(closure_components(n_strands, braid_word))


def closure_components(n_strands, braid_word):
    positions = list(range(n_strands))
    for generator in braid_word:
        index = abs(generator) - 1
        positions[index], positions[index + 1] = positions[index + 1], positions[index]

    next_strand = [None] * n_strands
    for top_position, original_strand in enumerate(positions):
        next_strand[original_strand] = top_position

    seen = set()
    cycles = []
    for start in range(n_strands):
        if start in seen:
            continue
        cycle = []
        strand = start
        while strand not in seen:
            seen.add(strand)
            cycle.append(strand)
            strand = next_strand[strand]
        cycles.append(tuple(sorted(cycle)))
    return tuple(sorted(cycles, key=lambda cycle: cycle[0]))


def program_payload(case):
    component_count_value = component_count(case["n_strands"], case["braid_word"])
    program = braid_program(
        program_id=case.get("case_id", "rf-local-case"),
        category_id="SU(2)_2",
        strand_count=case["n_strands"],
        braid_word=case["braid_word"],
        framings=case["framings"],
        omega_labels=(0,) * component_count_value,
        fixed_labels=(LABEL_SIGMA,) * component_count_value,
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
        "suite": "su2-2-rf-local-backend-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "oracle_script": str(ORACLE_PATH.relative_to(REPO_ROOT)),
        "example_count": exact_output["example_count"],
        "move_regression_count": exact_output["move_regression_count"],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/su2_2_rf_local_backend.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/su2_2_rf_local_backend.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This is B1-prime: fixed all-sigma braid closures evaluated by explicit R/F matrices.",
            "The SU(2)_2 braid oracle is used only as an external exact comparison backend.",
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
    oracle = load_oracle()
    exact_output = run_suite(oracle)
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(f"examples: {exact_output['example_count']}")
    print(f"move regressions: {exact_output['move_regression_count']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
