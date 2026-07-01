"""Stress-test the pointed Vec_{Z/3}^q Kirby linking-matrix evaluator.

Run from the repository root:

    DOT_SAGE="$PWD/.sage" sage experiments/sage/vec_z3_pointed_stress.sage.py

The category is the pointed modular category on A=Z/3 with q(x)=zeta_3^(x^2).
For a framed link with integer linking matrix Q and Omega labels a, this script
checks invariance under unimodular basis changes:

    Q' = B^T Q B
    a' = B^T a  mod 3

where B records new basis vectors in the old basis.
"""

from __future__ import annotations

import argparse
from itertools import product
from pathlib import Path
import subprocess
import sys
import time

from sage.all import CyclotomicField, Matrix, ZZ, identity_matrix
from sage.env import SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-candidates"
    / "vec-z3-pointed-stress-v1.json"
)

sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.artifacts import dumps_certificate, hash_json, make_certificate  # noqa: E402


FIELD = CyclotomicField(3)
ZETA = FIELD.gen()


def run_suite():
    cases = [run_dimension_case(size) for size in range(1, 6)]
    status = "pass" if all(case["status"] == "pass" for case in cases) else "fail"
    return {
        "schema": "twisted-yetter.vec-z3-pointed-stress.v1",
        "status": status,
        "category_id": "Vec_Z3_q",
        "quadratic_form": "q(x)=zeta_3^(x^2)",
        "universal_group": "Z/3",
        "scope": (
            "pointed linking-matrix evaluator stress tests for Omega_a invariance "
            "under unimodular Kirby basis changes"
        ),
        "not_scope": (
            "non-pointed link evaluation, F/R-symbol traces, dotted/special links, "
            "closed 4-manifold normalization, or exotic-pair computation"
        ),
        "dimension_cases": cases,
        "total_move_count": sum(case["move_count"] for case in cases),
        "total_comparison_count": sum(case["comparison_count"] for case in cases),
        "total_failure_count": sum(case["failure_count"] for case in cases),
    }


def run_dimension_case(size):
    matrix = seed_linking_matrix(size)
    moves = basis_moves(size)
    before_values = all_omega_values(matrix)
    failures = []
    sample_controls = []

    for move in moves:
        basis = move["basis"]
        after_matrix = basis.transpose() * matrix * basis
        after_values = all_omega_values(after_matrix)
        move_failures = []

        for labels in product(range(3), repeat=size):
            after_labels = transform_labels(basis, labels)
            before_value = before_values[tuple(labels)]
            after_value = after_values[after_labels]
            if before_value != after_value:
                move_failures.append(
                    {
                        "labels_before": list(labels),
                        "labels_after": list(after_labels),
                        "before_value": cyclotomic_json(before_value),
                        "after_value": cyclotomic_json(after_value),
                    }
                )

        if move_failures:
            failures.append(
                {
                    "move_name": move["name"],
                    "basis": matrix_json(basis),
                    "after_matrix": matrix_json(after_matrix),
                    "failures": move_failures[:5],
                    "failure_count": len(move_failures),
                }
            )

        if len(sample_controls) < 8:
            sample_labels = tuple((index + size) % 3 for index in range(size))
            sample_after_labels = transform_labels(basis, sample_labels)
            sample_controls.append(
                {
                    "move_name": move["name"],
                    "basis": matrix_json(basis),
                    "labels_before": list(sample_labels),
                    "labels_after": list(sample_after_labels),
                    "before_value": cyclotomic_json(before_values[sample_labels]),
                    "after_value": cyclotomic_json(after_values[sample_after_labels]),
                    "status": (
                        "pass"
                        if before_values[sample_labels] == after_values[sample_after_labels]
                        else "fail"
                    ),
                }
            )

    comparison_count = len(moves) * (3**size)
    return {
        "size": size,
        "status": "pass" if not failures else "fail",
        "seed_matrix": matrix_json(matrix),
        "move_count": len(moves),
        "comparison_count": comparison_count,
        "failure_count": sum(item["failure_count"] for item in failures),
        "failures": failures,
        "sample_controls": sample_controls,
    }


def seed_linking_matrix(size):
    entries = {
        1: [[1]],
        2: [[2, -1], [-1, 1]],
        3: [[1, 1, -1], [1, 0, 1], [-1, 1, 2]],
        4: [[2, 1, -1, 0], [1, -1, 1, 2], [-1, 1, 0, -1], [0, 2, -1, 1]],
        5: [
            [1, -1, 2, 0, 1],
            [-1, 2, 1, -1, 0],
            [2, 1, -2, 1, -1],
            [0, -1, 1, 1, 2],
            [1, 0, -1, 2, 0],
        ],
    }
    return Matrix(ZZ, entries[size])


def basis_moves(size):
    moves = []
    seen = set()

    def add_move(name, basis):
        if basis.det() not in (ZZ(1), ZZ(-1)):
            raise ValueError(f"basis move is not unimodular: {name}")
        key = tuple(tuple(int(entry) for entry in row) for row in basis.rows())
        if key not in seen:
            seen.add(key)
            moves.append({"name": name, "basis": basis})

    identity = identity_matrix(ZZ, size)
    for target in range(size):
        for source in range(size):
            if target == source:
                continue
            for sign in (-1, 1):
                basis = Matrix(ZZ, identity)
                basis[source, target] += sign
                add_move(f"slide-{target}-over-{source}-sign-{sign:+d}", basis)

    for left in range(size):
        for right in range(left + 1, size):
            basis = Matrix(ZZ, identity)
            basis[left, left] = 0
            basis[right, right] = 0
            basis[left, right] = 1
            basis[right, left] = 1
            add_move(f"swap-{left}-{right}", basis)

    for index in range(size):
        basis = Matrix(ZZ, identity)
        basis[index, index] = -1
        add_move(f"reverse-{index}", basis)

    if size >= 3:
        basis = Matrix(ZZ, identity)
        basis[1, 0] += 1
        basis[2, 0] -= 1
        basis[2, 1] += 1
        add_move("compound-three-component-slide", basis)

    if size >= 4:
        basis = Matrix(ZZ, identity)
        basis[1, 0] += 1
        basis[2, 1] += 1
        basis[3, 2] -= 1
        add_move("compound-chain-slide", basis)

    if size >= 5:
        basis = Matrix(ZZ, identity)
        basis[4, 0] += 1
        basis[3, 1] -= 1
        basis[2, 4] += 1
        basis[0, 3] -= 1
        add_move("compound-five-component-mix", basis)

    return moves


def all_omega_values(linking_matrix):
    size = linking_matrix.nrows()
    entries = tuple(tuple(int(linking_matrix[row, column]) for column in range(size)) for row in range(size))
    label_vectors = tuple(product(range(3), repeat=size))
    sector_exponents = tuple(
        (simple_labels, quadratic_exponent_mod3(entries, simple_labels))
        for simple_labels in label_vectors
    )
    return {
        tuple(labels): omega_value_from_sector_exponents(labels, sector_exponents)
        for labels in label_vectors
    }


def quadratic_exponent_mod3(entries, simple_labels):
    size = len(simple_labels)
    exponent = 0
    for index, simple in enumerate(simple_labels):
        exponent += simple * simple * entries[index][index]
    for left in range(size):
        for right in range(left + 1, size):
            exponent += 2 * simple_labels[left] * simple_labels[right] * entries[left][right]
    return exponent % 3


def omega_value_from_sector_exponents(omega_labels, sector_exponents):
    counts = [0, 0, 0]
    for simple_labels, quadratic_exponent in sector_exponents:
        character_exponent = sum(
            omega_label * simple_label
            for omega_label, simple_label in zip(omega_labels, simple_labels, strict=True)
        )
        counts[(quadratic_exponent + character_exponent) % 3] += 1
    return FIELD(counts[0]) + FIELD(counts[1]) * ZETA + FIELD(counts[2]) * ZETA**2


def transform_labels(basis, labels):
    size = len(labels)
    return tuple(
        int(sum(int(basis[row, column]) * labels[row] for row in range(size)) % 3)
        for column in range(size)
    )


def matrix_json(matrix):
    return [[int(entry) for entry in row] for row in matrix.rows()]


def cyclotomic_json(value):
    value = FIELD(value)
    return {
        "field": "CyclotomicField(3)",
        "zeta_symbol": "zeta3",
        "display": str(value),
        "coefficients": [str(coefficient) for coefficient in value.list()],
    }


def build_certificate(exact_output, output_path, started_at, elapsed_seconds):
    input_definition = {
        "suite": "vec-z3-pointed-stress-v1",
        "output_path": str(output_path.relative_to(REPO_ROOT)),
        "sizes": [case["size"] for case in exact_output["dimension_cases"]],
    }
    return make_certificate(
        status=exact_output["status"],
        command="sage experiments/sage/vec_z3_pointed_stress.sage.py",
        argv=[Path(sys.argv[0]).name, *sys.argv[1:]],
        git=git_metadata(),
        tool_versions={"python": sys.version.split()[0], "sage": SAGE_VERSION},
        input_hash=hash_json(input_definition),
        exact_output=exact_output,
        generator_script=str(Path(__file__).relative_to(REPO_ROOT)),
        reproduce_command=(
            'DOT_SAGE="$PWD/.sage" sage experiments/sage/vec_z3_pointed_stress.sage.py '
            f"--output {output_path.relative_to(REPO_ROOT)}"
        ),
        started_at_utc=started_at,
        finished_at_utc=utc_now_iso(),
        elapsed_seconds=int(elapsed_seconds),
        repo_root=str(REPO_ROOT),
        notes=[
            "This artifact is specific to the pointed modular category Vec_{Z/3}^q.",
            "It checks linking-matrix basis-change invariance of the Omega_a sum.",
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
    exact_output = run_suite()
    certificate = build_certificate(exact_output, output_path, started_at, time.time() - start)
    output_path.write_text(dumps_certificate(certificate))

    print(f"wrote {output_path.relative_to(REPO_ROOT)}")
    print(f"status: {exact_output['status']}")
    print(f"moves: {exact_output['total_move_count']}")
    print(f"comparisons: {exact_output['total_comparison_count']}")
    print(f"failures: {exact_output['total_failure_count']}")

    if exact_output["status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
