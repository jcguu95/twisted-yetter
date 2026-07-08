#!/usr/bin/env python3
"""SU(3)_2 standard-form character controls for small handle examples."""

from __future__ import annotations

from datetime import UTC, datetime
from itertools import product
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
CATALOG = REPO_ROOT / "experiments/inputs/small-handle-examples/special-handle-catalog-v1.json"
EVALUATOR_PATH = REPO_ROOT / "experiments/sage/su3_2_anyonwiki_fr_braid_evaluator.py"
OUTPUT = (
    REPO_ROOT
    / "experiments/results/small-handle-examples/su3-2-standard-form-character-controls-v1.json"
)
MODULUS = 3
TOLERANCE = 1e-8


def command(argv: list[str]) -> str | None:
    try:
        return subprocess.check_output(argv, cwd=REPO_ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def repo_metadata() -> dict[str, object]:
    status_short = command(["git", "status", "--short"])
    return {
        "root": str(REPO_ROOT),
        "git_commit": command(["git", "rev-parse", "HEAD"]),
        "dirty": bool(status_short),
        "status_short": status_short,
    }


def rel(path: Path) -> str:
    return str(path.resolve().relative_to(REPO_ROOT))


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load module from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def complex_json(value: complex) -> dict[str, str]:
    value = complex(value)
    return {
        "field": "complex128",
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "display": f"{value.real:.17g}{value.imag:+.17g}j",
    }


def mod_vector(vector: list[int], modulus: int = MODULUS) -> tuple[int, ...]:
    return tuple(int(entry) % modulus for entry in vector)


def dot_mod(left: tuple[int, ...], right: list[int], modulus: int = MODULUS) -> int:
    return sum(a * int(b) for a, b in zip(left, right, strict=True)) % modulus


def mat_col(matrix: list[list[int]], column: int) -> tuple[int, ...]:
    return tuple(int(row[column]) for row in matrix)


def add_mod(left: tuple[int, ...], right: tuple[int, ...], modulus: int = MODULUS) -> tuple[int, ...]:
    return tuple((a + b) % modulus for a, b in zip(left, right, strict=True))


def cohomology_representatives(
    d2: list[list[int]],
    d3: list[list[int]],
    quotient_basis: list[list[int]],
) -> list[dict[str, Any]]:
    n1 = len(d2)
    n2 = len(d2[0]) if d2 else len(d3)
    n3 = len(d3[0]) if d3 else 0
    cocycles = []
    for alpha in product(range(MODULUS), repeat=n2):
        if all(dot_mod(alpha, list(mat_col(d3, col))) == 0 for col in range(n3)):
            cocycles.append(alpha)

    coboundaries = {tuple(0 for _ in range(n2))}
    for beta in product(range(MODULUS), repeat=n1):
        values = []
        for handle_index in range(n2):
            values.append(
                sum(int(beta[row]) * int(d2[row][handle_index]) for row in range(n1)) % MODULUS
            )
        coboundaries.add(tuple(values))

    remaining = set(cocycles)
    reps = []
    for alpha in sorted(cocycles):
        if alpha not in remaining:
            continue
        coset = {add_mod(alpha, boundary) for boundary in coboundaries}
        remaining.difference_update(coset)
        values_on_basis = [
            dot_mod(alpha, basis_vector)
            for basis_vector in quotient_basis
        ]
        reps.append(
            {
                "representative_on_two_handles": list(alpha),
                "coset_size": len(coset),
                "values_on_h2_quotient_basis": values_on_basis,
            }
        )
    return reps


def hopf_ratio(su3, evaluator, left: str, right: str, linking: int) -> complex:
    if linking == 0:
        return 1.0 + 0.0j
    positive = linking > 0
    hopf = su3.hopf_expected(evaluator, left, right, positive=positive)
    ratio = hopf / (evaluator.dimension(left) * evaluator.dimension(right))
    return ratio ** abs(int(linking))


def form_value(su3, evaluator, form: list[list[int]], character_powers: list[int]) -> complex:
    rank = len(form)
    if rank == 0:
        return 1.0 + 0.0j
    total = 0.0 + 0.0j
    for labels in product(evaluator.labels, repeat=rank):
        term = 1.0 + 0.0j
        for index, label in enumerate(labels):
            term *= evaluator.dimension(label) ** 2
            term *= evaluator.twist(label) ** int(form[index][index])
            term *= su3.character_value(character_powers[index], label)
        for i in range(rank):
            for j in range(i + 1, rank):
                term *= hopf_ratio(su3, evaluator, labels[i], labels[j], int(form[i][j]))
        total += term
    return total


def analyze_example(su3, evaluator, example: dict[str, Any]) -> dict[str, Any]:
    form = [[int(value) for value in row] for row in example["expected"]["h2_intersection_form"]]
    d2 = [[int(value) for value in row] for row in example["d2_matrix"]]
    d3 = [[int(value) for value in row] for row in example["d3_matrix"]]
    quotient_basis = [[int(value) for value in row] for row in example["h2_quotient_basis"]]
    reps = cohomology_representatives(d2, d3, quotient_basis)
    baseline = form_value(su3, evaluator, form, [0] * len(form))
    rows = []
    for rep in reps:
        powers = list(rep["values_on_h2_quotient_basis"])
        value = form_value(su3, evaluator, form, powers)
        ratio = value / baseline if abs(baseline) > TOLERANCE else complex("nan")
        rows.append(
            {
                **rep,
                "standard_form_value": complex_json(value),
                "baseline_ratio": complex_json(ratio),
                "differs_from_untwisted": bool(abs(value - baseline) > TOLERANCE),
            }
        )
    nonbaseline = [row for row in rows if row["differs_from_untwisted"]]
    return {
        "id": example["id"],
        "candidate_status": example["candidate_status"],
        "recognition_status": example["recognition_status"],
        "handle_counts": {
            "one": len(example["one_handles"]),
            "two": len(example["two_handles"]),
            "three": len(example["three_handles"]),
        },
        "h2_rank": len(form),
        "h2_intersection_form": form,
        "z3_character_count": len(rows),
        "nonbaseline_character_count": len(nonbaseline),
        "has_interesting_su3_2_character_twist": bool(nonbaseline),
        "untwisted_value": complex_json(baseline),
        "rows": rows,
    }


def main() -> int:
    started = time.monotonic()
    utc_start = datetime.now(UTC).isoformat()
    catalog = json.loads(CATALOG.read_text())
    su3 = load_module(EVALUATOR_PATH, "su3_2_anyonwiki_small_handle_controls")
    evaluator = su3.SU32AnyonWikiFRBraidEvaluator(
        category_parameter="cat_1_3_1",
        braiding_convention="anyonwiki_direct",
    )
    examples = [analyze_example(su3, evaluator, example) for example in catalog["examples"]]
    interesting = [example["id"] for example in examples if example["has_interesting_su3_2_character_twist"]]
    payload = {
        "schema": "twisted-yetter.small-handle-su3-2-standard-form-character-controls.v1",
        "status": "pass",
        "mathematical_status": "STANDARD_FORM_FLOATING_CONTROL_NOT_SPECIAL_DOTTED_RT_EVALUATION",
        "generator_script": rel(Path(__file__)),
        "argv": sys.argv[1:],
        "reproduce_command": "python experiments/scripts/small_handle_su3_2_character_controls.py",
        "utc_start": utc_start,
        "utc_finish": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "repo": repo_metadata(),
        "input": {
            "catalog": rel(CATALOG),
            "catalog_id": catalog["catalog_id"],
            "example_count": len(catalog["examples"]),
        },
        "category": su3.evaluator_metadata(evaluator),
        "coefficient_group": "Z/3, detected from the SU(3)_2 simple-current/triality character group",
        "claim_boundary": {
            "not_full_special_dotted_evaluator": True,
            "not_new_4_manifold_invariant_claim": True,
            "meaning": (
                "For each catalog example, reduce to the recorded H2 quotient "
                "intersection form and evaluate all legal Z/3 H2-character "
                "controls using SU(3)_2 modular data. This tests whether the "
                "standard-form controls have nontrivial character dependence."
            ),
        },
        "example_count": len(examples),
        "interesting_example_count": len(interesting),
        "interesting_example_ids": interesting,
        "examples": examples,
    }
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(
        json.dumps(
            {
                "artifact": rel(OUTPUT),
                "status": payload["status"],
                "example_count": payload["example_count"],
                "interesting_example_count": payload["interesting_example_count"],
                "interesting_example_ids": payload["interesting_example_ids"],
                "elapsed_seconds": payload["elapsed_seconds"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
