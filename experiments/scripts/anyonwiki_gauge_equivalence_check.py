#!/usr/bin/env python3
"""Check scalar gauge equivalence between two AnyonWiki multiplicity-free data sets."""

from __future__ import annotations

import argparse
import cmath
import hashlib
import itertools
import json
import math
import os
import platform
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Iterable


ROOT_DEFAULT = Path("experiments/inputs/anyon-wiki-data/FR_6_1_4_5")
OUT_DEFAULT = Path(
    "experiments/results/anyon-wiki-su3-2/"
    "su3-2-anyonwiki-cat-1-3-1-vs-cat-1-3-2-gauge-check-v1.json"
)
SCHEMA = "twisted-yetter.anyonwiki-gauge-equivalence-check.v1"


def load_json(path: Path) -> object:
    return json.loads(path.read_text())


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def file_record(path: Path) -> dict[str, object]:
    text = path.read_text()
    return {
        "path": path.as_posix(),
        "bytes": len(text.encode()),
        "line_count": text.count("\n") + (0 if text.endswith("\n") else 1),
        "sha256": sha256(path),
    }


def as_complex(row: dict[str, object]) -> complex:
    return complex(float(row["real"]), float(row["imag"]))


def rows_to_table(path: Path) -> dict[tuple[int, ...], complex]:
    payload = load_json(path)
    assert isinstance(payload, dict)
    rows = payload["rows"]
    assert isinstance(rows, list)
    table: dict[tuple[int, ...], complex] = {}
    for row in rows:
        assert isinstance(row, dict)
        labels = tuple(int(x) for x in row["labels"])
        table[labels] = as_complex(row)
    return table


def load_category(root: Path, name: str) -> dict[str, object]:
    cat_root = root / name
    return {
        "name": name,
        "hex": rows_to_table(cat_root / "hexsol.json"),
        "pent": rows_to_table(cat_root / "pentsol.json"),
        "files": [
            file_record(cat_root / "hexsol.json"),
            file_record(cat_root / "pentsol.json"),
            file_record(cat_root / "pivsol.json"),
        ],
    }


def fusion_triples(root: Path) -> set[tuple[int, int, int]]:
    payload = load_json(root / "structconst.json")
    assert isinstance(payload, dict)
    triples: set[tuple[int, int, int]] = set()
    for row in payload["rows"]:
        triples.add((int(row["left"]), int(row["right"]), int(row["output"])))
    return triples


def fusion_automorphisms(triples: set[tuple[int, int, int]], labels: list[int]) -> list[dict[int, int]]:
    autos: list[dict[int, int]] = []
    nonunit = [x for x in labels if x != 1]
    for perm_tail in itertools.permutations(nonunit):
        perm = {1: 1}
        perm.update(dict(zip(nonunit, perm_tail, strict=True)))
        mapped = {(perm[a], perm[b], perm[c]) for (a, b, c) in triples}
        if mapped == triples:
            autos.append(perm)
    return autos


def permute_key(key: tuple[int, ...], perm: dict[int, int]) -> tuple[int, ...]:
    return tuple(perm[x] for x in key)


def omega_power(value: complex, tol: float) -> tuple[int | None, float]:
    roots = [cmath.exp(2j * math.pi * k / 3) for k in range(3)]
    if abs(value) < tol:
        return None, float("inf")
    unit = value / abs(value)
    distances = [abs(unit - root) for root in roots]
    best = min(range(3), key=distances.__getitem__)
    magnitude_error = abs(abs(value) - 1.0)
    error = max(distances[best], magnitude_error)
    if error <= tol:
        return best, error
    return None, error


def gaussian_solve_mod_p(
    equations: list[tuple[list[int], int, str]],
    variable_count: int,
    p: int,
) -> dict[str, object]:
    matrix = [[x % p for x in coeffs] + [rhs % p] for coeffs, rhs, _ in equations]
    row_sources = [source for _, _, source in equations]
    rank = 0
    pivots: list[int] = []
    for col in range(variable_count):
        pivot = None
        for row in range(rank, len(matrix)):
            if matrix[row][col] % p:
                pivot = row
                break
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        row_sources[rank], row_sources[pivot] = row_sources[pivot], row_sources[rank]
        inv = pow(matrix[rank][col] % p, -1, p)
        matrix[rank] = [(x * inv) % p for x in matrix[rank]]
        for row in range(len(matrix)):
            if row != rank and matrix[row][col] % p:
                factor = matrix[row][col] % p
                matrix[row] = [
                    (matrix[row][i] - factor * matrix[rank][i]) % p
                    for i in range(variable_count + 1)
                ]
        pivots.append(col)
        rank += 1

    inconsistent_rows = [
        {"row": idx, "source": row_sources[idx], "rhs": matrix[idx][-1]}
        for idx, row in enumerate(matrix)
        if all(x % p == 0 for x in row[:variable_count]) and row[-1] % p != 0
    ]
    if inconsistent_rows:
        return {
            "solvable": False,
            "rank": rank,
            "nullity": variable_count - rank,
            "pivot_count": len(pivots),
            "sample_inconsistent_rows": inconsistent_rows[:8],
        }

    solution = [0] * variable_count
    for pivot_row, pivot_col in enumerate(pivots):
        solution[pivot_col] = matrix[pivot_row][-1] % p
    residuals = [
        idx
        for idx, (coeffs, rhs, _) in enumerate(equations)
        if (sum(coeffs[col] * solution[col] for col in range(variable_count)) - rhs) % p
        != 0
    ]
    return {
        "solvable": True,
        "rank": rank,
        "nullity": variable_count - rank,
        "pivot_count": len(pivots),
        "one_solution_mod_3": solution,
        "verified_equation_residuals_zero": len(residuals) == 0,
        "nonzero_residual_count": len(residuals),
        "sample_nonzero_residual_equation_indices": residuals[:8],
    }


def category_value(
    category: dict[str, object],
    kind: str,
    key: tuple[int, ...],
    variant: str,
) -> complex | None:
    hex_table = category["hex"]
    pent_table = category["pent"]
    assert isinstance(hex_table, dict)
    assert isinstance(pent_table, dict)
    if kind == "F":
        value = pent_table.get(key)
        if value is None:
            return None
        if variant in {"complex_conjugate_all", "conjugate_f_reverse_braiding"}:
            return value.conjugate()
        return value
    if kind == "R":
        if variant == "reverse_braiding_only":
            swapped = (key[1], key[0], key[2])
            value = hex_table.get(swapped)
            if value is None or abs(value) == 0:
                return None
            return 1 / value
        if variant == "conjugate_f_reverse_braiding":
            swapped = (key[1], key[0], key[2])
            value = hex_table.get(swapped)
            if value is None or abs(value) == 0:
                return None
            return 1 / value
        value = hex_table.get(key)
        if value is None:
            return None
        if variant == "complex_conjugate_all":
            return value.conjugate()
        return value
    raise ValueError(kind)


def build_variables(triples: Iterable[tuple[int, int, int]]) -> tuple[dict[tuple[int, int, int], int], list[list[int]]]:
    channels = sorted(triples)
    return {channel: idx for idx, channel in enumerate(channels)}, [list(x) for x in channels]


def attempt_equivalence(
    source: dict[str, object],
    target: dict[str, object],
    triples: set[tuple[int, int, int]],
    perm: dict[int, int],
    source_variant: str,
    f_coboundary_sign: int,
    r_coboundary_sign: int,
    tol: float,
) -> dict[str, object]:
    variable_index, variable_labels = build_variables(triples)
    equations: list[tuple[list[int], int, str]] = []
    ratio_errors: list[float] = []
    non_zeta3: list[dict[str, object]] = []
    missing: list[dict[str, object]] = []

    target_hex = target["hex"]
    target_pent = target["pent"]
    assert isinstance(target_hex, dict)
    assert isinstance(target_pent, dict)

    expected_target_hex = {permute_key(key, perm) for key in triples}
    if set(target_hex) != expected_target_hex:
        return {
            "solvable": False,
            "reason": "hex_support_mismatch_after_automorphism",
            "missing_target_hex_count": len(expected_target_hex - set(target_hex)),
            "extra_target_hex_count": len(set(target_hex) - expected_target_hex),
        }

    for key in sorted(triples):
        source_value = category_value(source, "R", key, source_variant)
        target_value = target_hex.get(permute_key(key, perm))
        if source_value is None or target_value is None:
            missing.append({"kind": "R", "source_key": list(key), "target_key": list(permute_key(key, perm))})
            continue
        exponent, error = omega_power(target_value / source_value, tol)
        ratio_errors.append(error)
        if exponent is None:
            non_zeta3.append({"kind": "R", "key": list(key), "error": error})
            continue
        coeffs = [0] * len(variable_index)
        coeffs[variable_index[(key[1], key[0], key[2])]] += r_coboundary_sign
        coeffs[variable_index[key]] -= r_coboundary_sign
        equations.append(([x % 3 for x in coeffs], exponent, f"R{key}"))

    source_pent = source["pent"]
    assert isinstance(source_pent, dict)
    expected_target_pent = {permute_key(key, perm) for key in source_pent}
    if set(target_pent) != expected_target_pent:
        return {
            "solvable": False,
            "reason": "pent_support_mismatch_after_automorphism",
            "missing_target_pent_count": len(expected_target_pent - set(target_pent)),
            "extra_target_pent_count": len(set(target_pent) - expected_target_pent),
        }

    for key in sorted(source_pent):
        target_key = permute_key(key, perm)
        if target_key not in target_pent:
            missing.append({"kind": "F", "source_key": list(key), "target_key": list(target_key)})
            continue
        source_value = category_value(source, "F", key, source_variant)
        target_value = target_pent[target_key]
        if source_value is None:
            missing.append({"kind": "F", "source_key": list(key), "target_key": list(target_key)})
            continue
        if abs(source_value) <= tol and abs(target_value) <= tol:
            continue
        if abs(source_value) <= tol or abs(target_value) <= tol:
            non_zeta3.append({"kind": "F", "key": list(key), "error": float("inf")})
            continue
        exponent, error = omega_power(target_value / source_value, tol)
        ratio_errors.append(error)
        if exponent is None:
            non_zeta3.append({"kind": "F", "key": list(key), "error": error})
            continue
        a, b, c, d, x, y = key
        coeffs = [0] * len(variable_index)
        for channel, sign in [
            ((a, b, x), 1),
            ((x, c, d), 1),
            ((b, c, y), -1),
            ((a, y, d), -1),
        ]:
            coeffs[variable_index[channel]] += f_coboundary_sign * sign
        equations.append(([x % 3 for x in coeffs], exponent, f"F{key}"))

    if missing or non_zeta3:
        return {
            "solvable": False,
            "reason": "missing_support_or_non_zeta3_ratio",
            "missing_count": len(missing),
            "non_zeta3_ratio_count": len(non_zeta3),
            "max_ratio_error": max(ratio_errors) if ratio_errors else None,
            "sample_missing": missing[:8],
            "sample_non_zeta3_ratios": non_zeta3[:8],
        }

    solve = gaussian_solve_mod_p(equations, len(variable_index), 3)
    solve.update(
        {
            "equation_count": len(equations),
            "equation_kind_counts": {
                "F": sum(1 for _, _, source in equations if source.startswith("F")),
                "R": sum(1 for _, _, source in equations if source.startswith("R")),
            },
            "variable_count": len(variable_index),
            "variable_labels": variable_labels if solve["solvable"] else None,
            "max_ratio_error": max(ratio_errors) if ratio_errors else None,
        }
    )
    return solve


def git_info(repo_root: Path) -> dict[str, object]:
    def run(args: list[str]) -> str:
        return subprocess.check_output(args, cwd=repo_root, text=True).strip()

    commit = run(["git", "rev-parse", "HEAD"])
    dirty = bool(run(["git", "status", "--porcelain"]))
    branch = run(["git", "branch", "--show-current"])
    return {"commit": commit, "branch": branch, "dirty": dirty}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input-root", type=Path, default=ROOT_DEFAULT)
    parser.add_argument("--output", type=Path, default=OUT_DEFAULT)
    parser.add_argument("--tolerance", type=float, default=1e-8)
    args = parser.parse_args()

    start = time.time()
    started_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(start))
    repo_root = Path.cwd()
    input_root = args.input_root
    cat1 = load_category(input_root, "cat_1_3_1")
    cat2 = load_category(input_root, "cat_1_3_2")
    triples = fusion_triples(input_root)
    labels = sorted({x for triple in triples for x in triple})
    autos = fusion_automorphisms(triples, labels)
    source_variants = [
        "identity",
        "complex_conjugate_all",
        "reverse_braiding_only",
        "conjugate_f_reverse_braiding",
    ]

    attempts: list[dict[str, object]] = []
    for auto_index, auto in enumerate(autos):
        for source_variant in source_variants:
            for f_sign in (1, -1):
                for r_sign in (1, -1):
                    result = attempt_equivalence(
                        cat1,
                        cat2,
                        triples,
                        auto,
                        source_variant,
                        f_sign,
                        r_sign,
                        args.tolerance,
                    )
                    attempts.append(
                        {
                            "automorphism_index": auto_index,
                            "automorphism": {str(k): auto[k] for k in sorted(auto)},
                            "source_variant_applied_to_cat_1_3_1": source_variant,
                            "f_coboundary_sign": f_sign,
                            "r_coboundary_sign": r_sign,
                            "result": result,
                        }
                    )

    successful = [attempt for attempt in attempts if attempt["result"].get("solvable")]
    reason_counts = Counter(str(attempt["result"].get("reason", "linear_inconsistent")) for attempt in attempts if not attempt["result"].get("solvable"))
    best_inconsistent = [
        attempt
        for attempt in attempts
        if not attempt["result"].get("solvable") and attempt["result"].get("reason") is None
    ][:8]
    finished = time.time()
    output = {
        "schema": SCHEMA,
        "status": "pass_found_scalar_gauge_solution" if successful else "inconclusive_no_scalar_gauge_solution_in_tested_conventions",
        "claim_status": "ESTABLISHED_WITHIN_EXPLICIT_ASSUMPTIONS" if successful else "INCONCLUSIVE",
        "started_at_utc": started_utc,
        "finished_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(finished)),
        "elapsed_seconds": round(finished - start, 6),
        "generator_script": "experiments/scripts/anyonwiki_gauge_equivalence_check.py",
        "argv": sys.argv,
        "reproduce_command": (
            "PYTHONPATH=src python experiments/scripts/anyonwiki_gauge_equivalence_check.py "
            f"--input-root {input_root.as_posix()} --output {args.output.as_posix()}"
        ),
        "repo": {"root": repo_root.as_posix(), **git_info(repo_root)},
        "python": {"version": platform.python_version(), "implementation": platform.python_implementation()},
        "inputs": {
            "fusion_ring": "FR_6_1_4_5",
            "source_category": "cat_1_3_1",
            "target_category": "cat_1_3_2",
            "files": [file_record(input_root / "structconst.json"), *cat1["files"], *cat2["files"]],
        },
        "method": {
            "description": (
                "Multiplicity-free scalar gauge search. Variables u_{ab}^c are exponents in Z/3; "
                "the checker projects target/source F and R ratios to <zeta_3> and solves the "
                "standard 2-cochain coboundary equations over GF(3)."
            ),
            "assumptions": [
                "Fusion spaces are one-dimensional, so scalar gauge variables suffice.",
                "All relevant target/source ratios must lie in the subgroup generated by zeta_3 within tolerance.",
                "The scan includes fusion-ring automorphisms, complex conjugation of all F/R data, and two braiding-reversal variants.",
                "The scan does not implement every possible tensor-opposite associator convention; a negative result is not a theorem of non-equivalence.",
            ],
            "tolerance": args.tolerance,
            "tested_source_variants": source_variants,
            "tested_coboundary_signs": {"F": [1, -1], "R": [1, -1]},
        },
        "fusion_automorphisms": [{str(k): auto[k] for k in sorted(auto)} for auto in autos],
        "summary": {
            "attempt_count": len(attempts),
            "successful_attempt_count": len(successful),
            "failure_reason_counts": dict(reason_counts),
        },
        "successful_attempts": successful,
        "sample_linear_inconsistent_attempts": best_inconsistent,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": output["status"], "output": args.output.as_posix(), "successful_attempt_count": len(successful)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
