#!/usr/bin/env sage --python
"""Exact rank-2 Fibonacci/Yang-Lee ribbon coherence certificate.

The output is an input certificate for
``build_low_rank_ribbon_realization_catalog_v4.py``.  It checks the four
braided rank-2 Fibonacci/Yang-Lee branches with exact Sage number-field
arithmetic, including pentagon, both hexagons, balancing, ribbon square
relations, and nondegenerate S-matrix determinant.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from sage.all import CyclotomicField, Matrix, PolynomialRing, identity_matrix
from sage.version import version as SAGE_VERSION


REPO_ROOT = Path(__file__).resolve().parents[2]
OUT = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "foundation-v2-safety-substrate"
    / "rank2-fibonacci-yang-lee-sage-coherence-v1.json"
)

LABELS = ["1", "x"]
BRANCHES = [
    {
        "realization_id": "rank2-fibonacci-yang-lee-fibonacci-plus",
        "dimension_root": "positive_fibonacci_phi",
        "theta_zeta10_power": 4,
        "r_1_zeta10_power": 6,
        "r_x_zeta10_power": 3,
    },
    {
        "realization_id": "rank2-fibonacci-yang-lee-fibonacci-minus",
        "dimension_root": "positive_fibonacci_phi",
        "theta_zeta10_power": 6,
        "r_1_zeta10_power": 4,
        "r_x_zeta10_power": 7,
    },
    {
        "realization_id": "rank2-fibonacci-yang-lee-yang-lee-plus",
        "dimension_root": "negative_yang_lee",
        "theta_zeta10_power": 2,
        "r_1_zeta10_power": 8,
        "r_x_zeta10_power": 9,
    },
    {
        "realization_id": "rank2-fibonacci-yang-lee-yang-lee-minus",
        "dimension_root": "negative_yang_lee",
        "theta_zeta10_power": 8,
        "r_1_zeta10_power": 2,
        "r_x_zeta10_power": 1,
    },
]


def utc_now() -> str:
    return datetime.now(UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def stable_content_hash(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def add_content_hash(payload: dict[str, Any]) -> dict[str, Any]:
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def outputs(left: str, right: str) -> list[str]:
    if left == "1":
        return [right]
    if right == "1":
        return [left]
    return ["1", "x"]


PAIR_OUTPUTS = {(a, b): outputs(a, b) for a in LABELS for b in LABELS}


class Rank2Data:
    def __init__(self, field: Any, zeta10: Any, dimension: Any, u: Any, r1: Any, rx: Any):
        self.field = field
        self.zeta10 = zeta10
        self.dimension = dimension
        self.u = u
        self.r1 = r1
        self.rx = rx
        self.f_matrices: dict[tuple[str, str, str, str], Any] = {}
        self.f_inverses: dict[tuple[str, str, str, str], Any] = {}
        self.left_labels: dict[tuple[str, str, str, str], list[str]] = {}
        self.right_labels: dict[tuple[str, str, str, str], list[str]] = {}
        self._build_f_data()

    def _build_f_data(self) -> None:
        for a in LABELS:
            for b in LABELS:
                for c in LABELS:
                    for d in LABELS:
                        left = [x for x in outputs(a, b) if d in outputs(x, c)]
                        right = [y for y in outputs(b, c) if d in outputs(a, y)]
                        if not left and not right:
                            continue
                        if len(left) != len(right):
                            raise ValueError((a, b, c, d, left, right))
                        if a == b == c == d == "x":
                            matrix = Matrix(
                                self.field,
                                [
                                    [1 / self.dimension, self.u],
                                    [self.u, -1 / self.dimension],
                                ],
                            )
                        elif len(left) == 1:
                            # Unit-normalized 1D associativity blocks.  The
                            # intermediate labels need not be textually equal.
                            matrix = Matrix(self.field, [[1]])
                        else:
                            raise ValueError((a, b, c, d, left, right))
                        key = (a, b, c, d)
                        self.f_matrices[key] = matrix
                        self.f_inverses[key] = matrix.inverse()
                        self.left_labels[key] = left
                        self.right_labels[key] = right

    def f_right_to_left(self, key: tuple[str, str, str, str]) -> Any:
        return self.f_matrices[key]

    def f_left_to_right(self, key: tuple[str, str, str, str]) -> Any:
        return self.f_inverses[key]

    def r_ab_to_ba(self, a: str, b: str, c: str) -> Any:
        if a == b == "x" and c == "1":
            return self.r1
        if a == b == "x" and c == "x":
            return self.rx
        return self.field(1)


def zero_matrix(field: Any, rows: int, cols: int) -> Any:
    return Matrix(field, rows, cols, [field(0)] * rows * cols)


def diagonal_braid(data: Rank2Data, source: list[str], target: list[str], a: str, b: str) -> Any:
    result = zero_matrix(data.field, len(target), len(source))
    row_index = {item: idx for idx, item in enumerate(target)}
    for col, label in enumerate(source):
        row = row_index.get(label)
        if row is not None:
            result[row, col] = data.r_ab_to_ba(a, b, label)
    return result


def restrict(matrix: Any, rows: list[str], desired_rows: list[str], cols: list[str], desired_cols: list[str]) -> Any:
    result = zero_matrix(matrix.base_ring(), len(desired_rows), len(desired_cols))
    for i, row in enumerate(desired_rows):
        for j, col in enumerate(desired_cols):
            result[i, j] = matrix[rows.index(row), cols.index(col)]
    return result


def matrix_is_zero(matrix: Any) -> bool:
    return all(entry == 0 for entry in matrix.list())


def matrix_error_payload(matrix: Any) -> dict[str, Any]:
    if matrix_is_zero(matrix):
        return {"zero": True, "first_nonzero": None}
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            if matrix[i, j] != 0:
                return {
                    "zero": False,
                    "first_nonzero": {
                        "row": i,
                        "col": j,
                        "value": str(matrix[i, j]),
                    },
                }
    raise AssertionError("unreachable")


def pentagon_bases(a: str, b: str, c: str, d: str, e: str) -> dict[str, list[tuple[str, str]]]:
    return {
        "v0": [(x, y) for x in outputs(a, b) for y in outputs(x, c) if e in outputs(y, d)],
        "v1": [(u, y) for u in outputs(b, c) for y in outputs(a, u) if e in outputs(y, d)],
        "v2": [(u, v) for u in outputs(b, c) for v in outputs(u, d) if e in outputs(a, v)],
        "v3": [(w, v) for w in outputs(c, d) for v in outputs(b, w) if e in outputs(a, v)],
        "v4": [(x, w) for x in outputs(a, b) for w in outputs(c, d) if e in outputs(x, w)],
    }


def pentagon_edge_v0_v1(data: Rank2Data, bases: dict[str, list[tuple[str, str]]], a: str, b: str, c: str) -> Any:
    result = zero_matrix(data.field, len(bases["v1"]), len(bases["v0"]))
    row_index = {item: idx for idx, item in enumerate(bases["v1"])}
    for col, (x, y) in enumerate(bases["v0"]):
        key = (a, b, c, y)
        matrix = data.f_left_to_right(key)
        left = data.left_labels[key]
        right = data.right_labels[key]
        for u_idx, u in enumerate(right):
            row = row_index.get((u, y))
            if row is not None:
                result[row, col] = matrix[u_idx, left.index(x)]
    return result


def pentagon_edge_v1_v2(data: Rank2Data, bases: dict[str, list[tuple[str, str]]], a: str, d: str, e: str) -> Any:
    result = zero_matrix(data.field, len(bases["v2"]), len(bases["v1"]))
    row_index = {item: idx for idx, item in enumerate(bases["v2"])}
    for col, (u, y) in enumerate(bases["v1"]):
        key = (a, u, d, e)
        matrix = data.f_left_to_right(key)
        left = data.left_labels[key]
        right = data.right_labels[key]
        for v_idx, v in enumerate(right):
            row = row_index.get((u, v))
            if row is not None:
                result[row, col] = matrix[v_idx, left.index(y)]
    return result


def pentagon_edge_v2_v3(data: Rank2Data, bases: dict[str, list[tuple[str, str]]], b: str, c: str, d: str) -> Any:
    result = zero_matrix(data.field, len(bases["v3"]), len(bases["v2"]))
    row_index = {item: idx for idx, item in enumerate(bases["v3"])}
    for col, (u, v) in enumerate(bases["v2"]):
        key = (b, c, d, v)
        matrix = data.f_left_to_right(key)
        left = data.left_labels[key]
        right = data.right_labels[key]
        for w_idx, w in enumerate(right):
            row = row_index.get((w, v))
            if row is not None:
                result[row, col] = matrix[w_idx, left.index(u)]
    return result


def pentagon_edge_v0_v4(data: Rank2Data, bases: dict[str, list[tuple[str, str]]], c: str, d: str, e: str) -> Any:
    result = zero_matrix(data.field, len(bases["v4"]), len(bases["v0"]))
    row_index = {item: idx for idx, item in enumerate(bases["v4"])}
    for col, (x, y) in enumerate(bases["v0"]):
        key = (x, c, d, e)
        matrix = data.f_left_to_right(key)
        left = data.left_labels[key]
        right = data.right_labels[key]
        for w_idx, w in enumerate(right):
            row = row_index.get((x, w))
            if row is not None:
                result[row, col] = matrix[w_idx, left.index(y)]
    return result


def pentagon_edge_v4_v3(data: Rank2Data, bases: dict[str, list[tuple[str, str]]], a: str, b: str, e: str) -> Any:
    result = zero_matrix(data.field, len(bases["v3"]), len(bases["v4"]))
    row_index = {item: idx for idx, item in enumerate(bases["v3"])}
    for col, (x, w) in enumerate(bases["v4"]):
        key = (a, b, w, e)
        matrix = data.f_left_to_right(key)
        left = data.left_labels[key]
        right = data.right_labels[key]
        for v_idx, v in enumerate(right):
            row = row_index.get((w, v))
            if row is not None:
                result[row, col] = matrix[v_idx, left.index(x)]
    return result


def scan_pentagon(data: Rank2Data) -> dict[str, Any]:
    active = 0
    worst = None
    for a in LABELS:
        for b in LABELS:
            for c in LABELS:
                for d in LABELS:
                    possible_e = sorted(
                        {
                            e
                            for x in outputs(a, b)
                            for y in outputs(x, c)
                            for e in outputs(y, d)
                        }
                    )
                    for e in possible_e:
                        bases = pentagon_bases(a, b, c, d, e)
                        if not bases["v0"] and not bases["v3"]:
                            continue
                        active += 1
                        top = (
                            pentagon_edge_v2_v3(data, bases, b, c, d)
                            * pentagon_edge_v1_v2(data, bases, a, d, e)
                            * pentagon_edge_v0_v1(data, bases, a, b, c)
                        )
                        bottom = (
                            pentagon_edge_v4_v3(data, bases, a, b, e)
                            * pentagon_edge_v0_v4(data, bases, c, d, e)
                        )
                        diff = top - bottom
                        if not matrix_is_zero(diff):
                            worst = {
                                "a": a,
                                "b": b,
                                "c": c,
                                "d": d,
                                "e": e,
                                "difference": matrix_error_payload(diff),
                            }
                            return {"status": "FAIL", "active_tuple_count": active, "worst_example": worst}
    return {"status": "PASS", "active_tuple_count": active, "worst_example": None}


def scan_right_hexagon(data: Rank2Data) -> dict[str, Any]:
    active = 0
    for a in LABELS:
        for b in LABELS:
            for c in LABELS:
                for d in LABELS:
                    domain = [y for y in outputs(b, c) if d in outputs(a, y)]
                    codomain = [y for y in outputs(b, c) if d in outputs(y, a)]
                    if not domain and not codomain:
                        continue
                    active += 1
                    direct = zero_matrix(data.field, len(codomain), len(domain))
                    for col, y in enumerate(domain):
                        if y in codomain:
                            direct[codomain.index(y), col] = data.r_ab_to_ba(a, y, d)
                    t1 = [x for x in outputs(a, b) if d in outputs(x, c)]
                    t2 = [x for x in outputs(b, a) if d in outputs(x, c)]
                    t3 = [z for z in outputs(a, c) if d in outputs(b, z)]
                    t4 = [z for z in outputs(c, a) if d in outputs(b, z)]
                    s1 = data.f_right_to_left((a, b, c, d))
                    s2 = diagonal_braid(data, t1, t2, a, b)
                    s3 = data.f_left_to_right((b, a, c, d))
                    s4 = diagonal_braid(data, t3, t4, a, c)
                    s5 = data.f_right_to_left((b, c, a, d))
                    path = s5 * s4 * s3 * s2 * s1
                    rows = data.left_labels[(b, c, a, d)]
                    path = restrict(path, rows, codomain, domain, domain)
                    diff = path - direct
                    if not matrix_is_zero(diff):
                        return {
                            "status": "FAIL",
                            "active_tuple_count": active,
                            "worst_example": {
                                "a": a,
                                "b": b,
                                "c": c,
                                "d": d,
                                "difference": matrix_error_payload(diff),
                            },
                        }
    return {"status": "PASS", "active_tuple_count": active, "worst_example": None}


def scan_left_hexagon(data: Rank2Data) -> dict[str, Any]:
    active = 0
    for a in LABELS:
        for b in LABELS:
            for c in LABELS:
                for d in LABELS:
                    domain = [x for x in outputs(a, b) if d in outputs(x, c)]
                    codomain = [x for x in outputs(a, b) if d in outputs(c, x)]
                    if not domain and not codomain:
                        continue
                    active += 1
                    direct = zero_matrix(data.field, len(codomain), len(domain))
                    for col, x in enumerate(domain):
                        if x in codomain:
                            direct[codomain.index(x), col] = data.r_ab_to_ba(x, c, d)
                    t1 = [y for y in outputs(b, c) if d in outputs(a, y)]
                    t2 = [y for y in outputs(c, b) if d in outputs(a, y)]
                    t3 = [z for z in outputs(a, c) if d in outputs(z, b)]
                    t4 = [z for z in outputs(c, a) if d in outputs(z, b)]
                    s1 = data.f_left_to_right((a, b, c, d))
                    s2 = diagonal_braid(data, t1, t2, b, c)
                    s3 = data.f_right_to_left((a, c, b, d))
                    s4 = diagonal_braid(data, t3, t4, a, c)
                    s5 = data.f_left_to_right((c, a, b, d))
                    path = s5 * s4 * s3 * s2 * s1
                    rows = data.right_labels[(c, a, b, d)]
                    path = restrict(path, rows, codomain, domain, domain)
                    diff = path - direct
                    if not matrix_is_zero(diff):
                        return {
                            "status": "FAIL",
                            "active_tuple_count": active,
                            "worst_example": {
                                "a": a,
                                "b": b,
                                "c": c,
                                "d": d,
                                "difference": matrix_error_payload(diff),
                            },
                        }
    return {"status": "PASS", "active_tuple_count": active, "worst_example": None}


def make_branch_data(branch: dict[str, Any], *, wrong_rx_shift: int = 0) -> tuple[Rank2Data, Any, Any]:
    cyclotomic = CyclotomicField(10)
    zeta10 = cyclotomic.gen()
    theta = zeta10 ** int(branch["theta_zeta10_power"])
    dimension = -(theta + theta ** -1)
    polynomial = PolynomialRing(cyclotomic, "u")
    u_var = polynomial.gen()
    field = cyclotomic.extension(u_var**2 - cyclotomic(1) / dimension, "u")
    u = field.gen()
    zeta10_ext = field(zeta10)
    dimension_ext = field(dimension)
    r1 = zeta10_ext ** int(branch["r_1_zeta10_power"])
    rx = zeta10_ext ** ((int(branch["r_x_zeta10_power"]) + wrong_rx_shift) % 10)
    return Rank2Data(field, zeta10_ext, dimension_ext, u, r1, rx), theta, dimension


def branch_certificate(branch: dict[str, Any]) -> dict[str, Any]:
    data, theta, dimension = make_branch_data(branch)
    zeta10 = data.zeta10
    theta_ext = zeta10 ** int(branch["theta_zeta10_power"])
    s_matrix = Matrix(data.field, [[1, data.dimension], [data.dimension, -1]])
    nontrivial_f = data.f_right_to_left(("x", "x", "x", "x"))
    checks = {
        "dimension_polynomial_d2_eq_d_plus_1": data.dimension**2 == data.dimension + 1,
        "u_square_eq_inverse_dimension": data.u**2 == 1 / data.dimension,
        "nontrivial_f_matrix_involutive": nontrivial_f * nontrivial_f
        == identity_matrix(data.field, 2),
        "twist_polynomial_theta2_plus_dtheta_plus_1": theta_ext**2
        + data.dimension * theta_ext
        + 1
        == 0,
        "r1_square_balances_unit_channel": data.r1**2 * theta_ext**2 == 1,
        "rx_square_balances_x_channel": data.rx**2 * theta_ext == 1,
        "s_matrix_determinant_nonzero": s_matrix.det() != 0,
    }
    pentagon = scan_pentagon(data)
    right_hexagon = scan_right_hexagon(data)
    left_hexagon = scan_left_hexagon(data)
    wrong_data, _, _ = make_branch_data(branch, wrong_rx_shift=5)
    wrong_right = scan_right_hexagon(wrong_data)
    wrong_left = scan_left_hexagon(wrong_data)
    checks.update(
        {
            "pentagon": pentagon["status"] == "PASS",
            "right_hexagon": right_hexagon["status"] == "PASS",
            "left_hexagon": left_hexagon["status"] == "PASS",
            "wrong_rx_square_root_rejected": (
                wrong_right["status"] == "FAIL" or wrong_left["status"] == "FAIL"
            ),
        }
    )
    status = "PASS" if all(checks.values()) else "FAIL"
    return {
        **branch,
        "status": status,
        "field": "CyclotomicField(10) extended by u^2=1/d",
        "dimension": str(dimension),
        "theta": f"zeta10^{branch['theta_zeta10_power']}",
        "r_symbols": {
            "R_xx_to_1": f"zeta10^{branch['r_1_zeta10_power']}",
            "R_xx_to_x": f"zeta10^{branch['r_x_zeta10_power']}",
        },
        "f_symbols": {
            "F_xxx_to_x_basis_1_x": [["1/d", "u"], ["u", "-1/d"]],
            "relations": ["d^2=d+1", "u^2=1/d"],
        },
        "exact_checks": checks,
        "scan_summaries": {
            "pentagon": pentagon,
            "right_hexagon": right_hexagon,
            "left_hexagon": left_hexagon,
        },
        "negative_controls": {
            "wrong_rx_square_root": {
                "right_hexagon_status": wrong_right["status"],
                "left_hexagon_status": wrong_left["status"],
            }
        },
    }


def build_payload() -> dict[str, Any]:
    started = time.monotonic()
    started_at = utc_now()
    branch_results = [branch_certificate(branch) for branch in BRANCHES]
    payload = {
        "schema": "twisted-yetter.rank2-fibonacci-yang-lee-sage-coherence.v1",
        "status": "PASS" if all(item["status"] == "PASS" for item in branch_results) else "FAIL",
        "generated_at_utc": started_at,
        "utc_finish": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": "experiments/sage/rank2_fibonacci_yang_lee_certificate.sage.py",
        "reproduce_command": (
            "env DOT_SAGE=$PWD/.sage sage --python "
            "experiments/sage/rank2_fibonacci_yang_lee_certificate.sage.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {
            "python": platform.python_version(),
            "sage": SAGE_VERSION,
        },
        "family_id": "rank2-fibonacci-yang-lee",
        "branch_count": len(branch_results),
        "branches": branch_results,
        "explicit_non_claims": [
            "This certificate resolves only the rank2 Fibonacci/Yang-Lee row.",
            "This certificate does not resolve semion, Ising, SU(2), or product rows.",
            "This certificate does not authorize a formal scan plan by itself.",
        ],
    }
    return add_content_hash(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    payload = build_payload()
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(
            json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    else:
        print(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
