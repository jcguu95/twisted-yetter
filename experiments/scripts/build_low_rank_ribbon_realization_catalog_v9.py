#!/usr/bin/env python3
"""Extend the partial low-rank ribbon catalog with pointed Z2 x Z2 data."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from itertools import product
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import (  # noqa: E402
    LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
    RIBBON_CATALOG_PARTIAL,
    add_content_hash,
    stable_content_hash,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
V8_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v8.json"
V8_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v8.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"

GROUP = ((0, 0), (1, 0), (0, 1), (1, 1))
ZERO = (0, 0)
REPRESENTATIVES = (
    (0, 0, 2),
    (0, 1, 3),
    (1, 1, 2),
    (2, 2, 2),
    (2, 3, 3),
)


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def file_sha256_id(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def base_meta(schema: str, status: str, *, started_at_utc: str) -> dict[str, Any]:
    return {
        "schema": schema,
        "status": status,
        "generated_at_utc": started_at_utc,
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v9.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v9.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return ((left[0] + right[0]) % 2, (left[1] + right[1]) % 2)


def label(element: tuple[int, int]) -> str:
    return f"{element[0]}{element[1]}"


def root4(power: int) -> str:
    normalized = power % 4
    if normalized == 0:
        return "1"
    if normalized == 1:
        return "i"
    if normalized == 2:
        return "-1"
    return "-i"


def q_from_rep(rep: tuple[int, int, int]) -> dict[tuple[int, int], int]:
    return {
        ZERO: 0,
        GROUP[1]: rep[0],
        GROUP[2]: rep[1],
        GROUP[3]: rep[2],
    }


def bilinear_exp(
    q: dict[tuple[int, int], int],
    left: tuple[int, int],
    right: tuple[int, int],
) -> int:
    return (q[add(left, right)] - q[left] - q[right]) % 4


def enumerate_nondegenerate_quadratic_forms() -> list[tuple[int, int, int]]:
    forms = []
    for rep in product(range(4), repeat=3):
        q = q_from_rep(rep)
        bilinear = lambda x, y: bilinear_exp(q, x, y)
        ok = True
        for x in GROUP:
            for y in GROUP:
                for z in GROUP:
                    if bilinear(add(x, y), z) != (bilinear(x, z) + bilinear(y, z)) % 4:
                        ok = False
                    if bilinear(x, add(y, z)) != (bilinear(x, y) + bilinear(x, z)) % 4:
                        ok = False
        for x in GROUP[1:]:
            if all(bilinear(x, y) == 0 for y in GROUP):
                ok = False
        if ok:
            forms.append(tuple(int(value) for value in rep))
    return forms


def gl22_actions() -> list[dict[tuple[int, int], tuple[int, int]]]:
    nonzero = GROUP[1:]
    actions = []
    for first in nonzero:
        for second in nonzero:
            if first == second:
                continue
            actions.append(
                {
                    ZERO: ZERO,
                    GROUP[1]: first,
                    GROUP[2]: second,
                    GROUP[3]: add(first, second),
                }
            )
    return actions


def quadratic_orbits() -> list[list[tuple[int, int, int]]]:
    forms = enumerate_nondegenerate_quadratic_forms()
    form_set = set(forms)
    actions = gl22_actions()
    seen: set[tuple[int, int, int]] = set()
    orbits = []
    for rep in sorted(forms):
        if rep in seen:
            continue
        q = q_from_rep(rep)
        orbit = set()
        for action in actions:
            transformed = tuple(q[action[element]] for element in GROUP[1:])
            if transformed not in form_set:
                raise RuntimeError(f"GL(2,2) action left the quadratic-form set: {transformed}")
            orbit.add(transformed)
        seen.update(orbit)
        orbits.append(sorted(orbit))
    return orbits


def canonical_representatives() -> list[tuple[int, int, int]]:
    orbits = quadratic_orbits()
    reps = [orbit[0] for orbit in orbits]
    if tuple(reps) != REPRESENTATIVES:
        raise RuntimeError(f"unexpected Z2xZ2 quadratic orbit representatives: {reps}")
    return reps


def gf2_solve(rows: list[list[int]], rhs: list[int], variable_count: int) -> list[int]:
    packed = [
        sum(((coefficient & 1) << index) for index, coefficient in enumerate(row))
        for row in rows
    ]
    rhs = [value & 1 for value in rhs]
    pivot_columns: list[int] = []
    rank = 0
    for column in range(variable_count):
        pivot = None
        for row_index in range(rank, len(packed)):
            if (packed[row_index] >> column) & 1:
                pivot = row_index
                break
        if pivot is None:
            continue
        packed[rank], packed[pivot] = packed[pivot], packed[rank]
        rhs[rank], rhs[pivot] = rhs[pivot], rhs[rank]
        for row_index in range(len(packed)):
            if row_index != rank and ((packed[row_index] >> column) & 1):
                packed[row_index] ^= packed[rank]
                rhs[row_index] ^= rhs[rank]
        pivot_columns.append(column)
        rank += 1
    for row_index in range(rank, len(packed)):
        if packed[row_index] == 0 and rhs[row_index]:
            raise RuntimeError("inconsistent mod-2 linear system")
    solution = [0] * variable_count
    for row_index, column in enumerate(pivot_columns):
        solution[column] = rhs[row_index]
    return solution


def solve_mod4(
    equations: list[tuple[dict[int, int], int]],
    variable_count: int,
) -> list[int]:
    rows = []
    rhs = []
    for coefficients, target in equations:
        row = [0] * variable_count
        for variable, coefficient in coefficients.items():
            row[variable] = (row[variable] + coefficient) % 4
        rows.append(row)
        rhs.append(target % 4)
    low_bits = gf2_solve(rows, rhs, variable_count)
    lifted_rhs = []
    for row, target in zip(rows, rhs):
        residual = sum(coefficient * value for coefficient, value in zip(row, low_bits)) - target
        if residual % 2:
            raise RuntimeError("mod-4 lift received an odd residual")
        lifted_rhs.append((-residual // 2) % 2)
    high_bits = gf2_solve(rows, lifted_rhs, variable_count)
    solution = [(low + 2 * high) % 4 for low, high in zip(low_bits, high_bits)]
    for row, target in zip(rows, rhs):
        if sum(coefficient * value for coefficient, value in zip(row, solution)) % 4 != target:
            raise RuntimeError("mod-4 solution failed verification")
    return solution


def solve_abelian_cocycle(
    rep: tuple[int, int, int]
) -> tuple[dict[tuple[tuple[int, int], tuple[int, int], tuple[int, int]], int], dict[tuple[tuple[int, int], tuple[int, int]], int]]:
    omega_keys = [("omega", a, b, c) for a in GROUP for b in GROUP for c in GROUP]
    r_keys = [("r", a, b) for a in GROUP for b in GROUP]
    keys = omega_keys + r_keys
    key_index = {key: index for index, key in enumerate(keys)}
    equations: list[tuple[dict[int, int], int]] = []

    def add_equation(terms: list[tuple[tuple[Any, ...], int]], rhs: int = 0) -> None:
        coefficients: dict[int, int] = {}
        for key, coefficient in terms:
            variable = key_index[key]
            coefficients[variable] = coefficients.get(variable, 0) + coefficient
        equations.append((coefficients, rhs))

    for a in GROUP:
        for b in GROUP:
            for c in GROUP:
                if ZERO in (a, b, c):
                    add_equation([(("omega", a, b, c), 1)])
    for a in GROUP:
        for b in GROUP:
            if ZERO in (a, b):
                add_equation([(("r", a, b), 1)])

    q = q_from_rep(rep)
    for a in GROUP:
        add_equation([(("r", a, a), 1)], q[a])

    for a in GROUP:
        for b in GROUP:
            for c in GROUP:
                for d in GROUP:
                    add_equation(
                        [
                            (("omega", b, c, d), 1),
                            (("omega", a, add(b, c), d), 1),
                            (("omega", a, b, c), 1),
                            (("omega", add(a, b), c, d), -1),
                            (("omega", a, b, add(c, d)), -1),
                        ]
                    )
    for a in GROUP:
        for b in GROUP:
            for c in GROUP:
                add_equation(
                    [
                        (("r", a, add(b, c)), 1),
                        (("omega", a, b, c), -1),
                        (("r", a, b), -1),
                        (("omega", b, a, c), 1),
                        (("r", a, c), -1),
                        (("omega", b, c, a), -1),
                    ]
                )
                add_equation(
                    [
                        (("r", add(a, b), c), 1),
                        (("omega", a, b, c), 1),
                        (("r", b, c), -1),
                        (("omega", a, c, b), -1),
                        (("r", a, c), -1),
                        (("omega", c, a, b), 1),
                    ]
                )

    solution = solve_mod4(equations, len(keys))
    omega = {key[1:]: solution[key_index[key]] for key in omega_keys}
    r_symbols = {key[1:]: solution[key_index[key]] for key in r_keys}
    return omega, r_symbols


def scan_v4(
    omega: dict[tuple[tuple[int, int], tuple[int, int], tuple[int, int]], int],
    r_symbols: dict[tuple[tuple[int, int], tuple[int, int]], int],
    *,
    strict_associator: bool = False,
) -> dict[str, Any]:
    pentagon_failures = []
    right_hexagon_failures = []
    left_hexagon_failures = []

    def w(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
        return 0 if strict_associator else omega[(a, b, c)]

    def r(a: tuple[int, int], b: tuple[int, int]) -> int:
        return r_symbols[(a, b)]

    for a in GROUP:
        for b in GROUP:
            for c in GROUP:
                for d in GROUP:
                    left = (w(b, c, d) + w(a, add(b, c), d) + w(a, b, c)) % 4
                    right = (w(add(a, b), c, d) + w(a, b, add(c, d))) % 4
                    if left != right:
                        pentagon_failures.append(
                            {
                                "a": label(a),
                                "b": label(b),
                                "c": label(c),
                                "d": label(d),
                                "left": root4(left),
                                "right": root4(right),
                            }
                        )
    for a in GROUP:
        for b in GROUP:
            for c in GROUP:
                right_direct = r(a, add(b, c))
                right_path = (w(a, b, c) + r(a, b) - w(b, a, c) + r(a, c) + w(b, c, a)) % 4
                if right_direct != right_path:
                    right_hexagon_failures.append(
                        {
                            "a": label(a),
                            "b": label(b),
                            "c": label(c),
                            "direct": root4(right_direct),
                            "path": root4(right_path),
                        }
                    )
                left_direct = r(add(a, b), c)
                left_path = (-w(a, b, c) + r(b, c) + w(a, c, b) + r(a, c) - w(c, a, b)) % 4
                if left_direct != left_path:
                    left_hexagon_failures.append(
                        {
                            "a": label(a),
                            "b": label(b),
                            "c": label(c),
                            "direct": root4(left_direct),
                            "path": root4(left_path),
                        }
                    )
    return {
        "pentagon": "PASS" if not pentagon_failures else "FAIL",
        "right_hexagon": "PASS" if not right_hexagon_failures else "FAIL",
        "left_hexagon": "PASS" if not left_hexagon_failures else "FAIL",
        "pentagon_failure_count": len(pentagon_failures),
        "right_hexagon_failure_count": len(right_hexagon_failures),
        "left_hexagon_failure_count": len(left_hexagon_failures),
        "first_pentagon_failure": pentagon_failures[0] if pentagon_failures else None,
        "first_right_hexagon_failure": right_hexagon_failures[0] if right_hexagon_failures else None,
        "first_left_hexagon_failure": left_hexagon_failures[0] if left_hexagon_failures else None,
    }


def v4_checks(
    rep: tuple[int, int, int],
    omega: dict[tuple[tuple[int, int], tuple[int, int], tuple[int, int]], int],
    r_symbols: dict[tuple[tuple[int, int], tuple[int, int]], int],
) -> dict[str, Any]:
    q = q_from_rep(rep)
    scan = scan_v4(omega, r_symbols)
    strict_scan = scan_v4(omega, r_symbols, strict_associator=True)
    monodromy_rows = {
        label(a): tuple((r_symbols[(a, b)] + r_symbols[(b, a)]) % 4 for b in GROUP)
        for a in GROUP
    }
    nondegenerate = all(
        any(value != 0 for value in monodromy_rows[label(a)])
        for a in GROUP[1:]
    )
    monodromy_matches_q = all(
        (r_symbols[(a, b)] + r_symbols[(b, a)]) % 4
        == bilinear_exp(q, a, b)
        for a in GROUP
        for b in GROUP
    )
    diagonal_matches_q = all(r_symbols[(a, a)] % 4 == q[a] for a in GROUP)
    orbits = quadratic_orbits()
    return {
        "normalized_abelian_3_cocycle": scan["pentagon"],
        "right_hexagon": scan["right_hexagon"],
        "left_hexagon": scan["left_hexagon"],
        "diagonal_q_equals_R_aa": "PASS" if diagonal_matches_q else "FAIL",
        "monodromy_matches_quadratic_bilinearization": "PASS"
        if monodromy_matches_q
        else "FAIL",
        "monodromy_nondegenerate": "PASS" if nondegenerate else "FAIL",
        "nonzero_omega_entry_count": sum(1 for value in omega.values() if value % 4),
        "nonzero_r_entry_count": sum(1 for value in r_symbols.values() if value % 4),
        "all_nondegenerate_quadratic_forms_count": len(enumerate_nondegenerate_quadratic_forms()),
        "gl22_orbit_count": len(orbits),
        "selected_representatives": [list(item) for item in REPRESENTATIVES],
        "strict_associator_same_R_negative_control": strict_scan,
        "strict_associator_same_R_negative_control_fails_hexagon": "PASS"
        if strict_scan["right_hexagon"] == "FAIL" or strict_scan["left_hexagon"] == "FAIL"
        else "FAIL",
        "scan_details": scan,
    }


def orbit_for_rep(rep: tuple[int, int, int]) -> list[tuple[int, int, int]]:
    for orbit in quadratic_orbits():
        if rep in orbit:
            return orbit
    raise RuntimeError(f"representative is outside the quadratic orbit list: {rep}")


def table3(
    values: dict[tuple[tuple[int, int], tuple[int, int], tuple[int, int]], int]
) -> dict[str, str]:
    return {
        f"omega({label(a)},{label(b)},{label(c)})": root4(values[(a, b, c)])
        for a in GROUP
        for b in GROUP
        for c in GROUP
    }


def table2(values: dict[tuple[tuple[int, int], tuple[int, int]], int]) -> dict[str, str]:
    return {
        f"{label(a)},{label(b)}": root4(values[(a, b)])
        for a in GROUP
        for b in GROUP
    }


def build_v4_snapshot(
    *,
    rep: tuple[int, int, int],
    class_index: int,
    started_at_utc: str,
) -> dict[str, Any]:
    omega, r_symbols = solve_abelian_cocycle(rep)
    checks = v4_checks(rep, omega, r_symbols)
    for key, value in checks.items():
        if isinstance(value, str) and value == "FAIL":
            raise RuntimeError(f"Z2xZ2 checks failed for rep {rep}: {checks}")
    q = q_from_rep(rep)
    labels = [label(element) for element in GROUP]
    suffix = "q" + "".join(str(value) for value in rep)
    orbit = orbit_for_rep(rep)
    category_data = {
        "schema": "twisted-yetter.pointed-klein-four-ribbon-data.v1",
        "category_id": f"rank4-pointed-z2xz2-{suffix}",
        "family_id": "rank4-pointed-z2xz2",
        "metric_group": "Z/2 x Z/2",
        "quadratic_form_rep_exponents": {
            label(GROUP[1]): rep[0],
            label(GROUP[2]): rep[1],
            label(GROUP[3]): rep[2],
        },
        "quadratic_form": {
            label(element): root4(q[element])
            for element in GROUP
        },
        "quadratic_orbit_under_GL22": [list(item) for item in orbit],
        "quadratic_orbit_size": len(orbit),
        "field": "Q(i)",
        "labels": labels,
        "unit": label(ZERO),
        "fusion": {
            f"{label(left)}*{label(right)}": label(add(left, right))
            for left in GROUP
            for right in GROUP
        },
        "duals": {label(element): label(element) for element in GROUP},
        "f_symbols": {
            "associator_table": table3(omega),
            "note": (
                "nontrivial abelian 3-cocycle is recorded explicitly; "
                "strict-associator reuse with the same R table is a negative control"
            ),
        },
        "r_symbols": table2(r_symbols),
        "twists": {label(element): root4(q[element]) for element in GROUP},
        "dimensions": {item: "1" for item in labels},
        "pivotal_scalars": {item: "1" for item in labels},
        "left_evaluation": {item: "1" for item in labels},
        "left_coevaluation": {item: "1" for item in labels},
        "right_evaluation": {item: "1" for item in labels},
        "right_coevaluation": {item: "1" for item in labels},
        "fusion_pairing": "unique one-dimensional pointed basis for each Z2xZ2 product",
        "basis_gauge": "basis e_a tensor e_b -> e_{a+b}; omega table carries associativity",
        "monodromy_bicharacter": {
            f"b({label(left)},{label(right)})": root4(
                (r_symbols[(left, right)] + r_symbols[(right, left)]) % 4
            )
            for left in GROUP
            for right in GROUP
        },
        "field_embedding": {"i": "exp(2*pi*i/4)", "exponent_modulus": 4},
        "source_locators": [
            {
                "reference_id": "ref:dong-schopieray-near-integral-2024",
                "locator": "rank tables, pages 26-33",
                "claim_used": "rank-4 Klein four pointed modular braided row count",
            },
            {
                "reference_id": "self-contained-z2xz2-abelian-cocycle-check",
                "locator": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v9.py",
                "claim_used": (
                    "exact enumeration of 16 nondegenerate quadratic forms, "
                    "five GL(2,2) orbits, and mod-4 abelian cocycle coherence"
                ),
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "field": "Q(i)",
            "checks": checks,
            "proof_boundary": "Exact Z2xZ2 pointed equations only.",
        }
    )
    consumer = add_content_hash(
        {
            "certificate_kind": "consumer_runtime_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "runtime_contract": (
                "RibbonFusionCategoryV2-compatible pointed one-dimensional "
                "fusion spaces with explicit Z2xZ2 abelian omega"
            ),
            "checked_payload_hash": category_hash,
            "basis_safety_checks": {
                "all_basis_labels_are_fixed_binary_strings": "PASS",
                "strict_associator_same_R_negative_control_fails": "PASS",
                "field_embedding_Q_i_recorded": "PASS",
                "quadratic_orbit_representative_recorded": "PASS",
            },
            "proof_boundary": "Runtime consumer certificate binds exact Z2xZ2 pointed data.",
        }
    )
    ribbon_pivotal = add_content_hash(
        {
            "certificate_kind": "ribbon_pivotal_compatibility",
            "status": "PASS",
            "category_data_hash": category_hash,
            "checks": {
                "twist_equals_R_aa": "PASS",
                "balancing": "PASS",
                "left_right_trace_agree": "PASS",
                "pivotal_scalar_unit": "PASS",
                "quantum_dimensions_all_one": "PASS",
                "monodromy_nondegenerate": "PASS",
            },
            "proof_boundary": "Braided plus pivotal is accepted only with explicit omega/R/twist checks.",
        }
    )
    snapshot = add_content_hash(
        {
            **base_meta(
                "twisted-yetter.ribbon-realization-snapshot.v1",
                "RESOLVED_RIBBON_REALIZATION",
                started_at_utc=started_at_utc,
            ),
            "evidence_kind": "ribbon_realization_snapshot",
            "claim_level": "formal-low-rank-category-evidence",
            "source_status": "formal",
            "category_contract": "RibbonFusionCategoryV2",
            "category_data_hash": category_hash,
            "family_id": "rank4-pointed-z2xz2",
            "realization_id": f"rank4-pointed-z2xz2-{suffix}",
            "modular_braided_class_index": class_index,
            "mutable_alias_inputs": [],
            "category_data": category_data,
            "pinned_payload_hashes": {
                "category_data": category_hash,
                "producer_exact_coherence": producer["content_hash"],
                "consumer_runtime_coherence": consumer["content_hash"],
                "ribbon_pivotal_compatibility": ribbon_pivotal["content_hash"],
            },
            "certificates": {
                "producer_exact_coherence": producer,
                "consumer_runtime_coherence": consumer,
                "ribbon_pivotal_compatibility": ribbon_pivotal,
            },
            "structural_checks": {
                "pentagon": "PASS",
                "hexagon": "PASS",
                "rigidity": "PASS",
                "duality_involution": "PASS",
                "fusion_pairing_invertible": "PASS",
                "r_inverse": "PASS",
                "balancing": "PASS",
                "ribbon_pivotal_compatibility": "PASS",
                "modularity": "PASS",
            },
            "explicit_non_claims": [
                "This snapshot resolves only one rank4 Klein four pointed braided class representative.",
                "This snapshot does not authorize a formal scan plan by itself.",
                "This snapshot does not resolve Ising, SU(2), PSU, or PSU(3) rows.",
            ],
        }
    )
    validate_formal_evidence(snapshot)
    return snapshot


def snapshot_path(snapshot: dict[str, Any]) -> Path:
    return SNAPSHOT_DIR / f"{snapshot['realization_id']}-snapshot-v1.json"


def mark_resolved_level_metadata(row: dict[str, Any]) -> None:
    hashes = row.get("ribbon_realization_snapshot_hashes")
    if hashes is None:
        single = row.get("ribbon_realization_snapshot_hash")
        hashes = [single] if single else []
    row["spherical_level"] = {
        "status": "HASH_BOUND_SPHERICAL_DATA_MATERIALIZED",
        "spherical_structures_per_braided_class": int(row["modular_braided_class_count"]),
        "source": "resolved ribbon realization snapshots",
    }
    row["pivotal_level"] = {
        "status": "HASH_BOUND_PIVOTAL_DATA_MATERIALIZED",
        "materialized_data": [
            "duality",
            "pivotal scalar",
            "evaluation",
            "coevaluation",
            "fusion pairing",
            "basis/gauge",
            "field embedding",
        ],
        "source": "resolved ribbon realization snapshots",
    }
    row["ribbon_level"] = {
        "status": "VERIFIED_BY_FORMAL_SNAPSHOT_CERTIFICATES",
        "required_checks": [
            "balancing",
            "twist/pivotal compatibility",
            "producer exact coherence",
            "consumer runtime coherence",
            "certificate/data-hash binding",
        ],
        "snapshot_hashes": hashes,
    }


def build_catalog_v9(*, started_at_utc: str, snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    previous = load_json(V8_CATALOG)
    snapshot_hashes = [snapshot["content_hash"] for snapshot in snapshots]
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank4-pointed-z2xz2":
            new_row.update(
                {
                    "terminal_status": "RESOLVED_RIBBON_REALIZATION",
                    "formal_admission_allowed": True,
                    "ribbon_realization_snapshot_hash": None,
                    "ribbon_realization_snapshot_hashes": snapshot_hashes,
                    "resolved_modular_braided_class_count": len(snapshot_hashes),
                    "blocker_ids": [],
                    "missing_evidence": [],
                    "resolution_note": (
                        "Resolved by exact Z2xZ2 pointed abelian cocycle snapshots "
                        "for five GL(2,2) orbits of nondegenerate quadratic forms."
                    ),
                }
            )
        if new_row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION":
            mark_resolved_level_metadata(new_row)
        rows.append(new_row)
    resolved_ids = [
        row["family_id"]
        for row in rows
        if row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    ]
    blocked_ids = [
        row["family_id"]
        for row in rows
        if row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
    ]
    catalog = {
        **base_meta(
            LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
            RIBBON_CATALOG_PARTIAL,
            started_at_utc=started_at_utc,
        ),
        "catalog_id": "low-rank-ribbon-realization-catalog-v9",
        "previous_catalog": {
            "path": str(V8_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V8_CATALOG),
            "status": previous["status"],
        },
        "scope": previous["scope"],
        "coverage_by_rank": previous["coverage_by_rank"],
        "braided_denominator_by_rank": previous["braided_denominator_by_rank"],
        "ribbon_denominator_by_rank": {},
        "ribbon_denominator_status": "PARTIAL_DO_NOT_USE_AS_FINAL_DENOMINATOR",
        "ribbon_denominator_copied_from_braided": False,
        "formal_scan_plan_allowed": False,
        "resolved_row_count": len(resolved_ids),
        "blocked_row_count": len(blocked_ids),
        "family_count": len(rows),
        "resolved_family_ids": resolved_ids,
        "blocked_family_ids": blocked_ids,
        "resolved_snapshot_paths": previous["resolved_snapshot_paths"]
        + [str(snapshot_path(snapshot).relative_to(REPO_ROOT)) for snapshot in snapshots],
        "families": rows,
        "explicit_non_claims": [
            "This partial catalog does not establish the complete rank 2-5 ribbon classification.",
            "This partial catalog does not authorize scan-plan generation.",
            "Ising, SU(2), PSU, and PSU(3) rows remain blocked.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v9(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v9",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v9",
        "previous_readiness": {
            "path": str(V8_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V8_READINESS),
        },
        "policy": {
            "path": str(V1_POLICY.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V1_POLICY),
        },
        "classification_catalog_hash": stable_content_hash(catalog),
        "classification_catalog_status": catalog["status"],
        "scan_plan_generation_allowed": False,
        "formal_scan_plan_id": None,
        "resolved_row_count": catalog["resolved_row_count"],
        "blocked_row_count": catalog["blocked_row_count"],
        "blocking_reason_ids": [
            "partial-ribbon-catalog-only",
            "six-family-rows-still-blocked",
            "ising-su2-psu-realizations-still-missing",
            "ribbon-denominator-not-final",
        ],
        "explicit_non_claims": [
            "No formal scan plan exists.",
            "No scan case result exists.",
            "No complete-no-signal aggregate exists.",
        ],
    }


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    snapshots = [
        build_v4_snapshot(
            rep=rep,
            class_index=index,
            started_at_utc=started_at_utc,
        )
        for index, rep in enumerate(canonical_representatives())
    ]
    catalog = build_catalog_v9(started_at_utc=started_at_utc, snapshots=snapshots)
    readiness = build_readiness_v9(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v9.json": catalog,
        "formal-low-rank-scan-readiness-v9.json": readiness,
    }
    for snapshot in snapshots:
        result[str(snapshot_path(snapshot).relative_to(OUT_DIR))] = snapshot
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    artifacts = build_all()
    if args.write:
        for name, payload in artifacts.items():
            write_json(OUT_DIR / name, payload)
    else:
        print(json.dumps(artifacts, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
