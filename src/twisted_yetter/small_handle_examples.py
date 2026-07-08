"""Algebraic sanity checks for small special-handle examples.

These helpers deliberately stop at the handle-chain/intersection-form level.
They do not evaluate a dotted Kirby diagram and do not claim a closed
Crane-Yetter value.  The purpose is to make the next special-dotted evaluator
fixtures precise: handle counts, d2/d3, H2, quotient relations, and legal
Z/2 2-handle cochains are all machine-readable before any RT calculation is
attempted.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Final, Mapping, Sequence

from twisted_yetter.linking_matrix import determinant, rank, signature


SMALL_HANDLE_CATALOG_SCHEMA: Final = (
    "twisted-yetter.small-special-handle-example-catalog.v1"
)
SMALL_HANDLE_SANITY_SCHEMA: Final = (
    "twisted-yetter.small-special-handle-example-sanity.v1"
)


def load_catalog(path: str | Path) -> dict[str, Any]:
    payload = json.loads(Path(path).read_text())
    if payload.get("schema") != SMALL_HANDLE_CATALOG_SCHEMA:
        raise ValueError(f"unsupported schema: {payload.get('schema')!r}")
    return payload


def analyze_catalog(payload: Mapping[str, Any]) -> dict[str, Any]:
    if payload.get("schema") != SMALL_HANDLE_CATALOG_SCHEMA:
        raise ValueError(f"unsupported schema: {payload.get('schema')!r}")
    example_analyses = [analyze_example(example) for example in payload["examples"]]
    statuses = {analysis["status"] for analysis in example_analyses}
    return {
        "schema": SMALL_HANDLE_SANITY_SCHEMA,
        "status": "pass" if statuses == {"pass"} else "fail",
        "mathematical_status": "ALGEBRAIC_HANDLE_SANITY_NOT_LINK_EVALUATOR_OUTPUT",
        "claim_boundary": {
            "not_rt_evaluation": True,
            "not_closed_4d_invariant": True,
            "not_special_dotted_projector_implementation": True,
            "purpose": (
                "fixture-level algebra for future Tham 5.11/special-dotted "
                "tests: d2, d3, H2, quotient form, and Z2 character "
                "cohomology"
            ),
        },
        "catalog_id": payload["catalog_id"],
        "example_count": len(example_analyses),
        "example_status_counts": _counts(analysis["status"] for analysis in example_analyses),
        "examples": example_analyses,
    }


def analyze_example(example: Mapping[str, Any]) -> dict[str, Any]:
    two_handles = list(example["two_handles"])
    one_handles = list(example["one_handles"])
    three_handles = list(example["three_handles"])
    d2 = _matrix(example["d2_matrix"])
    d3 = _matrix(example["d3_matrix"])
    q2 = _matrix(example["q2_matrix"])
    h2_kernel_basis = _matrix(example["h2_kernel_basis"])
    h2_quotient_basis = _matrix(example["h2_quotient_basis"])

    failures: list[dict[str, Any]] = []
    failures.extend(_shape_failures(example, d2, d3, q2, h2_kernel_basis, h2_quotient_basis))

    d2_rank = rank(d2)
    d3_rank = rank(_transpose(d3))
    kernel_rank = len(two_handles) - d2_rank
    h2_rank = kernel_rank - d3_rank
    d2_d3 = _matmul(d2, d3)
    d3_columns = _columns(d3)
    augmented = _augmented_surgery_matrix(d2, q2)
    quotient_form = _bilinear_matrix(q2, h2_quotient_basis)
    kernel_form = _bilinear_matrix(q2, h2_kernel_basis)

    if any(any(entry != 0 for entry in row) for row in d2_d3):
        failures.append({"kind": "chain-complex-failure", "d2_times_d3": d2_d3})
    for index, vector in enumerate(h2_kernel_basis):
        if any(value != 0 for value in _matvec(d2, vector)):
            failures.append({"kind": "kernel-basis-not-cycle", "index": index, "vector": vector})
    if rank(h2_kernel_basis) != len(h2_kernel_basis):
        failures.append({"kind": "kernel-basis-dependent"})
    if len(h2_kernel_basis) != kernel_rank:
        failures.append(
            {
                "kind": "kernel-basis-rank-mismatch",
                "expected_rank": kernel_rank,
                "basis_count": len(h2_kernel_basis),
            }
        )
    for index, vector in enumerate(h2_quotient_basis):
        if any(value != 0 for value in _matvec(d2, vector)):
            failures.append({"kind": "quotient-basis-not-cycle", "index": index, "vector": vector})
    if len(h2_quotient_basis) != h2_rank:
        failures.append(
            {
                "kind": "quotient-basis-rank-mismatch",
                "expected_rank": h2_rank,
                "basis_count": len(h2_quotient_basis),
            }
        )

    relation_radical_checks = _relation_radical_checks(q2, d3_columns, h2_kernel_basis)
    if not all(check["is_radical_on_kernel"] for check in relation_radical_checks):
        failures.append({"kind": "d3-relation-not-radical", "checks": relation_radical_checks})

    if rank(d3_columns + h2_quotient_basis) != kernel_rank:
        failures.append(
            {
                "kind": "d3-plus-quotient-basis-does-not-span-kernel",
                "rank": rank(d3_columns + h2_quotient_basis),
                "kernel_rank": kernel_rank,
            }
        )

    expected = dict(example.get("expected", {}))
    expected_form = expected.get("h2_intersection_form")
    if expected_form is not None and quotient_form != _matrix(expected_form):
        failures.append(
            {
                "kind": "expected-h2-form-mismatch",
                "expected": expected_form,
                "actual": quotient_form,
            }
        )

    augmented_signature = signature(augmented)
    quotient_signature = signature(quotient_form) if quotient_form else (0, 0, 0)
    betti = {
        "b0": 1,
        "b1": len(one_handles) - d2_rank,
        "b2": h2_rank,
        "b3": len(three_handles) - d3_rank,
        "b4": 1,
    }
    euler_from_handles = 2 - len(one_handles) + len(two_handles) - len(three_handles)
    euler_from_betti = betti["b0"] - betti["b1"] + betti["b2"] - betti["b3"] + betti["b4"]
    if euler_from_handles != euler_from_betti:
        failures.append(
            {
                "kind": "euler-mismatch",
                "from_handles": euler_from_handles,
                "from_betti": euler_from_betti,
            }
        )

    z2 = _z2_cohomology(d2, d3, h2_quotient_basis)
    su2_2_twisted_controls = _su2_2_z2_twisted_standard_controls(quotient_form, z2)

    return {
        "id": example["id"],
        "status": "pass" if not failures else "fail",
        "mathematical_status": "ALGEBRAIC_HANDLE_SANITY_NOT_LINK_EVALUATOR_OUTPUT",
        "candidate_status": example["candidate_status"],
        "recognition_status": example["recognition_status"],
        "purpose": example["purpose"],
        "handle_counts": {
            "0": 1,
            "1": len(one_handles),
            "2": len(two_handles),
            "3": len(three_handles),
            "4": 1,
        },
        "chain_complex": {
            "one_handles": one_handles,
            "two_handles": two_handles,
            "three_handles": three_handles,
            "d2_matrix_c2_to_c1": d2,
            "d3_matrix_c3_to_c2": d3,
            "d2_rank": d2_rank,
            "d3_rank": d3_rank,
            "d2_times_d3": d2_d3,
        },
        "homology_ranks_over_Q": betti,
        "euler_characteristic": {
            "from_handles": euler_from_handles,
            "from_betti_ranks": euler_from_betti,
        },
        "h2": {
            "kernel_rank": kernel_rank,
            "rank": h2_rank,
            "kernel_basis_in_two_handle_coordinates": h2_kernel_basis,
            "d3_relation_columns": d3_columns,
            "quotient_basis_representatives": h2_quotient_basis,
            "relation_radical_checks": relation_radical_checks,
        },
        "forms": {
            "q2_on_two_handles": q2,
            "q_on_kernel_basis": kernel_form,
            "q_on_h2_quotient_basis": quotient_form,
            "h2_form_determinant": determinant(quotient_form) if quotient_form else 1,
            "h2_signature_triple_positive_negative_zero": list(quotient_signature),
            "h2_signature": quotient_signature[0] - quotient_signature[1],
            "standard_su2_2_omega_control": _standard_su2_2_control(quotient_form),
            "su2_2_z2_twisted_standard_controls": su2_2_twisted_controls,
        },
        "augmented_dotted_surgery_matrix": {
            "matrix": augmented,
            "determinant": determinant(augmented),
            "rank": rank(augmented),
            "nullity": len(augmented) - rank(augmented),
            "signature_triple_positive_negative_zero": list(augmented_signature),
            "signature": augmented_signature[0] - augmented_signature[1],
            "interpretation": (
                "homology-boundary sanity only; not a proof that the Kirby "
                "boundary is S3 or a standard connected sum"
            ),
        },
        "z2_character_cohomology": z2,
        "expected": expected,
        "failure_count": len(failures),
        "failures": failures,
    }


def stable_json(payload: Mapping[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def _shape_failures(
    example: Mapping[str, Any],
    d2: list[list[int]],
    d3: list[list[int]],
    q2: list[list[int]],
    h2_kernel_basis: list[list[int]],
    h2_quotient_basis: list[list[int]],
) -> list[dict[str, Any]]:
    failures: list[dict[str, Any]] = []
    n1 = len(example["one_handles"])
    n2 = len(example["two_handles"])
    n3 = len(example["three_handles"])
    if len(d2) != n1 or any(len(row) != n2 for row in d2):
        failures.append({"kind": "bad-d2-shape", "expected": [n1, n2], "actual": _shape(d2)})
    if len(d3) != n2 or any(len(row) != n3 for row in d3):
        failures.append({"kind": "bad-d3-shape", "expected": [n2, n3], "actual": _shape(d3)})
    if len(q2) != n2 or any(len(row) != n2 for row in q2):
        failures.append({"kind": "bad-q2-shape", "expected": [n2, n2], "actual": _shape(q2)})
    if any(q2[i][j] != q2[j][i] for i in range(len(q2)) for j in range(len(q2))):
        failures.append({"kind": "q2-not-symmetric"})
    if any(len(vector) != n2 for vector in h2_kernel_basis):
        failures.append({"kind": "bad-h2-kernel-vector-length"})
    if any(len(vector) != n2 for vector in h2_quotient_basis):
        failures.append({"kind": "bad-h2-quotient-vector-length"})
    return failures


def _matrix(rows: Sequence[Sequence[Any]]) -> list[list[int]]:
    return [[_int(value) for value in row] for row in rows]


def _int(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"expected int matrix entry, got {value!r}")
    return value


def _shape(matrix: Sequence[Sequence[int]]) -> list[int]:
    return [len(matrix), len(matrix[0]) if matrix else 0]


def _transpose(matrix: Sequence[Sequence[int]]) -> list[list[int]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def _columns(matrix: Sequence[Sequence[int]]) -> list[list[int]]:
    return _transpose(matrix)


def _matmul(left: Sequence[Sequence[int]], right: Sequence[Sequence[int]]) -> list[list[int]]:
    if not left:
        return []
    width = len(right[0]) if right else 0
    return [
        [
            sum(left[row][inner] * right[inner][col] for inner in range(len(right)))
            for col in range(width)
        ]
        for row in range(len(left))
    ]


def _matvec(matrix: Sequence[Sequence[int]], vector: Sequence[int]) -> list[int]:
    return [sum(row[col] * vector[col] for col in range(len(vector))) for row in matrix]


def _bilinear_matrix(q2: Sequence[Sequence[int]], basis: Sequence[Sequence[int]]) -> list[list[int]]:
    return [[_bilinear(q2, left, right) for right in basis] for left in basis]


def _bilinear(q2: Sequence[Sequence[int]], left: Sequence[int], right: Sequence[int]) -> int:
    return sum(
        left[i] * q2[i][j] * right[j]
        for i in range(len(q2))
        for j in range(len(q2))
    )


def _augmented_surgery_matrix(d2: Sequence[Sequence[int]], q2: Sequence[Sequence[int]]) -> list[list[int]]:
    n1 = len(d2)
    n2 = len(q2)
    rows: list[list[int]] = []
    for i in range(n1):
        rows.append([0 for _ in range(n1)] + list(d2[i]))
    for j in range(n2):
        rows.append([d2[i][j] for i in range(n1)] + list(q2[j]))
    return rows


def _relation_radical_checks(
    q2: Sequence[Sequence[int]],
    relations: Sequence[Sequence[int]],
    kernel_basis: Sequence[Sequence[int]],
) -> list[dict[str, Any]]:
    checks = []
    for index, relation in enumerate(relations):
        pairings = [_bilinear(q2, relation, vector) for vector in kernel_basis]
        checks.append(
            {
                "relation_index": index,
                "relation_vector": list(relation),
                "pairings_against_kernel_basis": pairings,
                "is_radical_on_kernel": all(pairing == 0 for pairing in pairings),
            }
        )
    return checks


def _z2_cohomology(
    d2: Sequence[Sequence[int]],
    d3: Sequence[Sequence[int]],
    quotient_basis: Sequence[Sequence[int]],
) -> dict[str, Any]:
    n2 = len(d3)
    all_cochains = [tuple((mask >> bit) & 1 for bit in range(n2)) for mask in range(1 << n2)]
    d3_columns = [tuple(entry % 2 for entry in column) for column in _columns(d3)]
    coboundary_generators = [tuple(entry % 2 for entry in row) for row in d2]
    coboundaries = sorted(_span_mod2(coboundary_generators, n2))
    cocycles = sorted(
        cochain
        for cochain in all_cochains
        if all(_dot_mod2(cochain, relation) == 0 for relation in d3_columns)
    )
    cocycle_set = set(cocycles)
    coboundaries_subset_cocycles = all(item in cocycle_set for item in coboundaries)
    seen: set[tuple[int, ...]] = set()
    quotient_representatives: list[dict[str, Any]] = []
    for cochain in cocycles:
        if cochain in seen:
            continue
        coset = sorted(_add_mod2(cochain, coboundary) for coboundary in coboundaries)
        seen.update(coset)
        representative = coset[0]
        quotient_representatives.append(
            {
                "representative": list(representative),
                "coset_size": len(coset),
                "values_on_h2_quotient_basis": [
                    _dot_mod2(representative, tuple(entry % 2 for entry in vector))
                    for vector in quotient_basis
                ],
            }
        )
    return {
        "coefficient_group": "Z/2",
        "interpretation": (
            "2-handle cochains alpha with d3^T alpha = 0, modulo d2^T "
            "one-handle coboundaries; representatives are lexicographic "
            "choices for bookkeeping, not canonical geometry"
        ),
        "cochain_count": len(all_cochains),
        "cocycle_count": len(cocycles),
        "coboundary_count": len(coboundaries),
        "coboundaries_subset_cocycles": coboundaries_subset_cocycles,
        "h2_character_count": len(quotient_representatives),
        "coboundary_generators": [list(item) for item in coboundary_generators],
        "coboundaries": [list(item) for item in coboundaries],
        "cocycle_representatives_before_quotient": [list(item) for item in cocycles],
        "cohomology_representatives": quotient_representatives,
    }


def _span_mod2(generators: Sequence[Sequence[int]], width: int) -> set[tuple[int, ...]]:
    subgroup = {tuple(0 for _ in range(width))}
    for generator in generators:
        gen = tuple(entry % 2 for entry in generator)
        subgroup |= {_add_mod2(item, gen) for item in tuple(subgroup)}
    return subgroup


def _add_mod2(left: Sequence[int], right: Sequence[int]) -> tuple[int, ...]:
    return tuple((left[index] + right[index]) % 2 for index in range(len(left)))


def _dot_mod2(left: Sequence[int], right: Sequence[int]) -> int:
    return sum(left[index] * right[index] for index in range(len(left))) % 2


def _standard_su2_2_control(form: Sequence[Sequence[int]]) -> dict[str, Any]:
    normalized = [list(row) for row in form]
    if normalized == [[1]]:
        return {
            "status": "recognized-local-control",
            "standard_form": "+1 framed Omega unknot",
            "claim_boundary": "ordinary local SU(2)_2 Omega control only",
            "value": _zeta_sparse([(0, 1), (3, 2), (8, 1)]),
        }
    if normalized == [[-1]]:
        return {
            "status": "recognized-local-control",
            "standard_form": "-1 framed Omega unknot",
            "claim_boundary": "ordinary local SU(2)_2 Omega control only",
            "value": _zeta_sparse([(0, 1), (8, 1), (13, 2)]),
        }
    if normalized == [[0, 1], [1, 0]]:
        return {
            "status": "recognized-local-control",
            "standard_form": "0-framed positive Hopf link with both components Omega colored",
            "claim_boundary": "ordinary local SU(2)_2 Omega Hopf control only",
            "value": _zeta_sparse([(0, 4)]),
        }
    return {
        "status": "not-recognized",
        "reason": "no hard-coded SU(2)_2 standard Omega control for this H2 form",
    }


def _su2_2_z2_twisted_standard_controls(
    form: Sequence[Sequence[int]],
    z2: Mapping[str, Any],
) -> dict[str, Any]:
    normalized = [list(row) for row in form]
    character_rows = list(z2["cohomology_representatives"])
    base: dict[str, Any] = {
        "category": "SU(2)_2",
        "coefficient_group": "Z/2",
        "mathematical_status": (
            "STANDARD_FORM_SU2_2_Z2_TWIST_CONTROLS_NOT_SPECIAL_DOTTED_RT_EVALUATION"
        ),
        "claim_boundary": {
            "not_closed_4d_invariant": True,
            "not_special_dotted_projector_implementation": True,
            "not_new_formula_claim": True,
            "purpose": (
                "baseline values for all H2 -> Z/2 characters after reducing "
                "the handle chain to its recognized ordinary H2 intersection form"
            ),
        },
        "character_count": len(character_rows),
    }

    def build(
        *,
        status: str,
        standard_form: str,
        value_for_bits: Any,
        extra: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        controls = []
        for item in character_rows:
            bits = list(item["values_on_h2_quotient_basis"])
            value = value_for_bits(bits)
            controls.append(
                {
                    "component_cochain_representative": list(item["representative"]),
                    "coset_size": item["coset_size"],
                    "h2_character_values_on_quotient_basis": bits,
                    "value": value,
                }
            )
        payload = dict(base)
        payload.update(
            {
                "status": status,
                "standard_form": standard_form,
                "controls": controls,
            }
        )
        if extra is not None:
            payload.update(dict(extra))
        return payload

    if normalized == [[1]]:
        return build(
            status="recognized-standard-form-control",
            standard_form="+1 framed Omega unknot",
            value_for_bits=lambda bits: _zeta_display(
                "-2*zeta16^3" if bits == [1] else "2*zeta16^3",
                [(3, -2)] if bits == [1] else [(3, 2)],
            ),
        )
    if normalized == [[-1]]:
        return build(
            status="recognized-standard-form-control",
            standard_form="-1 framed Omega unknot",
            value_for_bits=lambda bits: _zeta_display(
                "-2*zeta16^13" if bits == [1] else "2*zeta16^13",
                [(13, -2)] if bits == [1] else [(13, 2)],
            ),
        )
    if normalized == [[0, 1], [1, 0]]:
        return build(
            status="recognized-standard-form-control",
            standard_form="0-framed positive Hopf link with both components Omega_alpha colored",
            value_for_bits=lambda bits: _zeta_display("4", [(0, 4)]),
        )
    if normalized == [[0, 1], [1, 1]]:
        return build(
            status="recognized-by-integral-basis-change-standard-control",
            standard_form="odd rank-2 unimodular form, diagonalized as <+1> + <-1>",
            value_for_bits=lambda bits: _zeta_display(
                "-4" if bits and bits[0] == 1 else "4",
                [(0, -4)] if bits and bits[0] == 1 else [(0, 4)],
            ),
            extra={
                "basis_change": {
                    "old_basis_columns_for_diagonal_basis": [[0, 1], [1, -1]],
                    "diagonal_form": [[1, 0], [0, -1]],
                    "character_rule": (
                        "If alpha=(a,b) on the catalog quotient basis, then "
                        "the diagonal-basis signs multiply to (-1)^a."
                    ),
                }
            },
        )
    payload = dict(base)
    payload.update(
        {
            "status": "not-recognized",
            "reason": "no SU(2)_2/Z2 standard twist control is registered for this H2 form",
            "controls": [],
        }
    )
    return payload


def _zeta_display(display: str, entries: Sequence[tuple[int, int]]) -> dict[str, Any]:
    return {
        "display": display,
        "sparse_sum": _zeta_sparse(entries),
    }


def _zeta_sparse(entries: Sequence[tuple[int, int]]) -> dict[str, Any]:
    combined: dict[int, int] = {}
    for exponent, coefficient in entries:
        combined[exponent % 16] = combined.get(exponent % 16, 0) + coefficient
    return {
        "kind": "Z[zeta_16]_sparse_sum",
        "root_symbol": "zeta_16 = exp(2*pi*i/16)",
        "terms": [
            {"exponent": exponent, "integer_coefficient": coefficient}
            for exponent, coefficient in sorted(combined.items())
            if coefficient != 0
        ],
    }


def _counts(values: Sequence[str] | Any) -> dict[str, int]:
    counts: dict[str, int] = {}
    for value in values:
        counts[str(value)] = counts.get(str(value), 0) + 1
    return dict(sorted(counts.items()))
