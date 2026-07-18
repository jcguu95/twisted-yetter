"""Exact R9 cancellation, normalization, and H2 transport fixtures."""

from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from numbers import Integral
from typing import Any, Mapping, Sequence


SCHEMA = "twisted-yetter.kirby-cancellation.v1"
KINDS = ("one_two", "two_three", "empty_zero", "empty_four")
EXPECTED_KEYS = {
    "schema",
    "cancellation_id",
    "kind",
    "source_snapshot_hash",
    "target_snapshot_hash",
    "source_handle_counts",
    "target_handle_counts",
    "local_geometry",
    "local_evaluation",
    "normalization",
    "chain_transport",
    "source_proof",
    "claim_boundary",
    "content_hash",
}
COUNT_KEYS = {"h0", "h1", "h2", "h3", "h4"}


def canonical_hash(payload: Mapping[str, Any]) -> str:
    body = deepcopy(dict(payload))
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _sha256_payload(payload: Mapping[str, Any]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _is_sha256(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 71
        and value.startswith("sha256:")
        and all(char in "0123456789abcdef" for char in value[7:])
    )


def _as_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError(f"{name} must be an integer")
    return int(value)


def _counts(value: object, *, name: str) -> dict[str, int]:
    if not isinstance(value, dict) or set(value) != COUNT_KEYS:
        raise ValueError(f"{name} handle-count schema mismatch")
    result = {
        key: _as_int(value[key], name=f"{name}.{key}")
        for key in sorted(COUNT_KEYS)
    }
    if any(item < 0 for item in result.values()):
        raise ValueError(f"{name} handle counts must be nonnegative")
    return result


def _matrix(
    value: object, *, rows: int, cols: int, name: str
) -> tuple[tuple[int, ...], ...]:
    if not isinstance(value, list) or len(value) != rows:
        raise ValueError(f"{name} must have {rows} rows")
    matrix: list[tuple[int, ...]] = []
    for row in value:
        if not isinstance(row, list) or len(row) != cols:
            raise ValueError(f"{name} must have {cols} columns")
        matrix.append(
            tuple(_as_int(item, name=f"{name} entry") for item in row)
        )
    return tuple(matrix)


def _rows(matrix: Sequence[Sequence[int]]) -> list[list[int]]:
    return [list(row) for row in matrix]


def _matmul(
    left: Sequence[Sequence[int]],
    right: Sequence[Sequence[int]],
    *,
    right_cols: int,
) -> tuple[tuple[int, ...], ...]:
    if left and len(left[0]) != len(right):
        raise ValueError("matrix dimensions do not compose")
    return tuple(
        tuple(
            sum(left[row][inner] * right[inner][col] for inner in range(len(right)))
            for col in range(right_cols)
        )
        for row in range(len(left))
    )


def _matvec_mod2(
    matrix: Sequence[Sequence[int]], vector: Sequence[int]
) -> tuple[int, ...]:
    if matrix and len(matrix[0]) != len(vector):
        raise ValueError("matrix/vector dimensions do not compose")
    return tuple(
        sum(row[index] * vector[index] for index in range(len(vector))) % 2
        for row in matrix
    )


def _columns(
    matrix: Sequence[Sequence[int]], column_count: int
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(matrix[row][col] for row in range(len(matrix)))
        for col in range(column_count)
    )


def _all_bits(width: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple((bits >> index) & 1 for index in range(width))
        for bits in range(1 << width)
    )


def _add_mod2(
    left: Sequence[int], right: Sequence[int]
) -> tuple[int, ...]:
    return tuple(
        (left[index] + right[index]) % 2 for index in range(len(left))
    )


def _span_mod2(
    generators: Sequence[Sequence[int]], width: int
) -> set[tuple[int, ...]]:
    span: set[tuple[int, ...]] = {tuple(0 for _ in range(width))}
    for generator in generators:
        normalized = tuple(value % 2 for value in generator)
        span |= {
            _add_mod2(item, normalized)
            for item in tuple(span)
        }
    return span


def _pairing_mod2(left: Sequence[int], right: Sequence[int]) -> int:
    if len(left) != len(right):
        raise ValueError("pairing vectors must have equal length")
    return sum(left[index] * right[index] for index in range(len(left))) % 2


def _fraction_payload(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def _read_fraction(value: object, *, name: str) -> Fraction:
    if not isinstance(value, dict) or set(value) != {"numerator", "denominator"}:
        raise ValueError(f"{name} exact-rational schema mismatch")
    numerator = _as_int(value["numerator"], name=f"{name}.numerator")
    denominator = _as_int(value["denominator"], name=f"{name}.denominator")
    if denominator <= 0:
        raise ValueError(f"{name} denominator must be positive")
    result = Fraction(numerator, denominator)
    if _fraction_payload(result) != value:
        raise ValueError(f"{name} rational is not canonically reduced")
    return result


def _normalization_denominator(
    c_dimension: Fraction,
    d_dimension: Fraction,
    transparent_dimension: Fraction,
    counts: Mapping[str, int],
) -> Fraction:
    return (
        c_dimension ** (counts["h2"] - counts["h1"])
        * (d_dimension * transparent_dimension) ** counts["h1"]
    )


def _chain_snapshot_hash(
    counts: Mapping[str, int],
    chain: Mapping[str, Any],
    *,
    side: str,
) -> str:
    return _sha256_payload(
        {
            "counts": dict(sorted(counts.items())),
            "c1_ids": chain[f"{side}_c1_ids"],
            "c2_ids": chain[f"{side}_c2_ids"],
            "c3_ids": chain[f"{side}_c3_ids"],
            "d2": chain[f"{side}_d2"],
            "d3": chain[f"{side}_d3"],
        }
    )


def _validate_h2_side(
    *,
    c1_ids: Sequence[str],
    c2_ids: Sequence[str],
    c3_ids: Sequence[str],
    d2: Sequence[Sequence[int]],
    d3: Sequence[Sequence[int]],
    basis_representatives: object,
    expected_class_count: object,
    side: str,
) -> tuple[tuple[tuple[int, ...], ...], set[tuple[int, ...]]]:
    n2 = len(c2_ids)
    cycles = tuple(
        vector
        for vector in _all_bits(n2)
        if all(value == 0 for value in _matvec_mod2(d2, vector))
    )
    boundaries = _span_mod2(_columns(d3, len(c3_ids)), n2)
    if not boundaries.issubset(set(cycles)):
        raise ValueError(f"{side} chain does not satisfy im d3 subset ker d2")
    canonical_cosets = {
        min(_add_mod2(cycle, boundary) for boundary in boundaries)
        for cycle in cycles
    }
    if expected_class_count != len(canonical_cosets):
        raise ValueError(f"{side} H2 class denominator is stale")
    if not isinstance(basis_representatives, list):
        raise TypeError(f"{side} H2 basis must be a list")
    basis = tuple(
        tuple(_as_int(item, name=f"{side} H2 basis") % 2 for item in vector)
        for vector in basis_representatives
        if isinstance(vector, list) and len(vector) == n2
    )
    if len(basis) != len(basis_representatives):
        raise ValueError(f"{side} H2 basis shape mismatch")
    generated = _span_mod2(basis, n2)
    generated_cosets = {
        min(_add_mod2(vector, boundary) for boundary in boundaries)
        for vector in generated
    }
    if generated_cosets != canonical_cosets or len(generated) != len(
        canonical_cosets
    ):
        raise ValueError(f"{side} H2 basis does not freely enumerate the quotient")
    return basis, boundaries


def validate_cancellation_fixture(payload: Mapping[str, Any]) -> None:
    """Reject stale, incomplete, or scope-inflated R9 cancellation data."""

    if set(payload) != EXPECTED_KEYS:
        missing = sorted(EXPECTED_KEYS - set(payload))
        extra = sorted(set(payload) - EXPECTED_KEYS)
        raise ValueError(
            f"cancellation schema mismatch: missing={missing}, extra={extra}"
        )
    if payload["schema"] != SCHEMA:
        raise ValueError("unsupported cancellation schema")
    if payload["kind"] not in KINDS:
        raise ValueError("unsupported cancellation kind")
    kind = str(payload["kind"])
    if payload["content_hash"] != canonical_hash(payload):
        raise ValueError("stale cancellation content hash")
    if not isinstance(payload["cancellation_id"], str) or not payload[
        "cancellation_id"
    ]:
        raise ValueError("cancellation ID must be nonempty")

    source_counts = _counts(
        payload["source_handle_counts"], name="source"
    )
    target_counts = _counts(
        payload["target_handle_counts"], name="target"
    )
    expected_source = dict(target_counts)
    if kind == "one_two":
        expected_source["h1"] += 1
        expected_source["h2"] += 1
    elif kind == "two_three":
        expected_source["h2"] += 1
        expected_source["h3"] += 1
    elif kind == "empty_zero":
        expected_source["h0"] += 1
    else:
        expected_source["h4"] += 1
    if source_counts != expected_source:
        raise ValueError("source/target handle counts do not match cancellation kind")

    chain = payload["chain_transport"]
    required_chain_keys = {
        "source_c1_ids",
        "source_c2_ids",
        "source_c3_ids",
        "target_c1_ids",
        "target_c2_ids",
        "target_c3_ids",
        "source_d2",
        "source_d3",
        "target_d2",
        "target_d3",
        "removed_component_ids",
        "forward_ambient_c2_mod2",
        "inverse_ambient_c2_mod2",
        "source_h2_basis_representatives_mod2",
        "target_h2_basis_representatives_mod2",
        "forward_h2_coordinate_matrix_mod2",
        "inverse_h2_coordinate_matrix_mod2",
        "source_h2_class_count_mod2",
        "target_h2_class_count_mod2",
        "character_pairing_check",
    }
    if not isinstance(chain, dict) or set(chain) != required_chain_keys:
        raise ValueError("cancellation chain-transport schema mismatch")
    id_keys = (
        "source_c1_ids",
        "source_c2_ids",
        "source_c3_ids",
        "target_c1_ids",
        "target_c2_ids",
        "target_c3_ids",
        "removed_component_ids",
    )
    for key in id_keys:
        ids = chain[key]
        if (
            not isinstance(ids, list)
            or any(not isinstance(item, str) or not item for item in ids)
            or len(ids) != len(set(ids))
        ):
            raise ValueError(f"{key} must contain unique nonempty IDs")
    source_c1 = chain["source_c1_ids"]
    source_c2 = chain["source_c2_ids"]
    source_c3 = chain["source_c3_ids"]
    target_c1 = chain["target_c1_ids"]
    target_c2 = chain["target_c2_ids"]
    target_c3 = chain["target_c3_ids"]
    source_d2 = _matrix(
        chain["source_d2"],
        rows=len(source_c1),
        cols=len(source_c2),
        name="source d2",
    )
    source_d3 = _matrix(
        chain["source_d3"],
        rows=len(source_c2),
        cols=len(source_c3),
        name="source d3",
    )
    target_d2 = _matrix(
        chain["target_d2"],
        rows=len(target_c1),
        cols=len(target_c2),
        name="target d2",
    )
    target_d3 = _matrix(
        chain["target_d3"],
        rows=len(target_c2),
        cols=len(target_c3),
        name="target d3",
    )
    if any(
        value != 0
        for row in _matmul(
            source_d2, source_d3, right_cols=len(source_c3)
        )
        for value in row
    ):
        raise ValueError("source d2*d3 is nonzero")
    if any(
        value != 0
        for row in _matmul(
            target_d2, target_d3, right_cols=len(target_c3)
        )
        for value in row
    ):
        raise ValueError("target d2*d3 is nonzero")

    if kind == "one_two":
        if len(chain["removed_component_ids"]) != 2:
            raise ValueError("1-2 cancellation must remove exactly two handles")
        removed = set(chain["removed_component_ids"])
        if not (
            len(source_c1) == len(target_c1) + 1
            and len(source_c2) == len(target_c2) + 1
            and set(target_c1).issubset(source_c1)
            and set(target_c2).issubset(source_c2)
            and removed == (
                (set(source_c1) - set(target_c1))
                | (set(source_c2) - set(target_c2))
            )
        ):
            raise ValueError("1-2 cancellation component removal is inconsistent")
    elif kind == "two_three":
        removed = set(chain["removed_component_ids"])
        if not (
            len(source_c2) == len(target_c2) + 1
            and len(source_c3) == len(target_c3) + 1
            and removed == (
                (set(source_c2) - set(target_c2))
                | (set(source_c3) - set(target_c3))
            )
        ):
            raise ValueError("2-3 cancellation component removal is inconsistent")
    elif chain["removed_component_ids"]:
        raise ValueError("empty 0/4 bookkeeping cannot remove link components")

    source_basis, source_boundaries = _validate_h2_side(
        c1_ids=source_c1,
        c2_ids=source_c2,
        c3_ids=source_c3,
        d2=source_d2,
        d3=source_d3,
        basis_representatives=chain[
            "source_h2_basis_representatives_mod2"
        ],
        expected_class_count=chain["source_h2_class_count_mod2"],
        side="source",
    )
    target_basis, target_boundaries = _validate_h2_side(
        c1_ids=target_c1,
        c2_ids=target_c2,
        c3_ids=target_c3,
        d2=target_d2,
        d3=target_d3,
        basis_representatives=chain[
            "target_h2_basis_representatives_mod2"
        ],
        expected_class_count=chain["target_h2_class_count_mod2"],
        side="target",
    )
    if chain["source_h2_class_count_mod2"] != chain[
        "target_h2_class_count_mod2"
    ]:
        raise ValueError("cancellation changed the H2 denominator")
    source_rank = len(source_basis)
    target_rank = len(target_basis)
    if source_rank != target_rank:
        raise ValueError("cancellation changed H2 rank")
    forward_ambient = _matrix(
        chain["forward_ambient_c2_mod2"],
        rows=len(target_c2),
        cols=len(source_c2),
        name="forward ambient C2",
    )
    inverse_ambient = _matrix(
        chain["inverse_ambient_c2_mod2"],
        rows=len(source_c2),
        cols=len(target_c2),
        name="inverse ambient C2",
    )
    forward_h2 = _matrix(
        chain["forward_h2_coordinate_matrix_mod2"],
        rows=target_rank,
        cols=source_rank,
        name="forward H2 coordinates",
    )
    inverse_h2 = _matrix(
        chain["inverse_h2_coordinate_matrix_mod2"],
        rows=source_rank,
        cols=target_rank,
        name="inverse H2 coordinates",
    )
    identity_source = tuple(
        tuple(1 if row == col else 0 for col in range(source_rank))
        for row in range(source_rank)
    )
    identity_target = tuple(
        tuple(1 if row == col else 0 for col in range(target_rank))
        for row in range(target_rank)
    )
    if tuple(
        tuple(value % 2 for value in row)
        for row in _matmul(
            inverse_h2, forward_h2, right_cols=source_rank
        )
    ) != identity_source:
        raise ValueError("H2 coordinate inverse is wrong on the source")
    if tuple(
        tuple(value % 2 for value in row)
        for row in _matmul(
            forward_h2, inverse_h2, right_cols=target_rank
        )
    ) != identity_target:
        raise ValueError("H2 coordinate inverse is wrong on the target")

    for source_coordinate in _all_bits(source_rank):
        source_vector = tuple(0 for _ in source_c2)
        for index, bit in enumerate(source_coordinate):
            if bit:
                source_vector = _add_mod2(source_vector, source_basis[index])
        target_vector = _matvec_mod2(forward_ambient, source_vector)
        target_coordinate = _matvec_mod2(forward_h2, source_coordinate)
        expected_target = tuple(0 for _ in target_c2)
        for index, bit in enumerate(target_coordinate):
            if bit:
                expected_target = _add_mod2(
                    expected_target, target_basis[index]
                )
        if _add_mod2(target_vector, expected_target) not in target_boundaries:
            raise ValueError("ambient cancellation map disagrees with H2 coordinates")
        recovered = _matvec_mod2(inverse_ambient, target_vector)
        if _add_mod2(recovered, source_vector) not in source_boundaries:
            raise ValueError("ambient inverse fails modulo cancellation boundaries")
        for source_character in _all_bits(source_rank):
            # If target coordinates are F*x, the target dual coordinates are
            # (F^-1)^T*chi.  Tiny fixture matrices are multiplied explicitly.
            target_character = tuple(
                sum(
                    inverse_h2[source_index][target_index]
                    * source_character[source_index]
                    for source_index in range(source_rank)
                )
                % 2
                for target_index in range(target_rank)
            )
            if _pairing_mod2(
                target_character, target_coordinate
            ) != _pairing_mod2(source_character, source_coordinate):
                raise ValueError("cancellation changed H2 character pairing")
    if chain["character_pairing_check"] != (
        "PASS_EXHAUSTIVE_H2_CLASSES_AND_CHARACTERS_MOD2"
    ):
        raise ValueError("character pairing check was not admitted")

    local_geometry = payload["local_geometry"]
    local_evaluation = payload["local_evaluation"]
    if not isinstance(local_geometry, dict) or not isinstance(
        local_evaluation, dict
    ):
        raise TypeError("local cancellation data must be objects")
    if local_evaluation.get("normalized_equality_supplied_as_input") is not False:
        raise ValueError("final normalized equality may not be supplied as input")
    if kind == "one_two":
        required_geometry = {
            "isolated_from_rest": True,
            "two_handle_may_be_knotted": True,
            "linked_to_other_handles": False,
        }
        if local_geometry != required_geometry:
            raise ValueError("1-2 local geometry is not the isolated source case")
        required_evaluation = {
            "disjoint_union_multiplicativity": "PASS",
            "cutting_identity": "PASS",
            "killing_identity": "PASS",
            "transparent_twist_trivial": "PASS",
            "raw_factor": "d(D) * d(transparent(F(Omega_C)))",
            "normalized_equality_supplied_as_input": False,
        }
        if local_evaluation != required_evaluation:
            raise ValueError("1-2 graphical inputs are incomplete")
    elif kind == "two_three":
        required_geometry = {
            "unlinked": True,
            "unknotted": True,
            "zero_framed": True,
        }
        if local_geometry != required_geometry:
            raise ValueError("2-3 local geometry is not the source case")
        required_evaluation = {
            "disjoint_union_multiplicativity": "PASS",
            "pivotal_dimension_preserved": "PASS",
            "raw_factor": "d(C)",
            "normalized_equality_supplied_as_input": False,
        }
        if local_evaluation != required_evaluation:
            raise ValueError("2-3 pivotal graphical inputs are incomplete")
    else:
        if local_geometry != {
            "link_diagram_unchanged": True,
            "normalization_uses_only_h1_h2": True,
        }:
            raise ValueError("empty 0/4 geometry bookkeeping is wrong")
        if local_evaluation != {
            "raw_factor": "1",
            "normalized_equality_supplied_as_input": False,
        }:
            raise ValueError("empty 0/4 local evaluation is wrong")

    normalization = payload["normalization"]
    if not isinstance(normalization, dict) or set(normalization) != {
        "formula",
        "c_dimension",
        "d_dimension",
        "transparent_dimension",
        "source_denominator",
        "target_denominator",
        "source_raw_numerator",
        "target_raw_numerator",
        "source_normalized_value",
        "target_normalized_value",
        "recurrence_check",
    }:
        raise ValueError("normalization schema mismatch")
    if normalization["formula"] != (
        "d(C)^(h2-h1) * (d(D)*d(transparent(F(Omega_C))))^h1"
    ):
        raise ValueError("normalization formula changed")
    c_dimension = _read_fraction(
        normalization["c_dimension"], name="c dimension"
    )
    d_dimension = _read_fraction(
        normalization["d_dimension"], name="d dimension"
    )
    transparent_dimension = _read_fraction(
        normalization["transparent_dimension"],
        name="transparent dimension",
    )
    if 0 in (c_dimension, d_dimension, transparent_dimension):
        raise ValueError("global dimensions must be nonzero")
    source_denominator = _normalization_denominator(
        c_dimension, d_dimension, transparent_dimension, source_counts
    )
    target_denominator = _normalization_denominator(
        c_dimension, d_dimension, transparent_dimension, target_counts
    )
    if _read_fraction(
        normalization["source_denominator"], name="source denominator"
    ) != source_denominator:
        raise ValueError("source normalization denominator is wrong")
    if _read_fraction(
        normalization["target_denominator"], name="target denominator"
    ) != target_denominator:
        raise ValueError("target normalization denominator is wrong")
    source_raw = _read_fraction(
        normalization["source_raw_numerator"], name="source raw numerator"
    )
    target_raw = _read_fraction(
        normalization["target_raw_numerator"], name="target raw numerator"
    )
    expected_factor = (
        d_dimension * transparent_dimension
        if kind == "one_two"
        else c_dimension
        if kind == "two_three"
        else Fraction(1)
    )
    if source_raw != expected_factor * target_raw:
        raise ValueError("raw cancellation factor is wrong")
    source_normalized = source_raw / source_denominator
    target_normalized = target_raw / target_denominator
    if _read_fraction(
        normalization["source_normalized_value"],
        name="source normalized value",
    ) != source_normalized:
        raise ValueError("source normalized value is stale")
    if _read_fraction(
        normalization["target_normalized_value"],
        name="target normalized value",
    ) != target_normalized:
        raise ValueError("target normalized value is stale")
    if source_normalized != target_normalized:
        raise ValueError("normalized cancellation values do not agree")
    expected_recurrence = {
        "one_two": "PASS_DENOMINATOR_MULTIPLIES_BY_DD_TIMES_TRANSPARENT",
        "two_three": "PASS_DENOMINATOR_MULTIPLIES_BY_DC",
        "empty_zero": "PASS_DENOMINATOR_UNCHANGED",
        "empty_four": "PASS_DENOMINATOR_UNCHANGED",
    }[kind]
    if normalization["recurrence_check"] != expected_recurrence:
        raise ValueError("normalization recurrence check is stale")

    source_proof = payload["source_proof"]
    if not isinstance(source_proof, dict) or set(source_proof) != {
        "lean_module",
        "lean_theorem",
        "source_ref",
        "source_locator",
        "pivotality_failure_locator",
    }:
        raise ValueError("cancellation source-proof schema mismatch")
    if source_proof["lean_module"] != (
        "TwistedYetter.Kirby.KirbyCancellation"
    ):
        raise ValueError("wrong cancellation Lean module")
    expected_theorem = {
        "one_two": "OneTwoLocalCalculation.normalized_sound",
        "two_three": "TwoThreeLocalCalculation.normalized_sound",
        "empty_zero": "GlobalDimensionProfile.denominator_addEmptyZero",
        "empty_four": "GlobalDimensionProfile.denominator_addEmptyFour",
    }[kind]
    if source_proof["lean_theorem"] != expected_theorem:
        raise ValueError("wrong cancellation Lean theorem")
    if source_proof["source_ref"] != "ref:baerenz-barrett-dichromatic-2018":
        raise ValueError("cancellation source reference changed")
    if "Remark 3.11" not in source_proof["pivotality_failure_locator"]:
        raise ValueError("pivotality failure warning was dropped")

    if payload["source_snapshot_hash"] != _chain_snapshot_hash(
        source_counts, chain, side="source"
    ):
        raise ValueError("source cancellation snapshot hash is stale")
    if payload["target_snapshot_hash"] != _chain_snapshot_hash(
        target_counts, chain, side="target"
    ):
        raise ValueError("target cancellation snapshot hash is stale")
    if payload["claim_boundary"] != (
        "NORMALIZED_INVARIANCE_IS_LEAN_DERIVED_FROM_EXPLICIT_LOCAL_IDENTITIES;"
        "KIRBY_COMPLETENESS_AND_FOUR_MANIFOLD_INVARIANCE_NOT_CLAIMED"
    ):
        raise ValueError("cancellation claim boundary changed")


def _base_chain() -> dict[str, Any]:
    return {
        "source_c1_ids": [],
        "source_c2_ids": ["persistent-h2"],
        "source_c3_ids": [],
        "target_c1_ids": [],
        "target_c2_ids": ["persistent-h2"],
        "target_c3_ids": [],
        "source_d2": [],
        "source_d3": [[]],
        "target_d2": [],
        "target_d3": [[]],
        "removed_component_ids": [],
        "forward_ambient_c2_mod2": [[1]],
        "inverse_ambient_c2_mod2": [[1]],
        "source_h2_basis_representatives_mod2": [[1]],
        "target_h2_basis_representatives_mod2": [[1]],
        "forward_h2_coordinate_matrix_mod2": [[1]],
        "inverse_h2_coordinate_matrix_mod2": [[1]],
        "source_h2_class_count_mod2": 2,
        "target_h2_class_count_mod2": 2,
        "character_pairing_check": (
            "PASS_EXHAUSTIVE_H2_CLASSES_AND_CHARACTERS_MOD2"
        ),
    }


def build_cancellation_fixture(kind: str) -> dict[str, Any]:
    """Build one deterministic terminal R9 fixture."""

    if kind not in KINDS:
        raise ValueError("unsupported cancellation kind")
    target_counts = {"h0": 1, "h1": 0, "h2": 1, "h3": 0, "h4": 1}
    source_counts = dict(target_counts)
    chain = _base_chain()
    if kind == "one_two":
        source_counts["h1"] += 1
        source_counts["h2"] += 1
        chain.update(
            {
                "source_c1_ids": ["cancel-h1"],
                "source_c2_ids": ["cancel-h2", "persistent-h2"],
                "source_d2": [[1, 0]],
                "source_d3": [[], []],
                "removed_component_ids": ["cancel-h1", "cancel-h2"],
                "forward_ambient_c2_mod2": [[0, 1]],
                "inverse_ambient_c2_mod2": [[0], [1]],
                "source_h2_basis_representatives_mod2": [[0, 1]],
            }
        )
        local_geometry = {
            "isolated_from_rest": True,
            "two_handle_may_be_knotted": True,
            "linked_to_other_handles": False,
        }
        local_evaluation = {
            "disjoint_union_multiplicativity": "PASS",
            "cutting_identity": "PASS",
            "killing_identity": "PASS",
            "transparent_twist_trivial": "PASS",
            "raw_factor": "d(D) * d(transparent(F(Omega_C)))",
            "normalized_equality_supplied_as_input": False,
        }
    elif kind == "two_three":
        source_counts["h2"] += 1
        source_counts["h3"] += 1
        chain.update(
            {
                "source_c2_ids": ["cancel-h2", "persistent-h2"],
                "source_c3_ids": ["cancel-h3"],
                "source_d2": [],
                "source_d3": [[1], [0]],
                "removed_component_ids": ["cancel-h2", "cancel-h3"],
                "forward_ambient_c2_mod2": [[0, 1]],
                "inverse_ambient_c2_mod2": [[0], [1]],
                "source_h2_basis_representatives_mod2": [[0, 1]],
            }
        )
        local_geometry = {
            "unlinked": True,
            "unknotted": True,
            "zero_framed": True,
        }
        local_evaluation = {
            "disjoint_union_multiplicativity": "PASS",
            "pivotal_dimension_preserved": "PASS",
            "raw_factor": "d(C)",
            "normalized_equality_supplied_as_input": False,
        }
    else:
        source_counts["h0" if kind == "empty_zero" else "h4"] += 1
        local_geometry = {
            "link_diagram_unchanged": True,
            "normalization_uses_only_h1_h2": True,
        }
        local_evaluation = {
            "raw_factor": "1",
            "normalized_equality_supplied_as_input": False,
        }

    c_dimension = Fraction(5)
    d_dimension = Fraction(7)
    transparent_dimension = Fraction(3)
    target_raw = Fraction(11)
    factor = (
        d_dimension * transparent_dimension
        if kind == "one_two"
        else c_dimension
        if kind == "two_three"
        else Fraction(1)
    )
    source_raw = factor * target_raw
    source_denominator = _normalization_denominator(
        c_dimension, d_dimension, transparent_dimension, source_counts
    )
    target_denominator = _normalization_denominator(
        c_dimension, d_dimension, transparent_dimension, target_counts
    )
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "cancellation_id": f"r9-{kind}-fixture",
        "kind": kind,
        "source_snapshot_hash": _chain_snapshot_hash(
            source_counts, chain, side="source"
        ),
        "target_snapshot_hash": _chain_snapshot_hash(
            target_counts, chain, side="target"
        ),
        "source_handle_counts": source_counts,
        "target_handle_counts": target_counts,
        "local_geometry": local_geometry,
        "local_evaluation": local_evaluation,
        "normalization": {
            "formula": (
                "d(C)^(h2-h1) * "
                "(d(D)*d(transparent(F(Omega_C))))^h1"
            ),
            "c_dimension": _fraction_payload(c_dimension),
            "d_dimension": _fraction_payload(d_dimension),
            "transparent_dimension": _fraction_payload(
                transparent_dimension
            ),
            "source_denominator": _fraction_payload(source_denominator),
            "target_denominator": _fraction_payload(target_denominator),
            "source_raw_numerator": _fraction_payload(source_raw),
            "target_raw_numerator": _fraction_payload(target_raw),
            "source_normalized_value": _fraction_payload(
                source_raw / source_denominator
            ),
            "target_normalized_value": _fraction_payload(
                target_raw / target_denominator
            ),
            "recurrence_check": {
                "one_two": (
                    "PASS_DENOMINATOR_MULTIPLIES_BY_DD_TIMES_TRANSPARENT"
                ),
                "two_three": "PASS_DENOMINATOR_MULTIPLIES_BY_DC",
                "empty_zero": "PASS_DENOMINATOR_UNCHANGED",
                "empty_four": "PASS_DENOMINATOR_UNCHANGED",
            }[kind],
        },
        "chain_transport": chain,
        "source_proof": {
            "lean_module": "TwistedYetter.Kirby.KirbyCancellation",
            "lean_theorem": {
                "one_two": "OneTwoLocalCalculation.normalized_sound",
                "two_three": "TwoThreeLocalCalculation.normalized_sound",
                "empty_zero": (
                    "GlobalDimensionProfile.denominator_addEmptyZero"
                ),
                "empty_four": (
                    "GlobalDimensionProfile.denominator_addEmptyFour"
                ),
            }[kind],
            "source_ref": "ref:baerenz-barrett-dichromatic-2018",
            "source_locator": (
                "Definition 3.6, Lemma 3.8, Theorem 3.9, equations "
                "(3.2.1), (3.3.1), (3.3.2), journal pages 685-687"
            ),
            "pivotality_failure_locator": (
                "Remark 3.11, journal page 687"
            ),
        },
        "claim_boundary": (
            "NORMALIZED_INVARIANCE_IS_LEAN_DERIVED_FROM_EXPLICIT_LOCAL_IDENTITIES;"
            "KIRBY_COMPLETENESS_AND_FOUR_MANIFOLD_INVARIANCE_NOT_CLAIMED"
        ),
    }
    payload["content_hash"] = canonical_hash(payload)
    validate_cancellation_fixture(payload)
    return payload


def all_cancellation_fixtures() -> tuple[dict[str, Any], ...]:
    return tuple(build_cancellation_fixture(kind) for kind in KINDS)


__all__ = [
    "KINDS",
    "SCHEMA",
    "all_cancellation_fixtures",
    "build_cancellation_fixture",
    "canonical_hash",
    "validate_cancellation_fixture",
]
