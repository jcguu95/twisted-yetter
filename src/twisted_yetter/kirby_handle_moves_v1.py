"""Fail-closed bookkeeping certificates for the three Kirby slide families.

The graphical evaluator equalities live in Lean.  This module checks the
separate handle-chain, framing, component-lineage, and mod-2
class/character-coordinate data.  In particular, it never promotes a linking
matrix congruence into a link-diagram proof.
"""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from numbers import Integral
from typing import Any, Mapping, Sequence

from twisted_yetter.presentation_moves import inverse_unimodular


SCHEMA = "twisted-yetter.kirby-handle-slide-bookkeeping.v1"
KINDS = ("one_over_one", "two_over_one", "two_over_two")
ROLE_PAIRS = {
    "one_over_one": ("dotted", "dotted"),
    "two_over_one": ("ordinary", "dotted"),
    "two_over_two": ("ordinary", "ordinary"),
}
GRAPHICAL_ROUTES = {
    "one_over_one": "BB_LEMMA_3_1_ORIGINAL_SLIDING",
    "two_over_one": "BB_LEMMA_3_1_ORIGINAL_SLIDING",
    "two_over_two": "R5_LEMMA_3_3_3_4_DERIVED_MOVIE",
}
EXPECTED_KEYS = {
    "schema",
    "move_id",
    "kind",
    "orientation_sign",
    "source_snapshot_hash",
    "target_snapshot_hash",
    "components",
    "handle_chain",
    "framing",
    "homological_transport",
    "graphical_proof",
    "claim_boundary",
    "content_hash",
}


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


def _as_int(value: object) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError("matrix entries must be integers")
    return int(value)


def _matrix(rows: object, *, name: str) -> tuple[tuple[int, ...], ...]:
    if not isinstance(rows, list):
        raise TypeError(f"{name} must be a JSON matrix")
    matrix = tuple(
        tuple(_as_int(value) for value in row)
        for row in rows
        if isinstance(row, list)
    )
    if len(matrix) != len(rows):
        raise TypeError(f"{name} rows must be JSON arrays")
    if matrix and any(len(row) != len(matrix[0]) for row in matrix):
        raise ValueError(f"{name} must be rectangular")
    return matrix


def _identity(size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(1 if row == col else 0 for col in range(size))
        for row in range(size)
    )


def _transpose(
    matrix: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], ...]:
    if not matrix:
        return ()
    return tuple(
        tuple(matrix[row][col] for row in range(len(matrix)))
        for col in range(len(matrix[0]))
    )


def _matmul(
    left: Sequence[Sequence[int]], right: Sequence[Sequence[int]]
) -> tuple[tuple[int, ...], ...]:
    if not left:
        return ()
    if not right:
        if len(left[0]) != 0:
            raise ValueError("matrix dimensions do not compose")
        return tuple(() for _ in left)
    if len(left[0]) != len(right):
        raise ValueError("matrix dimensions do not compose")
    return tuple(
        tuple(
            sum(left[row][inner] * right[inner][col] for inner in range(len(right)))
            for col in range(len(right[0]))
        )
        for row in range(len(left))
    )


def _matvec_mod2(
    matrix: Sequence[Sequence[int]], vector: Sequence[int]
) -> tuple[int, ...]:
    if matrix and len(matrix[0]) != len(vector):
        raise ValueError("matrix/vector dimensions do not compose")
    return tuple(
        sum(row[col] * vector[col] for col in range(len(vector))) % 2
        for row in matrix
    )


def _mod2(matrix: Sequence[Sequence[int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(value % 2 for value in row) for row in matrix)


def _rows(matrix: Sequence[Sequence[int]]) -> list[list[int]]:
    return [list(row) for row in matrix]


def _all_bits(width: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple((bits >> index) & 1 for index in range(width))
        for bits in range(1 << width)
    )


def _pairing_mod2(left: Sequence[int], right: Sequence[int]) -> int:
    if len(left) != len(right):
        raise ValueError("pairing vectors must have equal length")
    return sum(left[index] * right[index] for index in range(len(left))) % 2


def _elementary_basis(
    size: int, sliding: int, stationary: int, sign: int
) -> tuple[tuple[int, ...], ...]:
    basis = [list(row) for row in _identity(size)]
    basis[stationary][sliding] += sign
    return tuple(tuple(row) for row in basis)


def _chain_state_hash(
    *,
    one_handle_ids: Sequence[str],
    two_handle_ids: Sequence[str],
    d2: Sequence[Sequence[int]],
    q2: Sequence[Sequence[int]] | None,
) -> str:
    return _sha256_payload(
        {
            "one_handle_ids": list(one_handle_ids),
            "two_handle_ids": list(two_handle_ids),
            "d2_c2_to_c1": _rows(d2),
            "q2_linking_matrix": None if q2 is None else _rows(q2),
        }
    )


def validate_handle_slide_bookkeeping(payload: Mapping[str, Any]) -> None:
    """Reject any malformed, stale, or mathematically inconsistent payload."""

    if set(payload) != EXPECTED_KEYS:
        missing = sorted(EXPECTED_KEYS - set(payload))
        extra = sorted(set(payload) - EXPECTED_KEYS)
        raise ValueError(f"handle-slide schema mismatch: missing={missing}, extra={extra}")
    if payload["schema"] != SCHEMA:
        raise ValueError("unsupported handle-slide schema")
    if payload["kind"] not in KINDS:
        raise ValueError("unsupported handle-slide kind")
    kind = str(payload["kind"])
    sign = payload["orientation_sign"]
    if sign not in (-1, 1) or isinstance(sign, bool):
        raise ValueError("orientation sign must be exactly +1 or -1")
    if not isinstance(payload["move_id"], str) or not payload["move_id"]:
        raise ValueError("move ID must be nonempty")
    if payload["content_hash"] != canonical_hash(payload):
        raise ValueError("stale handle-slide content hash")

    components = payload["components"]
    if not isinstance(components, dict):
        raise TypeError("components must be an object")
    required_component_keys = {
        "sliding_id",
        "stationary_id",
        "sliding_role",
        "stationary_role",
        "source_one_handle_ids",
        "source_two_handle_ids",
        "target_one_handle_ids",
        "target_two_handle_ids",
        "lineage",
    }
    if set(components) != required_component_keys:
        raise ValueError("component-lineage schema mismatch")
    sliding_id = components["sliding_id"]
    stationary_id = components["stationary_id"]
    if (
        not isinstance(sliding_id, str)
        or not isinstance(stationary_id, str)
        or not sliding_id
        or not stationary_id
        or sliding_id == stationary_id
    ):
        raise ValueError("slide component IDs must be nonempty and distinct")
    expected_roles = ROLE_PAIRS[kind]
    observed_roles = (
        components["sliding_role"],
        components["stationary_role"],
    )
    if observed_roles != expected_roles:
        raise ValueError("component roles do not match the slide kind")
    source_one_ids = components["source_one_handle_ids"]
    source_two_ids = components["source_two_handle_ids"]
    target_one_ids = components["target_one_handle_ids"]
    target_two_ids = components["target_two_handle_ids"]
    if not all(
        isinstance(ids, list)
        and all(isinstance(item, str) and item for item in ids)
        and len(ids) == len(set(ids))
        for ids in (source_one_ids, source_two_ids, target_one_ids, target_two_ids)
    ):
        raise ValueError("handle IDs must be unique nonempty strings")
    if source_one_ids != target_one_ids or source_two_ids != target_two_ids:
        raise ValueError("handle-slide component lineage changed stable IDs")
    all_ids = source_one_ids + source_two_ids
    if set(components["lineage"].keys()) != set(all_ids):
        raise ValueError("component lineage does not cover every handle")
    if any(components["lineage"][item] != item for item in all_ids):
        raise ValueError("handle-slide lineage must preserve stable component IDs")
    if kind == "one_over_one":
        if sliding_id not in source_one_ids or stationary_id not in source_one_ids:
            raise ValueError("one-over-one participants must both be one-handles")
    elif kind == "two_over_one":
        if sliding_id not in source_two_ids or stationary_id not in source_one_ids:
            raise ValueError("two-over-one participants have wrong handle indices")
    elif sliding_id not in source_two_ids or stationary_id not in source_two_ids:
        raise ValueError("two-over-two participants must both be two-handles")

    chain = payload["handle_chain"]
    if not isinstance(chain, dict) or set(chain) != {
        "source_d2_c2_to_c1",
        "target_d2_c2_to_c1",
        "c1_basis_matrix",
        "c1_inverse_basis_matrix",
        "c2_basis_matrix",
        "c2_inverse_basis_matrix",
        "source_q2_linking_matrix",
        "target_q2_linking_matrix",
        "equation",
    }:
        raise ValueError("handle-chain schema mismatch")
    source_d2 = _matrix(chain["source_d2_c2_to_c1"], name="source d2")
    target_d2 = _matrix(chain["target_d2_c2_to_c1"], name="target d2")
    n1 = len(source_one_ids)
    n2 = len(source_two_ids)
    if len(source_d2) != n1 or (n1 and len(source_d2[0]) != n2):
        raise ValueError("source d2 shape does not match handle counts")
    if len(target_d2) != n1 or (n1 and len(target_d2[0]) != n2):
        raise ValueError("target d2 shape does not match handle counts")
    p1 = _matrix(chain["c1_basis_matrix"], name="C1 basis")
    p1_inv = _matrix(chain["c1_inverse_basis_matrix"], name="C1 inverse")
    p2 = _matrix(chain["c2_basis_matrix"], name="C2 basis")
    p2_inv = _matrix(chain["c2_inverse_basis_matrix"], name="C2 inverse")
    if p1 != tuple(tuple(row) for row in p1) or len(p1) != n1:
        raise ValueError("C1 basis shape mismatch")
    if p2 != tuple(tuple(row) for row in p2) or len(p2) != n2:
        raise ValueError("C2 basis shape mismatch")
    if p1_inv != inverse_unimodular(p1):
        raise ValueError("C1 inverse basis matrix is stale")
    if p2_inv != inverse_unimodular(p2):
        raise ValueError("C2 inverse basis matrix is stale")

    if kind == "one_over_one":
        sliding = source_one_ids.index(sliding_id)
        stationary = source_one_ids.index(stationary_id)
        expected_p1 = _elementary_basis(n1, sliding, stationary, int(sign))
        expected_p2 = _identity(n2)
    elif kind == "two_over_one":
        expected_p1 = _identity(n1)
        expected_p2 = _identity(n2)
    else:
        sliding = source_two_ids.index(sliding_id)
        stationary = source_two_ids.index(stationary_id)
        expected_p1 = _identity(n1)
        expected_p2 = _elementary_basis(n2, sliding, stationary, int(sign))
    if p1 != expected_p1 or p2 != expected_p2:
        raise ValueError("basis matrices do not match the oriented slide kind")

    expected_d2 = _matmul(_matmul(p1_inv, source_d2), p2)
    if target_d2 != expected_d2:
        raise ValueError("target d2 is not P1^-1 * d2 * P2")
    if chain["equation"] != "d2_target = P1^-1 * d2_source * P2":
        raise ValueError("handle-chain convention string changed")

    source_q_raw = chain["source_q2_linking_matrix"]
    target_q_raw = chain["target_q2_linking_matrix"]
    if kind == "two_over_two":
        source_q = _matrix(source_q_raw, name="source q2")
        target_q = _matrix(target_q_raw, name="target q2")
        if len(source_q) != n2 or any(len(row) != n2 for row in source_q):
            raise ValueError("source q2 shape mismatch")
        if source_q != _transpose(source_q):
            raise ValueError("source q2 must be symmetric")
        expected_q = _matmul(_matmul(_transpose(p2), source_q), p2)
        if target_q != expected_q:
            raise ValueError("target q2 is not P2^T * q2 * P2")
    elif source_q_raw is not None or target_q_raw is not None:
        raise ValueError("only two-over-two may claim a linking-matrix congruence")

    framing = payload["framing"]
    if not isinstance(framing, dict) or "mode" not in framing:
        raise ValueError("framing bookkeeping is missing")
    if kind == "one_over_one":
        if framing != {"mode": "NOT_APPLICABLE_TO_DOTTED_ONE_HANDLE"}:
            raise ValueError("one-over-one cannot carry integer framing arithmetic")
    elif kind == "two_over_one":
        if set(framing) != {
            "mode",
            "source_sliding_framing",
            "target_sliding_framing",
            "diagram_tracking_witness_hash",
        }:
            raise ValueError("two-over-one framing schema mismatch")
        if framing["mode"] != "PINNED_BY_TYPED_DIAGRAM_NOT_Q_CONGRUENCE":
            raise ValueError("two-over-one framing scope is unsafe")
        if not _is_sha256(framing["diagram_tracking_witness_hash"]):
            raise ValueError("two-over-one framing witness must be hash-bound")
        _as_int(framing["source_sliding_framing"])
        _as_int(framing["target_sliding_framing"])
    else:
        if set(framing) != {
            "mode",
            "source_sliding_framing",
            "stationary_framing",
            "mutual_linking",
            "target_sliding_framing",
            "formula",
        }:
            raise ValueError("two-over-two framing schema mismatch")
        source_q = _matrix(source_q_raw, name="source q2")
        target_q = _matrix(target_q_raw, name="target q2")
        sliding = source_two_ids.index(sliding_id)
        stationary = source_two_ids.index(stationary_id)
        expected_values = (
            source_q[sliding][sliding],
            source_q[stationary][stationary],
            source_q[sliding][stationary],
            target_q[sliding][sliding],
        )
        observed_values = tuple(
            _as_int(framing[key])
            for key in (
                "source_sliding_framing",
                "stationary_framing",
                "mutual_linking",
                "target_sliding_framing",
            )
        )
        if observed_values != expected_values:
            raise ValueError("framing values do not match the linking matrices")
        if framing["mode"] != "DERIVED_FROM_Q_PRIME_EQUALS_PT_Q_P":
            raise ValueError("two-over-two framing mode changed")
        if framing["formula"] != "f_i' = f_i + 2*sign*lk(i,j) + f_j":
            raise ValueError("framing convention string changed")
        expected_framing = (
            expected_values[0]
            + 2 * int(sign) * expected_values[2]
            + expected_values[1]
        )
        if expected_values[3] != expected_framing:
            raise ValueError("two-over-two diagonal framing formula failed")

    transport = payload["homological_transport"]
    if not isinstance(transport, dict) or set(transport) != {
        "class_transform_mod2",
        "character_transform_mod2",
        "source_cycle_count_mod2",
        "target_cycle_count_mod2",
        "pairing_check",
    }:
        raise ValueError("homological transport schema mismatch")
    class_transform = _matrix(
        transport["class_transform_mod2"], name="class transform"
    )
    character_transform = _matrix(
        transport["character_transform_mod2"], name="character transform"
    )
    if class_transform != _mod2(p2_inv):
        raise ValueError("H2 class coordinates must transform by P2^-1 mod 2")
    if character_transform != _mod2(_transpose(p2)):
        raise ValueError("character coordinates must transform by P2^T mod 2")
    source_cycles = tuple(
        vector
        for vector in _all_bits(n2)
        if all(value == 0 for value in _matvec_mod2(source_d2, vector))
    )
    target_cycles = tuple(
        vector
        for vector in _all_bits(n2)
        if all(value == 0 for value in _matvec_mod2(target_d2, vector))
    )
    if transport["source_cycle_count_mod2"] != len(source_cycles):
        raise ValueError("source cycle denominator is stale")
    if transport["target_cycle_count_mod2"] != len(target_cycles):
        raise ValueError("target cycle denominator is stale")
    for source_cycle in source_cycles:
        target_cycle = _matvec_mod2(class_transform, source_cycle)
        if target_cycle not in target_cycles:
            raise ValueError("transported H2 class is not a target cycle")
        for source_character in _all_bits(n2):
            target_character = _matvec_mod2(
                character_transform, source_character
            )
            if _pairing_mod2(target_character, target_cycle) != _pairing_mod2(
                source_character, source_cycle
            ):
                raise ValueError("H2 class/character pairing changed")
    if transport["pairing_check"] != "PASS_EXHAUSTIVE_MOD2_CYCLES_AND_COCHAINS":
        raise ValueError("homological pairing check was not admitted")

    graphical = payload["graphical_proof"]
    if not isinstance(graphical, dict) or set(graphical) != {
        "route",
        "lean_module",
        "lean_theorem",
        "source_ref",
        "source_locator",
        "diagram_input_hash",
        "matrix_certificate_scope",
    }:
        raise ValueError("graphical proof schema mismatch")
    if graphical["route"] != GRAPHICAL_ROUTES[kind]:
        raise ValueError("wrong graphical proof route for slide kind")
    expected_theorem = (
        "OrdinaryHandleSlide.sound"
        if kind != "two_over_two"
        else "TwoHandleOverTwoSlide.sound"
    )
    if graphical["lean_theorem"] != expected_theorem:
        raise ValueError("wrong Lean theorem for slide kind")
    if graphical["lean_module"] != (
        "TwistedYetter.Kirby.KirbyHandleMoves"
    ):
        raise ValueError("wrong Lean module")
    if graphical["source_ref"] != "ref:baerenz-barrett-dichromatic-2018":
        raise ValueError("handle-slide source reference changed")
    if not isinstance(graphical["source_locator"], str) or not graphical[
        "source_locator"
    ]:
        raise ValueError("handle-slide source locator is missing")
    if not _is_sha256(graphical["diagram_input_hash"]):
        raise ValueError("graphical input must be content-addressed")
    if graphical["matrix_certificate_scope"] != (
        "BOOKKEEPING_ONLY_NOT_A_LINK_DIAGRAM_OR_EVALUATOR_PROOF"
    ):
        raise ValueError("matrix certificate was promoted beyond its scope")

    source_hash = _chain_state_hash(
        one_handle_ids=source_one_ids,
        two_handle_ids=source_two_ids,
        d2=source_d2,
        q2=None if source_q_raw is None else _matrix(source_q_raw, name="source q2"),
    )
    target_hash = _chain_state_hash(
        one_handle_ids=target_one_ids,
        two_handle_ids=target_two_ids,
        d2=target_d2,
        q2=None if target_q_raw is None else _matrix(target_q_raw, name="target q2"),
    )
    if payload["source_snapshot_hash"] != source_hash:
        raise ValueError("source handle-chain snapshot hash is stale")
    if payload["target_snapshot_hash"] != target_hash:
        raise ValueError("target handle-chain snapshot hash is stale")
    if payload["claim_boundary"] != (
        "GRAPHICAL_EQUALITY_IS_LEAN_PROVED_RELATIVE_TO_EXPLICIT_SLIDING_INPUTS;"
        "CHAIN_AND_MATRIX_DATA_ONLY_CERTIFY_BOOKKEEPING"
    ):
        raise ValueError("handle-slide claim boundary changed")


def build_handle_slide_bookkeeping(
    kind: str, orientation_sign: int
) -> dict[str, Any]:
    """Build one deterministic positive or negative R8 bookkeeping fixture."""

    if kind not in KINDS:
        raise ValueError("unsupported handle-slide kind")
    if orientation_sign not in (-1, 1):
        raise ValueError("orientation sign must be exactly +1 or -1")

    if kind == "one_over_one":
        one_ids = ["h1-a", "h1-b"]
        two_ids = ["h2-a", "h2-b"]
        sliding_id, stationary_id = one_ids
        source_d2 = ((1, 1), (0, 0))
        p1 = _elementary_basis(2, 0, 1, orientation_sign)
        p2 = _identity(2)
        source_q = None
    elif kind == "two_over_one":
        one_ids = ["h1-a"]
        two_ids = ["h2-a", "h2-b"]
        sliding_id, stationary_id = two_ids[0], one_ids[0]
        source_d2 = ((1, 0),)
        p1 = _identity(1)
        p2 = _identity(2)
        source_q = None
    else:
        one_ids = ["h1-a"]
        two_ids = ["h2-a", "h2-b"]
        sliding_id, stationary_id = two_ids
        source_d2 = ((0, 0),)
        p1 = _identity(1)
        p2 = _elementary_basis(2, 0, 1, orientation_sign)
        source_q = ((1, 2), (2, -1))

    p1_inv = inverse_unimodular(p1)
    p2_inv = inverse_unimodular(p2)
    target_d2 = _matmul(_matmul(p1_inv, source_d2), p2)
    target_q = (
        None
        if source_q is None
        else _matmul(_matmul(_transpose(p2), source_q), p2)
    )
    move_id = f"{kind}-{'positive' if orientation_sign == 1 else 'negative'}"
    diagram_hash = _sha256_payload(
        {
            "schema": "twisted-yetter.lean-parametric-slide-input.v1",
            "move_id": move_id,
            "kind": kind,
            "orientation_sign": orientation_sign,
        }
    )
    if kind == "one_over_one":
        framing: dict[str, Any] = {
            "mode": "NOT_APPLICABLE_TO_DOTTED_ONE_HANDLE"
        }
    elif kind == "two_over_one":
        framing = {
            "mode": "PINNED_BY_TYPED_DIAGRAM_NOT_Q_CONGRUENCE",
            "source_sliding_framing": 0,
            "target_sliding_framing": 0,
            "diagram_tracking_witness_hash": diagram_hash,
        }
    else:
        assert source_q is not None and target_q is not None
        framing = {
            "mode": "DERIVED_FROM_Q_PRIME_EQUALS_PT_Q_P",
            "source_sliding_framing": source_q[0][0],
            "stationary_framing": source_q[1][1],
            "mutual_linking": source_q[0][1],
            "target_sliding_framing": target_q[0][0],
            "formula": "f_i' = f_i + 2*sign*lk(i,j) + f_j",
        }
    source_cycle_count = sum(
        all(value == 0 for value in _matvec_mod2(source_d2, vector))
        for vector in _all_bits(len(two_ids))
    )
    target_cycle_count = sum(
        all(value == 0 for value in _matvec_mod2(target_d2, vector))
        for vector in _all_bits(len(two_ids))
    )
    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "move_id": move_id,
        "kind": kind,
        "orientation_sign": orientation_sign,
        "source_snapshot_hash": _chain_state_hash(
            one_handle_ids=one_ids,
            two_handle_ids=two_ids,
            d2=source_d2,
            q2=source_q,
        ),
        "target_snapshot_hash": _chain_state_hash(
            one_handle_ids=one_ids,
            two_handle_ids=two_ids,
            d2=target_d2,
            q2=target_q,
        ),
        "components": {
            "sliding_id": sliding_id,
            "stationary_id": stationary_id,
            "sliding_role": ROLE_PAIRS[kind][0],
            "stationary_role": ROLE_PAIRS[kind][1],
            "source_one_handle_ids": one_ids,
            "source_two_handle_ids": two_ids,
            "target_one_handle_ids": one_ids,
            "target_two_handle_ids": two_ids,
            "lineage": {item: item for item in one_ids + two_ids},
        },
        "handle_chain": {
            "source_d2_c2_to_c1": _rows(source_d2),
            "target_d2_c2_to_c1": _rows(target_d2),
            "c1_basis_matrix": _rows(p1),
            "c1_inverse_basis_matrix": _rows(p1_inv),
            "c2_basis_matrix": _rows(p2),
            "c2_inverse_basis_matrix": _rows(p2_inv),
            "source_q2_linking_matrix": (
                None if source_q is None else _rows(source_q)
            ),
            "target_q2_linking_matrix": (
                None if target_q is None else _rows(target_q)
            ),
            "equation": "d2_target = P1^-1 * d2_source * P2",
        },
        "framing": framing,
        "homological_transport": {
            "class_transform_mod2": _rows(_mod2(p2_inv)),
            "character_transform_mod2": _rows(_mod2(_transpose(p2))),
            "source_cycle_count_mod2": source_cycle_count,
            "target_cycle_count_mod2": target_cycle_count,
            "pairing_check": "PASS_EXHAUSTIVE_MOD2_CYCLES_AND_COCHAINS",
        },
        "graphical_proof": {
            "route": GRAPHICAL_ROUTES[kind],
            "lean_module": "TwistedYetter.Kirby.KirbyHandleMoves",
            "lean_theorem": (
                "OrdinaryHandleSlide.sound"
                if kind != "two_over_two"
                else "TwoHandleOverTwoSlide.sound"
            ),
            "source_ref": "ref:baerenz-barrett-dichromatic-2018",
            "source_locator": (
                "Lemma 3.1 and Theorem 3.9, Table 2, journal pages 680-681, 685-687"
                if kind != "two_over_two"
                else "Lemmas 3.3-3.4 and Theorem 3.9, Table 2, journal pages 681-687"
            ),
            "diagram_input_hash": diagram_hash,
            "matrix_certificate_scope": (
                "BOOKKEEPING_ONLY_NOT_A_LINK_DIAGRAM_OR_EVALUATOR_PROOF"
            ),
        },
        "claim_boundary": (
            "GRAPHICAL_EQUALITY_IS_LEAN_PROVED_RELATIVE_TO_EXPLICIT_SLIDING_INPUTS;"
            "CHAIN_AND_MATRIX_DATA_ONLY_CERTIFY_BOOKKEEPING"
        ),
    }
    payload["content_hash"] = canonical_hash(payload)
    validate_handle_slide_bookkeeping(payload)
    return payload


def all_handle_slide_bookkeeping_fixtures() -> tuple[dict[str, Any], ...]:
    return tuple(
        build_handle_slide_bookkeeping(kind, sign)
        for kind in KINDS
        for sign in (1, -1)
    )


__all__ = [
    "GRAPHICAL_ROUTES",
    "KINDS",
    "ROLE_PAIRS",
    "SCHEMA",
    "all_handle_slide_bookkeeping_fixtures",
    "build_handle_slide_bookkeeping",
    "canonical_hash",
    "validate_handle_slide_bookkeeping",
]
