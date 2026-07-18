"""Fail-closed R10 Kirby/Cerf topology-boundary certificates."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from numbers import Integral
from typing import Any, Mapping, Sequence


SCHEMA = "twisted-yetter.kirby-completeness-movie.v1"
SPECIAL_MOVE_KINDS = (
    "framed_isotopy",
    "one_over_one",
    "two_over_one",
    "two_over_two",
    "one_two_birth",
    "one_two_death",
    "two_three_birth",
    "two_three_death",
)
GENERAL_CERF_MOVE_FAMILIES = (
    "level_isotopy_indices_0_through_4",
    "same_index_slide_1",
    "same_index_slide_2",
    "same_index_slide_3",
    "zero_one_birth_death",
    "one_two_birth_death",
    "two_three_birth_death",
    "three_four_birth_death",
)
EXCLUDED_FROM_SPECIAL_MOVIE = (
    "zero_one_birth_death",
    "three_over_three_slide",
    "three_four_birth_death",
)
COUNT_KEYS = ("h0", "h1", "h2", "h3", "h4")
TOP_LEVEL_KEYS = {
    "schema",
    "movie_id",
    "manifold",
    "completeness_boundary",
    "source_presentation_hash",
    "target_presentation_hash",
    "steps",
    "composite_h2_transport",
    "claim_boundary",
    "content_hash",
}
STEP_KEYS = {
    "step_id",
    "kind",
    "orientation",
    "source_presentation_id",
    "target_presentation_id",
    "source_presentation_hash",
    "target_presentation_hash",
    "source_handle_counts",
    "target_handle_counts",
    "source_h2_model_certificate_hash",
    "target_h2_model_certificate_hash",
    "h2_matrix_mod2",
    "h2_inverse_mod2",
    "character_pairing_certificate",
    "local_topology_certificate_hash",
    "source_proof",
}
FORBIDDEN_EVALUATOR_KEYS = {
    "evaluator_equality",
    "evaluator_value",
    "evaluation_state",
    "raw_numerator",
    "normalized_value",
    "local_evaluator_equality",
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


def _as_int(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError(f"{name} must be an integer")
    return int(value)


def _counts(value: object, *, name: str) -> dict[str, int]:
    if not isinstance(value, dict) or tuple(sorted(value)) != tuple(
        sorted(COUNT_KEYS)
    ):
        raise ValueError(f"{name} handle-count schema mismatch")
    counts = {
        key: _as_int(value[key], name=f"{name}.{key}")
        for key in COUNT_KEYS
    }
    if any(item < 0 for item in counts.values()):
        raise ValueError(f"{name} handle counts must be nonnegative")
    return counts


def _matrix(
    value: object, *, width: int, name: str
) -> tuple[tuple[int, ...], ...]:
    if not isinstance(value, list) or len(value) != width:
        raise ValueError(f"{name} must have {width} rows")
    rows: list[tuple[int, ...]] = []
    for row in value:
        if not isinstance(row, list) or len(row) != width:
            raise ValueError(f"{name} must be a square {width}-matrix")
        rows.append(
            tuple(_as_int(item, name=f"{name} entry") % 2 for item in row)
        )
    return tuple(rows)


def _matmul_mod2(
    left: Sequence[Sequence[int]], right: Sequence[Sequence[int]]
) -> tuple[tuple[int, ...], ...]:
    width = len(left)
    return tuple(
        tuple(
            sum(left[row][inner] * right[inner][col] for inner in range(width))
            % 2
            for col in range(width)
        )
        for row in range(width)
    )


def _matvec_mod2(
    matrix: Sequence[Sequence[int]], vector: Sequence[int]
) -> tuple[int, ...]:
    return tuple(
        sum(row[index] * vector[index] for index in range(len(vector))) % 2
        for row in matrix
    )


def _transpose(
    matrix: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(matrix[row][col] for row in range(len(matrix)))
        for col in range(len(matrix))
    )


def _all_bits(width: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple((bits >> index) & 1 for index in range(width))
        for bits in range(1 << width)
    )


def _pairing(left: Sequence[int], right: Sequence[int]) -> int:
    return sum(a * b for a, b in zip(left, right, strict=True)) % 2


def _identity(width: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(1 if row == col else 0 for col in range(width))
        for row in range(width)
    )


def _rows(matrix: Sequence[Sequence[int]]) -> list[list[int]]:
    return [list(row) for row in matrix]


def _presentation_hash(
    *,
    manifold_snapshot_hash: str,
    presentation_id: str,
    counts: Mapping[str, int],
) -> str:
    return _sha256_payload(
        {
            "schema": "twisted-yetter.special-kirby-presentation-snapshot.v1",
            "manifold_snapshot_hash": manifold_snapshot_hash,
            "presentation_id": presentation_id,
            "handle_counts": dict(counts),
            "normal_form": "unique-zero-and-four-handles",
        }
    )


def _h2_model_hash(presentation_hash: str) -> str:
    return _sha256_payload(
        {
            "schema": "twisted-yetter.h2-model-certificate.v1",
            "presentation_hash": presentation_hash,
            "common_model": "H2(X;F2)-fixture-dimension-2",
        }
    )


def _local_certificate_hash(step: Mapping[str, Any]) -> str:
    return _sha256_payload(
        {
            key: step[key]
            for key in sorted(STEP_KEYS - {"local_topology_certificate_hash"})
        }
    )


def _pairing_certificate(
    matrix: Sequence[Sequence[int]],
    inverse: Sequence[Sequence[int]],
) -> dict[str, object]:
    pair_count = 0
    inverse_transpose = _transpose(inverse)
    for alpha in _all_bits(len(matrix)):
        target_alpha = _matvec_mod2(matrix, alpha)
        for character in _all_bits(len(matrix)):
            target_character = _matvec_mod2(
                inverse_transpose, character
            )
            if _pairing(target_character, target_alpha) != _pairing(
                character, alpha
            ):
                raise AssertionError("fixture pairing transport is not sound")
            pair_count += 1
    return {
        "status": "PASS_EXHAUSTIVE_CLASS_CHARACTER_PAIRING",
        "coefficient_field": "F2",
        "h2_dimension": len(matrix),
        "checked_pair_count": pair_count,
        "target_character_rule": "(M^-1)^T chi",
    }


def _count_transition(
    kind: str, source: Mapping[str, int]
) -> dict[str, int]:
    target = dict(source)
    if kind == "one_two_birth":
        target["h1"] += 1
        target["h2"] += 1
    elif kind == "one_two_death":
        target["h1"] -= 1
        target["h2"] -= 1
    elif kind == "two_three_birth":
        target["h2"] += 1
        target["h3"] += 1
    elif kind == "two_three_death":
        target["h2"] -= 1
        target["h3"] -= 1
    return target


def _walk_keys(value: object) -> tuple[str, ...]:
    keys: list[str] = []
    if isinstance(value, dict):
        for key, nested in value.items():
            keys.append(str(key))
            keys.extend(_walk_keys(nested))
    elif isinstance(value, list):
        for nested in value:
            keys.extend(_walk_keys(nested))
    return tuple(keys)


def validate_topology_movie(payload: Mapping[str, Any]) -> None:
    """Reject stale, under-scoped, or evaluator-contaminated R10 data."""

    if set(payload) != TOP_LEVEL_KEYS:
        missing = sorted(TOP_LEVEL_KEYS - set(payload))
        extra = sorted(set(payload) - TOP_LEVEL_KEYS)
        raise ValueError(
            f"topology movie schema mismatch: missing={missing}, extra={extra}"
        )
    if payload["schema"] != SCHEMA:
        raise ValueError("unsupported topology movie schema")
    if payload["content_hash"] != canonical_hash(payload):
        raise ValueError("stale topology movie content hash")
    if not isinstance(payload["movie_id"], str) or not payload["movie_id"]:
        raise ValueError("movie ID must be nonempty")

    forbidden = FORBIDDEN_EVALUATOR_KEYS.intersection(_walk_keys(payload))
    if forbidden:
        raise ValueError(
            f"topology boundary contains evaluator data: {sorted(forbidden)}"
        )

    manifold = payload["manifold"]
    expected_manifold_keys = {
        "manifold_id",
        "manifold_snapshot_hash",
        "dimension",
        "smooth",
        "compact",
        "connected",
        "boundary_mode",
        "orientation_mode",
        "scope_certificate_hash",
    }
    if not isinstance(manifold, dict) or set(manifold) != expected_manifold_keys:
        raise ValueError("manifold scope schema mismatch")
    required_scope = {
        "dimension": 4,
        "smooth": True,
        "compact": True,
        "connected": True,
        "boundary_mode": "closed",
        "orientation_mode": "oriented",
    }
    if any(manifold[key] != value for key, value in required_scope.items()):
        raise ValueError("manifold lies outside the exact closed R10 scope")
    for key in ("manifold_snapshot_hash", "scope_certificate_hash"):
        if not _is_sha256(manifold[key]):
            raise ValueError(f"{key} must be content-addressed")

    boundary = payload["completeness_boundary"]
    if not isinstance(boundary, dict) or set(boundary) != {
        "general_cerf",
        "table_two_link_refinement",
        "evaluator_equality_included",
    }:
        raise ValueError("completeness boundary schema mismatch")
    if boundary["evaluator_equality_included"] is not False:
        raise ValueError("topology completeness may not contain evaluator equality")

    general = boundary["general_cerf"]
    if not isinstance(general, dict) or set(general) != {
        "status",
        "source_ref",
        "source_locator",
        "exact_scope",
        "move_families",
        "source_scope_caveat",
    }:
        raise ValueError("general Cerf boundary schema mismatch")
    if general["status"] != "IMPORTED_SOURCE_BACKED_TOPOLOGY_INPUT":
        raise ValueError("general Cerf theorem must remain an imported input")
    if tuple(general["move_families"]) != GENERAL_CERF_MOVE_FAMILIES:
        raise ValueError("general Cerf move denominator is incomplete")
    if any(
        not isinstance(general[key], str) or not general[key].strip()
        for key in (
            "source_ref",
            "source_locator",
            "exact_scope",
            "source_scope_caveat",
        )
    ):
        raise ValueError("general Cerf source metadata is incomplete")

    special = boundary["table_two_link_refinement"]
    if not isinstance(special, dict) or set(special) != {
        "status",
        "source_refs",
        "source_locator",
        "endpoint_normal_form",
        "move_families",
        "excluded_general_moves",
        "source_scope_caveat",
        "derived_from_general_cerf_in_lean",
    }:
        raise ValueError("Table 2 refinement boundary schema mismatch")
    if special["status"] != (
        "IMPORTED_SOURCE_BACKED_LINK_CALCULUS_REFINEMENT"
    ):
        raise ValueError("Table 2 refinement must remain an imported input")
    if special["derived_from_general_cerf_in_lean"] is not False:
        raise ValueError("Table 2 refinement is not Lean-derived from Cerf")
    if tuple(special["move_families"]) != SPECIAL_MOVE_KINDS:
        raise ValueError("special move denominator is incomplete")
    if tuple(special["excluded_general_moves"]) != (
        EXCLUDED_FROM_SPECIAL_MOVIE
    ):
        raise ValueError("excluded general moves are not explicit")
    normal_form = special["endpoint_normal_form"]
    if normal_form != {
        "ordered_by_increasing_index": True,
        "unique_zero_handle": True,
        "unique_four_handle": True,
        "diagrammed_handle_indices": [1, 2],
        "higher_handles_closed_implicitly": [3, 4],
    }:
        raise ValueError("special endpoint normal form is weakened")
    if (
        not isinstance(special["source_refs"], list)
        or len(special["source_refs"]) < 2
        or any(not item for item in special["source_refs"])
        or not isinstance(special["source_locator"], str)
        or not special["source_locator"].strip()
        or not isinstance(special["source_scope_caveat"], str)
        or not special["source_scope_caveat"].strip()
    ):
        raise ValueError("Table 2 source metadata or caveat is incomplete")

    steps = payload["steps"]
    if not isinstance(steps, list) or len(steps) != len(SPECIAL_MOVE_KINDS):
        raise ValueError("fixture must cover every special move constructor")
    if {step.get("kind") for step in steps if isinstance(step, dict)} != set(
        SPECIAL_MOVE_KINDS
    ):
        raise ValueError("special move coverage is not eight of eight")

    source_movie_hash = payload["source_presentation_hash"]
    target_movie_hash = payload["target_presentation_hash"]
    if not _is_sha256(source_movie_hash) or not _is_sha256(target_movie_hash):
        raise ValueError("movie endpoints must be content-addressed")

    seen_ids: set[str] = set()
    expected_source_hash = source_movie_hash
    composite = _identity(2)
    composite_inverse = _identity(2)
    for index, step in enumerate(steps):
        if not isinstance(step, dict) or set(step) != STEP_KEYS:
            raise ValueError(f"step {index} schema mismatch")
        step_id = step["step_id"]
        if not isinstance(step_id, str) or not step_id or step_id in seen_ids:
            raise ValueError("step IDs must be unique and nonempty")
        seen_ids.add(step_id)
        kind = step["kind"]
        if kind not in SPECIAL_MOVE_KINDS:
            raise ValueError("non-Table-2 move entered the special movie")
        expected_orientation = (
            "positive_or_negative"
            if kind in {"one_over_one", "two_over_one", "two_over_two"}
            else "not_applicable"
        )
        orientation = step["orientation"]
        if expected_orientation == "positive_or_negative":
            if orientation not in {"positive", "negative"}:
                raise ValueError("slide orientation must be explicit")
        elif orientation != expected_orientation:
            raise ValueError("non-slide move has a fake band orientation")

        source_counts = _counts(
            step["source_handle_counts"], name=f"step {index} source"
        )
        target_counts = _counts(
            step["target_handle_counts"], name=f"step {index} target"
        )
        if source_counts["h0"] != 1 or source_counts["h4"] != 1:
            raise ValueError("source leaves unique-zero/four normal form")
        if target_counts["h0"] != 1 or target_counts["h4"] != 1:
            raise ValueError("target leaves unique-zero/four normal form")
        if target_counts != _count_transition(kind, source_counts):
            raise ValueError(f"{kind} handle-count transition is invalid")

        expected_step_source = _presentation_hash(
            manifold_snapshot_hash=manifold["manifold_snapshot_hash"],
            presentation_id=step["source_presentation_id"],
            counts=source_counts,
        )
        expected_step_target = _presentation_hash(
            manifold_snapshot_hash=manifold["manifold_snapshot_hash"],
            presentation_id=step["target_presentation_id"],
            counts=target_counts,
        )
        if step["source_presentation_hash"] != expected_step_source:
            raise ValueError("source presentation hash is stale")
        if step["target_presentation_hash"] != expected_step_target:
            raise ValueError("target presentation hash is stale")
        if step["source_presentation_hash"] != expected_source_hash:
            raise ValueError("movie presentation lineage is broken")
        expected_source_hash = step["target_presentation_hash"]
        if step["source_h2_model_certificate_hash"] != _h2_model_hash(
            step["source_presentation_hash"]
        ):
            raise ValueError("source H2 model certificate is stale")
        if step["target_h2_model_certificate_hash"] != _h2_model_hash(
            step["target_presentation_hash"]
        ):
            raise ValueError("target H2 model certificate is stale")

        matrix = _matrix(
            step["h2_matrix_mod2"], width=2, name=f"step {index} H2 map"
        )
        inverse = _matrix(
            step["h2_inverse_mod2"],
            width=2,
            name=f"step {index} H2 inverse",
        )
        if (
            _matmul_mod2(matrix, inverse) != _identity(2)
            or _matmul_mod2(inverse, matrix) != _identity(2)
        ):
            raise ValueError("H2 transport matrices are not inverse")
        expected_pairing = _pairing_certificate(matrix, inverse)
        if step["character_pairing_certificate"] != expected_pairing:
            raise ValueError("class/character pairing certificate is stale")

        proof = step["source_proof"]
        if not isinstance(proof, dict) or set(proof) != {
            "status",
            "source_ref",
            "source_locator",
        }:
            raise ValueError("local topology source proof schema mismatch")
        if proof["status"] != "SOURCE_BACKED_TOPOLOGY_WITNESS":
            raise ValueError("local topology witness status is not admitted")
        if not proof["source_ref"] or not proof["source_locator"]:
            raise ValueError("local topology witness lacks a source locator")
        if step["local_topology_certificate_hash"] != _local_certificate_hash(
            step
        ):
            raise ValueError("local topology certificate hash is stale")

        composite = _matmul_mod2(matrix, composite)
        composite_inverse = _matmul_mod2(
            composite_inverse, inverse
        )

    if expected_source_hash != target_movie_hash:
        raise ValueError("movie target hash does not match final step")

    composite_record = payload["composite_h2_transport"]
    if not isinstance(composite_record, dict) or set(composite_record) != {
        "status",
        "matrix_mod2",
        "inverse_mod2",
        "character_pairing_certificate",
        "step_count",
    }:
        raise ValueError("composite H2 transport schema mismatch")
    if composite_record["status"] != "PASS_COMPOSED_H2_TRANSPORT":
        raise ValueError("composite H2 transport did not pass")
    if composite_record["step_count"] != len(steps):
        raise ValueError("composite step denominator is stale")
    if _matrix(
        composite_record["matrix_mod2"], width=2, name="composite H2 map"
    ) != composite:
        raise ValueError("composite H2 matrix is stale")
    if _matrix(
        composite_record["inverse_mod2"],
        width=2,
        name="composite H2 inverse",
    ) != composite_inverse:
        raise ValueError("composite H2 inverse is stale")
    if composite_record["character_pairing_certificate"] != (
        _pairing_certificate(composite, composite_inverse)
    ):
        raise ValueError("composite pairing certificate is stale")

    claim_boundary = payload["claim_boundary"]
    if not isinstance(claim_boundary, dict) or set(claim_boundary) != {
        "mathematical_status",
        "lean_proves",
        "trusted_topology_inputs",
        "explicit_non_claims",
    }:
        raise ValueError("claim boundary schema mismatch")
    if claim_boundary["mathematical_status"] != (
        "R10_TOPOLOGY_BOUNDARY_ESTABLISHED_AS_EXPLICIT_SOURCE_BACKED_INPUT"
    ):
        raise ValueError("R10 mathematical status is scope-inflated")
    if (
        not isinstance(claim_boundary["trusted_topology_inputs"], list)
        or len(claim_boundary["trusted_topology_inputs"]) != 2
        or not isinstance(claim_boundary["explicit_non_claims"], list)
        or len(claim_boundary["explicit_non_claims"]) < 4
    ):
        raise ValueError("claim boundary omits inputs or non-claims")


def build_topology_movie_fixture() -> dict[str, Any]:
    """Build one deterministic movie covering all special constructors."""

    movie_id = "r10-table-two-whitelist-and-h2-composition-fixture"
    manifold_snapshot_hash = _sha256_payload(
        {
            "schema": "twisted-yetter.manifold-snapshot.v1",
            "manifold_id": "r10-formal-topology-fixture-X",
        }
    )
    manifold = {
        "manifold_id": "r10-formal-topology-fixture-X",
        "manifold_snapshot_hash": manifold_snapshot_hash,
        "dimension": 4,
        "smooth": True,
        "compact": True,
        "connected": True,
        "boundary_mode": "closed",
        "orientation_mode": "oriented",
        "scope_certificate_hash": _sha256_payload(
            {
                "manifold_snapshot_hash": manifold_snapshot_hash,
                "scope": "closed-connected-smooth-oriented-four-manifold",
            }
        ),
    }
    counts: dict[str, int] = {
        "h0": 1,
        "h1": 2,
        "h2": 3,
        "h3": 2,
        "h4": 1,
    }
    matrices = {
        "framed_isotopy": ([[1, 0], [0, 1]], [[1, 0], [0, 1]]),
        "one_over_one": ([[1, 1], [0, 1]], [[1, 1], [0, 1]]),
        "two_over_one": ([[1, 0], [1, 1]], [[1, 0], [1, 1]]),
        "two_over_two": ([[0, 1], [1, 0]], [[0, 1], [1, 0]]),
        "one_two_birth": ([[1, 1], [0, 1]], [[1, 1], [0, 1]]),
        "one_two_death": ([[1, 1], [0, 1]], [[1, 1], [0, 1]]),
        "two_three_birth": ([[1, 0], [1, 1]], [[1, 0], [1, 1]]),
        "two_three_death": ([[1, 0], [1, 1]], [[1, 0], [1, 1]]),
    }
    orientations = {
        "one_over_one": "positive",
        "two_over_one": "negative",
        "two_over_two": "positive",
    }
    presentation_id = f"{movie_id}-presentation-00"
    presentation_hash = _presentation_hash(
        manifold_snapshot_hash=manifold_snapshot_hash,
        presentation_id=presentation_id,
        counts=counts,
    )
    source_movie_hash = presentation_hash
    steps: list[dict[str, Any]] = []
    composite = _identity(2)
    composite_inverse = _identity(2)
    for index, kind in enumerate(SPECIAL_MOVE_KINDS):
        target_counts = _count_transition(kind, counts)
        target_id = f"{movie_id}-presentation-{index + 1:02d}"
        target_hash = _presentation_hash(
            manifold_snapshot_hash=manifold_snapshot_hash,
            presentation_id=target_id,
            counts=target_counts,
        )
        matrix_list, inverse_list = matrices[kind]
        matrix = tuple(tuple(row) for row in matrix_list)
        inverse = tuple(tuple(row) for row in inverse_list)
        step: dict[str, Any] = {
            "step_id": f"{movie_id}-step-{index:02d}-{kind}",
            "kind": kind,
            "orientation": orientations.get(kind, "not_applicable"),
            "source_presentation_id": presentation_id,
            "target_presentation_id": target_id,
            "source_presentation_hash": presentation_hash,
            "target_presentation_hash": target_hash,
            "source_handle_counts": dict(counts),
            "target_handle_counts": dict(target_counts),
            "source_h2_model_certificate_hash": _h2_model_hash(
                presentation_hash
            ),
            "target_h2_model_certificate_hash": _h2_model_hash(target_hash),
            "h2_matrix_mod2": _rows(matrix),
            "h2_inverse_mod2": _rows(inverse),
            "character_pairing_certificate": _pairing_certificate(
                matrix, inverse
            ),
            "source_proof": {
                "status": "SOURCE_BACKED_TOPOLOGY_WITNESS",
                "source_ref": (
                    "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                    if kind == "framed_isotopy"
                    else "ref:baerenz-barrett-dichromatic-2018"
                ),
                "source_locator": (
                    "Theorem 4.2.12, printed page 110"
                    if kind == "framed_isotopy"
                    else "Theorem 3.9 and Table 2, journal pages 685-687"
                ),
            },
        }
        step["local_topology_certificate_hash"] = _local_certificate_hash(step)
        steps.append(step)
        composite = _matmul_mod2(matrix, composite)
        composite_inverse = _matmul_mod2(composite_inverse, inverse)
        counts = target_counts
        presentation_id = target_id
        presentation_hash = target_hash

    payload: dict[str, Any] = {
        "schema": SCHEMA,
        "movie_id": movie_id,
        "manifold": manifold,
        "completeness_boundary": {
            "general_cerf": {
                "status": "IMPORTED_SOURCE_BACKED_TOPOLOGY_INPUT",
                "source_ref": (
                    "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                ),
                "source_locator": (
                    "Definition 4.2.1, Theorem 4.2.12, and "
                    "Proposition 4.2.13, printed pages 104 and 110-111"
                ),
                "exact_scope": (
                    "two ordered relative handle decompositions of one "
                    "compact smooth pair (X, boundary-minus X)"
                ),
                "move_families": list(GENERAL_CERF_MOVE_FAMILIES),
                "source_scope_caveat": (
                    "Theorem 4.2.12 contains all adjacent-index births and "
                    "deaths and index-three slides; it is not by itself the "
                    "five-family Table 2 link theorem."
                ),
            },
            "table_two_link_refinement": {
                "status": (
                    "IMPORTED_SOURCE_BACKED_LINK_CALCULUS_REFINEMENT"
                ),
                "source_refs": [
                    "ref:baerenz-barrett-dichromatic-2018",
                    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
                    "ref:de-sa-link-calculus-1979",
                ],
                "source_locator": (
                    "Bärenz-Barrett Theorem 3.9 and Table 2, journal "
                    "pages 685-687; Gompf-Stipsicz Section 5.1, printed "
                    "pages 139-148; de Sa, pages 16-30"
                ),
                "endpoint_normal_form": {
                    "ordered_by_increasing_index": True,
                    "unique_zero_handle": True,
                    "unique_four_handle": True,
                    "diagrammed_handle_indices": [1, 2],
                    "higher_handles_closed_implicitly": [3, 4],
                },
                "move_families": list(SPECIAL_MOVE_KINDS),
                "excluded_general_moves": list(
                    EXCLUDED_FROM_SPECIAL_MOVIE
                ),
                "source_scope_caveat": (
                    "Lean does not derive the special link calculus from "
                    "general Cerf theory. This refinement is a separately "
                    "visible topology input and is exactly where a source "
                    "scope error must fail."
                ),
                "derived_from_general_cerf_in_lean": False,
            },
            "evaluator_equality_included": False,
        },
        "source_presentation_hash": source_movie_hash,
        "target_presentation_hash": presentation_hash,
        "steps": steps,
        "composite_h2_transport": {
            "status": "PASS_COMPOSED_H2_TRANSPORT",
            "matrix_mod2": _rows(composite),
            "inverse_mod2": _rows(composite_inverse),
            "character_pairing_certificate": _pairing_certificate(
                composite, composite_inverse
            ),
            "step_count": len(steps),
        },
        "claim_boundary": {
            "mathematical_status": (
                "R10_TOPOLOGY_BOUNDARY_ESTABLISHED_AS_EXPLICIT_"
                "SOURCE_BACKED_INPUT"
            ),
            "lean_proves": [
                "the general and special move whitelists are distinct types",
                "special movies compose only typed Table 2 moves",
                "every special move carries an H2 equivalence",
                "movie H2 equivalences compose",
                "derived character transport preserves every pairing",
            ],
            "trusted_topology_inputs": [
                "general Cerf completeness for compact relative handle decompositions",
                "special five-family Table 2 link-calculus refinement",
            ],
            "explicit_non_claims": [
                "R10 does not re-prove Cerf theory in Lean.",
                "R10 does not derive the Table 2 refinement from general Cerf theory in Lean.",
                "R10 does not contain or prove an evaluator equality.",
                "R10 does not yet define the twisted four-manifold invariant.",
                "R10 does not identify that invariant with Crane-Yetter.",
            ],
        },
    }
    payload["content_hash"] = canonical_hash(payload)
    validate_topology_movie(payload)
    return payload


def all_topology_movie_fixtures() -> tuple[dict[str, Any], ...]:
    return (build_topology_movie_fixture(),)
