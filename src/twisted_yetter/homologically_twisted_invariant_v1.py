"""Fail-closed runtime certificate for the conditional R11 Kirby invariant."""

from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from numbers import Integral
from typing import Any, Mapping, Sequence

from twisted_yetter.kirby_completeness_v1 import (
    SPECIAL_MOVE_KINDS,
    build_topology_movie_fixture,
    validate_topology_movie,
)


SCHEMA = "twisted-yetter.homologically-twisted-kirby-runtime.v1"
COEFFICIENT_FIELD = "Q-exact-runtime-fixture"
H2_DIMENSION = 2
ALPHA_DENOMINATOR = 1 << H2_DIMENSION
PROOF_OBJECT_KIND = {
    "framed_isotopy": "R7_GeneratedIsotopy",
    "one_over_one": "R8_OrdinaryHandleSlide.oneOverOne",
    "two_over_one": "R8_OrdinaryHandleSlide.twoOverOne",
    "two_over_two": "R8_TwoHandleOverTwoSlide.twoOverTwo",
    "one_two_birth": "R9_OneTwoLocalCalculation.birth_direction",
    "one_two_death": "R9_OneTwoLocalCalculation.death_direction",
    "two_three_birth": "R9_TwoThreeLocalCalculation.birth_direction",
    "two_three_death": "R9_TwoThreeLocalCalculation.death_direction",
}
SLIDE_KIND = {
    "one_over_one": "one_over_one",
    "two_over_one": "two_over_one",
    "two_over_two": "two_over_two",
}
TOP_LEVEL_KEYS = {
    "schema",
    "runtime_id",
    "category",
    "topology_movie",
    "steps",
    "movie_result",
    "marked_pair_system",
    "claim_boundary",
    "content_hash",
}
STEP_KEYS = {
    "step_index",
    "step_id",
    "topology_kind",
    "topology_orientation",
    "source_presentation_hash",
    "target_presentation_hash",
    "local_proof_binding",
    "alpha_cases",
}
ALPHA_CASE_KEYS = {
    "source_alpha",
    "target_alpha_derived",
    "source_state",
    "target_state",
}
STATE_KEYS = {
    "handle_counts",
    "raw_numerator",
    "denominator",
    "normalized_value",
}
FORBIDDEN_KEYS = {
    "step_value_equal",
    "normalized_equality_input",
    "arbitrary_equality",
    "handwritten_target_alpha",
    "final_invariant_input",
    "crane_yetter_identification",
    "latest_alias",
}


def canonical_hash(payload: Mapping[str, Any]) -> str:
    """Hash a JSON payload while omitting its own content-hash field."""

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


def _fraction_payload(value: Fraction) -> dict[str, int]:
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
    }


def _fraction(value: object, *, name: str) -> Fraction:
    if not isinstance(value, dict) or set(value) != {
        "numerator",
        "denominator",
    }:
        raise ValueError(f"{name} exact fraction schema mismatch")
    numerator = _as_int(value["numerator"], name=f"{name}.numerator")
    denominator = _as_int(
        value["denominator"], name=f"{name}.denominator"
    )
    if denominator <= 0:
        raise ValueError(f"{name} denominator must be positive")
    result = Fraction(numerator, denominator)
    if result.numerator != numerator or result.denominator != denominator:
        raise ValueError(f"{name} fraction is not reduced")
    return result


def _counts(value: object, *, name: str) -> dict[str, int]:
    keys = {"h0", "h1", "h2", "h3", "h4"}
    if not isinstance(value, dict) or set(value) != keys:
        raise ValueError(f"{name} handle-count schema mismatch")
    result = {
        key: _as_int(value[key], name=f"{name}.{key}") for key in keys
    }
    if any(count < 0 for count in result.values()):
        raise ValueError(f"{name} handle counts must be nonnegative")
    return result


def _matrix(
    value: object, *, width: int, name: str
) -> tuple[tuple[int, ...], ...]:
    if not isinstance(value, list) or len(value) != width:
        raise ValueError(f"{name} must have {width} rows")
    result: list[tuple[int, ...]] = []
    for row in value:
        if not isinstance(row, list) or len(row) != width:
            raise ValueError(f"{name} must be a square matrix")
        result.append(
            tuple(_as_int(item, name=f"{name} entry") % 2 for item in row)
        )
    return tuple(result)


def _matvec_mod2(
    matrix: Sequence[Sequence[int]], vector: Sequence[int]
) -> tuple[int, ...]:
    return tuple(
        sum(row[index] * vector[index] for index in range(len(vector))) % 2
        for row in matrix
    )


def _matmul_mod2(
    left: Sequence[Sequence[int]], right: Sequence[Sequence[int]]
) -> tuple[tuple[int, ...], ...]:
    width = len(left)
    return tuple(
        tuple(
            sum(left[row][inner] * right[inner][column]
                for inner in range(width))
            % 2
            for column in range(width)
        )
        for row in range(width)
    )


def _identity(width: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(1 if row == column else 0 for column in range(width))
        for row in range(width)
    )


def _all_alphas() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple((bits >> index) & 1 for index in range(H2_DIMENSION))
        for bits in range(ALPHA_DENOMINATOR)
    )


def _denominator(
    profile: Mapping[str, int], counts: Mapping[str, int]
) -> Fraction:
    c_dimension = Fraction(profile["c_dimension"])
    one_two_factor = Fraction(
        profile["d_dimension"] * profile["transparent_dimension"]
    )
    exponent = counts["h2"] - counts["h1"]
    return (
        c_dimension**exponent
        * one_two_factor ** counts["h1"]
    )


def _transition_raw(
    kind: str, source_raw: Fraction, profile: Mapping[str, int]
) -> Fraction:
    one_two_factor = Fraction(
        profile["d_dimension"] * profile["transparent_dimension"]
    )
    two_three_factor = Fraction(profile["c_dimension"])
    if kind == "one_two_birth":
        return one_two_factor * source_raw
    if kind == "one_two_death":
        return source_raw / one_two_factor
    if kind == "two_three_birth":
        return two_three_factor * source_raw
    if kind == "two_three_death":
        return source_raw / two_three_factor
    return source_raw


def _state(
    counts: Mapping[str, int],
    raw: Fraction,
    profile: Mapping[str, int],
) -> dict[str, object]:
    denominator = _denominator(profile, counts)
    return {
        "handle_counts": dict(counts),
        "raw_numerator": _fraction_payload(raw),
        "denominator": _fraction_payload(denominator),
        "normalized_value": _fraction_payload(raw / denominator),
    }


def _proof_binding(
    step: Mapping[str, Any],
) -> dict[str, object]:
    kind = str(step["kind"])
    binding: dict[str, object] = {
        "proof_object_kind": PROOF_OBJECT_KIND[kind],
        "move_id": step["step_id"],
        "source_presentation_hash": step["source_presentation_hash"],
        "target_presentation_hash": step["target_presentation_hash"],
        "realizes_exact_topology_move": True,
    }
    if kind in SLIDE_KIND:
        binding.update(
            {
                "graphical_slide_kind": SLIDE_KIND[kind],
                "graphical_orientation": step["orientation"],
            }
        )
    binding["graphical_certificate_hash"] = _sha256_payload(binding)
    return binding


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


def build_invariant_runtime_fixture() -> dict[str, object]:
    """Build one deterministic exact fixture covering every R11 step."""

    topology = build_topology_movie_fixture()
    validate_topology_movie(topology)
    profile = {
        "c_dimension": 2,
        "d_dimension": 3,
        "transparent_dimension": 5,
    }
    category_snapshot_hash = _sha256_payload(
        {
            "schema": "twisted-yetter.r11-category-fixture.v1",
            "field": COEFFICIENT_FIELD,
            "profile": profile,
            "sliding_data": "R5-fixture-bound",
            "closed_scalarization": "End(unit)-to-Q-fixture",
        }
    )
    category = {
        "category_snapshot_hash": category_snapshot_hash,
        "coherence_certificate_hash": _sha256_payload(
            {
                "category_snapshot_hash": category_snapshot_hash,
                "dimension_profile": profile,
                "sliding_data": "same-snapshot",
                "scalarization": "same-snapshot",
            }
        ),
        "single_snapshot_coherent": True,
        "scalarization_matches_ground_field": True,
        "coefficient_field": COEFFICIENT_FIELD,
        "dimension_profile": profile,
    }

    current_values = {
        alpha: Fraction(101 + index * 7)
        for index, alpha in enumerate(_all_alphas())
    }
    initial_values = dict(current_values)
    steps: list[dict[str, object]] = []
    composite = _identity(H2_DIMENSION)

    for index, topology_step in enumerate(topology["steps"]):
        matrix = _matrix(
            topology_step["h2_matrix_mod2"],
            width=H2_DIMENSION,
            name=f"topology step {index} H2 matrix",
        )
        source_counts = _counts(
            topology_step["source_handle_counts"],
            name=f"topology step {index} source counts",
        )
        target_counts = _counts(
            topology_step["target_handle_counts"],
            name=f"topology step {index} target counts",
        )
        target_values: dict[tuple[int, ...], Fraction] = {}
        alpha_cases: list[dict[str, object]] = []
        kind = str(topology_step["kind"])

        for alpha in _all_alphas():
            target_alpha = _matvec_mod2(matrix, alpha)
            source_raw = current_values[alpha]
            target_raw = _transition_raw(kind, source_raw, profile)
            target_values[target_alpha] = target_raw
            alpha_cases.append(
                {
                    "source_alpha": list(alpha),
                    "target_alpha_derived": list(target_alpha),
                    "source_state": _state(
                        source_counts, source_raw, profile
                    ),
                    "target_state": _state(
                        target_counts, target_raw, profile
                    ),
                }
            )

        steps.append(
            {
                "step_index": index,
                "step_id": topology_step["step_id"],
                "topology_kind": kind,
                "topology_orientation": topology_step["orientation"],
                "source_presentation_hash":
                    topology_step["source_presentation_hash"],
                "target_presentation_hash":
                    topology_step["target_presentation_hash"],
                "local_proof_binding": _proof_binding(topology_step),
                "alpha_cases": alpha_cases,
            }
        )
        current_values = target_values
        composite = _matmul_mod2(matrix, composite)

    final_counts = _counts(
        topology["steps"][-1]["target_handle_counts"],
        name="final counts",
    )
    initial_counts = _counts(
        topology["steps"][0]["source_handle_counts"],
        name="initial counts",
    )
    marked_cases = []
    for alpha in _all_alphas():
        target_alpha = _matvec_mod2(composite, alpha)
        chosen_value = (
            initial_values[alpha] / _denominator(profile, initial_counts)
        )
        target_value = (
            current_values[target_alpha]
            / _denominator(profile, final_counts)
        )
        marked_cases.append(
            {
                "geometric_alpha": list(alpha),
                "chosen_coordinate": list(alpha),
                "target_coordinate_derived": list(target_alpha),
                "chosen_value": _fraction_payload(chosen_value),
                "target_value": _fraction_payload(target_value),
            }
        )

    result: dict[str, object] = {
        "schema": SCHEMA,
        "runtime_id": "r11-eight-move-all-alpha-exact-fixture",
        "category": category,
        "topology_movie": {
            "content_hash": topology["content_hash"],
            "movie_id": topology["movie_id"],
            "source_presentation_hash":
                topology["source_presentation_hash"],
            "target_presentation_hash":
                topology["target_presentation_hash"],
            "fixture": topology,
        },
        "steps": steps,
        "movie_result": {
            "status": "PASS_MOVIE_INVARIANCE_EXACT_ALL_ALPHA",
            "step_count": len(steps),
            "directed_constructor_coverage": list(SPECIAL_MOVE_KINDS),
            "alpha_count_per_step": ALPHA_DENOMINATOR,
            "checked_step_alpha_count":
                len(steps) * ALPHA_DENOMINATOR,
            "composite_h2_matrix_mod2": [
                list(row) for row in composite
            ],
        },
        "marked_pair_system": {
            "status": "PASS_CHOSEN_AND_TARGET_REALIZATIONS_ALL_ALPHA",
            "geometric_alpha_count": ALPHA_DENOMINATOR,
            "uses_exact_r10_completeness_movie": True,
            "marked_transport_is_derived": True,
            "cases": marked_cases,
        },
        "claim_boundary": {
            "status":
                "R11_RUNTIME_INTEGRATION_ONLY_NOT_A_CATEGORY_IMPORT",
            "mathematical_status":
                "HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT_"
                "ESTABLISHED_UNDER_LISTED_AXIOMS",
            "explicit_non_claims": [
                "This fixture does not identify the Kirby invariant with Crane-Yetter.",
                "This fixture does not import a concrete category snapshot.",
                "This fixture does not validate a numerical experiment artifact.",
                "This fixture does not replace the Lean proof.",
            ],
        },
    }
    result["content_hash"] = canonical_hash(result)
    validate_invariant_runtime(result)
    return result


def validate_invariant_runtime(payload: Mapping[str, Any]) -> None:
    """Reject stale, mismatched, or equality-injected R11 runtime data."""

    if set(payload) != TOP_LEVEL_KEYS:
        missing = sorted(TOP_LEVEL_KEYS - set(payload))
        extra = sorted(set(payload) - TOP_LEVEL_KEYS)
        raise ValueError(
            f"R11 runtime schema mismatch: missing={missing}, extra={extra}"
        )
    if payload["schema"] != SCHEMA:
        raise ValueError("unsupported R11 runtime schema")
    if payload["content_hash"] != canonical_hash(payload):
        raise ValueError("stale R11 runtime content hash")
    forbidden = FORBIDDEN_KEYS.intersection(_walk_keys(payload))
    if forbidden:
        raise ValueError(
            f"R11 runtime contains forbidden equality or claim data: "
            f"{sorted(forbidden)}"
        )

    category = payload["category"]
    expected_category_keys = {
        "category_snapshot_hash",
        "coherence_certificate_hash",
        "single_snapshot_coherent",
        "scalarization_matches_ground_field",
        "coefficient_field",
        "dimension_profile",
    }
    if not isinstance(category, dict) or set(category) != (
        expected_category_keys
    ):
        raise ValueError("R11 category schema mismatch")
    if not _is_sha256(category["category_snapshot_hash"]):
        raise ValueError("R11 category snapshot hash is invalid")
    if not _is_sha256(category["coherence_certificate_hash"]):
        raise ValueError("R11 category coherence hash is invalid")
    if category["single_snapshot_coherent"] is not True:
        raise ValueError("R11 category inputs are not one-snapshot coherent")
    if category["scalarization_matches_ground_field"] is not True:
        raise ValueError("R11 scalarization is not certified")
    profile = category["dimension_profile"]
    if not isinstance(profile, dict) or set(profile) != {
        "c_dimension",
        "d_dimension",
        "transparent_dimension",
    }:
        raise ValueError("R11 dimension profile schema mismatch")
    checked_profile = {
        key: _as_int(value, name=f"profile.{key}")
        for key, value in profile.items()
    }
    if any(value == 0 for value in checked_profile.values()):
        raise ValueError("R11 dimension profile must be nonzero")

    topology_record = payload["topology_movie"]
    expected_topology_keys = {
        "content_hash",
        "movie_id",
        "source_presentation_hash",
        "target_presentation_hash",
        "fixture",
    }
    if not isinstance(topology_record, dict) or set(topology_record) != (
        expected_topology_keys
    ):
        raise ValueError("R11 topology-movie binding schema mismatch")
    topology = topology_record["fixture"]
    if not isinstance(topology, dict):
        raise ValueError("R11 topology fixture must be an object")
    validate_topology_movie(topology)
    for key in expected_topology_keys - {"fixture"}:
        if topology_record[key] != topology[key]:
            raise ValueError(f"stale R10 topology binding: {key}")

    steps = payload["steps"]
    if not isinstance(steps, list) or len(steps) != len(
        SPECIAL_MOVE_KINDS
    ):
        raise ValueError("R11 must cover exactly eight directed steps")
    if [step.get("topology_kind") for step in steps] != list(
        SPECIAL_MOVE_KINDS
    ):
        raise ValueError("R11 directed-constructor coverage changed")

    composite = _identity(H2_DIMENSION)
    for index, (step, topology_step) in enumerate(
        zip(steps, topology["steps"], strict=True)
    ):
        if not isinstance(step, dict) or set(step) != STEP_KEYS:
            raise ValueError(f"R11 step {index} schema mismatch")
        if step["step_index"] != index:
            raise ValueError(f"R11 step {index} index mismatch")
        for local_key, topology_key in (
            ("step_id", "step_id"),
            ("topology_kind", "kind"),
            ("topology_orientation", "orientation"),
            ("source_presentation_hash", "source_presentation_hash"),
            ("target_presentation_hash", "target_presentation_hash"),
        ):
            if step[local_key] != topology_step[topology_key]:
                raise ValueError(
                    f"R11 step {index} stale topology binding: {local_key}"
                )

        binding = step["local_proof_binding"]
        if not isinstance(binding, dict):
            raise ValueError(f"R11 step {index} proof binding must be an object")
        certificate_hash = binding.get("graphical_certificate_hash")
        binding_body = dict(binding)
        binding_body.pop("graphical_certificate_hash", None)
        if certificate_hash != _sha256_payload(binding_body):
            raise ValueError(f"R11 step {index} stale graphical certificate")
        kind = str(step["topology_kind"])
        if binding.get("proof_object_kind") != PROOF_OBJECT_KIND[kind]:
            raise ValueError(f"R11 step {index} wrong proof object kind")
        if binding.get("move_id") != step["step_id"]:
            raise ValueError(f"R11 step {index} proof move ID mismatch")
        if binding.get("source_presentation_hash") != (
            step["source_presentation_hash"]
        ):
            raise ValueError(f"R11 step {index} proof source hash mismatch")
        if binding.get("target_presentation_hash") != (
            step["target_presentation_hash"]
        ):
            raise ValueError(f"R11 step {index} proof target hash mismatch")
        if binding.get("realizes_exact_topology_move") is not True:
            raise ValueError(f"R11 step {index} lacks topology witness")
        if kind in SLIDE_KIND:
            if binding.get("graphical_slide_kind") != SLIDE_KIND[kind]:
                raise ValueError(f"R11 step {index} graphical kind mismatch")
            if binding.get("graphical_orientation") != (
                step["topology_orientation"]
            ):
                raise ValueError(
                    f"R11 step {index} graphical orientation mismatch"
                )
        elif {
            "graphical_slide_kind",
            "graphical_orientation",
        }.intersection(binding):
            raise ValueError(
                f"R11 step {index} non-slide contains slide binding"
            )

        matrix = _matrix(
            topology_step["h2_matrix_mod2"],
            width=H2_DIMENSION,
            name=f"R11 step {index} H2 matrix",
        )
        composite = _matmul_mod2(matrix, composite)
        source_counts = _counts(
            topology_step["source_handle_counts"],
            name=f"R11 step {index} source counts",
        )
        target_counts = _counts(
            topology_step["target_handle_counts"],
            name=f"R11 step {index} target counts",
        )
        cases = step["alpha_cases"]
        if not isinstance(cases, list) or len(cases) != ALPHA_DENOMINATOR:
            raise ValueError(f"R11 step {index} alpha denominator incomplete")
        observed_source_alphas: set[tuple[int, ...]] = set()
        observed_target_alphas: set[tuple[int, ...]] = set()
        for case_index, case in enumerate(cases):
            if not isinstance(case, dict) or set(case) != ALPHA_CASE_KEYS:
                raise ValueError(
                    f"R11 step {index} alpha case {case_index} schema mismatch"
                )
            source_alpha = tuple(
                _as_int(value, name="source alpha") % 2
                for value in case["source_alpha"]
            )
            target_alpha = tuple(
                _as_int(value, name="target alpha") % 2
                for value in case["target_alpha_derived"]
            )
            if len(source_alpha) != H2_DIMENSION or len(target_alpha) != (
                H2_DIMENSION
            ):
                raise ValueError(f"R11 step {index} alpha width mismatch")
            if target_alpha != _matvec_mod2(matrix, source_alpha):
                raise ValueError(f"R11 step {index} target alpha handwritten")
            observed_source_alphas.add(source_alpha)
            observed_target_alphas.add(target_alpha)
            source_state = _validate_state(
                case["source_state"],
                profile=checked_profile,
                expected_counts=source_counts,
                name=f"R11 step {index} source state",
            )
            target_state = _validate_state(
                case["target_state"],
                profile=checked_profile,
                expected_counts=target_counts,
                name=f"R11 step {index} target state",
            )
            expected_target_raw = _transition_raw(
                kind, source_state["raw"], checked_profile
            )
            if target_state["raw"] != expected_target_raw:
                raise ValueError(
                    f"R11 step {index} local raw factor/direction mismatch"
                )
            if source_state["normalized"] != target_state["normalized"]:
                raise ValueError(
                    f"R11 step {index} normalized values do not agree"
                )
        if observed_source_alphas != set(_all_alphas()):
            raise ValueError(f"R11 step {index} source alpha coverage changed")
        if observed_target_alphas != set(_all_alphas()):
            raise ValueError(f"R11 step {index} target alpha coverage changed")

    movie_result = payload["movie_result"]
    expected_movie_keys = {
        "status",
        "step_count",
        "directed_constructor_coverage",
        "alpha_count_per_step",
        "checked_step_alpha_count",
        "composite_h2_matrix_mod2",
    }
    if not isinstance(movie_result, dict) or set(movie_result) != (
        expected_movie_keys
    ):
        raise ValueError("R11 movie result schema mismatch")
    if movie_result["status"] != "PASS_MOVIE_INVARIANCE_EXACT_ALL_ALPHA":
        raise ValueError("R11 movie result is not passing")
    if movie_result["step_count"] != len(steps):
        raise ValueError("R11 movie step count mismatch")
    if movie_result["directed_constructor_coverage"] != list(
        SPECIAL_MOVE_KINDS
    ):
        raise ValueError("R11 movie coverage mismatch")
    if movie_result["alpha_count_per_step"] != ALPHA_DENOMINATOR:
        raise ValueError("R11 alpha denominator mismatch")
    if movie_result["checked_step_alpha_count"] != (
        len(steps) * ALPHA_DENOMINATOR
    ):
        raise ValueError("R11 checked step-alpha count mismatch")
    observed_composite = _matrix(
        movie_result["composite_h2_matrix_mod2"],
        width=H2_DIMENSION,
        name="R11 composite H2 matrix",
    )
    if observed_composite != composite:
        raise ValueError("R11 composite H2 matrix is stale")

    marked = payload["marked_pair_system"]
    expected_marked_keys = {
        "status",
        "geometric_alpha_count",
        "uses_exact_r10_completeness_movie",
        "marked_transport_is_derived",
        "cases",
    }
    if not isinstance(marked, dict) or set(marked) != expected_marked_keys:
        raise ValueError("R11 marked-pair schema mismatch")
    if marked["status"] != (
        "PASS_CHOSEN_AND_TARGET_REALIZATIONS_ALL_ALPHA"
    ):
        raise ValueError("R11 marked-pair result is not passing")
    if marked["geometric_alpha_count"] != ALPHA_DENOMINATOR:
        raise ValueError("R11 marked geometric-alpha denominator mismatch")
    if marked["uses_exact_r10_completeness_movie"] is not True:
        raise ValueError("R11 marked system bypasses R10 completeness")
    if marked["marked_transport_is_derived"] is not True:
        raise ValueError("R11 marked target coordinate is not derived")
    marked_cases = marked["cases"]
    if not isinstance(marked_cases, list) or len(marked_cases) != (
        ALPHA_DENOMINATOR
    ):
        raise ValueError("R11 marked-pair cases are incomplete")
    observed_geometric: set[tuple[int, ...]] = set()
    for case in marked_cases:
        if not isinstance(case, dict) or set(case) != {
            "geometric_alpha",
            "chosen_coordinate",
            "target_coordinate_derived",
            "chosen_value",
            "target_value",
        }:
            raise ValueError("R11 marked-pair case schema mismatch")
        geometric = tuple(case["geometric_alpha"])
        chosen = tuple(case["chosen_coordinate"])
        target = tuple(case["target_coordinate_derived"])
        if chosen != geometric:
            raise ValueError("R11 chosen coordinate does not represent alpha")
        if target != _matvec_mod2(composite, chosen):
            raise ValueError("R11 marked target coordinate was handwritten")
        if _fraction(case["chosen_value"], name="chosen value") != _fraction(
            case["target_value"], name="target value"
        ):
            raise ValueError("R11 marked presentations disagree")
        observed_geometric.add(geometric)
    if observed_geometric != set(_all_alphas()):
        raise ValueError("R11 marked geometric-alpha coverage changed")

    claim = payload["claim_boundary"]
    if not isinstance(claim, dict) or set(claim) != {
        "status",
        "mathematical_status",
        "explicit_non_claims",
    }:
        raise ValueError("R11 claim boundary schema mismatch")
    if claim["mathematical_status"] != (
        "HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT_"
        "ESTABLISHED_UNDER_LISTED_AXIOMS"
    ):
        raise ValueError("R11 mathematical status changed")
    nonclaims = "\n".join(claim["explicit_non_claims"])
    for required in (
        "does not identify the Kirby invariant with Crane-Yetter",
        "does not import a concrete category snapshot",
        "does not validate a numerical experiment artifact",
        "does not replace the Lean proof",
    ):
        if required not in nonclaims:
            raise ValueError(f"R11 missing non-claim: {required}")


def _validate_state(
    value: object,
    *,
    profile: Mapping[str, int],
    expected_counts: Mapping[str, int],
    name: str,
) -> dict[str, Fraction]:
    if not isinstance(value, dict) or set(value) != STATE_KEYS:
        raise ValueError(f"{name} schema mismatch")
    counts = _counts(value["handle_counts"], name=f"{name}.counts")
    if counts != dict(expected_counts):
        raise ValueError(f"{name} handle counts are stale")
    raw = _fraction(value["raw_numerator"], name=f"{name}.raw")
    denominator = _fraction(
        value["denominator"], name=f"{name}.denominator"
    )
    expected_denominator = _denominator(profile, counts)
    if denominator != expected_denominator:
        raise ValueError(f"{name} signed-exponent denominator is wrong")
    normalized = _fraction(
        value["normalized_value"], name=f"{name}.normalized"
    )
    if normalized != raw / denominator:
        raise ValueError(f"{name} normalized value is stale")
    return {
        "raw": raw,
        "denominator": denominator,
        "normalized": normalized,
    }
