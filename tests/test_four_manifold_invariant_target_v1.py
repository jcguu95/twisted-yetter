from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.four_manifold_invariant_target_v1 import (
    ESTABLISHED_CONDITIONS,
    EXPLICIT_NONCLAIMS,
    MATHEMATICAL_STATUS,
    OPEN_CONDITIONS,
    REQUIRED_CONDITIONS,
    RUNTIME_STATUS,
    build_target_runtime,
    canonical_hash,
    validate_target_runtime,
)


@pytest.fixture
def runtime() -> dict[str, object]:
    return build_target_runtime()


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_target_condition_denominator_and_partition_are_exact(
    runtime: dict[str, object],
) -> None:
    validate_target_runtime(runtime)
    assert runtime["status"] == RUNTIME_STATUS
    assert runtime["mathematical_status"] == MATHEMATICAL_STATUS
    assert runtime["required_conditions"] == list(REQUIRED_CONDITIONS)
    assert runtime["established_conditions"] == list(ESTABLISHED_CONDITIONS)
    assert runtime["open_conditions"] == list(OPEN_CONDITIONS)
    assert runtime["condition_counts"] == {
        "required": 6,
        "established": 2,
        "open": 4,
    }


def test_three_handle_inverse_dimension_is_explicit(
    runtime: dict[str, object],
) -> None:
    normalization = runtime["three_handle_normalization"]
    assert normalization["dimension_symbol"] == "d(C)"
    assert normalization["three_handle_weight"] == "d(C)^-1"
    assert normalization["isolated_two_handle_factor"] == "d(C)"
    assert normalization["cancelling_pair_product"] == "1"
    assert len(normalization["lean_witnesses"]) == 3


def test_target_theorem_requires_concrete_inputs(
    runtime: dict[str, object],
) -> None:
    theorem = runtime["target_theorem"]
    assert theorem["lean_input_type"] == "FourManifoldInvariantInputs"
    assert theorem["lean_theorem"] == (
        "FourManifoldInvariantInputs.four_manifold_invariant_target"
    )
    assert theorem["concrete_input_instance_constructed"] is False
    assert runtime["four_manifold_invariant_established"] is False


def test_crane_yetter_identification_is_not_a_target_condition(
    runtime: dict[str, object],
) -> None:
    assert all(
        "crane_yetter" not in condition
        for condition in runtime["required_conditions"]
    )
    assert "Crane-Yetter" in "\n".join(EXPLICIT_NONCLAIMS)


def test_premature_invariant_promotion_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["four_manifold_invariant_established"] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="premature"):
        validate_target_runtime(mutation)


def test_missing_or_duplicate_condition_fails_closed(
    runtime: dict[str, object],
) -> None:
    missing = deepcopy(runtime)
    missing["open_conditions"].pop()
    missing["condition_counts"]["open"] = 3
    rehash(missing)
    with pytest.raises(ValueError, match="open target-condition"):
        validate_target_runtime(missing)

    duplicate = deepcopy(runtime)
    duplicate["required_conditions"][-1] = duplicate["required_conditions"][-2]
    rehash(duplicate)
    with pytest.raises(ValueError, match="required target-condition"):
        validate_target_runtime(duplicate)


def test_wrong_three_handle_convention_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["three_handle_normalization"]["three_handle_weight"] = "1"
    rehash(mutation)
    with pytest.raises(ValueError, match="three-handle"):
        validate_target_runtime(mutation)


def test_concrete_input_promotion_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["target_theorem"]["concrete_input_instance_constructed"] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="target theorem"):
        validate_target_runtime(mutation)


def test_stale_hash_fails_closed(runtime: dict[str, object]) -> None:
    mutation = deepcopy(runtime)
    mutation["status"] = "EDITED_WITHOUT_REHASH"
    with pytest.raises(ValueError, match="status mismatch|stale"):
        validate_target_runtime(mutation)
