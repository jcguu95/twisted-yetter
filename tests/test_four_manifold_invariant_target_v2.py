from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.four_manifold_invariant_target_v2 import (
    ESTABLISHED_CONDITIONS,
    EXPLICIT_NONCLAIMS,
    H2_LEAN_WITNESSES,
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
        "established": 3,
        "open": 3,
    }


def test_chain_derived_h2_scope_is_exact(runtime: dict[str, object]) -> None:
    h2 = runtime["chain_derived_marked_h2_transport"]
    assert h2["status"] == "ESTABLISHED_GENERIC_MECHANISM"
    assert h2["move_input"] == "chain_homotopy_equivalence"
    assert h2["derived_output"] == (
        "additive_equivalence_on_second_homology"
    )
    assert h2["handwritten_h2_equivalence_admitted"] is False
    assert h2["handwritten_target_character_admitted"] is False
    assert h2["lean_witnesses"] == list(H2_LEAN_WITNESSES)
    assert "boundary matrices" in h2["remaining_concrete_boundary"]


def test_target_theorem_still_requires_concrete_inputs(
    runtime: dict[str, object],
) -> None:
    assert runtime["four_manifold_invariant_established"] is False
    assert runtime["target_theorem"][
        "concrete_input_instance_constructed"
    ] is False


def test_three_handle_inverse_dimension_remains_explicit(
    runtime: dict[str, object],
) -> None:
    normalization = runtime["three_handle_normalization"]
    assert normalization["three_handle_weight"] == "d(C)^-1"
    assert normalization["isolated_two_handle_factor"] == "d(C)"
    assert normalization["cancelling_pair_product"] == "1"


def test_premature_invariant_promotion_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["four_manifold_invariant_established"] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="premature"):
        validate_target_runtime(mutation)


def test_reopening_chain_derived_h2_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    h2_condition = mutation["established_conditions"].pop()
    mutation["open_conditions"].insert(0, h2_condition)
    mutation["condition_counts"] = {
        "required": 6,
        "established": 2,
        "open": 4,
    }
    rehash(mutation)
    with pytest.raises(ValueError, match="established"):
        validate_target_runtime(mutation)


def test_handwritten_h2_or_character_transport_fails_closed(
    runtime: dict[str, object],
) -> None:
    for key in (
        "handwritten_h2_equivalence_admitted",
        "handwritten_target_character_admitted",
    ):
        mutation = deepcopy(runtime)
        mutation["chain_derived_marked_h2_transport"][key] = True
        rehash(mutation)
        with pytest.raises(ValueError, match="handwritten"):
            validate_target_runtime(mutation)


def test_missing_required_condition_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["required_conditions"].pop()
    rehash(mutation)
    with pytest.raises(ValueError, match="required target-condition"):
        validate_target_runtime(mutation)


def test_stale_hash_fails_closed(runtime: dict[str, object]) -> None:
    mutation = deepcopy(runtime)
    mutation["chain_derived_marked_h2_transport"]["chain_ring"] = "Q"
    with pytest.raises(ValueError, match="stale"):
        validate_target_runtime(mutation)


def test_nonclaim_denominator_is_exact(runtime: dict[str, object]) -> None:
    assert runtime["explicit_nonclaims"] == list(EXPLICIT_NONCLAIMS)
    assert any(
        "boundary matrices" in item for item in runtime["explicit_nonclaims"]
    )
