from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.kirby_cancellation_v1 import (
    all_cancellation_fixtures,
    build_cancellation_fixture,
    canonical_hash,
    validate_cancellation_fixture,
)


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_all_required_cancellations_and_empty_end_handles_validate() -> None:
    fixtures = all_cancellation_fixtures()

    assert len(fixtures) == 4
    assert {fixture["kind"] for fixture in fixtures} == {
        "one_two",
        "two_three",
        "empty_zero",
        "empty_four",
    }
    for fixture in fixtures:
        validate_cancellation_fixture(fixture)
        assert (
            fixture["normalization"]["source_normalized_value"]
            == fixture["normalization"]["target_normalized_value"]
        )


def test_one_two_really_removes_an_acyclic_c2_to_c1_pair() -> None:
    fixture = build_cancellation_fixture("one_two")
    chain = fixture["chain_transport"]

    assert chain["source_d2"] == [[1, 0]]
    assert chain["removed_component_ids"] == ["cancel-h1", "cancel-h2"]
    assert chain["source_h2_basis_representatives_mod2"] == [[0, 1]]
    assert chain["target_h2_basis_representatives_mod2"] == [[1]]


def test_two_three_really_quotients_an_image_d3_generator() -> None:
    fixture = build_cancellation_fixture("two_three")
    chain = fixture["chain_transport"]

    assert chain["source_d3"] == [[1], [0]]
    assert chain["removed_component_ids"] == ["cancel-h2", "cancel-h3"]
    assert chain["source_h2_class_count_mod2"] == 2
    assert chain["target_h2_class_count_mod2"] == 2


def test_integer_exponent_normalization_is_not_nat_truncated() -> None:
    fixture = build_cancellation_fixture("one_two")
    normalization = fixture["normalization"]

    # Source has h2-h1 = 1 here, while the validator implements arbitrary
    # signed exponents with Fraction rather than Nat subtraction.
    assert normalization["formula"].startswith("d(C)^(h2-h1)")
    assert normalization["source_denominator"] == {
        "numerator": 105,
        "denominator": 1,
    }


def test_missing_transparent_twist_condition_fails_closed() -> None:
    fixture = build_cancellation_fixture("one_two")
    mutated = deepcopy(fixture)
    mutated["local_evaluation"]["transparent_twist_trivial"] = "MISSING"
    rehash(mutated)

    with pytest.raises(ValueError, match="graphical inputs"):
        validate_cancellation_fixture(mutated)


def test_missing_pivotal_dimension_condition_fails_closed() -> None:
    fixture = build_cancellation_fixture("two_three")
    mutated = deepcopy(fixture)
    mutated["local_evaluation"]["pivotal_dimension_preserved"] = "MISSING"
    rehash(mutated)

    with pytest.raises(ValueError, match="pivotal"):
        validate_cancellation_fixture(mutated)


def test_wrong_raw_factor_or_denominator_fails_closed() -> None:
    fixture = build_cancellation_fixture("one_two")
    wrong_raw = deepcopy(fixture)
    wrong_raw["normalization"]["source_raw_numerator"] = {
        "numerator": 230,
        "denominator": 1,
    }
    rehash(wrong_raw)
    with pytest.raises(ValueError, match="raw cancellation factor"):
        validate_cancellation_fixture(wrong_raw)

    wrong_denominator = deepcopy(fixture)
    wrong_denominator["normalization"]["source_denominator"] = {
        "numerator": 21,
        "denominator": 1,
    }
    rehash(wrong_denominator)
    with pytest.raises(ValueError, match="denominator"):
        validate_cancellation_fixture(wrong_denominator)


def test_hidden_inconclusive_h2_or_wrong_character_map_fails_closed() -> None:
    fixture = build_cancellation_fixture("two_three")
    wrong_count = deepcopy(fixture)
    wrong_count["chain_transport"]["source_h2_class_count_mod2"] = 4
    rehash(wrong_count)
    with pytest.raises(ValueError, match="class denominator"):
        validate_cancellation_fixture(wrong_count)

    wrong_dual = deepcopy(fixture)
    wrong_dual["chain_transport"]["inverse_h2_coordinate_matrix_mod2"] = [[0]]
    rehash(wrong_dual)
    with pytest.raises(ValueError, match="inverse"):
        validate_cancellation_fixture(wrong_dual)


def test_final_normalized_equality_cannot_be_an_input() -> None:
    fixture = build_cancellation_fixture("one_two")
    mutated = deepcopy(fixture)
    mutated["local_evaluation"]["normalized_equality_supplied_as_input"] = True
    rehash(mutated)

    with pytest.raises(ValueError, match="may not be supplied"):
        validate_cancellation_fixture(mutated)


def test_stale_hash_and_mutable_alias_fail_closed() -> None:
    fixture = build_cancellation_fixture("empty_four")
    stale = deepcopy(fixture)
    stale["source_handle_counts"]["h4"] += 1
    with pytest.raises(ValueError, match="stale"):
        validate_cancellation_fixture(stale)

    aliased = deepcopy(fixture)
    aliased["latest_alias"] = "current"
    rehash(aliased)
    with pytest.raises(ValueError, match="schema mismatch"):
        validate_cancellation_fixture(aliased)
