from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.kirby_handle_moves_v1 import (
    all_handle_slide_bookkeeping_fixtures,
    build_handle_slide_bookkeeping,
    canonical_hash,
    validate_handle_slide_bookkeeping,
)


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_all_three_slide_kinds_and_both_orientations_are_terminal() -> None:
    fixtures = all_handle_slide_bookkeeping_fixtures()

    assert len(fixtures) == 6
    assert {
        (fixture["kind"], fixture["orientation_sign"])
        for fixture in fixtures
    } == {
        ("one_over_one", 1),
        ("one_over_one", -1),
        ("two_over_one", 1),
        ("two_over_one", -1),
        ("two_over_two", 1),
        ("two_over_two", -1),
    }
    for fixture in fixtures:
        validate_handle_slide_bookkeeping(fixture)


def test_only_two_over_two_claims_linking_matrix_congruence() -> None:
    for fixture in all_handle_slide_bookkeeping_fixtures():
        chain = fixture["handle_chain"]
        assert isinstance(chain, dict)
        if fixture["kind"] == "two_over_two":
            assert chain["source_q2_linking_matrix"] is not None
            assert fixture["framing"]["mode"] == (
                "DERIVED_FROM_Q_PRIME_EQUALS_PT_Q_P"
            )
        else:
            assert chain["source_q2_linking_matrix"] is None


def test_wrong_role_pair_fails_closed() -> None:
    fixture = build_handle_slide_bookkeeping("two_over_one", 1)
    mutated = deepcopy(fixture)
    mutated["components"]["stationary_role"] = "ordinary"
    rehash(mutated)

    with pytest.raises(ValueError, match="roles"):
        validate_handle_slide_bookkeeping(mutated)


def test_wrong_oriented_basis_change_fails_closed() -> None:
    fixture = build_handle_slide_bookkeeping("one_over_one", -1)
    mutated = deepcopy(fixture)
    mutated["handle_chain"]["c1_basis_matrix"] = [[1, 0], [1, 1]]
    rehash(mutated)

    with pytest.raises(ValueError, match="basis"):
        validate_handle_slide_bookkeeping(mutated)


def test_wrong_framing_formula_fails_closed() -> None:
    fixture = build_handle_slide_bookkeeping("two_over_two", 1)
    mutated = deepcopy(fixture)
    mutated["framing"]["target_sliding_framing"] += 1
    rehash(mutated)

    with pytest.raises(ValueError, match="framing"):
        validate_handle_slide_bookkeeping(mutated)


def test_wrong_class_transport_fails_closed() -> None:
    fixture = build_handle_slide_bookkeeping("two_over_two", 1)
    mutated = deepcopy(fixture)
    mutated["homological_transport"]["class_transform_mod2"] = [
        [1, 0],
        [0, 1],
    ]
    rehash(mutated)

    with pytest.raises(ValueError, match="class coordinates"):
        validate_handle_slide_bookkeeping(mutated)


def test_wrong_character_dual_transport_fails_closed() -> None:
    fixture = build_handle_slide_bookkeeping("two_over_two", 1)
    mutated = deepcopy(fixture)
    mutated["homological_transport"]["character_transform_mod2"] = [
        [1, 0],
        [0, 1],
    ]
    rehash(mutated)

    with pytest.raises(ValueError, match="character coordinates"):
        validate_handle_slide_bookkeeping(mutated)


def test_matrix_bookkeeping_cannot_masquerade_as_graphical_proof() -> None:
    fixture = build_handle_slide_bookkeeping("two_over_two", -1)
    mutated = deepcopy(fixture)
    mutated["graphical_proof"]["matrix_certificate_scope"] = (
        "FULL_LINK_DIAGRAM_PROOF"
    )
    rehash(mutated)

    with pytest.raises(ValueError, match="promoted"):
        validate_handle_slide_bookkeeping(mutated)


def test_stale_hash_and_extra_alias_fail_closed() -> None:
    fixture = build_handle_slide_bookkeeping("two_over_one", -1)
    stale = deepcopy(fixture)
    stale["orientation_sign"] = 1
    with pytest.raises(ValueError, match="stale"):
        validate_handle_slide_bookkeeping(stale)

    aliased = deepcopy(fixture)
    aliased["current_alias"] = "latest"
    rehash(aliased)
    with pytest.raises(ValueError, match="schema mismatch"):
        validate_handle_slide_bookkeeping(aliased)
