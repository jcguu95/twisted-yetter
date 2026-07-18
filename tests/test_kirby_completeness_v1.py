from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.kirby_completeness_v1 import (
    EXCLUDED_FROM_SPECIAL_MOVIE,
    GENERAL_CERF_MOVE_FAMILIES,
    SPECIAL_MOVE_KINDS,
    build_topology_movie_fixture,
    canonical_hash,
    validate_topology_movie,
)


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_complete_fixture_validates_and_covers_both_whitelists() -> None:
    fixture = build_topology_movie_fixture()
    validate_topology_movie(fixture)

    boundary = fixture["completeness_boundary"]
    assert tuple(
        boundary["general_cerf"]["move_families"]
    ) == GENERAL_CERF_MOVE_FAMILIES
    assert tuple(
        boundary["table_two_link_refinement"]["move_families"]
    ) == SPECIAL_MOVE_KINDS
    assert {
        step["kind"] for step in fixture["steps"]
    } == set(SPECIAL_MOVE_KINDS)


def test_general_moves_excluded_from_table_two_are_never_hidden() -> None:
    fixture = build_topology_movie_fixture()
    special = fixture["completeness_boundary"]["table_two_link_refinement"]

    assert tuple(special["excluded_general_moves"]) == (
        EXCLUDED_FROM_SPECIAL_MOVIE
    )
    assert not {
        "zero_one_birth",
        "three_over_three",
        "three_four_birth",
    }.intersection(step["kind"] for step in fixture["steps"])


def test_every_special_endpoint_keeps_unique_zero_and_four_handles() -> None:
    fixture = build_topology_movie_fixture()

    for step in fixture["steps"]:
        assert step["source_handle_counts"]["h0"] == 1
        assert step["source_handle_counts"]["h4"] == 1
        assert step["target_handle_counts"]["h0"] == 1
        assert step["target_handle_counts"]["h4"] == 1


def test_h2_and_character_transport_is_exhaustive_and_composed() -> None:
    fixture = build_topology_movie_fixture()

    for step in fixture["steps"]:
        pairing = step["character_pairing_certificate"]
        assert pairing["status"] == (
            "PASS_EXHAUSTIVE_CLASS_CHARACTER_PAIRING"
        )
        assert pairing["checked_pair_count"] == 16
    composite = fixture["composite_h2_transport"]
    assert composite["status"] == "PASS_COMPOSED_H2_TRANSPORT"
    assert composite["step_count"] == len(SPECIAL_MOVE_KINDS)
    assert (
        composite["character_pairing_certificate"]["checked_pair_count"]
        == 16
    )


def test_topology_boundary_contains_no_evaluator_equality() -> None:
    fixture = build_topology_movie_fixture()
    boundary = fixture["completeness_boundary"]

    assert boundary["evaluator_equality_included"] is False
    assert "R10 does not contain or prove an evaluator equality." in (
        fixture["claim_boundary"]["explicit_non_claims"]
    )


def test_relative_or_unoriented_scope_fails_closed() -> None:
    fixture = build_topology_movie_fixture()
    relative = deepcopy(fixture)
    relative["manifold"]["boundary_mode"] = "relative"
    rehash(relative)
    with pytest.raises(ValueError, match="exact closed R10 scope"):
        validate_topology_movie(relative)

    unoriented = deepcopy(fixture)
    unoriented["manifold"]["orientation_mode"] = "unoriented"
    rehash(unoriented)
    with pytest.raises(ValueError, match="exact closed R10 scope"):
        validate_topology_movie(unoriented)


def test_zero_one_or_three_slide_cannot_enter_special_movie() -> None:
    fixture = build_topology_movie_fixture()
    zero_one = deepcopy(fixture)
    zero_one["steps"][0]["kind"] = "zero_one_birth"
    rehash(zero_one)
    with pytest.raises(ValueError, match="coverage|non-Table-2"):
        validate_topology_movie(zero_one)

    three_slide = deepcopy(fixture)
    three_slide["steps"][0]["kind"] = "three_over_three"
    rehash(three_slide)
    with pytest.raises(ValueError, match="coverage|non-Table-2"):
        validate_topology_movie(three_slide)


def test_missing_refinement_caveat_or_fake_derivation_fails_closed() -> None:
    fixture = build_topology_movie_fixture()
    missing = deepcopy(fixture)
    missing["completeness_boundary"]["table_two_link_refinement"][
        "source_scope_caveat"
    ] = ""
    rehash(missing)
    with pytest.raises(ValueError, match="caveat"):
        validate_topology_movie(missing)

    fake = deepcopy(fixture)
    fake["completeness_boundary"]["table_two_link_refinement"][
        "derived_from_general_cerf_in_lean"
    ] = True
    rehash(fake)
    with pytest.raises(ValueError, match="not Lean-derived"):
        validate_topology_movie(fake)


def test_handwritten_character_or_evaluator_data_fails_closed() -> None:
    fixture = build_topology_movie_fixture()
    character = deepcopy(fixture)
    character["steps"][0]["target_character_mod2"] = [1, 0]
    rehash(character)
    with pytest.raises(ValueError, match="step 0 schema"):
        validate_topology_movie(character)

    evaluator = deepcopy(fixture)
    evaluator["claim_boundary"]["evaluator_equality"] = "left=right"
    rehash(evaluator)
    with pytest.raises(ValueError, match="evaluator data"):
        validate_topology_movie(evaluator)


def test_broken_counts_lineage_inverse_and_composite_fail_closed() -> None:
    fixture = build_topology_movie_fixture()
    wrong_counts = deepcopy(fixture)
    wrong_counts["steps"][4]["target_handle_counts"]["h2"] += 1
    rehash(wrong_counts)
    with pytest.raises(ValueError, match="handle-count transition|stale"):
        validate_topology_movie(wrong_counts)

    wrong_lineage = deepcopy(fixture)
    wrong_lineage["steps"][1]["source_presentation_id"] = "rebound-alias"
    rehash(wrong_lineage)
    with pytest.raises(ValueError, match="source presentation hash"):
        validate_topology_movie(wrong_lineage)

    wrong_inverse = deepcopy(fixture)
    wrong_inverse["steps"][2]["h2_inverse_mod2"] = [[1, 0], [0, 1]]
    rehash(wrong_inverse)
    with pytest.raises(ValueError, match="not inverse"):
        validate_topology_movie(wrong_inverse)

    wrong_composite = deepcopy(fixture)
    wrong_composite["composite_h2_transport"]["matrix_mod2"] = [
        [1, 0],
        [0, 1],
    ]
    rehash(wrong_composite)
    with pytest.raises(ValueError, match="composite H2 matrix"):
        validate_topology_movie(wrong_composite)


def test_stale_hash_and_mutable_alias_fail_closed() -> None:
    fixture = build_topology_movie_fixture()
    stale = deepcopy(fixture)
    stale["movie_id"] = "changed-without-rehash"
    with pytest.raises(ValueError, match="stale"):
        validate_topology_movie(stale)

    alias = deepcopy(fixture)
    alias["latest_alias"] = "current"
    rehash(alias)
    with pytest.raises(ValueError, match="schema mismatch"):
        validate_topology_movie(alias)
