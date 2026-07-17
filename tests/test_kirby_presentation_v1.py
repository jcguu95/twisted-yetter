from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.kirby_presentation_v1 import (
    PresentationValidationError,
    add_content_hash,
    build_reference_fixture,
    deserialize_presentation,
    serialize_presentation,
    stable_content_hash,
    validate_presentation,
)


def repaired(payload: dict) -> dict:
    return add_content_hash(payload)


def test_reference_fixture_is_content_addressed_and_round_trips() -> None:
    fixture = build_reference_fixture()
    validate_presentation(fixture)
    assert fixture["content_hash"] == stable_content_hash(fixture)
    assert deserialize_presentation(serialize_presentation(fixture)) == fixture
    assert len(fixture["declared_slices"]) == len(fixture["events"]) + 1
    assert fixture["declared_slices"][0]["active_strands"] == []
    assert fixture["declared_slices"][-1]["active_strands"] == []


def test_all_three_component_roles_are_represented() -> None:
    fixture = build_reference_fixture()
    assert {item["role"] for item in fixture["components"]} == {
        "ordinary",
        "dotted",
        "specially_dotted",
    }


def test_mutable_alias_is_rejected_even_with_a_fresh_hash() -> None:
    fixture = build_reference_fixture()
    fixture["alias"] = "current"
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="extra=.*alias"):
        validate_presentation(fixture)


def test_stale_content_hash_is_rejected() -> None:
    fixture = build_reference_fixture()
    fixture["presentation_id"] = "silently-rebound"
    with pytest.raises(PresentationValidationError, match="content hash"):
        validate_presentation(fixture)


def test_inactive_strand_lineage_is_rejected() -> None:
    fixture = build_reference_fixture()
    fixture["events"][8]["first_strand"] = "not-active"
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="inactive strand"):
        validate_presentation(fixture)


def test_declared_slice_mismatch_is_rejected() -> None:
    fixture = build_reference_fixture()
    fixture["declared_slices"][3]["active_strands"] = []
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="declared Morse slices"):
        validate_presentation(fixture)


def test_blackboard_writhe_must_be_derived_from_events() -> None:
    fixture = build_reference_fixture()
    fixture["components"][0]["blackboard_writhe"] = 0
    fixture["components"][0]["integer_framing"] = 0
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="writhe"):
        validate_presentation(fixture)


def test_nonadjacent_crossing_is_rejected() -> None:
    fixture = build_reference_fixture()
    event = deepcopy(fixture["events"][4])
    event["under_strand"] = "D0-"
    fixture["events"][4] = event
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="not adjacent"):
        validate_presentation(fixture)
