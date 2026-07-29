from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.kirby_presentation_v1 import (
    PresentationValidationError,
    add_content_hash,
    build_reference_fixture,
    deserialize_presentation,
    materialize_declared_slices,
    serialize_presentation,
    stable_content_hash,
    validate_presentation,
)


def repaired(payload: dict) -> dict:
    return add_content_hash(payload)


def fusion_coupon_fixture() -> dict:
    fixture = build_reference_fixture()
    fixture["components"] = [deepcopy(fixture["components"][0])]
    fixture["components"][0]["blackboard_writhe"] = 0
    fixture["components"][0]["integer_framing"] = 0
    fixture["dotted_cuts"] = []
    fixture["events"] = [
        {
            "event_id": "e0",
            "kind": "birth",
            "component_id": "K0",
            "positive_strand": "A+",
            "negative_strand": "A-",
            "insert_at": 0,
        },
        {
            "event_id": "e1",
            "kind": "coupon",
            "coupon_id": "fusion-projection",
            "label": "x-tensor-y-to-z",
            "input_strands": ["A+", "A-"],
            "output_strands": [
                {
                    "strand_id": "Z+",
                    "component_id": "K0",
                    "orientation": "positive",
                }
            ],
            "replace_at": 0,
        },
        {
            "event_id": "e2",
            "kind": "coupon",
            "coupon_id": "fusion-inclusion",
            "label": "z-to-x-tensor-y",
            "input_strands": ["Z+"],
            "output_strands": [
                {
                    "strand_id": "A+",
                    "component_id": "K0",
                    "orientation": "positive",
                },
                {
                    "strand_id": "A-",
                    "component_id": "K0",
                    "orientation": "negative",
                },
            ],
            "replace_at": 0,
        },
        {
            "event_id": "e3",
            "kind": "death",
            "component_id": "K0",
            "first_strand": "A+",
            "second_strand": "A-",
        },
    ]
    fixture["declared_slices"] = materialize_declared_slices(fixture)
    return repaired(fixture)


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


def test_uppercase_content_hash_is_rejected() -> None:
    fixture = build_reference_fixture()
    fixture["content_hash"] = (
        "sha256:" + fixture["content_hash"][len("sha256:") :].upper()
    )
    with pytest.raises(PresentationValidationError, match="lowercase"):
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


def test_death_requires_opposite_orientations() -> None:
    fixture = build_reference_fixture()
    fixture["components"] = [fixture["components"][0]]
    fixture["components"][0]["blackboard_writhe"] = 0
    fixture["components"][0]["integer_framing"] = 0
    fixture["events"] = [
        {
            "event_id": "e0",
            "kind": "birth",
            "component_id": "K0",
            "positive_strand": "A+",
            "negative_strand": "A-",
            "insert_at": 0,
        },
        {
            "event_id": "e1",
            "kind": "birth",
            "component_id": "K0",
            "positive_strand": "B+",
            "negative_strand": "B-",
            "insert_at": 1,
        },
        {
            "event_id": "e2",
            "kind": "death",
            "component_id": "K0",
            "first_strand": "A+",
            "second_strand": "B+",
        },
        {
            "event_id": "e3",
            "kind": "death",
            "component_id": "K0",
            "first_strand": "B-",
            "second_strand": "A-",
        },
    ]
    fixture["declared_slices"] = []
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="opposite"):
        validate_presentation(fixture)


def test_general_coupon_replaces_an_exact_input_word() -> None:
    fixture = fusion_coupon_fixture()
    validate_presentation(fixture)
    assert [
        strand["strand_id"]
        for strand in fixture["declared_slices"][2]["active_strands"]
    ] == ["Z+"]


def test_coupon_input_order_is_not_treated_as_an_unordered_set() -> None:
    fixture = fusion_coupon_fixture()
    fixture["events"][1]["input_strands"] = ["A-", "A+"]
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="exact declared"):
        validate_presentation(fixture)


def test_coupon_rejects_duplicate_output_strands() -> None:
    fixture = fusion_coupon_fixture()
    fixture["events"][1]["output_strands"].append(
        deepcopy(fixture["events"][1]["output_strands"][0])
    )
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="duplicate"):
        validate_presentation(fixture)


def test_coupon_rejects_unknown_output_component() -> None:
    fixture = fusion_coupon_fixture()
    fixture["events"][1]["output_strands"][0]["component_id"] = "unknown"
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="unknown component"):
        validate_presentation(fixture)


def test_coupon_cannot_silently_change_existing_strand_metadata() -> None:
    fixture = fusion_coupon_fixture()
    fixture["events"][2]["output_strands"][0]["orientation"] = "negative"
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="conflicting"):
        validate_presentation(fixture)


def test_v1_coupon_shape_is_rejected_instead_of_guessed() -> None:
    fixture = build_reference_fixture()
    coupon = fixture["events"][2]
    coupon["strands"] = coupon.pop("input_strands")
    coupon.pop("output_strands")
    coupon.pop("replace_at")
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="keys mismatch"):
        validate_presentation(fixture)


def test_v2_payload_is_rejected_instead_of_migrated() -> None:
    fixture = build_reference_fixture()
    fixture["schema"] = "twisted-yetter.kirby-presentation.v2"
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match="unsupported"):
        validate_presentation(fixture)


def test_empty_puncture_word_is_valid() -> None:
    fixture = build_reference_fixture()
    fixture["dotted_cuts"][0]["punctures"] = []
    validate_presentation(repaired(fixture))


def test_same_strand_may_occur_more_than_once() -> None:
    fixture = build_reference_fixture()
    first = deepcopy(fixture["dotted_cuts"][0]["punctures"][0])
    second = deepcopy(first)
    second["direction"] = "against_disk_orientation"
    second["character_exponent_sign"] = -1
    second["cut_position"] = 1
    fixture["dotted_cuts"][0]["punctures"] = [first, second]
    validate_presentation(repaired(fixture))


def test_multiple_dotted_disks_have_independent_words() -> None:
    fixture = build_reference_fixture()
    fixture["components"].append(
        {
            "component_id": "D1",
            "role": "dotted",
            "orientation": "positive",
            "integer_framing": 0,
            "blackboard_writhe": 0,
            "framing_correction": 0,
            "kirby_label": "omega-D",
        }
    )
    fixture["events"][-1:-1] = [
        {
            "event_id": "e12",
            "kind": "birth",
            "component_id": "D1",
            "positive_strand": "D1+",
            "negative_strand": "D1-",
            "insert_at": 2,
        },
        {
            "event_id": "e13",
            "kind": "death",
            "component_id": "D1",
            "first_strand": "D1+",
            "second_strand": "D1-",
        },
    ]
    second_cut = deepcopy(fixture["dotted_cuts"][0])
    second_cut["dotted_component_id"] = "D1"
    second_cut["punctures"] = []
    second_cut["source_locator"] = "fixture D1 empty puncture word"
    fixture["dotted_cuts"].append(second_cut)
    fixture["declared_slices"] = materialize_declared_slices(fixture)
    validate_presentation(repaired(fixture))


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (
            lambda value: value.__setitem__("dotted_cuts", []),
            "exactly one cut record",
        ),
        (
            lambda value: value["dotted_cuts"].append(
                deepcopy(value["dotted_cuts"][0])
            ),
            "duplicate IDs",
        ),
        (
            lambda value: value["dotted_cuts"][0].__setitem__(
                "dotted_component_id", "K0"
            ),
            "literal dotted",
        ),
        (
            lambda value: value["dotted_cuts"][0]["punctures"][0].__setitem__(
                "strand_id", "unknown"
            ),
            "unknown strand",
        ),
        (
            lambda value: value["dotted_cuts"][0]["punctures"][0].__setitem__(
                "two_handle_component_id", "S0"
            ),
            "ownership mismatch",
        ),
        (
            lambda value: value["dotted_cuts"][0]["punctures"][1].__setitem__(
                "cut_position", 0
            ),
            "list index",
        ),
        (
            lambda value: value["dotted_cuts"][0]["punctures"][0].__setitem__(
                "character_exponent_sign", -1
            ),
            "direction/exponent sign",
        ),
        (
            lambda value: value["dotted_cuts"][0].__setitem__(
                "source_refs", []
            ),
            "source_refs",
        ),
    ],
)
def test_invalid_dotted_cut_data_fails_closed(mutate, message: str) -> None:
    fixture = build_reference_fixture()
    mutate(fixture)
    fixture = repaired(fixture)
    with pytest.raises(PresentationValidationError, match=message):
        validate_presentation(fixture)
