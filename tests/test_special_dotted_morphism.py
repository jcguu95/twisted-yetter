import json
from pathlib import Path

import pytest

from experiments.scripts.akbulut_yasui_figure21_morse_draft import (
    COMPONENT_BY_PIECE,
    COMPONENT_ORDER,
    build_figure21_right,
)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import (
    compile_projected_morphism,
    preflight_horizontal_disk_corridor,
    replay_forms,
)


def zero_puncture_input():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", between=("red1.left", "red1.right"))
    m.cap("A1")
    m.cap("red1")
    return m.forms, {"red1": "red", "A1": "A"}


def one_puncture_input():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", at="far-right")
    m.cross(over="A1.left", under="red1.right")
    m.cross(over="red1.left", under="A1.left")
    m.cap("red1")
    m.cap("A1")
    return m.forms, {"red1": "red", "A1": "A"}


def two_puncture_input():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", at="far-right")
    m.cross(over="A1.left", under="red1.right")
    m.cross(over="red1.left", under="A1.left")
    m.cross(over="A1.left", under="red1.left")
    m.cross(over="red1.right", under="A1.left")
    m.cap("red1")
    m.cap("A1")
    return m.forms, {"red1": "red", "A1": "A"}


@pytest.mark.parametrize(
    ("factory", "expected"),
    [(zero_puncture_input, 0), (one_puncture_input, 1), (two_puncture_input, 2)],
)
def test_special_disk_compiler_counts_small_puncture_controls(factory, expected):
    forms, component_by_piece = factory()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    certificate = ir["special_disk_certificates"][0]
    assert certificate["forced_cut_count"] == expected
    assert certificate["signed_disk_intersections"] in (
        certificate["d2_linking_row"],
        [-value for value in certificate["d2_linking_row"]],
    )
    assert replay_forms(ir["ordinary_forms"])


def test_special_disk_compiler_rejects_self_crossing_special_component():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cross(over="red1.left", under="red1.right")
    m.cap("red1")
    with pytest.raises(ValueError, match="self-crossings"):
        compile_projected_morphism(
            m.forms,
            component_by_piece={"red1": "red"},
            special_components=("red",),
        )


def test_one_puncture_has_a_horizontal_projector_slice():
    forms, component_by_piece = one_puncture_input()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    preflight = preflight_horizontal_disk_corridor(forms, ir)
    assert preflight["status"] == "PASS_COMMON_HORIZONTAL_PROJECTOR_SLICE"
    assert preflight["projector_strands"] == ["A1.left"]


def test_two_punctures_on_one_strand_fail_closed_as_nonhorizontal():
    forms, component_by_piece = two_puncture_input()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    preflight = preflight_horizontal_disk_corridor(forms, ir)
    assert preflight["status"] == "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR"
    assert preflight["duplicate_active_strands"] == ["A1.left"]


def test_multiple_special_components_parse_but_numeric_support_fails_closed():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("blue1", at="far-right")
    m.cap("blue1")
    m.cap("red1")
    ir = compile_projected_morphism(
        m.forms,
        component_by_piece={"red1": "red", "blue1": "blue"},
        special_components=("red", "blue"),
    )
    assert ir["special_component_count"] == 2
    assert ir["numeric_support"] == (
        "UNSUPPORTED_MULTIPLE_SPECIAL_COMPONENTS_FAIL_CLOSED"
    )


def test_figure21_disk_certificate_regression():
    builder = build_figure21_right()
    ir = compile_projected_morphism(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
        component_order=COMPONENT_ORDER,
    )
    certificate = ir["special_disk_certificates"][0]
    assert len(ir["component_order"]) == 12
    assert ir["crossing_count"] == 106
    assert certificate["red_projection_self_crossings"] == 0
    assert certificate["boundary_crossing_count"] == 78
    assert certificate["inside_arc_interval_count"] == 39
    assert certificate["forced_cut_count"] == 29
    assert certificate["d2_linking_row"] == [5, 2, 0, 0, 0, 0, 6, -2, 5, -2, 1]
    assert certificate["signed_disk_intersections"] == [
        -5,
        -2,
        0,
        0,
        0,
        0,
        -6,
        2,
        -5,
        2,
        -1,
    ]
    assert certificate["disk_to_linking_orientation_sign"] == -1
    assert ir["vacuum_projectors"][0]["corridor_status"] == "NOT_LINEARIZED"
    preflight = preflight_horizontal_disk_corridor(builder.forms, ir)
    assert preflight["status"] == "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR"
    assert len(preflight["nonmonotone_cut_ids"]) == 8


def test_figure21_topology_artifact_is_conservative_and_reproducible():
    artifact = json.loads(
        Path(
            "experiments/results/akbulut-yasui/"
            "figure21-right-special-disk-topology-v1.json"
        ).read_text()
    )
    assert artifact["status"] == "MORPHISM_TOPOLOGY_CONTROLS_PASS_NOT_LINEARIZED"
    assert artifact["mathematical_status"] == (
        "DRAFT_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM"
    )
    assert artifact["git_dirty"] is False
    assert artifact["link_certificate"]["determinant"] == 1
    assert artifact["link_certificate"]["rank"] == 12
    assert artifact["link_certificate"]["signature"]["signature"] == -8
    certificate = artifact["projected_morphism_ir"]["special_disk_certificates"][0]
    assert certificate["forced_cut_count"] == 29
    assert certificate["signed_disk_intersections"] == [
        -value for value in certificate["d2_linking_row"]
    ]
    assert artifact["corridor_preflight"]["status"] == (
        "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR"
    )
