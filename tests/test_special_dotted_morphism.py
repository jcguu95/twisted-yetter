import pytest

from experiments.scripts.akbulut_yasui_figure21_morse_draft import (
    COMPONENT_BY_PIECE,
    build_figure21_right,
)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import (
    compile_projected_morphism,
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
