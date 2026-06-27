from pathlib import Path

import pytest

from twisted_yetter.link_controls import (
    ELEMENTARY_LINK_CONTROLS_CLAIM_LEVEL,
    EMPTY_LINK_VALUE,
    ElementaryLinkValue,
    colored_framed_unknot_value,
    control_certificate,
    elementary_expected_value,
    load_fixture_expected_value,
)
from twisted_yetter.link_diagram import Component, LinkDiagram, hopf_link, unlink, unknot
from twisted_yetter.su2_level2 import SQRT2, QuadraticSurd, RootOfUnityPower


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")


def test_empty_link_fixture_has_value_one() -> None:
    value = load_fixture_expected_value(TOY_FIXTURE_DIR / "s4-empty.json", {})

    assert value == EMPTY_LINK_VALUE
    assert value == ElementaryLinkValue(QuadraticSurd(1), RootOfUnityPower(16, 0))


@pytest.mark.parametrize(
    ("label", "expected_dimension"),
    [
        ("0", QuadraticSurd(1)),
        ("1", SQRT2),
        ("2", QuadraticSurd(1)),
    ],
)
def test_zero_framed_colored_unknot_is_quantum_dimension(
    label: str,
    expected_dimension: QuadraticSurd,
) -> None:
    diagram = unknot("u", framing=0)

    assert elementary_expected_value(diagram, {"u": label}) == ElementaryLinkValue(
        expected_dimension,
        RootOfUnityPower(16, 0),
    )


def test_integer_framed_unknot_uses_symbolic_twist_power_times_dimension() -> None:
    assert colored_framed_unknot_value("1", framing=3) == ElementaryLinkValue(
        SQRT2,
        RootOfUnityPower(16, 9),
    )
    assert colored_framed_unknot_value("2", framing=-1) == ElementaryLinkValue(
        QuadraticSurd(1),
        RootOfUnityPower(16, 8),
    )


def test_framed_unknot_fixture_uses_machine_readable_framing() -> None:
    value = load_fixture_expected_value(
        TOY_FIXTURE_DIR / "cp2-plus-one-framed-unknot.json",
        {"cp2_h": "2"},
    )

    assert value == ElementaryLinkValue(QuadraticSurd(1), RootOfUnityPower(16, 8))


def test_split_unlink_fixture_is_multiplicative() -> None:
    value = load_fixture_expected_value(
        TOY_FIXTURE_DIR / "unlink-two-component.json",
        {"u1": "1", "u2": "1"},
    )

    assert value == colored_framed_unknot_value("1") * colored_framed_unknot_value("1")
    assert value == ElementaryLinkValue(QuadraticSurd(2), RootOfUnityPower(16, 0))


def test_split_unlink_with_nonzero_framings_is_product_of_component_controls() -> None:
    diagram = unlink(["left", "right"], framings=[2, -1])
    value = elementary_expected_value(diagram, {"left": "1", "right": "2"})

    assert value == ElementaryLinkValue(SQRT2, RootOfUnityPower(16, 14))


def test_control_certificate_records_source_needed_boundary() -> None:
    diagram = LinkDiagram("one", components=(Component("u", 0),))
    certificate = control_certificate(diagram, {"u": "1"})

    assert certificate["schema"] == "twisted-yetter.elementary-link-control.v1"
    assert certificate["status"] == "pass"
    assert certificate["expected_value"] == ElementaryLinkValue(
        SQRT2,
        RootOfUnityPower(16, 0),
    ).to_jsonable()
    assert certificate["claim"] == ELEMENTARY_LINK_CONTROLS_CLAIM_LEVEL
    assert certificate["claim"]["claim_level"].startswith("SOURCE NEEDED")
    assert "closed 4D invariant" in certificate["claim"]["not_scope"]


def test_rejects_crossing_diagram_so_hopf_stays_for_later_nodes() -> None:
    with pytest.raises(NotImplementedError, match="crossings"):
        elementary_expected_value(hopf_link(), {"h1": "0", "h2": "0"})


def test_label_mapping_must_match_components_exactly() -> None:
    diagram = unlink(["a", "b"])

    with pytest.raises(ValueError, match="missing=\\['b'\\]"):
        elementary_expected_value(diagram, {"a": "0"})

    with pytest.raises(ValueError, match="extra=\\['c'\\]"):
        elementary_expected_value(diagram, {"a": "0", "b": "1", "c": "2"})


def test_unknown_labels_and_noninteger_framings_are_rejected() -> None:
    with pytest.raises(ValueError, match="unknown SU\\(2\\)_2"):
        colored_framed_unknot_value("bad", framing=0)

    with pytest.raises(TypeError, match="integer"):
        colored_framed_unknot_value("1", framing=True)
