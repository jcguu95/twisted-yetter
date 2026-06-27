import json
from pathlib import Path

import pytest

from twisted_yetter.hopf_controls import (
    HOPF_CONTROL_CLAIM_LEVEL,
    hopf_control_certificate,
    hopf_expected_value,
    load_hopf_fixture_expected_value,
    positive_hopf_sanity,
)
from twisted_yetter.link_diagram import (
    Component,
    Crossing,
    LinkDiagram,
    StrandRef,
    hopf_link,
    unlink,
)
from twisted_yetter.su2_level2 import SQRT2, QuadraticSurd, hopf_control_entry


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")


@pytest.mark.parametrize(
    ("fixture_name", "labels", "expected"),
    [
        ("hopf-link.json", {"h1": "0", "h2": "1"}, SQRT2),
        ("hopf-link.json", {"h1": "1", "h2": "1"}, QuadraticSurd(0)),
        ("hopf-link.json", {"h1": "1", "h2": "2"}, -SQRT2),
        ("s2x-s2-hopf-zero-framed.json", {"s2_a": "2", "s2_b": "2"}, QuadraticSurd(1)),
    ],
)
def test_hopf_fixture_values_are_s_over_s00_exactly(
    fixture_name: str,
    labels: dict[str, str],
    expected: QuadraticSurd,
) -> None:
    value = load_hopf_fixture_expected_value(TOY_FIXTURE_DIR / fixture_name, labels)

    assert value == expected
    left, right = labels.values()
    assert value == hopf_control_entry(left, right)


@pytest.mark.parametrize("fixture_name", ["hopf-link.json", "s2x-s2-hopf-zero-framed.json"])
def test_hopf_fixture_sanity_records_crossings_and_linking(fixture_name: str) -> None:
    diagram_path = TOY_FIXTURE_DIR / fixture_name
    diagram = LinkDiagram.from_json(json.loads(diagram_path.read_text()))

    assert positive_hopf_sanity(diagram) == {
        "component_ids": list(diagram.component_ids),
        "framings": [0, 0],
        "crossing_count": 2,
        "crossing_signs": [1, 1],
        "linking_matrix": [[0, 1], [1, 0]],
    }


def test_hopf_certificate_records_source_needed_local_convention_boundary() -> None:
    diagram = hopf_link()
    certificate = hopf_control_certificate(diagram, {"h1": "1", "h2": "2"})

    assert certificate["schema"] == "twisted-yetter.hopf-link-control.v1"
    assert certificate["status"] == "pass"
    assert certificate["expected_value"] == (-SQRT2).to_jsonable()
    assert certificate["claim"] == HOPF_CONTROL_CLAIM_LEVEL
    assert certificate["claim"]["claim_level"].startswith("SOURCE NEEDED")
    assert "general crossing evaluator" in certificate["claim"]["not_scope"]
    assert "twisted formula" in certificate["claim"]["not_scope"]


def test_hopf_controls_reject_no_crossing_and_non_hopf_crossing_diagrams() -> None:
    with pytest.raises(NotImplementedError, match="exactly two components"):
        hopf_expected_value(LinkDiagram("empty", components=()), {})

    with pytest.raises(NotImplementedError, match="exactly two crossings"):
        hopf_expected_value(unlink(["u1", "u2"]), {"u1": "0", "u2": "0"})

    with pytest.raises(NotImplementedError, match="positive crossings"):
        hopf_expected_value(hopf_link(linking=-1), {"h1": "0", "h2": "0"})


def test_hopf_controls_reject_nonzero_framing_and_self_crossing() -> None:
    with pytest.raises(NotImplementedError, match="0-framed"):
        hopf_expected_value(hopf_link(framings=(1, 0)), {"h1": "0", "h2": "0"})

    self_crossing = LinkDiagram(
        "self-crossing-not-hopf",
        components=(Component("a", 0), Component("b", 0)),
        crossings=(
            Crossing("x1", 1, StrandRef("a", "a1"), StrandRef("a", "a2")),
            Crossing("x2", 1, StrandRef("a", "a3"), StrandRef("b", "b1")),
        ),
    )
    with pytest.raises(NotImplementedError, match="self-crossings"):
        hopf_expected_value(self_crossing, {"a": "0", "b": "0"})


def test_label_mapping_and_unknown_labels_are_rejected() -> None:
    diagram = hopf_link()

    with pytest.raises(ValueError, match="missing=\\['h2'\\]"):
        hopf_expected_value(diagram, {"h1": "0"})

    with pytest.raises(ValueError, match="extra=\\['x'\\]"):
        hopf_expected_value(diagram, {"h1": "0", "h2": "1", "x": "2"})

    with pytest.raises(ValueError, match="unknown SU\\(2\\)_2"):
        hopf_expected_value(diagram, {"h1": "bad", "h2": "0"})
