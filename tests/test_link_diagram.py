import json
from pathlib import Path

import pytest

from twisted_yetter.link_diagram import (
    LINK_DIAGRAM_SCHEMA,
    Component,
    Crossing,
    LinkDiagram,
    StrandRef,
    cp2_diagram,
    hopf_link,
    s2x_s2_diagram,
    s4_diagram,
    unlink,
    unknot,
)


def test_unknot_and_framed_unknot_are_valid_diagrams() -> None:
    zero = unknot("u", framing=0)
    framed = unknot("u_plus", framing=3)

    assert zero.linking_matrix() == ((0,),)
    assert framed.linking_matrix() == ((3,),)
    assert framed.to_matrix_presentation().framings == (3,)


def test_unlink_and_hopf_link_derive_expected_linking_matrices() -> None:
    two_component_unlink = unlink(["a", "b"], framings=[2, -1])
    positive_hopf = hopf_link(component_ids=("a", "b"), framings=(0, 0), linking=1)
    negative_hopf = hopf_link(component_ids=("a", "b"), framings=(0, 0), linking=-1)

    assert two_component_unlink.linking_matrix() == ((2, 0), (0, -1))
    assert positive_hopf.linking_matrix() == ((0, 1), (1, 0))
    assert negative_hopf.linking_matrix() == ((0, -1), (-1, 0))


def test_toy_kirby_diagrams_match_existing_matrix_examples() -> None:
    assert s4_diagram().linking_matrix() == ()
    assert cp2_diagram().linking_matrix() == ((1,),)
    assert s2x_s2_diagram().linking_matrix() == ((0, 1), (1, 0))


def test_round_trips_json_payloads() -> None:
    diagram = hopf_link(component_ids=("left", "right"), framings=(4, 5), linking=1)
    payload = diagram.to_json()

    assert payload["schema"] == LINK_DIAGRAM_SCHEMA
    assert json.loads(json.dumps(payload)) == payload
    assert LinkDiagram.from_json(payload).linking_matrix() == ((4, 1), (1, 5))


@pytest.mark.parametrize(
    ("fixture_name", "expected_matrix"),
    [
        ("s4-empty.json", ()),
        ("cp2-plus-one-framed-unknot.json", ((1,),)),
        ("unlink-two-component.json", ((0, 0), (0, 0))),
        ("hopf-link.json", ((0, 1), (1, 0))),
        ("s2x-s2-hopf-zero-framed.json", ((0, 1), (1, 0))),
    ],
)
def test_toy_diagram_fixtures_are_valid(
    fixture_name: str, expected_matrix: tuple[tuple[int, ...], ...]
) -> None:
    fixture_path = Path("experiments/inputs/toy-diagrams") / fixture_name
    payload = json.loads(fixture_path.read_text())

    assert LinkDiagram.from_json(payload).linking_matrix() == expected_matrix


def test_rejects_missing_framing_and_unknown_component_ids() -> None:
    with pytest.raises(ValueError, match="framing"):
        LinkDiagram.from_json(
            {
                "schema": LINK_DIAGRAM_SCHEMA,
                "diagram_id": "bad",
                "components": [{"id": "a", "dotted": False, "orientation": "+"}],
                "crossings": [],
            }
        )

    with pytest.raises(ValueError, match="unknown component"):
        LinkDiagram(
            "bad-crossing",
            components=(Component("a", 0),),
            crossings=(
                Crossing(
                    "x1",
                    1,
                    over=StrandRef("a", "a1"),
                    under=StrandRef("missing", "m1"),
                ),
            ),
        )


def test_rejects_malformed_crossings() -> None:
    base_payload = {
        "schema": LINK_DIAGRAM_SCHEMA,
        "diagram_id": "bad-crossing-payload",
        "components": [
            {"id": "a", "framing": 0, "dotted": False, "orientation": "+"},
            {"id": "b", "framing": 0, "dotted": False, "orientation": "+"},
        ],
        "crossings": [
            {
                "id": "x1",
                "sign": 1,
                "over": {"component_id": "a", "arc_id": "a1"},
                "under": {"component_id": "b", "arc_id": "b1"},
            }
        ],
    }

    malformed = dict(base_payload)
    malformed["crossings"] = [{**base_payload["crossings"][0], "sign": 0}]
    with pytest.raises(ValueError, match="-1 or 1"):
        LinkDiagram.from_json(malformed)

    malformed = dict(base_payload)
    malformed["crossings"] = [{**base_payload["crossings"][0], "over": []}]
    with pytest.raises(TypeError, match="over"):
        LinkDiagram.from_json(malformed)


def test_rejects_odd_inter_component_signed_crossing_sum() -> None:
    diagram = LinkDiagram(
        "one-crossing-not-closed-as-linking-sanity",
        components=(Component("a", 0), Component("b", 0)),
        crossings=(
            Crossing(
                "x1",
                1,
                over=StrandRef("a", "a1"),
                under=StrandRef("b", "b1"),
            ),
        ),
    )

    with pytest.raises(ValueError, match="even"):
        diagram.linking_matrix()
