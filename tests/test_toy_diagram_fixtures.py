import json
from pathlib import Path

import pytest

from twisted_yetter.link_diagram import LINK_DIAGRAM_SCHEMA, LinkDiagram


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")

EXPECTED_FIXTURES = {
    "s4-empty.json": {
        "diagram_id": "s4-empty-kirby-diagram",
        "component_ids": (),
        "framings": (),
        "crossing_count": 0,
        "linking_matrix": (),
    },
    "cp2-plus-one-framed-unknot.json": {
        "diagram_id": "cp2-plus-one-framed-unknot",
        "component_ids": ("cp2_h",),
        "framings": (1,),
        "crossing_count": 0,
        "linking_matrix": ((1,),),
    },
    "unlink-two-component.json": {
        "diagram_id": "unlink-2",
        "component_ids": ("u1", "u2"),
        "framings": (0, 0),
        "crossing_count": 0,
        "linking_matrix": ((0, 0), (0, 0)),
    },
    "hopf-link.json": {
        "diagram_id": "hopf-linking-1",
        "component_ids": ("h1", "h2"),
        "framings": (0, 0),
        "crossing_count": 2,
        "linking_matrix": ((0, 1), (1, 0)),
    },
    "s2x-s2-hopf-zero-framed.json": {
        "diagram_id": "s2x-s2-hopf-zero-framed",
        "component_ids": ("s2_a", "s2_b"),
        "framings": (0, 0),
        "crossing_count": 2,
        "linking_matrix": ((0, 1), (1, 0)),
    },
}


def _load_fixture(name: str) -> LinkDiagram:
    payload = json.loads((TOY_FIXTURE_DIR / name).read_text())
    assert payload["schema"] == LINK_DIAGRAM_SCHEMA
    return LinkDiagram.from_json(payload)


def test_toy_fixture_inventory_matches_directory() -> None:
    fixture_names = {path.name for path in TOY_FIXTURE_DIR.glob("*.json")}

    assert fixture_names == set(EXPECTED_FIXTURES)


@pytest.mark.parametrize("fixture_name", sorted(EXPECTED_FIXTURES))
def test_toy_fixtures_load_with_expected_schema_and_ids(fixture_name: str) -> None:
    expected = EXPECTED_FIXTURES[fixture_name]
    diagram = _load_fixture(fixture_name)

    assert diagram.diagram_id == expected["diagram_id"]
    assert diagram.component_ids == expected["component_ids"]
    assert diagram.framings == expected["framings"]
    assert len(diagram.crossings) == expected["crossing_count"]


@pytest.mark.parametrize("fixture_name", sorted(EXPECTED_FIXTURES))
def test_toy_fixtures_have_expected_linking_matrix(fixture_name: str) -> None:
    expected = EXPECTED_FIXTURES[fixture_name]
    diagram = _load_fixture(fixture_name)

    assert diagram.linking_matrix() == expected["linking_matrix"]
    assert diagram.to_matrix_presentation().matrix == expected["linking_matrix"]


@pytest.mark.parametrize("fixture_name", sorted(EXPECTED_FIXTURES))
def test_toy_fixtures_have_unique_component_and_crossing_ids(fixture_name: str) -> None:
    diagram = _load_fixture(fixture_name)
    crossing_ids = tuple(crossing.crossing_id for crossing in diagram.crossings)

    assert len(diagram.component_ids) == len(set(diagram.component_ids))
    assert len(crossing_ids) == len(set(crossing_ids))
