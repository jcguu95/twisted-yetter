import json
from pathlib import Path

import pytest

from twisted_yetter.finite_groups import TRIVIAL_GROUP, Z2_GROUP
from twisted_yetter.h2_marking import (
    BLOCKED_HIGH_CLAIMS,
    DOES_NOT_COMPUTE,
    H2_DECORATION_SCHEMA,
    h2_component_decoration_certificate,
    stable_h2_decoration_json,
    zero_h2_component_decoration_certificate,
)
from twisted_yetter.link_diagram import LINK_DIAGRAM_SCHEMA, LinkDiagram


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")
BASIS_KWARGS = {
    "basis_id": "toy-kirby-component-order",
    "basis_status": "Kirby component order only",
    "basis_source_status": "schema-test-safe / not certified H2 marking",
}


def test_s4_empty_fixture_has_explicit_zero_decoration() -> None:
    diagram = _load_fixture("s4-empty.json")

    certificate = zero_h2_component_decoration_certificate(
        diagram,
        TRIVIAL_GROUP,
        **BASIS_KWARGS,
    )

    assert certificate["schema"] == H2_DECORATION_SCHEMA
    assert certificate["status"] == "pass"
    assert certificate["claim_level"] == "schema-test-safe"
    assert certificate["finite_group_id"] == "trivial"
    assert certificate["component_ids"] == []
    assert certificate["decoration_vector"] == []
    assert certificate["decoration_by_component"] == {}
    assert certificate["zero_decoration"] is True
    assert certificate["all_trivial_decoration_explicit"] is True
    assert certificate["metadata_validation"]["valid"] is True


def test_cp2_unknot_z2_zero_decoration_records_component_id() -> None:
    diagram = _load_fixture("cp2-plus-one-framed-unknot.json")

    certificate = zero_h2_component_decoration_certificate(
        diagram,
        Z2_GROUP,
        **BASIS_KWARGS,
    )

    assert certificate["finite_group_id"] == "Z/2"
    assert certificate["component_ids"] == ["cp2_h"]
    assert certificate["decoration_vector"] == [
        {"component_id": "cp2_h", "element_id": "0", "element": [0]}
    ]
    assert certificate["decoration_by_component"] == {"cp2_h": "0"}
    assert certificate["ordinary_surgery_gate_status"] == "blocked"


def test_s2xs2_hopf_z2_decoration_aligns_vector_with_component_order() -> None:
    diagram = _load_fixture("s2x-s2-hopf-zero-framed.json")

    certificate = h2_component_decoration_certificate(
        diagram,
        Z2_GROUP,
        decoration_vector=[(1,), (0,)],
        **BASIS_KWARGS,
    )

    assert certificate["component_ids"] == ["s2_a", "s2_b"]
    assert certificate["decoration_vector"] == [
        {"component_id": "s2_a", "element_id": "1", "element": [1]},
        {"component_id": "s2_b", "element_id": "0", "element": [0]},
    ]
    assert certificate["decoration_by_component"] == {"s2_a": "1", "s2_b": "0"}
    assert certificate["zero_decoration"] is False
    assert certificate["basis_id"] == BASIS_KWARGS["basis_id"]
    assert certificate["basis_status"] == BASIS_KWARGS["basis_status"]
    assert certificate["basis_source_status"] == BASIS_KWARGS["basis_source_status"]


def test_mapping_input_is_canonicalized_to_diagram_component_order() -> None:
    diagram = _load_fixture("s2x-s2-hopf-zero-framed.json")

    certificate = h2_component_decoration_certificate(
        diagram,
        Z2_GROUP,
        decoration_by_component={"s2_b": (1,), "s2_a": (0,)},
        **BASIS_KWARGS,
    )

    assert certificate["decoration_vector"] == [
        {"component_id": "s2_a", "element_id": "0", "element": [0]},
        {"component_id": "s2_b", "element_id": "1", "element": [1]},
    ]
    assert list(certificate["decoration_by_component"]) == ["s2_a", "s2_b"]


def test_certificate_json_is_stable_and_has_no_float_markers() -> None:
    diagram = _load_fixture("s2x-s2-hopf-zero-framed.json")
    first = h2_component_decoration_certificate(
        diagram,
        Z2_GROUP,
        decoration_vector=[(1,), (1,)],
        **BASIS_KWARGS,
    )
    second = h2_component_decoration_certificate(
        diagram,
        Z2_GROUP,
        decoration_vector=[(1,), (1,)],
        **BASIS_KWARGS,
    )

    assert first == second
    assert stable_h2_decoration_json(first) == stable_h2_decoration_json(second)
    assert json.loads(stable_h2_decoration_json(first)) == first
    assert ".0" not in stable_h2_decoration_json(first)


def test_rejects_length_id_value_and_basis_errors() -> None:
    diagram = _load_fixture("s2x-s2-hopf-zero-framed.json")

    with pytest.raises(ValueError, match="length"):
        h2_component_decoration_certificate(
            diagram,
            Z2_GROUP,
            decoration_vector=[(0,)],
            **BASIS_KWARGS,
        )

    with pytest.raises(ValueError, match="component ids"):
        h2_component_decoration_certificate(
            diagram,
            Z2_GROUP,
            decoration_by_component={"s2_a": (0,), "missing": (1,)},
            **BASIS_KWARGS,
        )

    with pytest.raises(ValueError, match="group element"):
        h2_component_decoration_certificate(
            diagram,
            Z2_GROUP,
            decoration_vector=[(2,), (0,)],
            **BASIS_KWARGS,
        )

    with pytest.raises(ValueError, match="basis_id"):
        h2_component_decoration_certificate(
            diagram,
            Z2_GROUP,
            basis_id="",
            basis_status=BASIS_KWARGS["basis_status"],
            basis_source_status=BASIS_KWARGS["basis_source_status"],
        )


def test_high_claims_are_blocked_and_refused() -> None:
    diagram = _load_fixture("cp2-plus-one-framed-unknot.json")
    certificate = zero_h2_component_decoration_certificate(
        diagram,
        Z2_GROUP,
        **BASIS_KWARGS,
    )

    assert certificate["certified_h2_marking_claim_allowed"] is False
    assert certificate["homeomorphism_marking_claim_allowed"] is False
    assert certificate["closed_4_manifold_claim_allowed"] is False
    assert certificate["exotic_detection_claim_allowed"] is False
    assert certificate["blocked_high_claims"] == list(BLOCKED_HIGH_CLAIMS)
    assert "certified H2 marking" in certificate["does_not_compute"]
    assert set(certificate["does_not_compute"]) == set(DOES_NOT_COMPUTE)

    with pytest.raises(ValueError, match="refuses certified H2/homeomorphism"):
        h2_component_decoration_certificate(
            diagram,
            Z2_GROUP,
            claim_certified_h2_marking=True,
            **BASIS_KWARGS,
        )


def _load_fixture(name: str) -> LinkDiagram:
    payload = json.loads((TOY_FIXTURE_DIR / name).read_text())
    assert payload["schema"] == LINK_DIAGRAM_SCHEMA
    return LinkDiagram.from_json(payload)
