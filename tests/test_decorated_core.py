import json
from pathlib import Path

import pytest

from twisted_yetter.decorated_core import (
    BLOCKED_HIGH_CLAIMS,
    DECORATED_CORE_SCHEMA,
    DOES_NOT_COMPUTE,
    decorated_core_input_artifact,
    stable_decorated_core_json,
    validate_decorated_core_artifact_metadata,
)
from twisted_yetter.finite_groups import TRIVIAL_GROUP, Z2_GROUP
from twisted_yetter.link_diagram import LINK_DIAGRAM_SCHEMA, LinkDiagram


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")
BASIS_KWARGS = {
    "basis_id": "toy-kirby-component-order",
    "basis_status": "Kirby component order only",
    "basis_source_status": "schema-test-safe / not certified H2 marking",
}


def test_empty_s4_trivial_artifact_is_explicit_and_metadata_only() -> None:
    diagram = _load_fixture("s4-empty.json")

    artifact = decorated_core_input_artifact(diagram, TRIVIAL_GROUP, **BASIS_KWARGS)

    assert artifact["schema"] == DECORATED_CORE_SCHEMA
    assert artifact["status"] == "pass"
    assert artifact["claim_level"] == "computed evidence scaffold"
    assert artifact["ordinary_surgery_gate_status"] == "blocked"
    assert artifact["diagram_id"] == "s4-empty-kirby-diagram"
    assert artifact["component_ids"] == []
    assert artifact["finite_group_id"] == "trivial"
    assert artifact["decoration_by_component"] == {}
    assert artifact["component_sector_metadata"] == []
    assert artifact["zero_decoration"] is True
    assert artifact["metadata_validation"]["valid"] is True


def test_cp2_z2_zero_decoration_routes_to_identity_sector_metadata() -> None:
    diagram = _load_fixture("cp2-plus-one-framed-unknot.json")

    artifact = decorated_core_input_artifact(
        diagram,
        Z2_GROUP,
        decoration_by_component={"cp2_h": (0,)},
        **BASIS_KWARGS,
    )

    assert artifact["diagram_id"] == "cp2-plus-one-framed-unknot"
    assert artifact["component_ids"] == ["cp2_h"]
    assert artifact["decoration_by_component"] == {"cp2_h": "0"}
    assert artifact["candidate_coefficient_certificate"]["finite_group_id"] == "Z/2"

    component_sector = artifact["component_sector_metadata"][0]
    assert component_sector["component_id"] == "cp2_h"
    assert component_sector["decoration_element_id"] == "0"
    assert component_sector["candidate_sector_id"] == "0"
    assert component_sector["candidate_sector_element"] == [0]
    assert [
        coefficient["character_value"]["value"]
        for coefficient in component_sector["candidate_coefficients"]
    ] == ["1", "1", "1"]


def test_cp2_z2_nonzero_decoration_references_nontrivial_sector() -> None:
    diagram = _load_fixture("cp2-plus-one-framed-unknot.json")

    artifact = decorated_core_input_artifact(
        diagram,
        Z2_GROUP,
        decoration_vector=[(1,)],
        **BASIS_KWARGS,
    )

    component_sector = artifact["component_sector_metadata"][0]
    assert artifact["decoration_by_component"] == {"cp2_h": "1"}
    assert artifact["zero_decoration"] is False
    assert component_sector["candidate_sector_id"] == "1"
    assert component_sector["candidate_sector_element"] == [1]
    assert [
        coefficient["character_value"]["value"]
        for coefficient in component_sector["candidate_coefficients"]
    ] == ["1", "-1", "1"]
    assert component_sector["coefficient_certificate_ref"] == (
        "candidate_coefficient_certificate"
    )


def test_s2xs2_hopf_component_decorations_align_to_component_order() -> None:
    diagram = _load_fixture("s2x-s2-hopf-zero-framed.json")

    artifact = decorated_core_input_artifact(
        diagram,
        Z2_GROUP,
        decoration_by_component={"s2_b": (0,), "s2_a": (1,)},
        **BASIS_KWARGS,
    )

    assert artifact["diagram_id"] == "s2x-s2-hopf-zero-framed"
    assert artifact["component_ids"] == ["s2_a", "s2_b"]
    assert artifact["decoration_by_component"] == {"s2_a": "1", "s2_b": "0"}
    assert [
        entry["component_id"] for entry in artifact["component_sector_metadata"]
    ] == ["s2_a", "s2_b"]
    assert [
        entry["candidate_sector_id"] for entry in artifact["component_sector_metadata"]
    ] == ["1", "0"]
    assert artifact["basis"]["basis_id"] == BASIS_KWARGS["basis_id"]


def test_json_is_stable_exact_and_has_no_float_markers() -> None:
    diagram = _load_fixture("s2x-s2-hopf-zero-framed.json")
    first = decorated_core_input_artifact(
        diagram,
        Z2_GROUP,
        decoration_vector=[(1,), (1,)],
        **BASIS_KWARGS,
    )
    second = decorated_core_input_artifact(
        diagram,
        Z2_GROUP,
        decoration_vector=[(1,), (1,)],
        **BASIS_KWARGS,
    )

    assert first == second
    assert stable_decorated_core_json(first) == stable_decorated_core_json(second)
    assert json.loads(stable_decorated_core_json(first)) == first
    assert ".0" not in stable_decorated_core_json(first)


def test_required_fields_and_scope_boundaries_are_explicit() -> None:
    diagram = _load_fixture("cp2-plus-one-framed-unknot.json")
    artifact = decorated_core_input_artifact(diagram, Z2_GROUP, **BASIS_KWARGS)

    assert artifact["theorem_claim_allowed"] is False
    assert artifact["closed_4_manifold_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["decorated_kirby_move_proof_claim_allowed"] is False
    assert artifact["blocked_high_claims"] == list(BLOCKED_HIGH_CLAIMS)
    assert artifact["does_not_compute"] == list(DOES_NOT_COMPUTE)
    for item in (
        "link evaluation",
        "Kirby color sum",
        "decorated Kirby move proof",
        "closed invariant",
        "exotic detection",
    ):
        assert item in artifact["does_not_compute"]

    validation = validate_decorated_core_artifact_metadata(
        {"claim_level": "computed evidence scaffold"}
    )
    assert validation["valid"] is False
    assert "diagram_id" in validation["missing_required_fields"]


def test_high_claims_and_unknown_claim_levels_are_refused() -> None:
    diagram = _load_fixture("cp2-plus-one-framed-unknot.json")

    with pytest.raises(ValueError, match="refuses theorem"):
        decorated_core_input_artifact(
            diagram,
            Z2_GROUP,
            claim_theorem=True,
            **BASIS_KWARGS,
        )
    with pytest.raises(ValueError, match="refuses theorem"):
        decorated_core_input_artifact(
            diagram,
            Z2_GROUP,
            claim_closed_invariant=True,
            **BASIS_KWARGS,
        )
    with pytest.raises(ValueError, match="refuses theorem"):
        decorated_core_input_artifact(
            diagram,
            Z2_GROUP,
            claim_exotic_detection=True,
            **BASIS_KWARGS,
        )
    with pytest.raises(ValueError, match="unsupported n35 claim level"):
        decorated_core_input_artifact(
            diagram,
            Z2_GROUP,
            claim_level="closed-4-manifold-invariant",
            **BASIS_KWARGS,
        )


def _load_fixture(name: str) -> LinkDiagram:
    payload = json.loads((TOY_FIXTURE_DIR / name).read_text())
    assert payload["schema"] == LINK_DIAGRAM_SCHEMA
    return LinkDiagram.from_json(payload)
