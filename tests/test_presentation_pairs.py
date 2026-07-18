import json
from pathlib import Path

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.presentation_pairs import (
    BLOCKED_HIGH_CLAIMS,
    DEFAULT_PAIR_SPECS,
    DOES_NOT_PROVE,
    PRESENTATION_PAIR_REGISTRY_SCHEMA,
    presentation_pair_registry_artifact_certificate,
    presentation_pair_registry_artifact,
    stable_presentation_pair_registry_json,
    validate_presentation_pair_registry_metadata,
)


def test_registry_contains_required_toy_pair_inventory() -> None:
    artifact = presentation_pair_registry_artifact()
    pairs = {pair["pair_id"]: pair for pair in artifact["pairs"]}

    assert artifact["schema"] == PRESENTATION_PAIR_REGISTRY_SCHEMA
    assert artifact["status"] == "pass"
    assert artifact["node_id"] == "n45-kirby-presentation-pair-generator"
    assert artifact["claim_level"] == "computed evidence scaffold"
    assert artifact["ordinary_surgery_gate_status"] == "blocked"
    assert artifact["pair_count"] == len(DEFAULT_PAIR_SPECS)
    assert set(pairs) == {
        "identity-s4-trivial-zero",
        "identity-cp2-z2-zero",
        "identity-cp2-z2-nonzero",
        "component-order-unlink-z2-mixed-dry-run",
        "component-relabel-s2xs2-hopf-z2-mixed-swap-dry-run",
    }

    identity = pairs["identity-s4-trivial-zero"]
    assert identity["left"]["fixture_path"] == (
        "experiments/inputs/toy-diagrams/s4-empty.json"
    )
    assert identity["left"]["diagram_id"] == "s4-empty-kirby-diagram"
    assert identity["right"]["diagram_id"] == "s4-empty-kirby-diagram"
    assert identity["relation_type"] == "identity"
    assert identity["relation_status"] == "candidate/dry-run"

    zero = pairs["identity-cp2-z2-zero"]
    assert zero["relation_type"] == "identity/zero-decoration"
    assert zero["left"]["zero_decoration"] is True
    assert zero["left"]["component_sector_ids"] == ["0"]
    assert zero["component_lineage"]["left_to_right"] == {"cp2_h": "cp2_h"}

    nonzero = pairs["identity-cp2-z2-nonzero"]
    assert nonzero["relation_type"] == "identity/nonzero-Z2-decoration"
    assert nonzero["left"]["zero_decoration"] is False
    assert nonzero["left"]["component_sector_ids"] == ["1"]
    assert nonzero["pair_kind"] == "presentation-sanity-pair"
    assert "not a closed invariant claim" in nonzero["claim_boundary"]


def test_component_order_dry_run_pair_is_explicitly_not_a_slide_proof() -> None:
    artifact = presentation_pair_registry_artifact()
    pairs = {pair["pair_id"]: pair for pair in artifact["pairs"]}
    pair = pairs["component-order-unlink-z2-mixed-dry-run"]

    assert pair["relation_type"] == "component-order-placeholder"
    assert pair["relation_status"] == "candidate/dry-run"
    assert pair["left"]["component_ids"] == ["u1", "u2"]
    assert pair["right"]["component_ids"] == ["u1", "u2"]
    assert pair["component_lineage"]["left_to_right"] == {"u1": "u2", "u2": "u1"}
    assert "not a transformed diagram" in pair["component_lineage"]["status"]
    assert pair["basis_map"]["claim_certified"] is False
    assert pair["basis_map"]["matrix"] is None
    assert "no component-order operation has been applied" in pair["basis_map"]["status"]

    hopf = pairs["component-relabel-s2xs2-hopf-z2-mixed-swap-dry-run"]
    assert hopf["pair_kind"] == "component-relabel-dry-run"
    assert hopf["left"]["component_sector_ids"] == ["1", "0"]
    assert hopf["right"]["component_sector_ids"] == ["0", "1"]
    assert hopf["component_lineage"]["left_to_right"] == {
        "s2_a": "s2_b",
        "s2_b": "s2_a",
    }
    assert "no diagram relabel operation is generated" in hopf["component_lineage"]["status"]


def test_n50_can_see_required_fields_on_every_pair() -> None:
    artifact = presentation_pair_registry_artifact()

    required_pair_fields = {
        "pair_id",
        "left",
        "right",
        "relation_type",
        "relation_status",
        "component_lineage",
        "basis_map",
        "pair_kind",
        "move_metadata",
        "decorated_core_case_refs",
        "decorated_core_cases",
        "claim_boundary",
        "claim_level",
        "source_status",
        "does_not_prove",
    }
    required_side_fields = {
        "fixture_path",
        "diagram_id",
        "decorated_core_case_id",
        "component_ids",
        "finite_group_id",
        "decoration_by_component",
        "zero_decoration",
        "component_sector_ids",
    }
    for pair in artifact["pairs"]:
        assert required_pair_fields <= set(pair)
        assert required_side_fields <= set(pair["left"])
        assert required_side_fields <= set(pair["right"])
        assert pair["relation_status"] == "candidate/dry-run"
        assert pair["n50_required_fields_present"] is True
        assert len(pair["decorated_core_cases"]) == 2
        for case in pair["decorated_core_cases"]:
            assert case["metadata_validation"]["valid"] is True


def test_matrix_level_basis_change_pairs_are_registered_separately() -> None:
    artifact = presentation_pair_registry_artifact()
    matrix_pairs = {pair["pair_id"]: pair for pair in artifact["matrix_presentation_pairs"]}

    assert artifact["matrix_pair_count"] == 3
    assert artifact["all_matrix_pairs_machine_checked"] is True
    assert set(matrix_pairs) == {
        "hyperbolic-shear",
        "odd-indefinite-swap",
        "odd-positive-shear",
    }

    shear = matrix_pairs["hyperbolic-shear"]
    assert shear["pair_kind"] == "matrix-basis-change-pair"
    assert shear["relation_status"] == "matrix-level-certified"
    assert shear["basis_map"]["claim_certified"] is True
    assert shear["basis_map"]["matrix"] == [[1, 1], [0, 1]]
    assert shear["basis_map"]["inverse_matrix"] == [[1, -1], [0, 1]]
    assert shear["decoration_transform_mod2"] == [[1, 1], [0, 1]]
    assert shear["character_transform_mod2"] == [[1, 0], [1, 1]]
    assert shear["source"]["matrix"] == [[0, 1], [1, 0]]
    assert shear["target"]["matrix"] == [[0, 1], [1, 2]]
    assert "not a link-diagram handle-slide proof" in shear["claim_boundary"]


def test_registry_json_is_stable_exact_and_float_free() -> None:
    artifact = presentation_pair_registry_artifact()

    assert artifact["all_pairs_json_stable"] is True
    assert artifact["all_pairs_exact_json_no_float_markers"] is True
    assert artifact["all_matrix_pairs_machine_checked"] is True
    assert artifact["metadata_validation"]["valid"] is True
    for pair in artifact["pairs"]:
        assert pair["stable_json_roundtrip"] is True
        assert pair["exact_json_no_float_markers"] is True
    for pair in artifact["matrix_presentation_pairs"]:
        assert pair["stable_json_roundtrip"] is True
        assert pair["exact_json_no_float_markers"] is True

    first_json = stable_presentation_pair_registry_json(artifact)
    second_json = stable_presentation_pair_registry_json(
        presentation_pair_registry_artifact()
    )
    assert first_json == second_json
    assert json.loads(first_json) == artifact
    assert ".0" not in first_json


def test_does_not_prove_blocks_equivalence_invariant_and_exotic_claims() -> None:
    artifact = presentation_pair_registry_artifact()

    assert artifact["proof_claim_allowed"] is False
    assert artifact["presentation_equivalence_claim_allowed"] is False
    assert artifact["decorated_kirby_move_proof_claim_allowed"] is False
    assert artifact["closed_4_manifold_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["blocked_high_claims"] == list(BLOCKED_HIGH_CLAIMS)
    assert artifact["does_not_prove"] == list(DOES_NOT_PROVE)
    for forbidden in (
        "presentation equivalence",
        "Kirby move proof",
        "closed invariant",
        "exotic claims",
    ):
        assert forbidden in artifact["does_not_prove"]
        for pair in artifact["pairs"]:
            assert forbidden in pair["does_not_prove"]
        for pair in artifact["matrix_presentation_pairs"]:
            assert forbidden in pair["does_not_prove"]


def test_artifact_certificate_records_reproducible_n45_registry() -> None:
    certificate = presentation_pair_registry_artifact_certificate()

    validate_certificate(certificate)
    assert certificate["generator_script"] == "src/twisted_yetter/presentation_pairs.py"
    assert certificate["exact_output"]["schema"] == PRESENTATION_PAIR_REGISTRY_SCHEMA
    assert certificate["exact_output"]["diagram_pair_count"] == len(DEFAULT_PAIR_SPECS)
    assert certificate["exact_output"]["matrix_pair_count"] == 3
    assert certificate["exact_output"]["ordinary_surgery_gate_status"] == "blocked"


def test_checked_in_n45_artifact_matches_current_registry_shape() -> None:
    path = Path("experiments/results/presentation-pairs/n45-presentation-pair-generator.json")
    if not path.exists():
        return

    certificate = json.loads(path.read_text())
    validate_certificate(certificate)
    exact_output = certificate["exact_output"]
    assert exact_output["schema"] == PRESENTATION_PAIR_REGISTRY_SCHEMA
    assert exact_output["metadata_validation"]["valid"] is True
    assert exact_output["pair_count"] == len(DEFAULT_PAIR_SPECS)
    assert exact_output["matrix_pair_count"] == 3


def test_registry_metadata_validator_rejects_missing_required_fields() -> None:
    validation = validate_presentation_pair_registry_metadata(
        {"claim_level": "computed evidence scaffold"}
    )

    assert validation["valid"] is False
    assert "pairs" in validation["missing_required_fields"]
