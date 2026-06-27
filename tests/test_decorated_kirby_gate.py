import json

import pytest

from twisted_yetter.decorated_kirby_gate import (
    BASIS_MATRIX_BLOCKER_ID,
    BLOCKED_FINAL_CLAIMS,
    COMPONENT_LINEAGE_BLOCKER_ID,
    DECORATED_KIRBY_GATE_ARTIFACT,
    DECORATED_KIRBY_GATE_SCHEMA,
    DECORATED_MOVE_CERT_BLOCKER_ID,
    MATRIX_LEVEL_ONLY_BLOCKER_ID,
    N35_PLANNED_CALLS_BLOCKER_ID,
    NODE_ID,
    NOT_GENERATED_LINK_MOVE_BLOCKER_ID,
    ORDINARY_SURGERY_BLOCKER_ID,
    PAIR_DRY_RUN_BLOCKER_ID,
    SOURCE_PROOF_BLOCKER_ID,
    decorated_kirby_gate_artifact_certificate,
    decorated_kirby_gate_artifact,
    stable_decorated_kirby_gate_json,
    validate_decorated_kirby_gate_artifact,
)
from twisted_yetter.presentation_pairs import presentation_pair_registry_artifact


def test_gate_consumes_n45_registry_and_classifies_builtin_pairs() -> None:
    registry = presentation_pair_registry_artifact()
    artifact = decorated_kirby_gate_artifact(registry)

    assert artifact["schema"] == DECORATED_KIRBY_GATE_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["input_registry_node_id"] == "n45-kirby-presentation-pair-generator"
    assert artifact["input_registry_validation"]["valid"] is True
    assert artifact["ordinary_surgery_gate_status"] == "blocked"
    assert artifact["diagram_pair_count"] == registry["diagram_pair_count"]
    assert artifact["matrix_pair_count"] == registry["matrix_pair_count"]
    assert artifact["pair_count"] == (
        registry["diagram_pair_count"] + registry["matrix_pair_count"]
    )
    assert artifact["classification_status_counts"] == {
        "pass": 0,
        "blocked": 5,
        "not-applicable": 0,
        "metadata-only": 3,
    }
    assert artifact["all_pairs_blocked_or_metadata_only"] is True
    assert artifact["all_pairs_have_structured_blockers"] is True
    assert artifact["final_decorated_gate_passed"] is False
    assert artifact["evaluator_comparison_input_pair_ids"] == []

    pair_ids = {pair["pair_id"] for pair in artifact["pair_classifications"]}
    assert pair_ids == {
        pair["pair_id"]
        for pair in registry["pairs"] + registry["matrix_presentation_pairs"]
    }
    assert all(
        pair["gate_decision"] == "blocked"
        for pair in artifact["pair_classifications"]
    )
    assert all(
        pair["usable_as_evaluator_comparison_input"] is False
        for pair in artifact["pair_classifications"]
    )
    assert all(
        pair["final_decorated_gate_passed"] is False
        for pair in artifact["pair_classifications"]
    )


def test_diagram_pair_failures_are_structured_stable_reason_ids() -> None:
    artifact = decorated_kirby_gate_artifact()
    expected_reasons = {
        PAIR_DRY_RUN_BLOCKER_ID,
        NOT_GENERATED_LINK_MOVE_BLOCKER_ID,
        DECORATED_MOVE_CERT_BLOCKER_ID,
        COMPONENT_LINEAGE_BLOCKER_ID,
        BASIS_MATRIX_BLOCKER_ID,
        N35_PLANNED_CALLS_BLOCKER_ID,
        ORDINARY_SURGERY_BLOCKER_ID,
        SOURCE_PROOF_BLOCKER_ID,
    }

    for pair in artifact["pair_classifications"]:
        if pair["registry_section"] != "pairs":
            continue
        assert set(pair["blocked_reason_ids"]) == expected_reasons
        assert pair["required_pair_fields_present"] is True
        for reason in pair["blocked_reasons"]:
            assert reason["status"] == "blocked"
            assert reason["reason_id"] in expected_reasons
            assert reason["claim_boundary"]

    component_order = next(
        pair
        for pair in artifact["pair_classifications"]
        if pair["pair_id"] == "component-order-unlink-z2-mixed-dry-run"
    )
    lineage_reason = next(
        reason
        for reason in component_order["blocked_reasons"]
        if reason["reason_id"] == COMPONENT_LINEAGE_BLOCKER_ID
    )
    assert "not a transformed diagram" in lineage_reason["component_lineage_status"]


def test_matrix_pairs_are_metadata_only_not_evaluator_inputs() -> None:
    artifact = decorated_kirby_gate_artifact()
    matrix_pairs = [
        pair
        for pair in artifact["pair_classifications"]
        if pair["registry_section"] == "matrix_presentation_pairs"
    ]

    assert {pair["pair_id"] for pair in matrix_pairs} == {
        "hyperbolic-shear",
        "odd-indefinite-swap",
        "odd-positive-shear",
    }
    for pair in matrix_pairs:
        assert pair["status"] == "metadata-only"
        assert pair["gate_decision"] == "blocked"
        assert pair["matrix_level_consistency_check"]["status"] == "pass"
        assert MATRIX_LEVEL_ONLY_BLOCKER_ID in pair["blocked_reason_ids"]
        assert NOT_GENERATED_LINK_MOVE_BLOCKER_ID in pair["blocked_reason_ids"]
        assert DECORATED_MOVE_CERT_BLOCKER_ID in pair["blocked_reason_ids"]
        assert ORDINARY_SURGERY_BLOCKER_ID in pair["blocked_reason_ids"]
        assert BASIS_MATRIX_BLOCKER_ID not in pair["blocked_reason_ids"]
        assert pair["usable_as_evaluator_comparison_input"] is False

    matrix_summary = artifact["matrix_level_consistency"]
    assert matrix_summary["status"] == "metadata-only"
    assert matrix_summary["matrix_pair_count"] == 3
    assert set(matrix_summary["machine_checked_matrix_pair_ids"]) == {
        "hyperbolic-shear",
        "odd-indefinite-swap",
        "odd-positive-shear",
    }


def test_gate_blocks_high_claims_and_refuses_claim_promoter_flags() -> None:
    artifact = decorated_kirby_gate_artifact()

    assert artifact["presentation_equivalence_theorem_claim_allowed"] is False
    assert artifact["decorated_kirby_move_theorem_claim_allowed"] is False
    assert artifact["closed_4_manifold_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["blocked_final_claims"] == list(BLOCKED_FINAL_CLAIMS)
    assert artifact["downstream_decision"]["n55-toy-closed-suite"] == "blocked"

    with pytest.raises(ValueError, match="refuses presentation theorem"):
        decorated_kirby_gate_artifact(claim_presentation_equivalence_theorem=True)
    with pytest.raises(ValueError, match="refuses presentation theorem"):
        decorated_kirby_gate_artifact(claim_decorated_kirby_move_theorem=True)
    with pytest.raises(ValueError, match="refuses presentation theorem"):
        decorated_kirby_gate_artifact(claim_closed_invariant=True)
    with pytest.raises(ValueError, match="refuses presentation theorem"):
        decorated_kirby_gate_artifact(claim_exotic_detection=True)


def test_gate_json_is_stable_exact_and_float_free() -> None:
    first = decorated_kirby_gate_artifact()
    second = decorated_kirby_gate_artifact()

    first_json = stable_decorated_kirby_gate_json(first)
    second_json = stable_decorated_kirby_gate_json(second)
    assert first_json == second_json
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    assert ".0" not in first_json
    assert first["metadata_validation"]["valid"] is True


def test_gate_certificate_envelope_is_valid_and_points_to_artifact() -> None:
    certificate = decorated_kirby_gate_artifact_certificate()

    assert certificate["status"] == "inconclusive"
    assert certificate["generator_script"] == "src/twisted_yetter/decorated_kirby_gate.py"
    assert certificate["argv"][-1] == DECORATED_KIRBY_GATE_ARTIFACT
    assert certificate["exact_output"]["schema"] == DECORATED_KIRBY_GATE_SCHEMA
    assert certificate["exact_output"]["classification_status_counts"] == {
        "pass": 0,
        "blocked": 5,
        "not-applicable": 0,
        "metadata-only": 3,
    }


def test_validator_rejects_missing_required_fields() -> None:
    validation = validate_decorated_kirby_gate_artifact(
        {"schema": DECORATED_KIRBY_GATE_SCHEMA}
    )

    assert validation["valid"] is False
    assert "pair_classifications" in validation["missing_required_fields"]
