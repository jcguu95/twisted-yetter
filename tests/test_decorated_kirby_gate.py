import json

import pytest

from twisted_yetter.decorated_kirby_gate import (
    BASIS_MATRIX_BLOCKER_ID,
    BLOCKED_FINAL_CLAIMS,
    COMPONENT_LINEAGE_BLOCKER_ID,
    DECORATED_KIRBY_GATE_SCHEMA,
    DECORATED_MOVE_CERT_BLOCKER_ID,
    NODE_ID,
    ORDINARY_SURGERY_BLOCKER_ID,
    PAIR_DRY_RUN_BLOCKER_ID,
    SOURCE_PROOF_BLOCKER_ID,
    decorated_kirby_gate_artifact,
    stable_decorated_kirby_gate_json,
    validate_decorated_kirby_gate_artifact,
)
from twisted_yetter.presentation_pairs import presentation_pair_registry_artifact


def test_gate_consumes_n45_registry_and_blocks_all_builtin_pairs() -> None:
    registry = presentation_pair_registry_artifact()
    artifact = decorated_kirby_gate_artifact(registry)

    assert artifact["schema"] == DECORATED_KIRBY_GATE_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["input_registry_node_id"] == "n45-kirby-presentation-pair-generator"
    assert artifact["input_registry_validation"]["valid"] is True
    assert artifact["ordinary_surgery_gate_status"] == "blocked"
    assert artifact["pair_count"] == registry["pair_count"]
    assert artifact["all_pairs_blocked"] is True
    assert artifact["all_pairs_have_structured_blockers"] is True
    assert artifact["final_decorated_gate_passed"] is False

    pair_ids = {pair["pair_id"] for pair in artifact["pair_classifications"]}
    assert pair_ids == {pair["pair_id"] for pair in registry["pairs"]}
    assert all(pair["status"] == "blocked" for pair in artifact["pair_classifications"])
    assert all(
        pair["final_decorated_gate_passed"] is False
        for pair in artifact["pair_classifications"]
    )


def test_pair_failures_are_structured_stable_reason_ids() -> None:
    artifact = decorated_kirby_gate_artifact()
    expected_reasons = {
        PAIR_DRY_RUN_BLOCKER_ID,
        DECORATED_MOVE_CERT_BLOCKER_ID,
        COMPONENT_LINEAGE_BLOCKER_ID,
        BASIS_MATRIX_BLOCKER_ID,
        ORDINARY_SURGERY_BLOCKER_ID,
        SOURCE_PROOF_BLOCKER_ID,
    }

    for pair in artifact["pair_classifications"]:
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


def test_validator_rejects_missing_required_fields() -> None:
    validation = validate_decorated_kirby_gate_artifact(
        {"schema": DECORATED_KIRBY_GATE_SCHEMA}
    )

    assert validation["valid"] is False
    assert "pair_classifications" in validation["missing_required_fields"]
