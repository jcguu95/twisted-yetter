import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.scalability_dry_run import (
    BLOCKED_CLAIMS,
    N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID,
    N50_DECORATED_GATE_BLOCKED_BLOCKER_ID,
    N55_TOY_CLOSED_BLOCKED_BLOCKER_ID,
    N70_DATA_BLOCKED_BLOCKER_ID,
    NO_REAL_EXOTIC_INPUT_BLOCKER_ID,
    NODE_ID,
    SCALABILITY_DRY_RUN_SCHEMA,
    scalability_dry_run_artifact,
    stable_scalability_dry_run_json,
    validate_scalability_dry_run_artifact,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
N75_ARTIFACT = (
    REPO_ROOT / "experiments/results/scalability/n75-scalability-dry-run.json"
)


def _assert_no_float(value: object) -> None:
    if isinstance(value, float):
        raise AssertionError(f"unexpected float value: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_float(item)
    elif isinstance(value, list | tuple):
        for item in value:
            _assert_no_float(item)


def test_n75_records_dry_run_blocked_status_and_upstream_statuses() -> None:
    artifact = scalability_dry_run_artifact()

    assert artifact["schema"] == SCALABILITY_DRY_RUN_SCHEMA
    assert artifact["status"] == "dry-run-blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == "dry-run/readiness ledger"
    assert artifact["input_statuses"] == {
        "ordinary_surgery_gate": "blocked",
        "candidate_validation_suite": "pass",
        "presentation_pair_registry": "pass",
        "decorated_kirby_gate": "blocked",
        "toy_closed_suite": "blocked",
        "exotic_input_certification": "data-blocked",
    }
    assert artifact["metadata_validation"]["valid"] is True


def test_n75_toy_scale_inventory_counts_existing_metadata_only() -> None:
    artifact = scalability_dry_run_artifact()
    inventory = artifact["toy_scale_inventory"]

    assert inventory["n36_case_count"] == 8
    assert inventory["n36_unique_fixture_count"] == 4
    assert inventory["n36_unique_diagram_count"] == 4
    assert inventory["n36_total_component_slots"] == 12
    assert inventory["n36_total_sector_slots"] == 12
    assert inventory["n45_pair_count"] == 5
    assert inventory["n45_matrix_pair_count"] == 3
    assert inventory["n50_pair_classification_count"] == 8
    assert inventory["n50_evaluator_input_pair_count"] == 0
    assert inventory["n55_toy_case_count"] == 8
    assert inventory["n70_candidate_count"] == 4
    assert inventory["real_exotic_input_count"] == 0
    assert inventory["certified_n80_target_count"] == 0
    assert "repo-local toy/candidate metadata" in inventory["counting_scope"]


def test_n75_blocks_n80_real_benchmark_and_high_claims() -> None:
    artifact = scalability_dry_run_artifact()

    assert artifact["readiness_routes"]["n80-exotic-computation"] == "blocked"
    assert artifact["readiness_routes"]["real_exotic_scaling_benchmark"] == "blocked"
    assert artifact["n80_exotic_computation_route_allowed"] is False
    assert artifact["real_exotic_input_scaling_claim_allowed"] is False
    assert artifact["performance_benchmark_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["closed_4_manifold_invariant_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)

    with pytest.raises(ValueError, match="dry-run-blocked"):
        scalability_dry_run_artifact(claim_n80_route=True)
    with pytest.raises(ValueError, match="dry-run-blocked"):
        scalability_dry_run_artifact(claim_exotic_computation=True)
    with pytest.raises(ValueError, match="dry-run-blocked"):
        scalability_dry_run_artifact(claim_real_scaling_success=True)
    with pytest.raises(ValueError, match="dry-run-blocked"):
        scalability_dry_run_artifact(claim_exotic_detection=True)


def test_n75_blockers_reference_n70_n55_n50_and_n24() -> None:
    artifact = scalability_dry_run_artifact()

    expected = [
        N70_DATA_BLOCKED_BLOCKER_ID,
        N55_TOY_CLOSED_BLOCKED_BLOCKER_ID,
        N50_DECORATED_GATE_BLOCKED_BLOCKER_ID,
        N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID,
        NO_REAL_EXOTIC_INPUT_BLOCKER_ID,
    ]
    assert artifact["blocked_reason_ids"] == expected
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["blockers"]}
    assert set(blockers) == set(expected)
    assert blockers[N70_DATA_BLOCKED_BLOCKER_ID]["observed"] == "data-blocked"
    assert blockers[N55_TOY_CLOSED_BLOCKED_BLOCKER_ID]["observed"] == "blocked"
    assert blockers[N50_DECORATED_GATE_BLOCKED_BLOCKER_ID]["observed"] == "blocked"
    assert blockers[N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID]["observed"] == "blocked"
    assert blockers[NO_REAL_EXOTIC_INPUT_BLOCKER_ID]["observed"] == (
        "zero certified real exotic input targets"
    )
    assert "n70-exotic-input-certification.json" in blockers[
        N70_DATA_BLOCKED_BLOCKER_ID
    ]["upstream_artifact"]


def test_n75_json_is_stable_exact_and_float_free() -> None:
    first = scalability_dry_run_artifact()
    second = scalability_dry_run_artifact()

    first_json = stable_scalability_dry_run_json(first)
    second_json = stable_scalability_dry_run_json(second)
    assert first_json == second_json
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    assert ".0" not in first_json
    _assert_no_float(first)


def test_validator_rejects_missing_required_fields() -> None:
    validation = validate_scalability_dry_run_artifact(
        {"schema": SCALABILITY_DRY_RUN_SCHEMA}
    )

    assert validation["valid"] is False
    assert "toy_scale_inventory" in validation["missing_required_fields"]


def test_checked_in_n75_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N75_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = scalability_dry_run_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "inconclusive"
    assert exact_output == generated
    assert exact_output["status"] == "dry-run-blocked"
    assert exact_output["metadata_validation"]["valid"] is True
    assert exact_output["readiness_routes"]["n80-exotic-computation"] == "blocked"
    assert exact_output["toy_scale_inventory"]["real_exotic_input_count"] == 0
