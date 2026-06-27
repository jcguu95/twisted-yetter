import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.exotic_computation import (
    BLOCKED_CLAIMS,
    EXOTIC_COMPUTATION_SCHEMA,
    N70_NO_CERTIFIED_INPUT_BLOCKER_ID,
    N70_NO_SELECTED_TARGET_BLOCKER_ID,
    N75_DRY_RUN_BLOCKED_BLOCKER_ID,
    NO_BENCHMARK_INPUT_BLOCKER_ID,
    NO_INVARIANT_INPUT_BLOCKER_ID,
    NODE_ID,
    exotic_computation_artifact,
    stable_exotic_computation_json,
    validate_exotic_computation_artifact,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
N80_ARTIFACT = (
    REPO_ROOT / "experiments/results/exotic-computation/n80-exotic-computation.json"
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


def test_n80_records_terminal_blocked_dependency_statuses() -> None:
    artifact = exotic_computation_artifact()

    assert artifact["schema"] == EXOTIC_COMPUTATION_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == "terminal blocked computation gate verdict"
    assert artifact["dependency_statuses"] == {
        "n70_status": "blocked",
        "n70_source_status": "source-needed",
        "n70_certified_input_count": 0,
        "n70_candidate_count": 4,
        "n70_any_candidate_certified": False,
        "n70_selected_computation_target": None,
        "n70_n80_route_allowed": False,
        "n75_status": "dry-run-blocked",
        "n75_readiness_status": "dry-run-blocked",
        "n75_n80_route_allowed": False,
        "n75_real_benchmark_available": False,
    }
    assert artifact["metadata_validation"]["valid"] is True


def test_n80_refuses_computation_values_benchmarks_and_result_routes() -> None:
    artifact = exotic_computation_artifact()

    assert artifact["computation_policy"] == {
        "invariant_run_allowed": False,
        "exotic_values_allowed": False,
        "comparison_certificate_allowed": False,
        "benchmark_allowed": False,
        "n82_result_classification_route_allowed": False,
        "source_guess_allowed": False,
        "network_allowed": False,
        "core_evaluator_change_allowed": False,
    }
    assert artifact["computation_run_summary"] == {
        "did_run_computation": False,
        "invariant_runs": [],
        "exotic_values": [],
        "benchmarks": [],
        "source_fetches": [],
        "engine_invocations": [],
        "reason": (
            "n70 certified_input_count=0 and selected_computation_target=null; "
            "n75 status=dry-run-blocked"
        ),
    }
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)

    with pytest.raises(ValueError, match="n80-exotic-computation is blocked"):
        exotic_computation_artifact(claim_invariant_run=True)
    with pytest.raises(ValueError, match="n80-exotic-computation is blocked"):
        exotic_computation_artifact(claim_exotic_values=True)
    with pytest.raises(ValueError, match="n80-exotic-computation is blocked"):
        exotic_computation_artifact(claim_benchmark=True)
    with pytest.raises(ValueError, match="n80-exotic-computation is blocked"):
        exotic_computation_artifact(claim_result_route=True)


def test_n80_blockers_explain_n70_and_n75_gate_closure() -> None:
    artifact = exotic_computation_artifact()

    expected = [
        N70_NO_CERTIFIED_INPUT_BLOCKER_ID,
        N70_NO_SELECTED_TARGET_BLOCKER_ID,
        N75_DRY_RUN_BLOCKED_BLOCKER_ID,
        NO_INVARIANT_INPUT_BLOCKER_ID,
        NO_BENCHMARK_INPUT_BLOCKER_ID,
    ]
    assert artifact["blocked_reason_ids"] == expected
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["blockers"]}
    assert set(blockers) == set(expected)
    assert blockers[N70_NO_CERTIFIED_INPUT_BLOCKER_ID]["observed"] == 0
    assert blockers[N70_NO_SELECTED_TARGET_BLOCKER_ID]["observed"] is None
    assert blockers[N75_DRY_RUN_BLOCKED_BLOCKER_ID]["observed"] == "dry-run-blocked"
    assert blockers[NO_INVARIANT_INPUT_BLOCKER_ID]["observed"] == (
        "no machine-readable certified exotic diagrams or H2 marking"
    )
    assert blockers[NO_BENCHMARK_INPUT_BLOCKER_ID]["observed"] == (
        "no certified real exotic size data"
    )


def test_n80_next_steps_route_back_to_source_acquisition_not_fake_compute() -> None:
    artifact = exotic_computation_artifact()

    assert artifact["next_steps"] == [
        "offline/source acquisition for n72",
        "rerun n72-dolgachev-source-capture after source records exist",
        "rerun n73-exotic-diagram-digitization after exact page/figure data exist",
        "rerun n74-exotic-h2-marking-certification after machine-readable diagrams exist",
        "rerun n70-exotic-input-certification until one certified target is selected",
        "rerun n75-scalability-dry-run only after n70 has a pass artifact",
    ]
    assert "Dolgachev calculation" in artifact["source_status"]
    assert "not a no-go theorem" in artifact["claim_boundary"]


def test_n80_json_is_stable_exact_and_float_free() -> None:
    first = exotic_computation_artifact()
    second = exotic_computation_artifact()

    first_json = stable_exotic_computation_json(first)
    second_json = stable_exotic_computation_json(second)
    assert first_json == second_json
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    assert ".0" not in first_json
    _assert_no_float(first)


def test_n80_validator_rejects_missing_required_fields() -> None:
    validation = validate_exotic_computation_artifact(
        {"schema": EXOTIC_COMPUTATION_SCHEMA}
    )

    assert validation["valid"] is False
    assert "dependency_statuses" in validation["missing_required_fields"]


def test_checked_in_n80_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N80_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = exotic_computation_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "inconclusive"
    assert exact_output == generated
    assert exact_output["status"] == "blocked"
    assert exact_output["metadata_validation"]["valid"] is True
    assert exact_output["computation_run_summary"]["did_run_computation"] is False
    assert exact_output["dependency_statuses"]["n70_certified_input_count"] == 0
