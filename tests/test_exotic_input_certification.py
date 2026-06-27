import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.exotic_input_certification import (
    BLOCKED_CLAIMS,
    EXOTIC_INPUT_CERTIFICATION_SCHEMA,
    MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
    MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
    MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
    N24_N50_UPSTREAM_BLOCKED_ID,
    N55_TOY_CLOSED_SUITE_BLOCKER_ID,
    NODE_ID,
    exotic_input_certification_ledger_artifact,
    stable_exotic_input_certification_ledger_json,
    validate_exotic_input_certification_ledger_artifact,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
N70_ARTIFACT = (
    REPO_ROOT
    / "experiments/inputs/exotic-pairs/n70-exotic-input-certification.json"
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


def test_n70_ledger_consumes_upstream_blocked_gates() -> None:
    artifact = exotic_input_certification_ledger_artifact()

    assert artifact["schema"] == EXOTIC_INPUT_CERTIFICATION_SCHEMA
    assert artifact["status"] == "data-blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == "executable gate/blocked ledger"
    assert artifact["input_statuses"] == {
        "ordinary_surgery_gate": "blocked",
        "decorated_kirby_gate": "blocked",
        "toy_closed_suite": "blocked",
    }
    assert artifact["candidate_count"] == 4
    assert artifact["any_candidate_certified"] is False
    assert artifact["selected_computation_target"] is None
    assert artifact["metadata_validation"]["valid"] is True


def test_n70_global_blockers_are_structured_reason_ids() -> None:
    artifact = exotic_input_certification_ledger_artifact()

    expected = [
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
        N55_TOY_CLOSED_SUITE_BLOCKER_ID,
        N24_N50_UPSTREAM_BLOCKED_ID,
    ]
    assert artifact["blocker_reason_ids"] == expected
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["blockers"]}
    assert set(blockers) == set(expected)
    assert blockers[N55_TOY_CLOSED_SUITE_BLOCKER_ID]["observed"] == "blocked"
    assert blockers[N24_N50_UPSTREAM_BLOCKED_ID]["observed"] == {
        "n24": "blocked",
        "n50": "blocked",
    }
    assert "machine-readable" in blockers[
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID
    ]["required"]


def test_n70_candidate_results_remain_data_blocked_inventory() -> None:
    artifact = exotic_input_certification_ledger_artifact()
    candidates = {case["candidate_id"]: case for case in artifact["candidate_results"]}

    assert set(candidates) == {
        "dolgachev-e1-23-vs-e1",
        "r8-vs-cp2-8bar",
        "akhmedov-park-cp2-2bar",
        "yasui-style-traces",
    }
    dolgachev = candidates["dolgachev-e1-23-vs-e1"]
    assert dolgachev["scout_rank"] == 1
    assert dolgachev["certified_for_n80"] is False
    assert dolgachev["status"] == "data-blocked"
    assert MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID in dolgachev[
        "blocked_reason_ids"
    ]
    assert MISSING_SOURCE_PAGE_CAPTURE_BLOCKER_ID in dolgachev[
        "blocked_reason_ids"
    ]
    assert MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID in dolgachev[
        "blocked_reason_ids"
    ]


def test_n70_blocks_n80_route_and_high_claims() -> None:
    artifact = exotic_input_certification_ledger_artifact()

    assert artifact["route_decision"]["n80-exotic-computation"] == "blocked"
    assert artifact["n80_exotic_computation_route_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["marked_distinction_claim_allowed"] is False
    assert artifact["cork_canonical_distinction_claim_allowed"] is False
    assert artifact["unmarked_total_function_distinction_claim_allowed"] is False
    assert artifact["closed_4_manifold_invariant_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)

    with pytest.raises(ValueError, match="data-blocked"):
        exotic_input_certification_ledger_artifact(claim_n80_route=True)
    with pytest.raises(ValueError, match="data-blocked"):
        exotic_input_certification_ledger_artifact(claim_exotic_detection=True)
    with pytest.raises(ValueError, match="data-blocked"):
        exotic_input_certification_ledger_artifact(claim_marked_distinction=True)
    with pytest.raises(ValueError, match="data-blocked"):
        exotic_input_certification_ledger_artifact(claim_closed_invariant=True)


def test_n70_ledger_json_is_stable_exact_and_float_free() -> None:
    first = exotic_input_certification_ledger_artifact()
    second = exotic_input_certification_ledger_artifact()

    first_json = stable_exotic_input_certification_ledger_json(first)
    second_json = stable_exotic_input_certification_ledger_json(second)
    assert first_json == second_json
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    assert ".0" not in first_json
    _assert_no_float(first)


def test_validator_rejects_missing_required_fields() -> None:
    validation = validate_exotic_input_certification_ledger_artifact(
        {"schema": EXOTIC_INPUT_CERTIFICATION_SCHEMA}
    )

    assert validation["valid"] is False
    assert "candidate_results" in validation["missing_required_fields"]


def test_checked_in_n70_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N70_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = exotic_input_certification_ledger_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "fail"
    assert exact_output["schema"] == generated["schema"]
    assert exact_output["status"] == "data-blocked"
    assert exact_output["node_id"] == generated["node_id"]
    assert exact_output["blocker_reason_ids"] == generated["blocker_reason_ids"]
    assert exact_output["input_statuses"] == generated["input_statuses"]
    assert exact_output["route_decision"] == generated["route_decision"]
    assert exact_output["blocked_claims"] == generated["blocked_claims"]
    assert exact_output["metadata_validation"]["valid"] is True
