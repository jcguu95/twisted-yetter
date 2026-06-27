import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.exotic_input_scout import (
    BLOCKED_CLAIMS,
    EXOTIC_INPUT_SCOUT_SCHEMA,
    MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
    MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
    N24_N50_N55_UPSTREAM_BLOCKED_ID,
    NODE_ID,
    SOURCE_NEEDED_BLOCKER_ID,
    exotic_input_scout_ledger_artifact,
    stable_exotic_input_scout_ledger_json,
    validate_exotic_input_scout_ledger_artifact,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
N65_ARTIFACT = (
    REPO_ROOT / "experiments/results/exotic-input-scout/n65-exotic-input-scout.json"
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


def test_n65_scout_records_ranked_source_needed_inventory() -> None:
    artifact = exotic_input_scout_ledger_artifact()

    assert artifact["schema"] == EXOTIC_INPUT_SCOUT_SCHEMA
    assert artifact["status"] == "scout-data-blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == "candidate inventory/scouting ledger"
    assert artifact["candidate_count"] == 4
    assert artifact["ranked_candidate_ids"] == [
        "dolgachev-e1-23-vs-e1",
        "r8-vs-cp2-8bar",
        "akhmedov-park-cp2-2bar",
        "yasui-style-traces",
    ]
    assert artifact["first_candidate_id"] == "dolgachev-e1-23-vs-e1"
    assert artifact["any_candidate_certified"] is False
    assert artifact["any_machine_readable_exotic_input"] is False
    assert artifact["selected_n70_target"] is None
    assert artifact["recommended_next_route"] == "n72-dolgachev-source-capture"
    assert artifact["metadata_validation"]["valid"] is True


def test_n65_candidate_rows_state_source_and_data_gaps() -> None:
    artifact = exotic_input_scout_ledger_artifact()
    candidates = {
        candidate["candidate_id"]: candidate
        for candidate in artifact["candidate_inventory"]
    }

    dolgachev = candidates["dolgachev-e1-23-vs-e1"]
    assert dolgachev["scout_rank"] == 1
    assert dolgachev["source_status"] == "source-needed"
    assert dolgachev["certified_for_n70"] is False
    assert dolgachev["certified_for_n80"] is False
    assert dolgachev["reference_stub_ids"] == ["akbulut-dolgachev-surface"]
    assert SOURCE_NEEDED_BLOCKER_ID in dolgachev["blocked_reason_ids"]
    assert MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID in dolgachev[
        "blocked_reason_ids"
    ]
    assert MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID in dolgachev[
        "blocked_reason_ids"
    ]
    assert "machine-readable Kirby or handle data for both sides" in dolgachev[
        "data_requirements"
    ]

    yasui = candidates["yasui-style-traces"]
    assert yasui["comparison_level"] == "not-selected"
    assert "relative-computation" in yasui["marking_route"]
    assert "closed-pair" in yasui["data_requirements"][0]


def test_n65_global_blockers_include_upstream_gate_statuses() -> None:
    artifact = exotic_input_scout_ledger_artifact()

    assert artifact["input_statuses"] == {
        "ordinary_surgery_gate": "blocked",
        "decorated_kirby_gate": "blocked",
        "toy_closed_suite": "blocked",
    }
    assert artifact["blocker_reason_ids"] == [
        SOURCE_NEEDED_BLOCKER_ID,
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
        N24_N50_N55_UPSTREAM_BLOCKED_ID,
    ]
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["blockers"]}
    assert blockers[N24_N50_N55_UPSTREAM_BLOCKED_ID]["observed"] == {
        "n24": "blocked",
        "n50": "blocked",
        "n55": "blocked",
    }
    assert "canonical metadata" in blockers[SOURCE_NEEDED_BLOCKER_ID]["required"]


def test_n65_refuses_certification_computation_and_exotic_claims() -> None:
    artifact = exotic_input_scout_ledger_artifact()

    assert artifact["n70_exotic_input_certification_pass_allowed"] is False
    assert artifact["n80_exotic_computation_route_allowed"] is False
    assert artifact["certified_exotic_input_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["closed_4_manifold_invariant_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)
    assert "not source-audited exotic input certification" in artifact[
        "claim_boundary"
    ]

    with pytest.raises(ValueError, match="inventory ledger"):
        exotic_input_scout_ledger_artifact(claim_certified_input=True)
    with pytest.raises(ValueError, match="inventory ledger"):
        exotic_input_scout_ledger_artifact(claim_n70_pass=True)
    with pytest.raises(ValueError, match="inventory ledger"):
        exotic_input_scout_ledger_artifact(claim_n80_route=True)
    with pytest.raises(ValueError, match="inventory ledger"):
        exotic_input_scout_ledger_artifact(claim_exotic_detection=True)
    with pytest.raises(ValueError, match="inventory ledger"):
        exotic_input_scout_ledger_artifact(claim_closed_invariant=True)


def test_n65_scout_json_is_stable_exact_and_float_free() -> None:
    first = exotic_input_scout_ledger_artifact()
    second = exotic_input_scout_ledger_artifact()

    first_json = stable_exotic_input_scout_ledger_json(first)
    second_json = stable_exotic_input_scout_ledger_json(second)
    assert first_json == second_json
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    assert ".0" not in first_json
    _assert_no_float(first)


def test_n65_validator_rejects_missing_required_fields() -> None:
    validation = validate_exotic_input_scout_ledger_artifact(
        {"schema": EXOTIC_INPUT_SCOUT_SCHEMA}
    )

    assert validation["valid"] is False
    assert "candidate_inventory" in validation["missing_required_fields"]


def test_checked_in_n65_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N65_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = exotic_input_scout_ledger_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "inconclusive"
    assert exact_output["schema"] == generated["schema"]
    assert exact_output["status"] == "scout-data-blocked"
    assert exact_output["node_id"] == generated["node_id"]
    assert exact_output["ranked_candidate_ids"] == generated["ranked_candidate_ids"]
    assert exact_output["blocker_reason_ids"] == generated["blocker_reason_ids"]
    assert exact_output["input_statuses"] == generated["input_statuses"]
    assert exact_output["blocked_claims"] == generated["blocked_claims"]
    assert exact_output["metadata_validation"]["valid"] is True
