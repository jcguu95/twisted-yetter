import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.dolgachev_source_capture import (
    BLOCKED_CLAIMS,
    CANDIDATE_ID,
    DIGITIZATION_INPUT_BLOCKER_ID,
    DOLGACHEV_SOURCE_CAPTURE_SCHEMA,
    EXACT_CITATION_BLOCKER_ID,
    MARKING_SOURCE_BLOCKER_ID,
    NODE_ID,
    REFERENCE_ID,
    SOURCE_CAPTURE_BLOCKER_ID,
    dolgachev_source_capture_ledger_artifact,
    stable_dolgachev_source_capture_ledger_json,
    validate_dolgachev_source_capture_ledger_artifact,
)
from twisted_yetter.exotic_input_scout import (
    MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
    MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
    SOURCE_NEEDED_BLOCKER_ID,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
N72_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/source-capture/n72-dolgachev-source-capture.json"
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


def test_n72_records_dolgachev_source_needed_inventory() -> None:
    artifact = dolgachev_source_capture_ledger_artifact()

    assert artifact["schema"] == DOLGACHEV_SOURCE_CAPTURE_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["source_status"] == "source-needed"
    assert artifact["node_id"] == NODE_ID
    assert artifact["candidate_id"] == CANDIDATE_ID
    assert artifact["candidate_display_name"] == "Dolgachev E(1)_{2,3} vs E(1)"
    assert artifact["upstream_node"] == "n65-exotic-input-scout"
    assert artifact["upstream_selected_candidate_status"] == {
        "source_status": "source-needed",
        "certified_for_n70": False,
        "certified_for_n80": False,
        "comparison_level": "not-certified",
    }
    assert artifact["metadata_validation"]["valid"] is True


def test_n72_reference_inventory_is_stub_only() -> None:
    artifact = dolgachev_source_capture_ledger_artifact()
    inventory = artifact["reference_inventory"]

    assert len(inventory) == 1
    reference = inventory[0]
    assert reference["reference_id"] == REFERENCE_ID
    assert reference["record_path"] == "wiki/references/akbulut-dolgachev-surface.org"
    assert reference["record_status"] == "stub/source-needed"
    assert reference["content_hash_status"] == "missing"
    assert reference["capture_time_status"] == "missing"
    assert reference["proved_in_source_claims"] == []
    assert "no local snapshot" in reference["locator_status"]
    assert "cannot support diagram" in reference["claim_boundary"]


def test_n72_lists_exact_missing_source_and_digitization_slots() -> None:
    artifact = dolgachev_source_capture_ledger_artifact()

    slot_ids = {
        slot["slot_id"] for slot in artifact["required_exact_source_slots"]
    }
    assert slot_ids == {
        "bibliographic-metadata",
        "source-snapshot-hash",
        "diagram-page-figure-ids",
        "handle-claim-citations",
        "comparison-claim-citations",
    }
    assert "exact diagram page/figure ids" in artifact["missing_fields"]
    assert "component ids for both sides" in artifact[
        "needed_kirby_handle_diagram_fields"
    ]
    assert "basis-change matrices for simplification and H2 comparison" in artifact[
        "digitization_input_requirements"
    ]
    assert artifact["n70_blocker_ids_addressed"] == [
        SOURCE_NEEDED_BLOCKER_ID,
        MISSING_MACHINE_READABLE_DIAGRAMS_BLOCKER_ID,
        MISSING_H2_MARKING_CERTIFICATE_BLOCKER_ID,
    ]


def test_n72_blockers_and_claim_boundary_remain_blocked() -> None:
    artifact = dolgachev_source_capture_ledger_artifact()

    assert artifact["blocker_reason_ids"] == [
        SOURCE_CAPTURE_BLOCKER_ID,
        EXACT_CITATION_BLOCKER_ID,
        DIGITIZATION_INPUT_BLOCKER_ID,
        MARKING_SOURCE_BLOCKER_ID,
    ]
    assert artifact["n73_ready"] is False
    assert artifact["n74_ready"] is False
    assert artifact["n70_exotic_input_certification_pass_allowed"] is False
    assert artifact["n80_exotic_computation_route_allowed"] is False
    assert artifact["machine_readable_diagram_claim_allowed"] is False
    assert artifact["h2_marking_certified_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)
    assert "not a source audit" in artifact["claim_boundary"]


def test_n72_refuses_promoted_claims() -> None:
    with pytest.raises(ValueError, match="source-needed checklist"):
        dolgachev_source_capture_ledger_artifact(claim_source_captured=True)
    with pytest.raises(ValueError, match="source-needed checklist"):
        dolgachev_source_capture_ledger_artifact(claim_machine_readable_diagram=True)
    with pytest.raises(ValueError, match="source-needed checklist"):
        dolgachev_source_capture_ledger_artifact(claim_h2_marking_certified=True)
    with pytest.raises(ValueError, match="source-needed checklist"):
        dolgachev_source_capture_ledger_artifact(claim_n70_pass=True)
    with pytest.raises(ValueError, match="source-needed checklist"):
        dolgachev_source_capture_ledger_artifact(claim_n80_route=True)
    with pytest.raises(ValueError, match="source-needed checklist"):
        dolgachev_source_capture_ledger_artifact(claim_exotic_detection=True)


def test_n72_json_is_stable_exact_and_float_free() -> None:
    first = dolgachev_source_capture_ledger_artifact()
    second = dolgachev_source_capture_ledger_artifact()

    first_json = stable_dolgachev_source_capture_ledger_json(first)
    assert first_json == stable_dolgachev_source_capture_ledger_json(second)
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    _assert_no_float(first)


def test_n72_validator_rejects_missing_required_fields() -> None:
    validation = validate_dolgachev_source_capture_ledger_artifact(
        {"schema": DOLGACHEV_SOURCE_CAPTURE_SCHEMA}
    )

    assert validation["valid"] is False
    assert "reference_inventory" in validation["missing_required_fields"]


def test_checked_in_n72_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N72_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = dolgachev_source_capture_ledger_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "inconclusive"
    assert exact_output["schema"] == generated["schema"]
    assert exact_output["status"] == "blocked"
    assert exact_output["source_status"] == "source-needed"
    assert exact_output["candidate_id"] == generated["candidate_id"]
    assert exact_output["reference_inventory"] == generated["reference_inventory"]
    assert exact_output["required_exact_source_slots"] == generated[
        "required_exact_source_slots"
    ]
    assert exact_output["missing_fields"] == generated["missing_fields"]
    assert exact_output["blocker_reason_ids"] == generated["blocker_reason_ids"]
    assert exact_output["blocked_claims"] == generated["blocked_claims"]
    assert exact_output["metadata_validation"]["valid"] is True
