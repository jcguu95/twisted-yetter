import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.dolgachev_source_capture import DOLGACHEV_SOURCE_CAPTURE_SCHEMA
from twisted_yetter.exotic_diagram_digitization import (
    BLOCKED_CLAIMS,
    CANDIDATE_ID,
    EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA,
    MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
    MISSING_LINEAGE_BLOCKER_ID,
    MISSING_PAGE_FIGURE_BLOCKER_ID,
    MISSING_SANITY_TARGETS_BLOCKER_ID,
    MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
    NODE_ID,
    exotic_diagram_digitization_ledger_artifact,
    stable_exotic_diagram_digitization_ledger_json,
    validate_exotic_diagram_digitization_ledger_artifact,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
N73_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/diagram-digitization/"
    / "n73-exotic-diagram-digitization.json"
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


def test_n73_records_blocked_digitization_gate_from_n72() -> None:
    artifact = exotic_diagram_digitization_ledger_artifact()

    assert artifact["schema"] == EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == "blocked digitization gate/schema checklist"
    assert artifact["candidate_id"] == CANDIDATE_ID
    assert artifact["upstream_node"] == "n72-dolgachev-source-capture"
    assert artifact["upstream_schema"] == DOLGACHEV_SOURCE_CAPTURE_SCHEMA
    assert artifact["upstream_status"] == "blocked"
    assert artifact["upstream_n73_ready"] is False
    assert artifact["metadata_validation"]["valid"] is True


def test_n73_does_not_emit_machine_readable_diagrams() -> None:
    artifact = exotic_diagram_digitization_ledger_artifact()

    assert artifact["diagram_payload_status"] == "not-produced"
    assert artifact["machine_readable_diagrams"] == []
    assert artifact["source_snapshot_status"] == "missing"
    assert artifact["page_figure_status"] == "missing"
    assert artifact["source_inventory"]["proved_in_source_diagram_claims"] == []
    assert "contains no machine-readable Dolgachev Kirby diagram" in artifact[
        "claim_boundary"
    ]


def test_n73_required_schema_fields_are_fixed() -> None:
    artifact = exotic_diagram_digitization_ledger_artifact()
    fields = artifact["required_schema_fields"]

    component_fields = {field["field"] for field in fields["component_fields"]}
    encoding_fields = {field["field"] for field in fields["encoding_fields"]}
    lineage_fields = {field["field"] for field in fields["lineage_fields"]}
    sanity_targets = {field["field"] for field in fields["sanity_targets"]}

    assert component_fields == {
        "side_id",
        "component_id",
        "handle_role",
        "framing",
        "dotted_status",
        "orientation",
    }
    assert encoding_fields == {"crossings", "pd_code", "braid_word", "source_locator"}
    assert lineage_fields == {
        "component_lineage",
        "handle_move_sequence",
        "basis_change_matrices",
    }
    assert sanity_targets == {
        "linking_matrix",
        "intersection_form",
        "handle_counts",
        "euler_characteristic",
        "signature",
        "h2_basis_comparison",
    }


def test_n73_blockers_are_source_and_digitization_blockers() -> None:
    artifact = exotic_diagram_digitization_ledger_artifact()

    expected = [
        MISSING_SOURCE_SNAPSHOT_BLOCKER_ID,
        MISSING_PAGE_FIGURE_BLOCKER_ID,
        MISSING_DIAGRAM_ENCODING_BLOCKER_ID,
        MISSING_LINEAGE_BLOCKER_ID,
        MISSING_SANITY_TARGETS_BLOCKER_ID,
    ]
    assert artifact["blocker_reason_ids"] == expected
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["blockers"]}
    assert set(blockers) == set(expected)
    assert "no local PDF/web snapshot" in blockers[
        MISSING_SOURCE_SNAPSHOT_BLOCKER_ID
    ]["observed"]
    assert "PD-code" in blockers[MISSING_DIAGRAM_ENCODING_BLOCKER_ID]["observed"]
    assert "basis matrices" in blockers[MISSING_LINEAGE_BLOCKER_ID]["required"]


def test_n73_blocks_all_downstream_claims() -> None:
    artifact = exotic_diagram_digitization_ledger_artifact()

    assert artifact["diagram_exists_claim_allowed"] is False
    assert artifact["digitized_components_claim_allowed"] is False
    assert artifact["schema_validated_claim_allowed"] is False
    assert artifact["matrix_sanity_claim_allowed"] is False
    assert artifact["n74_marking_certification_ready"] is False
    assert artifact["n70_exotic_input_certification_pass_allowed"] is False
    assert artifact["n80_exotic_computation_route_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)


def test_n73_refuses_promoted_claims() -> None:
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(
            claim_machine_readable_diagram=True
        )
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(claim_digitized_components=True)
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(claim_schema_validated=True)
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(claim_matrix_sanity=True)
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(claim_n74_ready=True)
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(claim_n70_pass=True)
    with pytest.raises(ValueError, match="blocked by n72 source gaps"):
        exotic_diagram_digitization_ledger_artifact(claim_n80_route=True)


def test_n73_json_is_stable_exact_and_float_free() -> None:
    first = exotic_diagram_digitization_ledger_artifact()
    second = exotic_diagram_digitization_ledger_artifact()

    first_json = stable_exotic_diagram_digitization_ledger_json(first)
    assert first_json == stable_exotic_diagram_digitization_ledger_json(second)
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    _assert_no_float(first)


def test_n73_validator_rejects_missing_required_fields() -> None:
    validation = validate_exotic_diagram_digitization_ledger_artifact(
        {"schema": EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA}
    )

    assert validation["valid"] is False
    assert "required_schema_fields" in validation["missing_required_fields"]


def test_checked_in_n73_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N73_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = exotic_diagram_digitization_ledger_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "inconclusive"
    assert exact_output["schema"] == generated["schema"]
    assert exact_output["status"] == "blocked"
    assert exact_output["node_id"] == generated["node_id"]
    assert exact_output["machine_readable_diagrams"] == []
    assert exact_output["required_schema_fields"] == generated[
        "required_schema_fields"
    ]
    assert exact_output["blocker_reason_ids"] == generated["blocker_reason_ids"]
    assert exact_output["blocked_claims"] == generated["blocked_claims"]
    assert exact_output["metadata_validation"]["valid"] is True
