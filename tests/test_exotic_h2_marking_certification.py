import json
from pathlib import Path

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.exotic_diagram_digitization import EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA
from twisted_yetter.exotic_h2_marking_certification import (
    BLOCKED_CLAIMS,
    CANDIDATE_ID,
    COMPARISON_LEVELS,
    EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA,
    MISSING_COMPONENT_LINEAGE_BLOCKER_ID,
    MISSING_H2_BASIS_BLOCKER_ID,
    MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
    MISSING_INTERSECTION_MATRIX_BLOCKER_ID,
    MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
    MISSING_SANITY_CHECK_BLOCKER_ID,
    MISSING_SOURCE_CITATION_BLOCKER_ID,
    NODE_ID,
    exotic_h2_marking_certification_ledger_artifact,
    stable_exotic_h2_marking_certification_ledger_json,
    validate_exotic_h2_marking_certification_ledger_artifact,
)
from twisted_yetter.h2_marking import H2_DECORATION_SCHEMA


REPO_ROOT = Path(__file__).resolve().parents[1]
N74_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/h2-marking/"
    / "n74-exotic-h2-marking-certification.json"
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


def test_n74_records_blocked_marking_gate_from_n73() -> None:
    artifact = exotic_h2_marking_certification_ledger_artifact()

    assert artifact["schema"] == EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA
    assert artifact["status"] == "blocked"
    assert artifact["node_id"] == NODE_ID
    assert artifact["claim_level"] == (
        "blocked H2/homeomorphism marking certification checklist"
    )
    assert artifact["candidate_id"] == CANDIDATE_ID
    assert artifact["upstream_node"] == "n73-exotic-diagram-digitization"
    assert artifact["upstream_schema"] == EXOTIC_DIAGRAM_DIGITIZATION_SCHEMA
    assert artifact["upstream_status"] == "blocked"
    assert artifact["upstream_n74_ready"] is False
    assert artifact["upstream_machine_readable_diagrams"] == []
    assert artifact["h2_schema_dependency"] == H2_DECORATION_SCHEMA
    assert artifact["metadata_validation"]["valid"] is True


def test_n74_comparison_level_is_inconclusive_not_certified() -> None:
    artifact = exotic_h2_marking_certification_ledger_artifact()

    assert artifact["comparison_level"] == "inconclusive"
    assert artifact["comparison_level_status"] == "inconclusive-source-blocked"
    assert artifact["allowed_comparison_levels"] == list(COMPARISON_LEVELS)
    assert "certifies no H2 marking" in artifact["claim_boundary"]

    for comparison_level in COMPARISON_LEVELS:
        candidate = exotic_h2_marking_certification_ledger_artifact(
            comparison_level=comparison_level
        )
        assert candidate["comparison_level"] == comparison_level
        assert candidate["metadata_validation"]["valid"] is True

    with pytest.raises(ValueError, match="comparison_level must be one of"):
        exotic_h2_marking_certification_ledger_artifact(
            comparison_level="cork-canonical-ish"
        )


def test_n74_required_fields_are_fixed() -> None:
    artifact = exotic_h2_marking_certification_ledger_artifact()
    fields = artifact["required_fields"]

    marking_fields = {field["field"] for field in fields["marking_fields"]}
    side_fields = {field["field"] for field in fields["side_fields"]}
    sanity_checks = {field["field"] for field in fields["sanity_checks"]}

    assert marking_fields == {
        "comparison_level",
        "side_h2_bases",
        "intersection_matrices",
        "homeomorphism_basis_identification_matrix",
        "component_to_h2_lineage",
        "cork_twist_marking",
        "source_citations",
        "sanity_checks",
    }
    assert side_fields == {
        "side_id",
        "h2_basis_id",
        "h2_basis_vectors",
        "component_lineage",
        "intersection_matrix",
    }
    assert sanity_checks == {
        "rank_agreement",
        "matrix_symmetry_integrality",
        "form_preservation",
        "determinant_signature_euler",
        "alpha_zero_route",
        "basis_change_unimodularity",
    }


def test_n74_blockers_are_marking_certification_blockers() -> None:
    artifact = exotic_h2_marking_certification_ledger_artifact()

    expected = [
        MISSING_MACHINE_DIAGRAM_BLOCKER_ID,
        MISSING_SOURCE_CITATION_BLOCKER_ID,
        MISSING_H2_BASIS_BLOCKER_ID,
        MISSING_INTERSECTION_MATRIX_BLOCKER_ID,
        MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID,
        MISSING_COMPONENT_LINEAGE_BLOCKER_ID,
        "marking-cork-twist-data-needed",
        MISSING_SANITY_CHECK_BLOCKER_ID,
    ]
    assert artifact["blocker_reason_ids"] == expected
    blockers = {blocker["reason_id"]: blocker for blocker in artifact["blockers"]}
    assert set(blockers) == set(expected)
    assert "no machine-readable diagrams" in blockers[
        MISSING_MACHINE_DIAGRAM_BLOCKER_ID
    ]["observed"]
    assert "no source snapshot" in blockers[MISSING_SOURCE_CITATION_BLOCKER_ID][
        "observed"
    ]
    assert "intersection form" in blockers[
        MISSING_IDENTIFICATION_MATRIX_BLOCKER_ID
    ]["required"]


def test_n74_blocks_all_downstream_and_distinction_claims() -> None:
    artifact = exotic_h2_marking_certification_ledger_artifact()

    assert artifact["certified_h2_marking_claim_allowed"] is False
    assert artifact["homeomorphism_comparison_claim_allowed"] is False
    assert artifact["marked_distinction_claim_allowed"] is False
    assert artifact["cork_canonical_distinction_claim_allowed"] is False
    assert artifact["orbit_multiset_distinction_claim_allowed"] is False
    assert artifact["unmarked_total_function_distinction_claim_allowed"] is False
    assert artifact["n70_exotic_input_certification_pass_allowed"] is False
    assert artifact["n80_exotic_computation_route_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["blocked_claims"] == list(BLOCKED_CLAIMS)


def test_n74_refuses_promoted_claims() -> None:
    with pytest.raises(ValueError, match="blocked by missing n73"):
        exotic_h2_marking_certification_ledger_artifact(
            claim_certified_h2_marking=True
        )
    with pytest.raises(ValueError, match="blocked by missing n73"):
        exotic_h2_marking_certification_ledger_artifact(
            claim_homeomorphism_comparison=True
        )
    with pytest.raises(ValueError, match="blocked by missing n73"):
        exotic_h2_marking_certification_ledger_artifact(claim_n70_pass=True)
    with pytest.raises(ValueError, match="blocked by missing n73"):
        exotic_h2_marking_certification_ledger_artifact(claim_n80_route=True)


def test_n74_json_is_stable_exact_and_float_free() -> None:
    first = exotic_h2_marking_certification_ledger_artifact()
    second = exotic_h2_marking_certification_ledger_artifact()

    first_json = stable_exotic_h2_marking_certification_ledger_json(first)
    assert first_json == stable_exotic_h2_marking_certification_ledger_json(second)
    assert first_json == json.dumps(first, indent=2, sort_keys=True)
    assert json.loads(first_json) == first
    _assert_no_float(first)


def test_n74_validator_rejects_missing_required_fields() -> None:
    validation = validate_exotic_h2_marking_certification_ledger_artifact(
        {"schema": EXOTIC_H2_MARKING_CERTIFICATION_SCHEMA}
    )

    assert validation["valid"] is False
    assert "required_fields" in validation["missing_required_fields"]


def test_checked_in_n74_artifact_matches_core_generator_output() -> None:
    certificate = json.loads(N74_ARTIFACT.read_text())
    validate_certificate(certificate)

    generated = exotic_h2_marking_certification_ledger_artifact()
    exact_output = certificate["exact_output"]

    assert certificate["status"] == "inconclusive"
    assert exact_output["schema"] == generated["schema"]
    assert exact_output["status"] == "blocked"
    assert exact_output["node_id"] == generated["node_id"]
    assert exact_output["comparison_level"] == "inconclusive"
    assert exact_output["upstream_machine_readable_diagrams"] == []
    assert exact_output["required_fields"] == generated["required_fields"]
    assert exact_output["blocker_reason_ids"] == generated["blocker_reason_ids"]
    assert exact_output["blocked_claims"] == generated["blocked_claims"]
    assert exact_output["metadata_validation"]["valid"] is True
