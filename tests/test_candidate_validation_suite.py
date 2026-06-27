import json

from twisted_yetter.candidate_validation_suite import (
    BLOCKED_HIGH_CLAIMS,
    CANDIDATE_VALIDATION_SUITE_ARTIFACT,
    CANDIDATE_VALIDATION_SUITE_SCHEMA,
    DEFAULT_CASE_SPECS,
    DOES_NOT_COMPUTE,
    candidate_validation_suite_artifact_certificate,
    many_case_candidate_validation_suite_artifact,
    stable_candidate_validation_suite_json,
    validate_candidate_validation_suite_metadata,
)


def test_suite_contains_required_many_case_inventory() -> None:
    artifact = many_case_candidate_validation_suite_artifact()
    cases = {case["case_id"]: case for case in artifact["cases"]}

    assert artifact["schema"] == CANDIDATE_VALIDATION_SUITE_SCHEMA
    assert artifact["status"] == "pass"
    assert artifact["claim_level"] == "computed evidence scaffold"
    assert artifact["ordinary_surgery_gate_status"] == "blocked"
    assert artifact["case_count"] == len(DEFAULT_CASE_SPECS)
    assert set(cases) == {
        "s4-trivial-zero",
        "cp2-z2-zero",
        "cp2-z2-nonzero",
        "s2xs2-hopf-z2-mixed-10",
        "s2xs2-hopf-z2-mixed-01",
        "unlink-two-component-z2-zero",
        "unlink-two-component-z2-mixed",
        "unlink-two-component-z2-nonzero",
    }

    assert cases["s4-trivial-zero"]["fixture_path"] == (
        "experiments/inputs/toy-diagrams/s4-empty.json"
    )
    assert cases["s4-trivial-zero"]["diagram_id"] == "s4-empty-kirby-diagram"
    assert cases["s4-trivial-zero"]["finite_group_id"] == "trivial"
    assert cases["s4-trivial-zero"]["zero_decoration"] is True
    assert cases["s4-trivial-zero"]["component_sector_ids"] == []

    assert cases["cp2-z2-zero"]["diagram_id"] == "cp2-plus-one-framed-unknot"
    assert cases["cp2-z2-zero"]["decoration_by_component"] == {"cp2_h": "0"}
    assert cases["cp2-z2-zero"]["zero_decoration"] is True
    assert cases["cp2-z2-zero"]["component_sector_ids"] == ["0"]

    assert cases["cp2-z2-nonzero"]["decoration_by_component"] == {"cp2_h": "1"}
    assert cases["cp2-z2-nonzero"]["zero_decoration"] is False
    assert cases["cp2-z2-nonzero"]["component_sector_ids"] == ["1"]


def test_hopf_and_unlink_z2_cases_record_sector_metadata() -> None:
    artifact = many_case_candidate_validation_suite_artifact()
    cases = {case["case_id"]: case for case in artifact["cases"]}

    assert cases["s2xs2-hopf-z2-mixed-10"]["diagram_component_ids"] == [
        "s2_a",
        "s2_b",
    ]
    assert cases["s2xs2-hopf-z2-mixed-10"]["decoration_by_component"] == {
        "s2_a": "1",
        "s2_b": "0",
    }
    assert cases["s2xs2-hopf-z2-mixed-10"]["component_sector_ids"] == ["1", "0"]
    assert cases["s2xs2-hopf-z2-mixed-10"]["component_sector_metadata"] == [
        {
            "component_id": "s2_a",
            "decoration_element_id": "1",
            "candidate_sector_id": "1",
        },
        {
            "component_id": "s2_b",
            "decoration_element_id": "0",
            "candidate_sector_id": "0",
        },
    ]

    assert cases["unlink-two-component-z2-zero"]["zero_decoration"] is True
    assert cases["unlink-two-component-z2-zero"]["component_sector_ids"] == ["0", "0"]
    assert cases["unlink-two-component-z2-mixed"]["component_sector_ids"] == ["1", "0"]
    assert cases["unlink-two-component-z2-nonzero"]["component_sector_ids"] == [
        "1",
        "1",
    ]


def test_all_cases_pass_metadata_validation_and_are_stable_exact_json() -> None:
    artifact = many_case_candidate_validation_suite_artifact()

    assert artifact["all_cases_pass_metadata_validation"] is True
    assert artifact["all_cases_json_stable"] is True
    assert artifact["all_cases_exact_json_no_float_markers"] is True
    assert artifact["metadata_validation"]["valid"] is True
    for case in artifact["cases"]:
        assert case["metadata_validation"]["valid"] is True
        assert case["stable_json_roundtrip"] is True
        assert case["exact_json_no_float_markers"] is True
        assert ".0" not in case["stable_json_sha256"]

    first_json = stable_candidate_validation_suite_json(artifact)
    second_json = stable_candidate_validation_suite_json(
        many_case_candidate_validation_suite_artifact()
    )
    assert first_json == second_json
    assert json.loads(first_json) == artifact
    assert ".0" not in first_json


def test_source_claim_fields_are_present_and_high_claims_remain_blocked() -> None:
    artifact = many_case_candidate_validation_suite_artifact()

    assert artifact["proof_claim_allowed"] is False
    assert artifact["closed_4_manifold_claim_allowed"] is False
    assert artifact["exotic_detection_claim_allowed"] is False
    assert artifact["decorated_kirby_move_proof_claim_allowed"] is False
    assert artifact["blocked_high_claims"] == list(BLOCKED_HIGH_CLAIMS)
    assert artifact["does_not_compute"] == list(DOES_NOT_COMPUTE)
    assert "not proof" in artifact["claim_boundary"]
    for forbidden in (
        "link evaluation",
        "Kirby color sum",
        "decorated Kirby move proof",
        "closed invariant",
        "exotic detection",
    ):
        assert forbidden in artifact["does_not_compute"]

    for case in artifact["cases"]:
        assert case["claim_level"] == "computed evidence scaffold"
        assert "source_status" in case
        assert case["source_status"]
        assert case["ordinary_surgery_gate_status"] == "blocked"


def test_reproducible_artifact_envelope_records_n36_contract() -> None:
    certificate = candidate_validation_suite_artifact_certificate()
    exact_output = certificate["exact_output"]

    assert certificate["schema"] == "twisted-yetter.certificate.v1"
    assert certificate["status"] == "pass"
    assert certificate["generator_script"] == (
        "src/twisted_yetter/candidate_validation_suite.py"
    )
    assert certificate["argv"] == [
        "python",
        "-m",
        "twisted_yetter.candidate_validation_suite",
        "--write",
        CANDIDATE_VALIDATION_SUITE_ARTIFACT,
    ]
    assert CANDIDATE_VALIDATION_SUITE_ARTIFACT in certificate["command"]
    assert CANDIDATE_VALIDATION_SUITE_ARTIFACT in certificate["reproduce_command"]

    assert exact_output["schema"] == CANDIDATE_VALIDATION_SUITE_SCHEMA
    assert exact_output["node_id"] == "n36-many-case-candidate-validation-suite"
    assert exact_output["status"] == "pass"
    assert exact_output["case_count"] == len(DEFAULT_CASE_SPECS)
    assert exact_output["all_cases_pass_metadata_validation"] is True
    assert exact_output["ordinary_surgery_gate_status"] == "blocked"
    assert exact_output["closed_4_manifold_claim_allowed"] is False
    assert exact_output["exotic_detection_claim_allowed"] is False
    assert "not theorem-level proof" in " ".join(certificate["notes"])


def test_suite_metadata_validator_rejects_missing_required_fields() -> None:
    validation = validate_candidate_validation_suite_metadata(
        {"claim_level": "computed evidence scaffold"}
    )

    assert validation["valid"] is False
    assert "cases" in validation["missing_required_fields"]
