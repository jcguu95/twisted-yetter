import json

from twisted_yetter.omega_a_contract import (
    FALSIFICATION_CRITERIA,
    MARKING_REQUIREMENTS,
    N33_REQUIREMENTS,
    OMEGA_A_CANDIDATE_FORMULA_ID,
    OMEGA_A_CONTRACT_SCHEMA,
    ORDINARY_SURGERY_GATE_ONE_OF_FIELDS,
    REQUIRED_ARTIFACT_FIELDS,
    REQUIRED_SOURCE_PROOF_SLOTS,
    SPECIALIZATION_CHECKS,
    omega_a_candidate_contract_certificate,
    omega_a_contract_claim_decision,
    stable_omega_a_contract_json,
    validate_omega_a_candidate_artifact_metadata,
)


def test_contract_certificate_is_candidate_and_deterministic() -> None:
    first = omega_a_candidate_contract_certificate()
    second = omega_a_candidate_contract_certificate()

    assert first == second
    assert first["schema"] == OMEGA_A_CONTRACT_SCHEMA
    assert first["status"] == "contract-active"
    assert first["claim_level"] == "candidate-experimental"
    assert "SOURCE NEEDED" in first["source_status"]
    assert first["candidate_formula_id"] == OMEGA_A_CANDIDATE_FORMULA_ID
    assert stable_omega_a_contract_json(first) == json.dumps(
        first,
        indent=2,
        sort_keys=True,
    )
    assert json.loads(stable_omega_a_contract_json(first)) == first


def test_required_artifact_schema_fields_are_explicit() -> None:
    certificate = omega_a_candidate_contract_certificate()

    assert certificate["allowed_claim_levels"] == [
        "candidate-experimental",
        "schema-test-safe",
    ]
    assert certificate["required_artifact_fields"] == list(
        REQUIRED_ARTIFACT_FIELDS
    )
    for field in (
        "claim_level",
        "source_status",
        "candidate_formula_id",
        "finite_group_id",
        "character_table_source",
        "character_data_source_status",
        "marking_basis_status",
    ):
        assert field in certificate["required_artifact_fields"]

    gate_requirement = certificate["ordinary_surgery_gate_requirement"]
    assert gate_requirement["one_of"] == list(
        ORDINARY_SURGERY_GATE_ONE_OF_FIELDS
    )
    assert gate_requirement["inherited_status"] == "blocked"
    assert gate_requirement["closed_4_manifold_claim_allowed"] is False

    character_requirement = certificate["character_table_requirement"]
    assert character_requirement["lambda_i_a_exact_required"] is True
    assert character_requirement["source_status_annotation_required"] is True
    assert character_requirement["floating_point_allowed"] is False


def test_high_claims_are_blocked_through_n30_policy() -> None:
    high_claims = (
        "decorated/twisted formula theorem",
        "claim-supporting closed 4D invariant",
        "exotic detection claim",
        "Reutter escape/no-go conclusion",
    )

    for claim in high_claims:
        decision = omega_a_contract_claim_decision(claim)
        assert decision["allowed"] is False
        assert decision["decision"] == "rejected"
        assert decision["inherited_blocker"] == "n24-ordinary-surgery-gate:blocked"
        assert decision["node_id"] == "n32-general-a-candidate-contract"

    assert omega_a_contract_claim_decision("candidate-experimental")[
        "allowed"
    ] is True
    assert omega_a_contract_claim_decision("schema-test-safe")["allowed"] is True
    assert omega_a_contract_claim_decision("provisional-low-confidence")[
        "decision"
    ] == "rejected-by-n32-contract"


def test_source_slots_specialization_checks_and_falsification_criteria_are_present() -> None:
    certificate = omega_a_candidate_contract_certificate()
    slot_ids = {
        slot["slot_id"] for slot in certificate["required_source_proof_slots"]
    }
    check_ids = {
        check["check_id"] for check in certificate["specialization_checks"]
    }
    criterion_ids = {
        criterion["criterion_id"]
        for criterion in certificate["falsification_criteria"]
    }

    assert certificate["required_source_proof_slots"] == [
        dict(slot) for slot in REQUIRED_SOURCE_PROOF_SLOTS
    ]
    assert "formula-source-or-proof" in slot_ids
    assert "lambda-action-source" in slot_ids
    assert "kirby-move-proof-scope" in slot_ids
    assert "ordinary-specialization-boundary" in slot_ids
    assert "z2-specialization-source" in slot_ids

    assert certificate["specialization_checks"] == [
        dict(check) for check in SPECIALIZATION_CHECKS
    ]
    assert "trivial-a-recovers-ordinary-omega-candidate" in check_ids
    assert "z2-nontrivial-sector-aligns-with-theta-target-if-sourced" in check_ids
    assert "character-orthogonality-and-exactness" in check_ids
    assert "zero-and-all-trivial-decorations" in check_ids

    assert certificate["falsification_criteria"] == [
        dict(criterion) for criterion in FALSIFICATION_CRITERIA
    ]
    assert "toy-examples-inconsistent" in criterion_ids
    assert "z2-mismatch-after-source-capture" in criterion_ids
    assert "handle-slide-or-presentation-mismatch" in criterion_ids
    assert "exact-arithmetic-inconsistency" in criterion_ids
    assert "marking-or-basis-mismatch" in criterion_ids
    assert "failed-example-recorded-against-candidate" in criterion_ids


def test_marking_requirements_force_basis_effects_to_be_represented() -> None:
    certificate = omega_a_candidate_contract_certificate()
    marking = certificate["marking_requirement"]
    requirement_ids = {
        requirement["requirement_id"] for requirement in marking["requirements"]
    }

    assert marking["marking_basis_status_required"] is True
    assert marking["basis_and_h2_effects_must_be_represented"] is True
    assert marking["basis_and_h2_effects_must_not_be_guessed"] is True
    assert marking["requirements"] == [
        dict(requirement) for requirement in MARKING_REQUIREMENTS
    ]
    assert "represent-h2-basis" in requirement_ids
    assert "record-basis-change-action" in requirement_ids
    assert "separate-marked-from-unmarked-claims" in requirement_ids


def test_n33_requirements_are_present_and_metadata_only() -> None:
    certificate = omega_a_candidate_contract_certificate()
    requirement_ids = {
        requirement["requirement_id"]
        for requirement in certificate["n33_requirements"]
    }

    assert certificate["n33_requirements"] == [
        dict(requirement) for requirement in N33_REQUIREMENTS
    ]
    assert "preserve-contract-metadata" in requirement_ids
    assert "keep-candidate-claim-level" in requirement_ids
    assert "cite-character-table-source" in requirement_ids
    assert "no-theorem-or-exotic-claim" in requirement_ids
    assert "no-coefficient-claim-without-later-implementation" in requirement_ids
    assert "Omega_a coefficients" in certificate["does_not_implement"]


def test_artifact_metadata_validation_requires_n33_fields() -> None:
    valid_artifact = {
        "claim_level": "candidate-experimental",
        "source_status": "candidate-experimental / SOURCE NEEDED",
        "candidate_formula_id": OMEGA_A_CANDIDATE_FORMULA_ID,
        "finite_group_id": "Z/2",
        "character_table_source": "twisted_yetter.finite_groups:Z2_GROUP",
        "character_data_source_status": "exact n11 table / lambda assignment candidate",
        "marking_basis_status": "not-in-scope: metadata-only contract fixture",
        "ordinary_surgery_gate_status": "blocked",
    }

    validation = validate_omega_a_candidate_artifact_metadata(valid_artifact)
    assert validation["valid"] is True
    assert validation["missing_fields"] == []
    assert validation["candidate_formula_id_matches"] is True
    assert validation["does_not_validate_formula_coefficients"] is True

    missing = validate_omega_a_candidate_artifact_metadata(
        {"claim_level": "candidate-experimental"}
    )
    assert missing["valid"] is False
    assert "source_status" in missing["missing_fields"]
    assert "candidate_formula_id" in missing["missing_fields"]
    assert "finite_group_id" in missing["missing_fields"]
    assert "character_table_source" in missing["missing_fields"]
    assert "character_data_source_status" in missing["missing_fields"]
    assert "marking_basis_status" in missing["missing_fields"]
    assert "ordinary_surgery_gate_status_or_explanation" in missing[
        "missing_fields"
    ]

    high_claim_artifact = {
        **valid_artifact,
        "claim_level": "exotic detection claim",
    }
    blocked = validate_omega_a_candidate_artifact_metadata(high_claim_artifact)
    assert blocked["valid"] is False
    assert blocked["claim_decision"]["allowed"] is False
