import json

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.ordinary_surgery_gate import ordinary_surgery_gate_certificate
from twisted_yetter.provisional_formula_policy import (
    ALLOWED_ARTIFACT_CLAIM_LEVELS,
    FORMULA_STATUS_LEDGER,
    N24_ACCEPTED_COMMIT,
    N24_ARTIFACT,
    PROVISIONAL_FORMULA_POLICY_SCHEMA,
    REJECTED_CLAIM_TYPES,
    REQUIRED_ARTIFACT_FIELDS,
    claim_policy_decision,
    provisional_formula_policy_artifact_certificate,
    provisional_formula_policy_certificate,
    stable_provisional_formula_policy_json,
)


def test_policy_certificate_inherits_n24_blockers() -> None:
    certificate = provisional_formula_policy_certificate()
    n24 = ordinary_surgery_gate_certificate()

    inherited = certificate["ordinary_surgery_gate_dependency"]
    assert certificate["schema"] == PROVISIONAL_FORMULA_POLICY_SCHEMA
    assert certificate["status"] == "policy-active"
    assert inherited["node_id"] == "n24-ordinary-surgery-gate"
    assert inherited["status"] == "blocked"
    assert inherited["accepted_as_blocker_at_commit"] == N24_ACCEPTED_COMMIT
    assert inherited["accepted_as_blocker_at_commit_short"] == "bbc48b2"
    assert inherited["artifact"] == N24_ARTIFACT
    assert inherited["blocked_source_slots"] == n24["blocked_source_slots"]
    assert inherited["blocked_reason_ids"] == [
        reason["reason_id"] for reason in n24["blocked_reasons"]
    ]
    assert inherited["closed_4_manifold_claim_allowed"] is False
    assert inherited["claim_supporting_closed_invariant_allowed"] is False


def test_policy_blocks_high_claims() -> None:
    certificate = provisional_formula_policy_certificate()

    assert certificate["rejected_claim_types"] == list(REJECTED_CLAIM_TYPES)
    for claim_type in REJECTED_CLAIM_TYPES:
        decision = claim_policy_decision(claim_type)
        assert decision["decision"] == "rejected"
        assert decision["allowed"] is False
        assert decision["inherited_blocker"] == "n24-ordinary-surgery-gate:blocked"

    assert claim_policy_decision("exotic detection claim")["allowed"] is False
    assert (
        claim_policy_decision("closed homologically twisted Yetter invariant value")[
            "allowed"
        ]
        is False
    )


def test_policy_allows_candidate_and_schema_experiments() -> None:
    certificate = provisional_formula_policy_certificate()

    assert certificate["allowed_artifact_claim_levels"] == list(
        ALLOWED_ARTIFACT_CLAIM_LEVELS
    )
    assert "candidate-experimental" in certificate["allowed_artifact_claim_levels"]
    assert "provisional-low-confidence" in certificate[
        "allowed_artifact_claim_levels"
    ]
    assert "schema-test-safe" in certificate["allowed_artifact_claim_levels"]
    assert "computed evidence scaffold" in certificate[
        "allowed_artifact_claim_levels"
    ]
    assert certificate["required_artifact_fields"] == list(REQUIRED_ARTIFACT_FIELDS)

    for claim_level in ALLOWED_ARTIFACT_CLAIM_LEVELS:
        decision = claim_policy_decision(claim_level)
        assert decision["decision"] == "allowed"
        assert decision["allowed"] is True
        assert decision["required_artifact_fields"] == list(
            REQUIRED_ARTIFACT_FIELDS
        )


def test_downstream_node_decisions_cover_n31_n32_n33_n35() -> None:
    certificate = provisional_formula_policy_certificate()
    decisions = {
        decision["node_id"]: decision
        for decision in certificate["downstream_policy_decisions"]
    }

    assert list(decisions) == [
        "n31-yetter-z2-surgical-source-capture",
        "n32-general-a-candidate-contract",
        "n33-omega-a-implementation",
        "n35-twisted-decorated-core",
    ]
    assert decisions["n31-yetter-z2-surgical-source-capture"][
        "decision"
    ] == "allowed"
    assert "provisional-low-confidence" in decisions[
        "n31-yetter-z2-surgical-source-capture"
    ]["allowed_claim_levels"]
    assert decisions["n32-general-a-candidate-contract"][
        "allowed_activity"
    ] == "candidate contract for the general finite A color"
    assert decisions["n33-omega-a-implementation"][
        "allowed_activity"
    ] == "finite A candidate-color implementation scaffold"
    assert decisions["n35-twisted-decorated-core"][
        "decision"
    ] == "allowed-with-blocked-ordinary-gate"
    assert "ordinary_surgery_gate_status" in decisions[
        "n35-twisted-decorated-core"
    ]["required_artifact_fields"]

    for decision in decisions.values():
        assert decision["source_status_required"] is True
        assert "claim_level" in decision["required_artifact_fields"]
        assert "source_status" in decision["required_artifact_fields"]


def test_formula_status_ledger_records_n30_scope() -> None:
    certificate = provisional_formula_policy_certificate()
    entries = {
        entry["formula_id"]: entry
        for entry in certificate["formula_status_ledger"]
    }

    assert list(FORMULA_STATUS_LEDGER) == certificate["formula_status_ledger"]
    assert entries["yetter-z2-surgical-formula"][
        "status"
    ] == "provisional-low-confidence"
    assert entries["general-finite-a-omega-a"]["status"] == "candidate-experimental"
    assert "Omega_a = sum_i d_i lambda_i(a) X_i" == entries[
        "general-finite-a-omega-a"
    ]["display"]
    assert entries["ordinary-surgery-gate-blocker"][
        "status"
    ] == "blocked executable gate certificate"
    assert entries["ordinary-surgery-gate-blocker"]["artifact"] == N24_ARTIFACT


def test_policy_json_is_stable_and_deterministic() -> None:
    first = provisional_formula_policy_certificate()
    second = provisional_formula_policy_certificate()

    assert first == second
    assert stable_provisional_formula_policy_json(first) == (
        stable_provisional_formula_policy_json(second)
    )
    assert json.loads(stable_provisional_formula_policy_json(first)) == first
    assert stable_provisional_formula_policy_json(first) == json.dumps(
        first,
        indent=2,
        sort_keys=True,
    )


def test_policy_global_boundaries_match_n30_scope() -> None:
    certificate = provisional_formula_policy_certificate()
    policy = certificate["global_policy"]

    assert policy["may_run_many_examples"] is True
    assert policy["passing_examples_are_proof"] is False
    assert policy["failures_must_be_recorded"] is True
    assert policy["downstream_twisted_outputs_must_be_provisional"] is True
    assert policy["must_cite_n24_for_closed_or_exotic_artifacts"] is True
    assert policy["must_not_implement_formula_here"] is True
    assert policy["must_not_source_audit_external_references_here"] is True
    assert "exotic detection claim" in certificate["still_blocked"]


def test_policy_artifact_certificate_is_valid() -> None:
    artifact = provisional_formula_policy_artifact_certificate()

    validate_certificate(artifact)
    assert artifact["status"] == "pass"
    assert (
        artifact["generator_script"]
        == "src/twisted_yetter/provisional_formula_policy.py"
    )
    assert artifact["exact_output"]["node_id"] == "n30-provisional-formula-policy"
    assert artifact["exact_output"]["ordinary_surgery_gate_dependency"][
        "artifact"
    ] == N24_ARTIFACT
