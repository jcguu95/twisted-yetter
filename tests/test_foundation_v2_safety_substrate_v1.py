import copy
import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    EXPECTED_MODULAR_BRAIDED_COUNTS,
    FOUNDATION_STATUS,
    RIBBON_CATALOG_BLOCKED,
    RIBBON_CATALOG_ESTABLISHED,
    FoundationSafetyError,
    add_content_hash,
    validate_formal_admission_policy,
    validate_formal_evidence,
    validate_formal_scan_readiness,
    validate_low_rank_ribbon_catalog,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_foundation_v2_safety_substrate_v1.py"
SPEC = importlib.util.spec_from_file_location("foundation_v2_safety_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def sha(char: str) -> str:
    return "sha256:" + char * 64


def valid_scan_plan_payload() -> dict:
    return add_content_hash(
        {
            "evidence_kind": "scan_plan",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "classification_catalog_status": RIBBON_CATALOG_ESTABLISHED,
            "audit_snapshot_state": "current-pinned",
            "audit_snapshot_hash": sha("1"),
            "classification_catalog_hash": sha("2"),
            "pinned_hashes": {
                "category_catalog": sha("3"),
                "manifold_catalog": sha("4"),
                "character_assignment_catalog": sha("5"),
                "evaluator_profile": sha("6"),
                "numeric_policy": sha("7"),
                "execution_semantics": sha("8"),
            },
            "scan_case_ids": ["case-0"],
        }
    )


def valid_partial_scan_plan_payload() -> dict:
    return add_content_hash(
        {
            "evidence_kind": "partial_scan_plan",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "scan_scope": "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET",
            "partial_scan_complete_claim_allowed": True,
            "full_scan_complete_claim_allowed": False,
            "audit_snapshot_state": "current-pinned",
            "audit_snapshot_hash": sha("1"),
            "classification_catalog_hash": sha("2"),
            "universal_grading_audit_hash": sha("3"),
            "pinned_hashes": {
                "category_subset_catalog": sha("4"),
                "manifold_catalog": sha("5"),
                "character_assignment_catalog": sha("6"),
                "evaluator_profile": sha("7"),
                "numeric_policy": sha("8"),
                "execution_semantics": sha("9"),
                "exclusion_ledger": sha("a"),
            },
            "admitted_family_ids": ["rank2-cyclic-z2", "rank3-cyclic-z3"],
            "excluded_blocked_family_ids": ["rank3-ising", "rank5-su2-4"],
            "discarded_trivial_universal_group_family_ids": ["rank3-psu2-5"],
            "unknown_universal_group_family_ids": ["rank5-psu3-4"],
            "trivial_rows_disposition": (
                "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
            ),
            "unknown_rows_disposition": "EXCLUDED_NOT_DISCARDED",
            "scan_case_ids": ["partial-case-0"],
        }
    )


def valid_partial_scan_aggregate_payload() -> dict:
    return add_content_hash(
        {
            "evidence_kind": "partial_scan_aggregate",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "scan_scope": "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET",
            "partial_scan_complete_claim_allowed": True,
            "full_scan_complete_claim_allowed": False,
            "scan_plan_hash": sha("b"),
            "enumerator_certificate": {"status": "PASS_PARTIAL_DENOMINATOR"},
            "expected_case_count": 1,
            "actual_case_count": 1,
            "excluded_blocked_family_ids": ["rank3-ising", "rank5-su2-4"],
            "discarded_trivial_universal_group_family_ids": ["rank3-psu2-5"],
            "unknown_universal_group_family_ids": ["rank5-psu3-4"],
            "aggregate_claim": "partial-admitted-subset-no-signal",
        }
    )


def valid_ribbon_snapshot_payload() -> dict:
    certs = {
        "producer_exact_coherence": {"status": "PASS", "content_hash": sha("a")},
        "consumer_runtime_coherence": {"status": "PASS", "content_hash": sha("b")},
        "ribbon_pivotal_compatibility": {"status": "PASS", "content_hash": sha("c")},
    }
    checks = {
        "pentagon": "PASS",
        "hexagon": "PASS",
        "rigidity": "PASS",
        "duality_involution": "PASS",
        "fusion_pairing_invertible": "PASS",
        "r_inverse": "PASS",
        "balancing": "PASS",
        "ribbon_pivotal_compatibility": "PASS",
    }
    return add_content_hash(
        {
            "evidence_kind": "ribbon_realization_snapshot",
            "claim_level": "formal-low-rank-category-evidence",
            "source_status": "formal",
            "category_contract": "RibbonFusionCategoryV2",
            "category_data_hash": sha("d"),
            "pinned_payload_hashes": {"category_payload": sha("e")},
            "certificates": certs,
            "structural_checks": checks,
        }
    )


def test_v1_policy_is_active_fail_closed() -> None:
    policy = load_json("formal-admission-policy-v1.json")

    validate_formal_admission_policy(policy)

    assert policy["foundation_status"] == FOUNDATION_STATUS
    assert policy["policy_status"] == "ACTIVE_FAIL_CLOSED"
    assert policy["formal_scan_status"] == (
        "BLOCKED_UNTIL_LOW_RANK_RIBBON_CATALOG_ESTABLISHED"
    )
    assert policy["partial_scan_status"] == (
        "AUTHORIZED_ONLY_FOR_VALIDATED_NONTRIVIAL_UNIVERSAL_CHARACTER_SUBSETS"
    )
    assert "partial_scan_plan" in policy["formal_evidence_kind_allowlist"]
    assert "partial_scan_aggregate" in policy["formal_evidence_kind_allowlist"]
    assert policy["policy_flags"]["derived_readiness_only"] is True
    assert policy["policy_flags"]["braided_denominator_is_not_ribbon_denominator"] is True
    assert (
        policy["policy_flags"][
            "trivial_universal_group_rows_discarded_for_nontrivial_character_scan"
        ]
        is True
    )


def test_formal_admission_rejects_authored_ready_aliases_and_stale_hashes() -> None:
    policy = load_json("formal-admission-policy-v1.json")

    fake_ready = valid_scan_plan_payload()
    fake_ready["readiness"] = "READY_FOR_SIGNAL_SCAN"
    fake_ready = add_content_hash(fake_ready)
    with pytest.raises(FoundationSafetyError, match="readiness"):
        validate_formal_evidence(fake_ready, policy=policy)

    alias_rebind = valid_scan_plan_payload()
    alias_rebind["mutable_alias_inputs"] = ["ising-A"]
    alias_rebind = add_content_hash(alias_rebind)
    with pytest.raises(FoundationSafetyError, match="mutable aliases"):
        validate_formal_evidence(alias_rebind, policy=policy)

    stale = valid_scan_plan_payload()
    stale["scan_case_ids"] = ["case-0", "case-added-after-hash"]
    with pytest.raises(FoundationSafetyError, match="content_hash"):
        validate_formal_evidence(stale, policy=policy)


def test_formal_admission_rejects_missing_hash_and_formula_masquerade() -> None:
    policy = load_json("formal-admission-policy-v1.json")

    missing_hash = valid_scan_plan_payload()
    del missing_hash["classification_catalog_hash"]
    missing_hash = add_content_hash(missing_hash)
    with pytest.raises(FoundationSafetyError, match="classification_catalog_hash"):
        validate_formal_evidence(missing_hash, policy=policy)

    masquerade = add_content_hash(
        {
            "evidence_kind": "scan_case_result",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formula-preflight",
            "scan_plan_hash": sha("9"),
            "scan_case_id": "case-0",
            "worker_revalidated_hashes": True,
            "input_hashes": {"category": sha("a")},
            "chunk_status": "PASS",
        }
    )
    with pytest.raises(FoundationSafetyError, match="source status"):
        validate_formal_evidence(masquerade, policy=policy)


def test_partial_scan_plan_is_allowed_only_with_explicit_exclusions() -> None:
    policy = load_json("formal-admission-policy-v1.json")

    valid = valid_partial_scan_plan_payload()
    validate_formal_evidence(valid, policy=policy)

    missing_discarded = valid_partial_scan_plan_payload()
    missing_discarded["discarded_trivial_universal_group_family_ids"] = None
    missing_discarded = add_content_hash(missing_discarded)
    with pytest.raises(FoundationSafetyError, match="discarded trivial"):
        validate_formal_evidence(missing_discarded, policy=policy)

    overlapping = valid_partial_scan_plan_payload()
    overlapping["admitted_family_ids"] = ["rank3-ising"]
    overlapping = add_content_hash(overlapping)
    with pytest.raises(FoundationSafetyError, match="overlap"):
        validate_formal_evidence(overlapping, policy=policy)


def test_partial_scan_aggregate_cannot_claim_full_completion() -> None:
    policy = load_json("formal-admission-policy-v1.json")

    valid = valid_partial_scan_aggregate_payload()
    validate_formal_evidence(valid, policy=policy)

    complete = valid_partial_scan_aggregate_payload()
    complete["aggregate_claim"] = "complete-no-signal"
    complete = add_content_hash(complete)
    with pytest.raises(FoundationSafetyError, match="full completion"):
        validate_formal_evidence(complete, policy=policy)

    wrong_denominator = valid_partial_scan_aggregate_payload()
    wrong_denominator["enumerator_certificate"] = {
        "status": "PASS_COMPLETE_DENOMINATOR"
    }
    wrong_denominator = add_content_hash(wrong_denominator)
    with pytest.raises(FoundationSafetyError, match="partial denominator"):
        validate_formal_evidence(wrong_denominator, policy=policy)


def test_low_rank_ribbon_catalog_is_terminal_but_blocked() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v1.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_BLOCKED
    assert catalog["braided_denominator_by_rank"] == {
        str(rank): count for rank, count in EXPECTED_MODULAR_BRAIDED_COUNTS.items()
    }
    assert catalog["ribbon_denominator_by_rank"] == {}
    assert catalog["ribbon_denominator_copied_from_braided"] is False
    assert catalog["formal_scan_plan_allowed"] is False
    assert catalog["resolved_row_count"] == 0
    assert catalog["blocked_row_count"] == catalog["family_count"] == 14
    assert {row["terminal_status"] for row in catalog["families"]} == {
        "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
    }
    assert all(row["blocker_ids"] and row["missing_evidence"] for row in catalog["families"])


def test_catalog_cannot_claim_established_while_rows_are_blocked() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v1.json")
    broken = copy.deepcopy(catalog)
    broken["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(broken)


def test_resolved_catalog_row_allows_ribbon_multiplicity_only_when_declared() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v9.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank4-pointed-z2xz2"
    ]
    extra_hash = sha("f")
    extra_hashes = [sha(char) for char in "01234"]

    broken = copy.deepcopy(catalog)
    broken_row = {item["family_id"]: item for item in broken["families"]}[
        "rank4-pointed-z2xz2"
    ]
    broken_row["ribbon_realization_snapshot_hashes"] = (
        row["ribbon_realization_snapshot_hashes"] + [extra_hash]
    )
    with pytest.raises(FoundationSafetyError, match="ribbon multiplicity"):
        validate_low_rank_ribbon_catalog(broken)

    explicit = copy.deepcopy(broken)
    explicit_row = {item["family_id"]: item for item in explicit["families"]}[
        "rank4-pointed-z2xz2"
    ]
    explicit_row["resolved_ribbon_realization_count"] = 10
    explicit_row["ribbon_realizations_per_braided_class"] = 2
    explicit_row["ribbon_realization_snapshot_hashes"] = (
        row["ribbon_realization_snapshot_hashes"] + extra_hashes
    )
    explicit_row["ribbon_level"]["snapshot_hashes"] = explicit_row[
        "ribbon_realization_snapshot_hashes"
    ]

    validate_low_rank_ribbon_catalog(explicit)


def test_resolved_catalog_row_rejects_duplicate_snapshot_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v9.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank4-pointed-z2xz2"
    ]
    broken = copy.deepcopy(catalog)
    broken_row = {item["family_id"]: item for item in broken["families"]}[
        "rank4-pointed-z2xz2"
    ]
    broken_row["ribbon_realization_snapshot_hashes"] = [
        row["ribbon_realization_snapshot_hashes"][0],
        row["ribbon_realization_snapshot_hashes"][0],
    ]
    broken_row["resolved_modular_braided_class_count"] = 2

    with pytest.raises(FoundationSafetyError, match="unique"):
        validate_low_rank_ribbon_catalog(broken)


def test_ribbon_snapshot_gate_checks_pivotal_twist_and_certificates() -> None:
    valid = valid_ribbon_snapshot_payload()
    validate_formal_evidence(valid)

    wrong_balancing = copy.deepcopy(valid)
    wrong_balancing["structural_checks"]["balancing"] = "FAIL"
    wrong_balancing = add_content_hash(wrong_balancing)
    with pytest.raises(FoundationSafetyError, match="balancing"):
        validate_formal_evidence(wrong_balancing)

    wrong_certificate = copy.deepcopy(valid)
    wrong_certificate["certificates"]["ribbon_pivotal_compatibility"]["status"] = "FAIL"
    wrong_certificate = add_content_hash(wrong_certificate)
    with pytest.raises(FoundationSafetyError, match="ribbon_pivotal_compatibility"):
        validate_formal_evidence(wrong_certificate)


def test_scan_aggregate_needs_complete_denominator_certificate() -> None:
    incomplete = add_content_hash(
        {
            "evidence_kind": "scan_aggregate",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "scan_plan_hash": sha("f"),
            "enumerator_certificate": {"status": "INCOMPLETE_DENOMINATOR"},
            "expected_case_count": 2,
            "actual_case_count": 1,
            "aggregate_claim": "complete-no-signal-under-frozen-plan",
        }
    )

    with pytest.raises(FoundationSafetyError, match="denominator"):
        validate_formal_evidence(incomplete)


def test_scan_readiness_blocks_plan_generation_until_catalog_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v1.json")
    readiness = load_json("formal-low-rank-scan-readiness-v1.json")

    validate_formal_scan_readiness(readiness, catalog=catalog)

    assert readiness["status"] == "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG"
    assert readiness["scan_plan_generation_allowed"] is False
    assert readiness["formal_scan_plan_id"] is None
    assert "zero-ribbon-realization-snapshots-admitted" in readiness[
        "blocking_reason_ids"
    ]


def test_resource_safety_ledger_marks_preflight_and_fr_only_as_unsafe() -> None:
    ledger = load_json("resource-safety-ledger-v1.json")
    entries = {entry["resource_id"]: entry for entry in ledger["entries"]}

    assert ledger["formal_low_rank_scan_allowed_by_default"] is False
    assert all(entry["formal_low_rank_scan_allowed"] is False for entry in entries.values())
    assert entries[
        "resource:twisted-yetter:category-input:historical-da4-fr-only-no-pivotal"
    ]["safety_status"] == "unsafe_for_formal_low_rank_scan"
    assert entries[
        "resource:twisted-yetter:result:yasui-da4-c3w1-preflight"
    ]["safety_status"] == "formula_preflight_not_formal_evidence"


def test_generator_builds_self_validating_v1_artifacts() -> None:
    artifacts = MODULE.build_all()
    policy = artifacts["formal-admission-policy-v1.json"]
    catalog = artifacts["low-rank-ribbon-realization-catalog-v1.json"]
    readiness = artifacts["formal-low-rank-scan-readiness-v1.json"]

    validate_formal_admission_policy(policy)
    validate_low_rank_ribbon_catalog(catalog)
    validate_formal_scan_readiness(readiness, catalog=catalog)
    assert catalog["status"] == RIBBON_CATALOG_BLOCKED
