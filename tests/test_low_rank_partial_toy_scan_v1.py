import importlib.util
import json
import sys
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import FoundationSafetyError, validate_formal_evidence


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_partial_toy_scan_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_partial_toy_scan_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_partial_toy_scan_plan_is_formal_but_not_full_scan_plan() -> None:
    plan = load_json("formal-low-rank-partial-toy-scan-plan-v1.json")

    validate_formal_evidence(plan)
    assert plan["evidence_kind"] == "partial_scan_plan"
    assert plan["scan_scope"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET"
    assert plan["toy_scope_notice"] == "Only the three checked-in toy diagrams are in this plan."
    assert plan["partial_scan_complete_claim_allowed"] is True
    assert plan["full_scan_complete_claim_allowed"] is False
    assert plan["scan_case_ids"] == [
        "partial-toy-pointed-chunk-v1",
        "partial-toy-product-semion-times-fib-chunk-v1",
    ]
    assert set(plan["pinned_hashes"]) == {
        "category_subset_catalog",
        "manifold_catalog",
        "character_assignment_catalog",
        "evaluator_profile",
        "numeric_policy",
        "execution_semantics",
        "exclusion_ledger",
    }
    assert "rank3-ising" in plan["excluded_blocked_family_ids"]
    assert "rank5-su2-4" in plan["excluded_blocked_family_ids"]
    assert "rank5-psu3-4" in plan["unknown_universal_group_family_ids"]


def test_partial_toy_scan_case_results_validate_and_pin_plan() -> None:
    plan = load_json("formal-low-rank-partial-toy-scan-plan-v1.json")
    pointed = load_json("formal-low-rank-partial-toy-scan-case-pointed-v1.json")
    product = load_json("formal-low-rank-partial-toy-scan-case-product-v1.json")

    for case in (pointed, product):
        validate_formal_evidence(case)
        assert case["scan_plan_hash"] == plan["content_hash"]
        assert case["worker_revalidated_hashes"] is True
        assert case["chunk_status"] == "PASS"
        assert case["input_hashes"]["scan_plan"] == plan["content_hash"]

    assert pointed["scan_case_id"] == "partial-toy-pointed-chunk-v1"
    assert pointed["subcase_count"] == 291
    assert pointed["result_summary"]["benchmark_status"] == "PASS_POINTED_TOY_BENCHMARK_FAST"
    assert product["scan_case_id"] == "partial-toy-product-semion-times-fib-chunk-v1"
    assert product["subcase_count"] == 56
    assert product["result_summary"]["benchmark_status"] == "PASS_PRODUCT_TOY_BENCHMARK_FAST"


def test_partial_toy_scan_aggregate_validates_but_cannot_claim_full_completion() -> None:
    aggregate = load_json("formal-low-rank-partial-toy-scan-aggregate-v1.json")

    validate_formal_evidence(aggregate)
    assert aggregate["evidence_kind"] == "partial_scan_aggregate"
    assert aggregate["status"] == "FORMAL_PARTIAL_TOY_SCAN_AGGREGATE_COMPLETE"
    assert aggregate["aggregate_claim"] == "partial-toy-scan-complete-for-admitted-subset"
    assert aggregate["expected_case_count"] == 2
    assert aggregate["actual_case_count"] == 2
    assert aggregate["enumerator_certificate"]["expected_subcase_count"] == 347
    assert aggregate["enumerator_certificate"]["actual_subcase_count"] == 347
    assert any("does not claim complete-no-signal" in item for item in aggregate["explicit_non_claims"])

    bad = dict(aggregate)
    bad["aggregate_claim"] = "complete-no-signal"
    bad["content_hash"] = MODULE.stable_content_hash(
        {key: value for key, value in bad.items() if key != "content_hash"}
    )
    with pytest.raises(FoundationSafetyError, match="partial aggregate cannot claim full completion"):
        validate_formal_evidence(bad)


def test_partial_toy_scan_builder_rebuilds_valid_artifacts() -> None:
    artifacts = MODULE.build_all()

    plan = artifacts["formal-low-rank-partial-toy-scan-plan-v1.json"]
    pointed = artifacts["formal-low-rank-partial-toy-scan-case-pointed-v1.json"]
    product = artifacts["formal-low-rank-partial-toy-scan-case-product-v1.json"]
    aggregate = artifacts["formal-low-rank-partial-toy-scan-aggregate-v1.json"]

    for payload in artifacts.values():
        validate_formal_evidence(payload)
    assert pointed["scan_plan_hash"] == plan["content_hash"]
    assert product["scan_plan_hash"] == plan["content_hash"]
    assert aggregate["scan_plan_hash"] == plan["content_hash"]
    assert aggregate["expected_case_count"] == 2
    assert aggregate["actual_case_count"] == 2
