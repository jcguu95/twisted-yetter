import importlib.util
import json
import sys
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import FoundationSafetyError, stable_content_hash
from twisted_yetter.foundation_safety import validate_formal_evidence


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "run_low_rank_product_partial_scan_benchmark_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_product_partial_scan_benchmark_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def load_benchmark() -> dict:
    return json.loads(
        (OUT / "low-rank-product-partial-scan-benchmark-v1.json").read_text(
            encoding="utf-8"
        )
    )


def load_product_snapshot() -> dict:
    return json.loads(
        (
            OUT
            / "ribbon-realization-snapshots"
            / "rank4-semion-times-fibonacci-semion-plus-x-fibonacci-plus-snapshot-v1.json"
        ).read_text(encoding="utf-8")
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_benchmark_shape(benchmark: dict) -> None:
    assert benchmark["status"] == "PASS_PRODUCT_TOY_BENCHMARK_FAST"
    assert benchmark["claim_level"] == "runtime-benchmark-preformal"
    assert benchmark["source_status"] == "preformal-runtime-benchmark-not-formal-scan-evidence"
    assert benchmark["scope"]["family_ids"] == ["rank4-semion-times-fibonacci"]
    assert benchmark["scope"]["snapshot_count"] == 8
    assert benchmark["scope"]["supported_component_counts"] == [0, 1, 2]
    assert benchmark["timing"]["case_count"] == 56
    assert len(benchmark["case_results"]) == 56
    assert benchmark["timing"]["elapsed_total_ms"] < 1000
    assert benchmark["timing"]["max_case_elapsed_ms"] < 1000
    assert {case["status"] for case in benchmark["case_results"]} == {
        "PASS_PRODUCT_BENCHMARK"
    }
    per_family = benchmark["timing"]["per_family"]["rank4-semion-times-fibonacci"]
    assert per_family["case_count"] == 56
    assert per_family["snapshot_count"] == 8
    assert len(benchmark["worker_contracts"]["distinct_character_projection_contract_hashes"]) == 8


def test_product_benchmark_artifact_records_semion_times_fib_toy_cases() -> None:
    benchmark = load_benchmark()

    assert_content_hash(benchmark)
    assert_benchmark_shape(benchmark)
    assert benchmark["checks"]["all_product_snapshots_included"] is True
    assert benchmark["checks"]["all_cases_passed"] is True
    assert benchmark["checks"]["character_projection_contracts_bound"] is True
    assert benchmark["checks"]["composite_field_expression_runtime_used"] is True
    assert benchmark["checks"]["no_formal_scan_evidence_claimed"] is True


def test_product_benchmark_artifact_is_not_formal_evidence() -> None:
    benchmark = load_benchmark()

    assert benchmark["scope"]["formal_partial_scan_plan_used"] is False
    assert benchmark["scope"]["formal_scan_case_result_produced"] is False
    assert any("not a scan_case_result" in item for item in benchmark["explicit_non_claims"])
    assert any("not a general Deligne product evaluator" in item for item in benchmark["explicit_non_claims"])

    with pytest.raises(FoundationSafetyError, match="unsupported formal evidence kind"):
        validate_formal_evidence(benchmark)


def test_product_expression_runtime_handles_composite_snapshot_values() -> None:
    assert MODULE.parse_expr("(i)*(zeta10^4)").to_json() == {"13": 1}
    assert MODULE.parse_expr("-zeta10^3 + zeta10^2 + 1").to_json() == {
        "0": 1,
        "4": 1,
        "6": -1,
    }


def test_product_character_projection_contract_is_pinned_not_guessed() -> None:
    snapshot = load_product_snapshot()
    contract = MODULE.character_projection_contract(snapshot)

    assert contract["projection_name"] == "semion_factor_first_coordinate"
    assert contract["label_to_degree"] == {
        "0|1": "0",
        "0|x": "0",
        "1|1": "1",
        "1|x": "1",
    }
    assert contract["content_hash"] == stable_content_hash(
        {key: value for key, value in contract.items() if key != "content_hash"}
    )

    bad = json.loads(json.dumps(snapshot))
    bad["category_data"]["labels"] = ["0|1", "1|1", "0|x", "1|x"]
    with pytest.raises(ValueError, match="unexpected product labels"):
        MODULE.character_projection_contract(bad)


def test_product_benchmark_generator_rebuilds_shape() -> None:
    artifacts = MODULE.build_all()
    benchmark = artifacts["low-rank-product-partial-scan-benchmark-v1.json"]

    assert_benchmark_shape(benchmark)
    assert benchmark["checks"]["all_product_snapshots_included"] is True
    assert benchmark["checks"]["all_cases_passed"] is True
    assert benchmark["checks"]["character_projection_contracts_bound"] is True
