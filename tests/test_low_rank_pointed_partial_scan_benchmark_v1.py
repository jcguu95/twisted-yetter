import importlib.util
import json
import sys
from pathlib import Path

from twisted_yetter.foundation_safety import FoundationSafetyError, stable_content_hash
from twisted_yetter.foundation_safety import validate_formal_evidence


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "run_low_rank_pointed_partial_scan_benchmark_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_pointed_partial_scan_benchmark_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


EXPECTED_PER_FAMILY = {
    "rank2-cyclic-z2": {"case_count": 14, "snapshot_count": 2},
    "rank3-cyclic-z3": {"case_count": 26, "snapshot_count": 2},
    "rank4-pointed-z2xz2": {"case_count": 105, "snapshot_count": 5},
    "rank4-pointed-z4": {"case_count": 84, "snapshot_count": 4},
    "rank5-su5-1": {"case_count": 62, "snapshot_count": 2},
}


def load_benchmark() -> dict:
    return json.loads(
        (OUT / "low-rank-pointed-partial-scan-benchmark-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_benchmark_shape(benchmark: dict) -> None:
    assert benchmark["status"] == "PASS_POINTED_TOY_BENCHMARK_FAST"
    assert benchmark["claim_level"] == "runtime-benchmark-preformal"
    assert benchmark["source_status"] == "preformal-runtime-benchmark-not-formal-scan-evidence"
    assert benchmark["timing"]["case_count"] == 291
    assert len(benchmark["case_results"]) == 291
    assert benchmark["scope"]["snapshot_count"] == 15
    assert benchmark["scope"]["family_ids"] == sorted(EXPECTED_PER_FAMILY)
    assert benchmark["timing"]["elapsed_total_ms"] < 1000
    assert benchmark["timing"]["max_case_elapsed_ms"] < 1000
    assert {case["status"] for case in benchmark["case_results"]} == {
        "PASS_POINTED_BENCHMARK"
    }
    for family_id, expected in EXPECTED_PER_FAMILY.items():
        actual = benchmark["timing"]["per_family"][family_id]
        assert actual["case_count"] == expected["case_count"]
        assert actual["snapshot_count"] == expected["snapshot_count"]


def test_pointed_benchmark_artifact_records_all_admitted_pointed_toy_cases() -> None:
    benchmark = load_benchmark()

    assert_content_hash(benchmark)
    assert_benchmark_shape(benchmark)
    assert benchmark["checks"]["all_pointed_admitted_families_included"] is True
    assert benchmark["checks"]["all_cases_passed"] is True
    assert benchmark["checks"]["no_formal_scan_evidence_claimed"] is True


def test_pointed_benchmark_artifact_is_not_formal_evidence() -> None:
    benchmark = load_benchmark()

    assert benchmark["scope"]["formal_partial_scan_plan_used"] is False
    assert benchmark["scope"]["formal_scan_case_result_produced"] is False
    assert any("not a scan_case_result" in item for item in benchmark["explicit_non_claims"])

    try:
        validate_formal_evidence(benchmark)
    except FoundationSafetyError as exc:
        assert "unsupported formal evidence kind" in str(exc)
    else:  # pragma: no cover - defensive fail-closed assertion
        raise AssertionError("pointed benchmark artifact unexpectedly validated")


def test_pointed_benchmark_generator_rebuilds_shape() -> None:
    artifacts = MODULE.build_all()
    benchmark = artifacts["low-rank-pointed-partial-scan-benchmark-v1.json"]

    assert_benchmark_shape(benchmark)
    assert benchmark["checks"]["all_pointed_admitted_families_included"] is True
    assert benchmark["checks"]["all_cases_passed"] is True
    assert benchmark["checks"]["no_formal_scan_evidence_claimed"] is True
