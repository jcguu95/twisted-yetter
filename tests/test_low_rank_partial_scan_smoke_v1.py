import importlib.util
import json
import sys
from pathlib import Path

from twisted_yetter.foundation_safety import FoundationSafetyError, stable_content_hash
from twisted_yetter.foundation_safety import validate_formal_evidence


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "run_low_rank_partial_scan_smoke_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_partial_scan_smoke_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def load_smoke() -> dict:
    return json.loads(
        (OUT / "low-rank-nontrivial-partial-scan-smoke-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_smoke_artifact_records_fast_rank2_z2_toy_cases_only() -> None:
    smoke = load_smoke()

    assert_content_hash(smoke)
    assert smoke["status"] == "PASS_RUNTIME_SMOKE_FAST"
    assert smoke["claim_level"] == "runtime-smoke-preformal"
    assert smoke["scope"]["family_ids"] == ["rank2-cyclic-z2"]
    assert smoke["scope"]["snapshot_ids"] == [
        "rank2-cyclic-z2-semion-plus",
        "rank2-cyclic-z2-semion-minus",
    ]
    assert smoke["timing"]["case_count"] == 10
    assert len(smoke["case_results"]) == 10
    assert smoke["timing"]["elapsed_total_ms"] < 1000
    assert smoke["timing"]["max_case_elapsed_ms"] < 1000
    assert {case["status"] for case in smoke["case_results"]} == {
        "PASS_RUNTIME_SMOKE"
    }


def test_smoke_artifact_is_not_formal_evidence() -> None:
    smoke = load_smoke()

    assert smoke["scope"]["formal_partial_scan_plan_used"] is False
    assert smoke["scope"]["formal_scan_case_result_produced"] is False
    assert any("not a scan_case_result" in item for item in smoke["explicit_non_claims"])

    try:
        validate_formal_evidence(smoke)
    except FoundationSafetyError as exc:
        assert "unsupported formal evidence kind" in str(exc)
    else:  # pragma: no cover - defensive fail-closed assertion
        raise AssertionError("runtime smoke artifact unexpectedly validated")


def test_smoke_generator_rebuilds_shape() -> None:
    artifacts = MODULE.build_all()
    smoke = artifacts["low-rank-nontrivial-partial-scan-smoke-v1.json"]

    assert smoke["status"] == "PASS_RUNTIME_SMOKE_FAST"
    assert smoke["timing"]["case_count"] == 10
    assert smoke["checks"]["all_cases_passed"] is True
    assert smoke["checks"]["no_formal_scan_evidence_claimed"] is True
