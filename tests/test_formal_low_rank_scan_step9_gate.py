import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    FoundationSafetyError,
    add_content_hash,
    validate_formal_evidence,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_formal_low_rank_scan_step9_gate_v1.py"
SPEC = importlib.util.spec_from_file_location("formal_low_rank_step9_gate_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def sha(char: str) -> str:
    return "sha256:" + char * 64


def test_step9_scan_aggregate_attempt_is_fail_closed() -> None:
    attempt = load_json("formal-low-rank-scan-aggregate-attempt-v1.json")

    assert attempt["status"] == "BLOCKED_NO_SCAN_CASE_RESULTS_OR_DENOMINATOR_CERTIFICATE"
    assert attempt["step"] == "implementation_order_step_9_scan_aggregate_and_admission_validator"
    assert attempt["evidence_kind"] == "blocked_scan_aggregate_attempt"
    assert attempt["claim_level"] == "not-formal-scan-evidence"
    assert attempt["source_status"] == "blocked"
    assert attempt["scan_case_result_count"] == 0
    assert attempt["scan_case_result_hashes"] == []
    assert attempt["expected_case_count"] is None
    assert attempt["actual_case_count"] == 0
    assert attempt["formal_scan_aggregate_produced"] is False
    assert attempt["formal_scan_aggregate_id"] is None
    assert attempt["formal_scan_aggregate_hash"] is None
    assert set(attempt["fail_closed_checks"].values()) == {"PASS"}

    blocked_reasons = set(attempt["blocked_reason_ids"])
    assert "no-formal-scan-plan" in blocked_reasons
    assert "no-target-scan-case-results" in blocked_reasons
    assert "no-enumerator-complete-denominator-certificate" in blocked_reasons

    with pytest.raises(FoundationSafetyError, match="unsupported formal evidence kind"):
        validate_formal_evidence(attempt)


def test_step9_attempt_pins_prior_blocked_gates() -> None:
    attempt = load_json("formal-low-rank-scan-aggregate-attempt-v1.json")
    inputs = attempt["input_artifacts"]

    assert inputs["catalog"]["status"] == "PARTIAL_RIBBON_REFINEMENT_PROGRESS"
    assert inputs["catalog"]["resolved_row_count"] == 8
    assert inputs["catalog"]["blocked_row_count"] == 6
    assert inputs["step6_scan_plan_generation_attempt"]["status"] == (
        "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG"
    )
    assert inputs["step7_control_scan_attempt"]["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN"
    assert inputs["step8_target_scan_attempt"]["status"] == (
        "BLOCKED_NO_FORMAL_SCAN_PLAN_OR_CONTROL_PASS"
    )

    for record in inputs.values():
        assert record["sha256"].startswith("sha256:")
        assert record["content_hash"].startswith("sha256:")


def test_step9_validator_rejects_aggregate_without_complete_denominator() -> None:
    masquerade = add_content_hash(
        {
            "evidence_kind": "scan_aggregate",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "scan_plan_hash": sha("1"),
            "enumerator_certificate": {
                "status": "MISSING_NO_FORMAL_SCAN_PLAN",
                "content_hash": None,
            },
            "expected_case_count": 0,
            "actual_case_count": 0,
            "aggregate_claim": "complete-no-signal-under-frozen-plan",
        }
    )

    with pytest.raises(FoundationSafetyError, match="complete denominator certificate"):
        validate_formal_evidence(masquerade)


def test_step9_validator_rejects_global_no_go_aggregate_claim() -> None:
    global_no_go = add_content_hash(
        {
            "evidence_kind": "scan_aggregate",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "scan_plan_hash": sha("2"),
            "enumerator_certificate": {"status": "PASS_COMPLETE_DENOMINATOR"},
            "expected_case_count": 0,
            "actual_case_count": 0,
            "aggregate_claim": "global-no-go-theorem",
        }
    )

    with pytest.raises(FoundationSafetyError, match="global no-go theorem"):
        validate_formal_evidence(global_no_go)


def test_generator_builds_valid_fail_closed_step9_artifact() -> None:
    artifacts = MODULE.build_all()
    attempt = artifacts["formal-low-rank-scan-aggregate-attempt-v1.json"]

    assert attempt["status"] == "BLOCKED_NO_SCAN_CASE_RESULTS_OR_DENOMINATOR_CERTIFICATE"
    assert attempt["scan_case_result_count"] == 0
    assert attempt["formal_scan_aggregate_produced"] is False
    assert attempt["formal_scan_aggregate_hash"] is None
