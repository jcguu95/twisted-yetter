import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    FoundationSafetyError,
    validate_formal_evidence,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_formal_low_rank_scan_step6_7_gate_v1.py"
SPEC = importlib.util.spec_from_file_location("formal_low_rank_step6_7_gate_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_step6_scan_plan_generation_attempt_is_fail_closed() -> None:
    attempt = load_json("formal-low-rank-scan-plan-generation-attempt-v1.json")

    assert attempt["status"] == "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG"
    assert attempt["step"] == "implementation_order_step_6_scan_plan_generator"
    assert attempt["claim_level"] == "not-formal-scan-evidence"
    assert attempt["formal_scan_plan_produced"] is False
    assert attempt["formal_scan_plan_id"] is None
    assert attempt["formal_scan_plan_hash"] is None
    assert attempt["scan_case_ids"] == []
    assert attempt["resolved_row_count"] == 8
    assert attempt["blocked_row_count"] == 6
    assert "catalog-status-is-not-established" in attempt["blocked_reason_ids"]
    assert "ribbon-denominator-is-not-final" in attempt["blocked_reason_ids"]
    assert set(attempt["fail_closed_checks"].values()) == {"PASS"}

    with pytest.raises(FoundationSafetyError, match="unsupported formal evidence kind"):
        validate_formal_evidence(attempt)


def test_step7_controls_do_not_run_without_formal_scan_plan() -> None:
    attempt = load_json("formal-low-rank-control-scan-attempt-v1.json")

    assert attempt["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN"
    assert attempt["step"] == "implementation_order_step_7_controls"
    assert attempt["claim_level"] == "not-formal-scan-evidence"
    assert attempt["formal_scan_case_results_produced"] is False
    assert attempt["control_case_results"] == []
    assert attempt["alpha0_control_status"] == "NOT_RUN_NO_FORMAL_SCAN_PLAN"
    assert attempt["ordinary_control_status"] == "NOT_RUN_NO_FORMAL_SCAN_PLAN"
    assert [item["target"] for item in attempt["control_targets"]] == [
        "S4",
        "CP2",
        "S2xS2",
        "unlink/Hopf",
        "alpha=0",
    ]
    assert set(attempt["fail_closed_checks"].values()) == {"PASS"}

    with pytest.raises(FoundationSafetyError, match="unsupported formal evidence kind"):
        validate_formal_evidence(attempt)


def test_step6_7_gate_summary_records_blocked_completion_semantics() -> None:
    scan_plan_attempt = load_json("formal-low-rank-scan-plan-generation-attempt-v1.json")
    control_attempt = load_json("formal-low-rank-control-scan-attempt-v1.json")
    summary = load_json("formal-low-rank-step6-7-gate-v1.json")

    assert summary["status"] == "STEP6_7_FAIL_CLOSED_COMPLETE"
    assert "fail-closed gates" in summary["completion_semantics"]
    assert summary["scan_plan_generation_attempt_hash"] == scan_plan_attempt["content_hash"]
    assert summary["control_scan_attempt_hash"] == control_attempt["content_hash"]
    assert summary["step_status"] == {
        "implementation_order_step_6_scan_plan_generator": "COMPLETE_FAIL_CLOSED_BLOCKED",
        "implementation_order_step_7_controls": "COMPLETE_FAIL_CLOSED_BLOCKED",
    }
    assert summary["formal_outputs"] == {
        "scan_plan": None,
        "scan_case_results": [],
        "scan_aggregate": None,
    }
    assert "FORMAL_LOW_RANK_SCAN_COMPLETE is still not claimed." in summary[
        "explicit_non_claims"
    ]


def test_generator_builds_valid_fail_closed_step6_7_artifacts() -> None:
    artifacts = MODULE.build_all()
    scan_plan_attempt = artifacts[
        "formal-low-rank-scan-plan-generation-attempt-v1.json"
    ]
    control_attempt = artifacts["formal-low-rank-control-scan-attempt-v1.json"]
    summary = artifacts["formal-low-rank-step6-7-gate-v1.json"]

    assert scan_plan_attempt["status"] == "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG"
    assert control_attempt["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN"
    assert summary["status"] == "STEP6_7_FAIL_CLOSED_COMPLETE"
    assert summary["formal_outputs"]["scan_plan"] is None
    assert summary["formal_outputs"]["scan_case_results"] == []
