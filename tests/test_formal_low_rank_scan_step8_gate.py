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
SCRIPT = ROOT / "experiments" / "scripts" / "build_formal_low_rank_scan_step8_gate_v1.py"
SPEC = importlib.util.spec_from_file_location("formal_low_rank_step8_gate_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_step8_target_scan_attempt_is_fail_closed() -> None:
    attempt = load_json("formal-low-rank-target-scan-attempt-v1.json")

    assert attempt["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN_OR_CONTROL_PASS"
    assert attempt["step"] == "implementation_order_step_8_admitted_exotic_target_scan_cases"
    assert attempt["evidence_kind"] == "blocked_target_scan_attempt"
    assert attempt["claim_level"] == "not-formal-scan-evidence"
    assert attempt["source_status"] == "blocked"
    assert attempt["admitted_target_set_status"] == "NOT_ENUMERATED_NO_FORMAL_SCAN_PLAN"
    assert attempt["admitted_target_scan_case_ids"] == []
    assert attempt["target_scan_case_results"] == []
    assert attempt["worker_jobs_dispatched"] == 0
    assert attempt["worker_revalidation_possible"] is False
    assert attempt["formal_target_scan_results_produced"] is False
    assert attempt["formal_scan_aggregate_candidate"] is None
    assert set(attempt["fail_closed_checks"].values()) == {"PASS"}

    blocked_reasons = set(attempt["blocked_reason_ids"])
    assert "no-formal-scan-plan" in blocked_reasons
    assert "no-formal-control-pass" in blocked_reasons
    assert "no-scan-case-ids-to-dispatch" in blocked_reasons
    assert "worker-cannot-revalidate-missing-pinned-scan-plan" in blocked_reasons

    with pytest.raises(FoundationSafetyError, match="unsupported formal evidence kind"):
        validate_formal_evidence(attempt)


def test_step8_attempt_pins_the_blocked_catalog_and_prior_gates() -> None:
    attempt = load_json("formal-low-rank-target-scan-attempt-v1.json")
    inputs = attempt["input_artifacts"]

    assert inputs["catalog"]["status"] == "PARTIAL_RIBBON_REFINEMENT_PROGRESS"
    assert inputs["catalog"]["resolved_row_count"] == 8
    assert inputs["catalog"]["blocked_row_count"] == 6
    assert inputs["step6_scan_plan_generation_attempt"]["status"] == (
        "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG"
    )
    assert inputs["step7_control_scan_attempt"]["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN"
    assert inputs["step6_7_gate"]["status"] == "STEP6_7_FAIL_CLOSED_COMPLETE"

    for record in inputs.values():
        assert record["sha256"].startswith("sha256:")
        assert record["content_hash"].startswith("sha256:")


def test_generator_builds_valid_fail_closed_step8_artifact() -> None:
    artifacts = MODULE.build_all()
    attempt = artifacts["formal-low-rank-target-scan-attempt-v1.json"]

    assert attempt["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN_OR_CONTROL_PASS"
    assert attempt["admitted_target_scan_case_ids"] == []
    assert attempt["target_scan_case_results"] == []
    assert attempt["worker_jobs_dispatched"] == 0
    assert attempt["formal_scan_aggregate_candidate"] is None
