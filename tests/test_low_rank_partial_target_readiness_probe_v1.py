import importlib.util
import json
import sys
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import FoundationSafetyError, validate_formal_evidence


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_partial_target_readiness_probe_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_partial_target_probe_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def load_probe() -> dict:
    return json.loads(
        (OUT / "low-rank-partial-target-readiness-probe-v1.json").read_text(
            encoding="utf-8"
        )
    )


def test_partial_target_probe_records_next_bottleneck_after_toy_aggregate() -> None:
    probe = load_probe()

    assert probe["status"] == "BLOCKED_NO_CERTIFIED_TARGET_INPUT_FOR_PARTIAL_SCAN"
    assert probe["claim_level"] == "not-formal-scan-evidence"
    assert probe["source_status"] == "blocked"
    assert probe["readiness_probe"] == {
        "formal_partial_toy_scan_aggregate_complete": True,
        "target_manifold_catalog_ready": False,
        "certified_exotic_input_ready": False,
        "worker_dispatch_allowed": False,
        "target_scan_case_results_produced": False,
    }
    blocked_reasons = set(probe["blocked_reason_ids"])
    assert "n70-blocked-no-certified-input" in blocked_reasons
    assert "missing-machine-readable-exotic-kirby-diagrams" in blocked_reasons
    assert "no-admitted-target-manifold-catalog" in blocked_reasons
    assert "partial-toy-aggregate-cannot-substitute-target-scan" in blocked_reasons
    assert set(probe["fail_closed_checks"].values()) == {"PASS"}


def test_partial_target_probe_is_not_formal_evidence() -> None:
    probe = load_probe()

    with pytest.raises(FoundationSafetyError, match="unsupported formal evidence kind"):
        validate_formal_evidence(probe)
    assert any("not a scan_case_result" in item for item in probe["explicit_non_claims"])
    assert any("does not claim no signal" in item for item in probe["explicit_non_claims"])


def test_partial_target_probe_builder_rebuilds_same_blocked_shape() -> None:
    artifacts = MODULE.build_all()
    probe = artifacts["low-rank-partial-target-readiness-probe-v1.json"]

    assert probe["status"] == "BLOCKED_NO_CERTIFIED_TARGET_INPUT_FOR_PARTIAL_SCAN"
    assert probe["readiness_probe"]["formal_partial_toy_scan_aggregate_complete"] is True
    assert probe["readiness_probe"]["target_manifold_catalog_ready"] is False
    assert probe["readiness_probe"]["worker_dispatch_allowed"] is False
