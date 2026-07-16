import importlib.util
import json
import sys
from pathlib import Path

from twisted_yetter.foundation_safety import FoundationSafetyError, stable_content_hash
from twisted_yetter.foundation_safety import validate_formal_evidence


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "probe_low_rank_product_partial_scan_surface_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_product_partial_scan_surface_probe_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def load_probe() -> dict:
    return json.loads(
        (OUT / "low-rank-product-partial-scan-surface-probe-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_probe_shape(probe: dict) -> None:
    assert probe["status"] == "BLOCKED_PRODUCT_ROW_EXECUTABLE_SURFACE_NOT_READY"
    assert probe["claim_level"] == "runtime-surface-probe-preformal"
    assert probe["source_status"] == "bottleneck-artifact-not-formal-scan-evidence"
    assert probe["scope"]["family_id"] == "rank4-semion-times-fibonacci"
    assert probe["scope"]["snapshot_count"] == 8
    assert probe["scope"]["formal_partial_scan_plan_used"] is False
    assert probe["scope"]["formal_scan_case_result_produced"] is False
    assert probe["surface_observations"]["validated_snapshot_count"] == 8
    assert probe["surface_observations"]["factorwise_f_r_construction_snapshot_count"] == 8
    assert probe["surface_observations"]["labels_per_snapshot"] == [4]
    assert probe["terminal_bottleneck"]["bottleneck_kind"] == (
        "IMPLEMENTATION_GAP_NOT_CATEGORY_DATA_GAP"
    )
    blocker_ids = {
        item["blocker_id"] for item in probe["terminal_bottleneck"]["blockers"]
    }
    assert blocker_ids == {
        "product-row-formal-worker-not-implemented",
        "composite-field-expression-runtime-not-implemented",
        "universal-character-projection-for-product-labels-not-bound-to-worker",
    }


def test_product_surface_probe_records_next_real_bottleneck() -> None:
    probe = load_probe()

    assert_content_hash(probe)
    assert_probe_shape(probe)
    assert probe["checks"]["partial_rule_admits_product_family"] is True
    assert probe["checks"]["all_product_snapshots_validate_as_formal_category_evidence"] is True
    assert probe["checks"]["toy_diagrams_load"] is True
    assert probe["checks"]["no_product_scan_case_result_produced"] is True
    assert probe["checks"]["bottleneck_recorded_fail_closed"] is True


def test_product_surface_probe_artifact_is_not_formal_evidence() -> None:
    probe = load_probe()

    assert any("not a scan_case_result" in item for item in probe["explicit_non_claims"])
    assert any("does not invalidate the product row snapshots" in item for item in probe["explicit_non_claims"])

    try:
        validate_formal_evidence(probe)
    except FoundationSafetyError as exc:
        assert "unsupported formal evidence kind" in str(exc)
    else:  # pragma: no cover - defensive fail-closed assertion
        raise AssertionError("product surface probe artifact unexpectedly validated")


def test_product_surface_probe_generator_rebuilds_shape() -> None:
    artifacts = MODULE.build_all()
    probe = artifacts["low-rank-product-partial-scan-surface-probe-v1.json"]

    assert_probe_shape(probe)
    assert probe["checks"]["partial_rule_admits_product_family"] is True
    assert probe["checks"]["all_product_snapshots_validate_as_formal_category_evidence"] is True
    assert probe["checks"]["bottleneck_recorded_fail_closed"] is True
