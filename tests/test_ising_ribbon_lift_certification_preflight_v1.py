import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = (
    ROOT
    / "experiments"
    / "scripts"
    / "build_ising_ribbon_lift_certification_preflight_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "ising_ribbon_lift_certification_preflight_v1", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_preflight() -> dict:
    return json.loads(
        (OUT / "ising-ribbon-lift-certification-preflight-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_preflight_record_hash(record: dict) -> None:
    body = dict(record)
    record_hash = body.pop("preflight_record_hash")
    assert record_hash == stable_content_hash(body)


def test_ising_certification_preflight_blocks_all_candidate_payloads() -> None:
    preflight = load_preflight()

    assert_content_hash(preflight)
    assert preflight["status"] == "ISING_RIBBON_LIFT_CERTIFICATION_BLOCKED"
    assert preflight["candidate_payload_count"] == 16
    assert preflight["ready_for_snapshot_promotion_count"] == 0
    assert preflight["blocked_payload_count"] == 16
    assert preflight["formal_snapshot_count"] == 0
    assert preflight["row_complete_status"] == "NOT_ROW_COMPLETE"
    assert preflight["formal_scan_plan_allowed"] is False
    assert set(preflight["checks"].values()) == {True}


def test_ising_certification_preflight_records_missing_formal_requirements() -> None:
    preflight = load_preflight()
    required = preflight["formal_snapshot_promotion_requirements"]

    assert required["category_contract"] == "RibbonFusionCategoryV2"
    assert required["producer_exact_coherence"] == "PASS_REQUIRED"
    assert required["consumer_runtime_coherence"] == "PASS_REQUIRED"
    assert required["ribbon_pivotal_compatibility_certificate"] == "PASS_REQUIRED"
    assert required["balancing"] == "PASS_REQUIRED"

    for record in preflight["preflight_records"]:
        assert_preflight_record_hash(record)
        assert record["preflight_status"] == (
            "BLOCKED_MISSING_FORMAL_PIVOTAL_RIBBON_EVIDENCE"
        )
        assert record["formal_snapshot_hash"] is None
        assert record["checks"]["candidate_payload_hash_present"] is True
        assert record["checks"]["source_branch_hash_present"] is True
        assert record["checks"]["f_r_twist_fusion_payload_present"] is True
        assert record["checks"]["evaluation_coevaluation_maps_materialized"] is False
        assert record["checks"]["fusion_pairing_certified"] is False
        assert record["checks"]["producer_exact_certificate_passed"] is False
        assert record["checks"]["runtime_consumer_certificate_passed"] is False
        assert record["checks"]["ribbon_pivotal_certificate_passed"] is False
        assert record["checks"]["formal_snapshot_produced"] is False
        assert {
            "evaluation_coevaluation_maps_materialized",
            "fusion_pairing_certified",
            "producer_exact_certificate_passed",
            "runtime_consumer_certificate_passed",
            "ribbon_pivotal_certificate_passed",
            "formal_snapshot_produced",
        }.issubset(set(record["missing_requirements"]))


def test_numeric_pivotal_profile_is_not_promoted_to_formal_certificate() -> None:
    preflight = load_preflight()
    profile = preflight["input_artifacts"]["numeric_pivotal_profile_reference"]

    assert profile["status"] == "SUPPORTED_FOR_NUMERIC_MORSE_CONTROLS"
    assert profile["formal_certificate"] is False
    assert "not a producer/runtime/ribbon-pivotal formal certificate" in profile["reason"]
    assert preflight["checks"]["numeric_pivotal_profile_is_not_formal_certificate"] is True
    assert any(
        "numeric SU(2)_k pivotal profile is not used as a formal certificate" in item
        for item in preflight["explicit_non_claims"]
    )


def test_generator_rebuilds_ising_certification_preflight_shape() -> None:
    artifacts = MODULE.build_all()
    preflight = artifacts["ising-ribbon-lift-certification-preflight-v1.json"]

    assert preflight["status"] == "ISING_RIBBON_LIFT_CERTIFICATION_BLOCKED"
    assert preflight["candidate_payload_count"] == 16
    assert preflight["ready_for_snapshot_promotion_count"] == 0
    assert preflight["blocked_payload_count"] == 16
    assert len(preflight["preflight_records"]) == 16
