import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_nontrivial_partial_scan_rule_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_nontrivial_partial_scan_rule_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_rule() -> dict:
    return json.loads(
        (OUT / "low-rank-nontrivial-partial-scan-rule-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_partial_scan_rule_authorizes_only_admitted_nontrivial_subset() -> None:
    rule = load_rule()

    assert_content_hash(rule)
    assert rule["status"] == "NONTRIVIAL_PARTIAL_SCAN_RULE_ACTIVE_NO_SCAN_RUN"
    assert rule["scan_scope"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET"
    assert rule["formal_partial_scan_plan_allowed_if_validator_accepts"] is True
    assert rule["formal_partial_scan_plan_emitted"] is False
    assert rule["formal_full_scan_plan_allowed"] is False
    assert rule["formal_full_scan_complete_claim_allowed"] is False
    assert rule["admitted_resolved_nontrivial_family_ids"] == [
        "rank2-cyclic-z2",
        "rank3-cyclic-z3",
        "rank4-pointed-z4",
        "rank4-pointed-z2xz2",
        "rank4-semion-times-fibonacci",
        "rank5-su5-1",
    ]
    assert rule["excluded_blocked_nontrivial_family_ids"] == [
        "rank3-ising",
        "rank5-su2-4",
    ]


def test_partial_scan_rule_discards_trivial_rows_but_not_unknown_rows() -> None:
    rule = load_rule()

    assert rule["discarded_trivial_universal_group_family_ids"] == [
        "rank2-fibonacci-yang-lee",
        "rank3-psu2-5",
        "rank4-fibxfib",
        "rank4-psu2-7",
        "rank5-psu2-9",
    ]
    assert rule["trivial_rows_disposition"] == (
        "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
    )
    assert rule["unknown_universal_group_family_ids"] == ["rank5-psu3-4"]
    assert rule["unknown_rows_disposition"] == "EXCLUDED_NOT_DISCARDED"
    assert any("not treated as trivial" in item for item in rule["explicit_non_claims"])


def test_generator_rebuilds_partial_scan_rule_shape() -> None:
    artifacts = MODULE.build_all()
    rule = artifacts["low-rank-nontrivial-partial-scan-rule-v1.json"]

    assert rule["status"] == "NONTRIVIAL_PARTIAL_SCAN_RULE_ACTIVE_NO_SCAN_RUN"
    assert rule["formal_partial_scan_plan_emitted"] is False
    assert rule["checks"]["trivial_rows_marked_discarded"] is True
    assert rule["checks"]["unknown_rows_not_discarded"] is True
