import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_nontrivial_growth_status_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_nontrivial_growth_status_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_status() -> dict:
    return json.loads(
        (OUT / "low-rank-nontrivial-growth-status-v1.json").read_text(encoding="utf-8")
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def targets_by_family(status: dict) -> dict[str, dict]:
    return {target["family_id"]: target for target in status["growth_targets"]}


def test_nontrivial_growth_status_records_galois_candidate_validation_without_completion() -> None:
    status = load_status()

    assert_content_hash(status)
    assert status["status"] == "GALOIS_BRANCH_CANDIDATES_STRICTLY_VALIDATED_REMAINING_BRANCHES_BLOCKED"
    assert status["growth_target_family_ids"] == ["rank3-ising", "rank5-su2-4"]
    assert status["row_complete_growth_target_family_ids"] == []
    assert status["still_blocked_growth_target_family_ids"] == ["rank3-ising", "rank5-su2-4"]
    assert status["classification_status"] == "NOT_ESTABLISHED_BY_THIS_STATUS"
    assert status["scan_plan_status"] == "NOT_AUTHORIZED_BY_THIS_STATUS"
    assert any("not row-complete" in item for item in status["explicit_non_claims"])


def test_nontrivial_growth_status_keeps_all_unfinished_rows_explicit() -> None:
    status = load_status()

    assert status["trivial_rows_not_grown_for_nontrivial_universal_character_scan"] == [
        "rank2-fibonacci-yang-lee",
        "rank3-psu2-5",
        "rank4-fibxfib",
        "rank4-psu2-7",
        "rank5-psu2-9",
    ]
    assert status["unknown_rows_not_ignored"] == ["rank5-psu3-4"]

    targets = targets_by_family(status)
    assert targets["rank3-ising"]["growth_status"] == (
        "GALOIS_BRANCH_CANDIDATES_STRICTLY_VALIDATED_NOT_ROW_COMPLETE"
    )
    assert targets["rank5-su2-4"]["growth_status"] == (
        "GALOIS_BRANCH_CANDIDATES_STRICTLY_VALIDATED_EXTENSION_BRANCHES_MISSING"
    )
    assert targets["rank3-ising"]["galois_powers"] == [1, 3, 5, 7, 9, 11, 13, 15]
    assert targets["rank5-su2-4"]["galois_powers"] == [1, 5, 7, 11, 13, 17, 19, 23]
    for target in targets.values():
        assert target["strict_validation_certificate"]["status"] == (
            "PASS_STRICT_PRINCIPAL_EXPORT_REVALIDATION"
        )
        assert target["galois_branch_candidate_certificate"]["status"] == (
            "PASS_STRICT_GALOIS_BRANCH_CANDIDATE_REVALIDATION"
        )
        assert target["galois_candidate_branch_count"] == 8
        assert target["formal_row_resolution_allowed"] is False
        assert target["formal_ribbon_realization_snapshot_produced"] is False
        assert target["remaining_growth"]


def test_generator_rebuilds_nontrivial_growth_status_shape() -> None:
    artifacts = MODULE.build_all()
    status = artifacts["low-rank-nontrivial-growth-status-v1.json"]

    assert status["growth_target_family_ids"] == ["rank3-ising", "rank5-su2-4"]
    assert status["row_complete_growth_target_family_ids"] == []
    assert status["still_blocked_growth_target_family_ids"] == ["rank3-ising", "rank5-su2-4"]
    assert len(status["growth_targets"]) == 2
