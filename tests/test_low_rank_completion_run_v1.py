import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_completion_run_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_completion_run_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


BLOCKED_ROW_ORDER = [
    "rank3-ising",
    "rank3-psu2-5",
    "rank4-psu2-7",
    "rank5-su2-4",
    "rank5-psu2-9",
    "rank5-psu3-4",
]


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_completion_run_records_terminal_blocked_result_without_scan_complete() -> None:
    ledger = load_json("low-rank-completion-run-v1.json")

    assert ledger["status"] == "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED"
    assert ledger["terminal_result_kind"] == "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED"
    assert ledger["final_claims_admission_state"] == "PAUSED_FOR_USER_REVIEW"
    assert ledger["starting_state"]["catalog_status"] == "PARTIAL_RIBBON_REFINEMENT_PROGRESS"
    assert ledger["starting_state"]["resolved_row_count"] == 8
    assert ledger["starting_state"]["blocked_row_count"] == 6
    assert ledger["starting_state"]["blocked_family_ids"] == BLOCKED_ROW_ORDER
    assert ledger["starting_state"]["formal_scan_plan_allowed"] is False
    assert ledger["starting_state"]["scan_plan_generation_allowed"] is False
    assert ledger["starting_state"]["formal_scan_plan_produced"] is False
    assert ledger["starting_state"]["formal_control_results_produced"] is False
    assert ledger["starting_state"]["formal_target_scan_results_produced"] is False
    assert ledger["starting_state"]["formal_scan_aggregate_produced"] is False
    assert "This run does not claim no-signal." in ledger["explicit_non_claims"]


def test_completion_run_does_not_skip_any_blocked_nonpointed_row() -> None:
    ledger = load_json("low-rank-completion-run-v1.json")
    rows = ledger["row_resolution_records"]

    assert ledger["row_resolution_order"] == BLOCKED_ROW_ORDER
    assert [row["family_id"] for row in rows] == BLOCKED_ROW_ORDER
    for row in rows:
        assert row["terminal_status"] == "TERMINAL_BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
        assert row["formal_admission_allowed"] is False
        assert row["snapshot_inventory_count"] == 0
        assert row["snapshot_inventory_paths"] == []
        assert "ribbon_realization_snapshot" in row["required_evidence"]
        assert "producer_exact_or_symbolic_coherence_certificate" in row["required_evidence"]
        assert "runtime_consumer_coherence_certificate" in row["required_evidence"]
        assert "ribbon_pivotal_compatibility_certificate" in row["required_evidence"]
        assert row["blocked_by"]
        assert row["missing_evidence"]


def test_terminal_blocker_is_a_blocker_not_a_final_scan_claim() -> None:
    ledger = load_json("low-rank-completion-run-v1.json")
    blocker = load_json("low-rank-ribbon-classification-terminal-blocked-v1.json")

    assert blocker["status"] == "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED"
    assert blocker["run_ledger_hash"] == ledger["content_hash"]
    assert blocker["terminal_blocked_family_ids"] == BLOCKED_ROW_ORDER
    assert blocker["terminal_blocked_row_count"] == 6
    assert blocker["formal_scan_route_status"] == "STOPPED_BEFORE_SCAN_PLAN"
    assert blocker["proposed_ctl_claim_kind"] == "terminal_blocker_not_scan_complete"
    assert "Not FORMAL_LOW_RANK_SCAN_COMPLETE." in blocker["explicit_non_claims"]
    assert "Not a no-signal result." in blocker["explicit_non_claims"]


def test_review_package_pauses_before_final_claim_admission() -> None:
    ledger = load_json("low-rank-completion-run-v1.json")
    blocker = load_json("low-rank-ribbon-classification-terminal-blocked-v1.json")
    review = load_json("low-rank-final-claim-review-package-v1.json")

    assert review["status"] == "READY_FOR_USER_REVIEW_BEFORE_FINAL_CLAIMS"
    assert review["run_ledger_hash"] == ledger["content_hash"]
    assert review["terminal_blocker_hash"] == blocker["content_hash"]
    assert review["review_required_before_admission"] is True
    assert review["final_claims_admitted"] is False
    assert review["proposed_final_ctl_claims"][0]["status"] == "PROPOSED_NOT_ADMITTED"
    assert "FORMAL_LOW_RANK_SCAN_COMPLETE" in review["claims_explicitly_not_proposed"]


def test_generator_builds_consistent_terminal_blocked_artifacts() -> None:
    artifacts = MODULE.build_all()
    ledger = artifacts["low-rank-completion-run-v1.json"]
    blocker = artifacts["low-rank-ribbon-classification-terminal-blocked-v1.json"]
    review = artifacts["low-rank-final-claim-review-package-v1.json"]

    assert ledger["status"] == "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED"
    assert blocker["run_ledger_hash"] == ledger["content_hash"]
    assert review["run_ledger_hash"] == ledger["content_hash"]
    assert review["terminal_blocker_hash"] == blocker["content_hash"]
