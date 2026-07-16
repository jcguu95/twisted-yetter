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
    / "build_low_rank_ribbon_classification_terminal_blocked_v2.py"
)
SPEC = importlib.util.spec_from_file_location(
    "low_rank_ribbon_classification_terminal_blocked_v2", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_blocker() -> dict:
    return json.loads(
        (OUT / "low-rank-ribbon-classification-terminal-blocked-v2.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_classification_blocker_hash(blocker: dict) -> None:
    body = dict(blocker)
    blocker_hash = body.pop("classification_blocker_hash")
    assert blocker_hash == stable_content_hash(body)


def test_low_rank_classification_terminal_blocker_closes_catalog_and_scan_route() -> None:
    blocker = load_blocker()

    assert_content_hash(blocker)
    assert blocker["status"] == "LOW_RANK_RIBBON_CLASSIFICATION_TERMINAL_BLOCKED"
    assert blocker["formal_terminal_result"] == "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED"
    assert set(blocker["checks"].values()) == {True}
    assert blocker["catalog_state"]["catalog_established"] is False
    assert blocker["catalog_state"]["primary_blocked_family_id"] == "rank3-ising"
    assert blocker["scan_route_state"]["formal_scan_plan_allowed"] is False
    assert blocker["scan_route_state"]["formal_aggregate_allowed"] is False
    assert blocker["scan_route_state"]["final_scan_complete_claim_allowed"] is False
    assert blocker["scan_route_state"]["no_signal_claim_allowed"] is False


def test_low_rank_classification_terminal_blocker_pins_ising_source_blocker() -> None:
    blocker = load_blocker()
    classification = blocker["classification_blocker"]

    assert_classification_blocker_hash(classification)
    assert classification["primary_blocking_family_id"] == "rank3-ising"
    assert classification["primary_blocker_status"] == (
        "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER"
    )
    assert classification["primary_blocker_hash"].startswith("sha256:")
    assert classification["catalog_established"] is False
    assert classification["formal_scan_plan_allowed"] is False
    assert classification["aggregate_allowed"] is False
    assert classification["scan_complete_claim_allowed"] is False
    assert classification["no_signal_claim_allowed"] is False
    assert blocker["input_artifacts"]["ising_formal_map_source_decision"]["status"] == (
        "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER"
    )


def test_low_rank_classification_terminal_blocker_preserves_gate_failures() -> None:
    blocker = load_blocker()
    gates = blocker["scan_route_state"]["gate_statuses"]

    assert gates == {
        "scan_plan_generation": "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG",
        "control_scan": "BLOCKED_NO_FORMAL_SCAN_PLAN",
        "target_scan": "BLOCKED_NO_FORMAL_SCAN_PLAN_OR_CONTROL_PASS",
        "scan_aggregate": "BLOCKED_NO_SCAN_CASE_RESULTS_OR_DENOMINATOR_CERTIFICATE",
    }
    assert any("not a completed scan" in item for item in blocker["terminal_explanation"])
    assert any("does not claim no signal" in item for item in blocker["explicit_non_claims"])
    assert any("does not claim the mathematical Ising row is impossible" in item for item in blocker["explicit_non_claims"])


def test_generator_rebuilds_low_rank_terminal_blocker_shape() -> None:
    artifacts = MODULE.build_all()
    blocker = artifacts["low-rank-ribbon-classification-terminal-blocked-v2.json"]

    assert blocker["status"] == "LOW_RANK_RIBBON_CLASSIFICATION_TERMINAL_BLOCKED"
    assert blocker["formal_terminal_result"] == "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED"
    assert blocker["classification_blocker"]["primary_blocking_family_id"] == "rank3-ising"
    assert blocker["scan_route_state"]["formal_scan_plan_allowed"] is False
