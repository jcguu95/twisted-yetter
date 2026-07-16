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
    / "build_ising_formal_map_source_decision_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "ising_formal_map_source_decision_v1", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_decision() -> dict:
    return json.loads(
        (OUT / "ising-formal-map-source-decision-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_blocker_hash(blocker: dict) -> None:
    body = dict(blocker)
    blocker_hash = body.pop("blocker_hash")
    assert blocker_hash == stable_content_hash(body)


def test_ising_formal_map_source_decision_is_terminal_repo_local_blocker() -> None:
    decision = load_decision()

    assert_content_hash(decision)
    assert decision["status"] == "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER"
    assert decision["decision"]["can_implement_formal_exporter_from_current_repo_local_sources"] is False
    assert decision["decision"]["can_promote_ising_candidate_payloads_to_snapshots"] is False
    assert decision["decision"]["formal_scan_plan_allowed"] is False
    assert decision["decision"]["row_complete_status"] == (
        "TERMINAL_BLOCKED_UNTIL_NEW_FORMAL_MAP_SOURCE"
    )
    assert set(decision["checks"].values()) == {True}


def test_ising_formal_map_source_decision_records_source_inventory() -> None:
    decision = load_decision()
    blocker = decision["terminal_blocker"]

    assert_blocker_hash(blocker)
    assert blocker["terminal_status"] == "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER"
    assert blocker["blocked_scope"] == (
        "current repo-local Ising row-complete ribbon realization snapshot production"
    )
    assert len(blocker["source_inventory_decisions"]) == 6
    source_ids = {item["source_id"] for item in blocker["source_inventory_decisions"]}
    assert {
        "su2k-fusion-braid-evaluator",
        "su2-k-standard-pivotal-profile",
        "legacy-ribbon-category-v2-adapter",
        "su2-2-rf-local-backend",
        "su2-2-rf-omega-backend",
        "sage-readme-evaluator-map",
    } == source_ids
    assert all(item["sha256"].startswith("sha256:") for item in blocker["source_inventory_decisions"])


def test_ising_formal_map_source_decision_does_not_overclaim() -> None:
    decision = load_decision()
    blocker = decision["terminal_blocker"]

    assert any(
        "future work that adds a source-backed formal SU(2)_2 eval/coeval derivation"
        in item
        for item in blocker["not_blocked_scope"]
    )
    assert any(
        "does not claim the mathematical Ising row is impossible" in item
        for item in decision["explicit_non_claims"]
    )
    assert any(
        "only blocks current repo-local formal snapshot production" in item
        for item in decision["explicit_non_claims"]
    )
    assert len(blocker["required_source_gaps"]) == 6
    assert any("square-root branch ledger" in item for item in blocker["required_source_gaps"])


def test_generator_rebuilds_ising_formal_map_source_decision_shape() -> None:
    artifacts = MODULE.build_all()
    decision = artifacts["ising-formal-map-source-decision-v1.json"]

    assert decision["status"] == "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER"
    assert decision["decision"]["can_implement_formal_exporter_from_current_repo_local_sources"] is False
    assert len(decision["terminal_blocker"]["source_inventory_decisions"]) == 6
