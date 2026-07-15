import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"


def load_json(name: str):
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_review_input_snapshots_are_durable_and_hash_checked():
    bundle = load_json("review-input-bundle-v0.json")

    assert bundle["status"] == "SEED_DRAFT_NOT_ADMITTED"
    assert bundle["input_count"] >= 12
    assert bundle["bundle_policy"]["manager_and_red_team_prose_is_non_normative"] is True

    for entry in bundle["inputs"]:
        snapshot_path = ROOT / entry["snapshot_path"]
        snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
        content = snapshot["content_utf8"].encode("utf-8")
        assert hashlib.sha256(content).hexdigest() == entry["sha256"]
        assert len(content) == entry["byte_length"]
        assert snapshot["normative_status"] == "NOT_NORMATIVE_NOT_CTL_ADMITTED"


def test_blocker_registry_preserves_open_p0s_without_group_closure():
    registry = load_json("blocker-registry-v0.json")
    coverage = load_json("blocker-coverage-matrix-v0.json")

    assert registry["closure_semantics"]["manager_acceptance_is_not_closure"] is True
    assert registry["closure_semantics"]["group_views_are_not_closure_units"] is True
    assert registry["blocker_count"] >= 100
    assert {item["severity"] for item in registry["blockers"]} == {"P0"}
    assert {item["status"] for item in registry["blockers"]} == {"OPEN"}

    coverage_by_id = {row["blocker_id"]: row for row in coverage["rows"]}
    assert set(coverage_by_id) == {item["blocker_id"] for item in registry["blockers"]}
    assert {row["closure_status"] for row in coverage["rows"]} == {"OPEN"}
    assert {row["guard_status"] for row in coverage["rows"]} == {"MISSING"}


def test_formal_admission_policy_blocks_all_formal_scan_routes():
    policy = load_json("formal-admission-policy-v0.json")

    assert policy["policy_status"] == "EMPTY_ALLOWLIST_BLOCK_ALL_FORMAL_SCAN_EVIDENCE"
    assert policy["formal_result_routes_allowlist"] == []
    assert policy["ready_targets_allowlist"] == []
    assert policy["claim_constructors_allowlist"] == []
    assert "No READY_FOR_SIGNAL_SCAN target is admitted." in policy["explicit_non_claims"]


def test_known_execution_surface_inventory_is_not_a_closed_world_claim():
    inventory = load_json("known-execution-surface-inventory-v0.json")

    assert inventory["completeness"] == "NOT_PROVABLE_KNOWN_SURFACES_ONLY"
    assert inventory["security_boundary"] == (
        "official_admission_and_publication_consumers_not_execution_prevention"
    )
    assert inventory["candidate_count"] > 0
    assert all(candidate["formal_admission_allowed"] is False for candidate in inventory["candidates"])


def test_historical_claim_audit_seed_is_discovery_only():
    audit = load_json("historical-claim-audit-seed-v0.json")

    assert audit["audit_status"] == "SEED_DISCOVERY_ONLY_NOT_COMPLETE_NOT_CURRENT_TRUTH"
    assert audit["ctl_current_state_warning"]
    assert audit["match_count"] > 0
