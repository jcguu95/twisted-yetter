import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    RIBBON_CATALOG_ESTABLISHED,
    RIBBON_CATALOG_PARTIAL,
    FoundationSafetyError,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v3.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v3", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v3_catalog_resolves_z3_and_z5_only() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v3.json")
    readiness = load_json("formal-low-rank-scan-readiness-v3.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 2
    assert catalog["blocked_row_count"] == 12
    assert catalog["resolved_family_ids"] == ["rank3-cyclic-z3", "rank5-su5-1"]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["status"] == "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY"
    assert readiness["scan_plan_generation_allowed"] is False


def test_rank5_su5_1_row_has_two_formal_z5_snapshot_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v3.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank5-su5-1"]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["resolved_modular_braided_class_count"] == 2
    assert len(row["ribbon_realization_snapshot_hashes"]) == 2
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []


def test_z5_snapshots_pass_formal_evidence_validation() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v3.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank5-su5-1"]
    expected_hashes = set(row["ribbon_realization_snapshot_hashes"])
    actual_hashes = set()

    for path in catalog["resolved_snapshot_paths"]:
        if "rank5-su5-1" not in path:
            continue
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        assert snapshot["family_id"] == "rank5-su5-1"
        assert snapshot["category_data"]["metric_group"] == "Z/5"
        assert snapshot["structural_checks"]["balancing"] == "PASS"
        assert snapshot["structural_checks"]["hexagon"] == "PASS"
        assert snapshot["structural_checks"]["modularity"] == "PASS"

    assert actual_hashes == expected_hashes


def test_v3_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v3.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_v3_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v3.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_family_ids"] == ["rank3-cyclic-z3", "rank5-su5-1"]
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
