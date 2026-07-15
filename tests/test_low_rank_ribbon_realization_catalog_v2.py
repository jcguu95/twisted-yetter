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
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v2.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v2", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v2_catalog_is_partial_and_scan_blocked() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v2.json")
    readiness = load_json("formal-low-rank-scan-readiness-v2.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 1
    assert catalog["blocked_row_count"] == 13
    assert catalog["resolved_family_ids"] == ["rank3-cyclic-z3"]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["status"] == "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY"
    assert readiness["scan_plan_generation_allowed"] is False
    assert readiness["formal_scan_plan_id"] is None


def test_rank3_z3_row_has_two_formal_snapshot_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v2.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank3-cyclic-z3"]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["resolved_modular_braided_class_count"] == 2
    assert len(row["ribbon_realization_snapshot_hashes"]) == 2
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []


def test_z3_snapshots_pass_formal_evidence_validation() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v2.json")
    expected_hashes = set(
        {item["family_id"]: item for item in catalog["families"]}[
            "rank3-cyclic-z3"
        ]["ribbon_realization_snapshot_hashes"]
    )
    actual_hashes = set()
    for path in catalog["resolved_snapshot_paths"]:
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        assert snapshot["family_id"] == "rank3-cyclic-z3"
        assert snapshot["structural_checks"]["balancing"] == "PASS"
        assert snapshot["structural_checks"]["hexagon"] == "PASS"
        assert snapshot["structural_checks"]["modularity"] == "PASS"
        assert snapshot["category_data"]["f_symbols"] == (
            "strict pointed gauge, all F(a,b,c)=1"
        )

    assert actual_hashes == expected_hashes


def test_rank2_z2_remains_blocked_for_nontrivial_cocycle_data() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v2.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank2-cyclic-z2"]

    assert row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
    assert row["formal_admission_allowed"] is False
    assert "rank2-cyclic-z2:semion-requires-nontrivial-abelian-cocycle-data" in row[
        "blocker_ids"
    ]
    assert any("nontrivial Z2 abelian cocycle" in item for item in row["missing_evidence"])


def test_partial_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v2.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v2.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
