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
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v5.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v5", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v5_catalog_resolves_rank2_z2_without_unblocking_scan() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v5.json")
    readiness = load_json("formal-low-rank-scan-readiness-v5.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 4
    assert catalog["blocked_row_count"] == 10
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank5-su5-1",
    ]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["status"] == "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY"
    assert readiness["scan_plan_generation_allowed"] is False


def test_rank2_z2_row_has_two_formal_semion_snapshot_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v5.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank2-cyclic-z2"]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["resolved_modular_braided_class_count"] == 2
    assert len(row["ribbon_realization_snapshot_hashes"]) == 2
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []
    assert row["pivotal_level"]["status"] == "HASH_BOUND_PIVOTAL_DATA_MATERIALIZED"
    assert row["ribbon_level"]["status"] == "VERIFIED_BY_FORMAL_SNAPSHOT_CERTIFICATES"


def test_rank2_z2_snapshots_use_nontrivial_associator_and_validate() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v5.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank2-cyclic-z2"]
    expected_hashes = set(row["ribbon_realization_snapshot_hashes"])
    actual_hashes = set()

    for path in catalog["resolved_snapshot_paths"]:
        if "rank2-cyclic-z2" not in path:
            continue
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        assert snapshot["family_id"] == "rank2-cyclic-z2"
        assert snapshot["category_data"]["f_symbols"]["omega_111"] == "-1"
        assert snapshot["category_data"]["r_symbols"]["R_11_to_0"] in {"i", "-i"}
        checks = snapshot["certificates"]["producer_exact_coherence"]["checks"]
        assert checks["normalized_abelian_3_cocycle"] == "PASS"
        assert checks["right_hexagon"] == "PASS"
        assert checks["left_hexagon"] == "PASS"
        assert checks["strict_associator_semion_hexagon_negative_control"] == "PASS"
        assert (
            checks["strict_associator_negative_control"]["right_hexagon"] == "FAIL"
        )

    assert actual_hashes == expected_hashes


def test_strict_pointed_z2_semion_control_fails_hexagon() -> None:
    strict = MODULE.scan_semion_exact(1, strict_associator=True)

    assert strict["pentagon"] == "PASS"
    assert strict["right_hexagon"] == "FAIL"
    assert strict["left_hexagon"] == "FAIL"


def test_v5_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v5.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_v5_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v5.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank5-su5-1",
    ]
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
