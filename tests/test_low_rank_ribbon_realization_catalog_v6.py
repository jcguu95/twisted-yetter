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
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v6.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v6", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v6_catalog_resolves_semion_times_fib_without_unblocking_scan() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v6.json")
    readiness = load_json("formal-low-rank-scan-readiness-v6.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 5
    assert catalog["blocked_row_count"] == 9
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank4-semion-times-fibonacci",
        "rank5-su5-1",
    ]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["scan_plan_generation_allowed"] is False


def test_rank4_semion_times_fib_row_has_eight_product_snapshot_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v6.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank4-semion-times-fibonacci"
    ]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["resolved_modular_braided_class_count"] == 8
    assert len(row["ribbon_realization_snapshot_hashes"]) == 8
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []


def test_rank4_semion_times_fib_snapshots_pin_validated_factor_hashes() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v6.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank4-semion-times-fibonacci"
    ]
    expected_hashes = set(row["ribbon_realization_snapshot_hashes"])
    actual_hashes = set()

    for path in catalog["resolved_snapshot_paths"]:
        if "rank4-semion-times-fibonacci" not in path:
            continue
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        data = snapshot["category_data"]
        assert data["product_type"] == "Deligne product"
        assert data["factor_family_ids"] == [
            "rank2-cyclic-z2",
            "rank2-fibonacci-yang-lee",
        ]
        assert len(data["labels"]) == 4
        assert len(data["factor_snapshot_hashes"]) == 2
        assert (
            snapshot["pinned_payload_hashes"]["semion_factor_snapshot"]
            == data["factor_snapshot_hashes"][0]
        )
        assert (
            snapshot["pinned_payload_hashes"]["fibonacci_yang_lee_factor_snapshot"]
            == data["factor_snapshot_hashes"][1]
        )
        checks = snapshot["certificates"]["producer_exact_coherence"]["checks"]
        assert checks["factorwise_pentagon"] == "PASS"
        assert checks["factorwise_hexagon"] == "PASS"
        assert checks["factorwise_balancing"] == "PASS"

    assert actual_hashes == expected_hashes


def test_v6_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v6.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_v6_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v6.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank4-semion-times-fibonacci",
        "rank5-su5-1",
    ]
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
