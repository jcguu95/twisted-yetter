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
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v8.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v8", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v8_catalog_resolves_z4_without_unblocking_scan() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v8.json")
    readiness = load_json("formal-low-rank-scan-readiness-v8.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 7
    assert catalog["blocked_row_count"] == 7
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank4-pointed-z4",
        "rank4-semion-times-fibonacci",
        "rank4-fibxfib",
        "rank5-su5-1",
    ]
    assert catalog["blocked_family_ids"] == [
        "rank3-ising",
        "rank3-psu2-5",
        "rank4-pointed-z2xz2",
        "rank4-psu2-7",
        "rank5-su2-4",
        "rank5-psu2-9",
        "rank5-psu3-4",
    ]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["scan_plan_generation_allowed"] is False


def test_rank4_pointed_z4_row_has_four_cyclic_metric_group_snapshots() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v8.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank4-pointed-z4"]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["modular_braided_class_count"] == 4
    assert row["resolved_modular_braided_class_count"] == 4
    assert len(row["ribbon_realization_snapshot_hashes"]) == 4
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []


def test_rank4_pointed_z4_snapshots_bind_nontrivial_associator_and_negative_control() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v8.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank4-pointed-z4"]
    expected_hashes = set(row["ribbon_realization_snapshot_hashes"])
    actual_hashes = set()
    parameters = set()

    for path in catalog["resolved_snapshot_paths"]:
        if "rank4-pointed-z4" not in path:
            continue
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        data = snapshot["category_data"]
        parameters.add(data["f_symbols"]["parameter_m"])
        assert data["metric_group"] == "Z/4"
        assert data["field"] == "Q(zeta16)"
        assert data["quadratic_form"].startswith("q(x)=zeta16^(")
        assert "omega_m" in data["f_symbols"]["associator"]
        assert data["f_symbols"]["note"].startswith("nontrivial associator is required")
        assert data["pivotal_scalars"] == {label: "1" for label in data["labels"]}
        checks = snapshot["certificates"]["producer_exact_coherence"]["checks"]
        assert checks["normalized_abelian_3_cocycle"] == "PASS"
        assert checks["right_hexagon"] == "PASS"
        assert checks["left_hexagon"] == "PASS"
        assert checks["monodromy_nondegenerate"] == "PASS"
        assert checks["strict_associator_z4_hexagon_negative_control"] == "PASS"
        strict = checks["strict_associator_negative_control"]
        assert strict["pentagon"] == "PASS"
        assert strict["right_hexagon"] == "FAIL"
        assert strict["left_hexagon"] == "FAIL"
        ribbon_checks = snapshot["certificates"]["ribbon_pivotal_compatibility"]["checks"]
        assert ribbon_checks["twist_equals_R_aa"] == "PASS"
        assert ribbon_checks["balancing"] == "PASS"

    assert actual_hashes == expected_hashes
    assert parameters == {2, 6, 10, 14}


def test_v8_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v8.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_v8_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v8.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank4-pointed-z4",
        "rank4-semion-times-fibonacci",
        "rank4-fibxfib",
        "rank5-su5-1",
    ]
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
