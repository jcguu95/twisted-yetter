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
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v9.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v9", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v9_catalog_resolves_z2xz2_without_unblocking_scan() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v9.json")
    readiness = load_json("formal-low-rank-scan-readiness-v9.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 8
    assert catalog["blocked_row_count"] == 6
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank4-pointed-z4",
        "rank4-pointed-z2xz2",
        "rank4-semion-times-fibonacci",
        "rank4-fibxfib",
        "rank5-su5-1",
    ]
    assert catalog["blocked_family_ids"] == [
        "rank3-ising",
        "rank3-psu2-5",
        "rank4-psu2-7",
        "rank5-su2-4",
        "rank5-psu2-9",
        "rank5-psu3-4",
    ]
    assert catalog["formal_scan_plan_allowed"] is False
    assert readiness["scan_plan_generation_allowed"] is False


def test_rank4_pointed_z2xz2_row_has_five_metric_group_snapshots() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v9.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank4-pointed-z2xz2"
    ]

    assert row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    assert row["formal_admission_allowed"] is True
    assert row["modular_braided_class_count"] == 5
    assert row["resolved_modular_braided_class_count"] == 5
    assert len(row["ribbon_realization_snapshot_hashes"]) == 5
    assert row["blocker_ids"] == []
    assert row["missing_evidence"] == []


def test_rank4_pointed_z2xz2_snapshots_bind_orbit_enumerator_and_cocycle() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v9.json")
    row = {item["family_id"]: item for item in catalog["families"]}[
        "rank4-pointed-z2xz2"
    ]
    expected_hashes = set(row["ribbon_realization_snapshot_hashes"])
    actual_hashes = set()
    reps = set()

    for path in catalog["resolved_snapshot_paths"]:
        if "rank4-pointed-z2xz2" not in path:
            continue
        snapshot = json.loads((ROOT / path).read_text(encoding="utf-8"))
        validate_formal_evidence(snapshot)
        actual_hashes.add(snapshot["content_hash"])
        data = snapshot["category_data"]
        rep = tuple(data["quadratic_form_rep_exponents"][label] for label in ["10", "01", "11"])
        reps.add(rep)
        assert data["metric_group"] == "Z/2 x Z/2"
        assert data["field"] == "Q(i)"
        assert data["duals"] == {label: label for label in data["labels"]}
        assert data["field_embedding"]["exponent_modulus"] == 4
        assert data["quadratic_orbit_size"] in {1, 3, 6}
        assert "associator_table" in data["f_symbols"]
        checks = snapshot["certificates"]["producer_exact_coherence"]["checks"]
        assert checks["all_nondegenerate_quadratic_forms_count"] == 16
        assert checks["gl22_orbit_count"] == 5
        assert checks["selected_representatives"] == [
            [0, 0, 2],
            [0, 1, 3],
            [1, 1, 2],
            [2, 2, 2],
            [2, 3, 3],
        ]
        assert checks["normalized_abelian_3_cocycle"] == "PASS"
        assert checks["right_hexagon"] == "PASS"
        assert checks["left_hexagon"] == "PASS"
        assert checks["diagonal_q_equals_R_aa"] == "PASS"
        assert checks["monodromy_matches_quadratic_bilinearization"] == "PASS"
        assert checks["monodromy_nondegenerate"] == "PASS"
        assert checks["strict_associator_same_R_negative_control_fails_hexagon"] == "PASS"
        strict = checks["strict_associator_same_R_negative_control"]
        assert strict["pentagon"] == "PASS"
        assert strict["right_hexagon"] == "FAIL"
        assert strict["left_hexagon"] == "FAIL"

    assert actual_hashes == expected_hashes
    assert reps == {(0, 0, 2), (0, 1, 3), (1, 1, 2), (2, 2, 2), (2, 3, 3)}


def test_v9_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v9.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_v9_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v9.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_family_ids"] == [
        "rank2-cyclic-z2",
        "rank2-fibonacci-yang-lee",
        "rank3-cyclic-z3",
        "rank4-pointed-z4",
        "rank4-pointed-z2xz2",
        "rank4-semion-times-fibonacci",
        "rank4-fibxfib",
        "rank5-su5-1",
    ]
    for name, payload in artifacts.items():
        if "snapshot" in name:
            validate_formal_evidence(payload)
