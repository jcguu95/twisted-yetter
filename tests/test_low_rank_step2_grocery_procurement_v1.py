import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    RIBBON_CATALOG_ESTABLISHED,
    RIBBON_CATALOG_PROCUREMENT_BLOCKED,
    FoundationSafetyError,
    validate_low_rank_ribbon_catalog,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
PROCUREMENT = OUT / "grocery-procurement"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_step2_grocery_procurement_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_step2_grocery_v1", SCRIPT)
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


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def load_out(name: str) -> dict:
    return load_json(OUT / name)


def load_procurement(name: str) -> dict:
    return load_json(PROCUREMENT / name)


def test_grocery_ledger_has_terminal_artifact_for_every_blocked_row() -> None:
    ledger = load_out("low-rank-step2-grocery-procurement-v1.json")

    assert ledger["status"] == "STEP2_GROCERY_PROCUREMENT_COMPLETE_PROCUREMENT_BLOCKED"
    assert ledger["blocked_family_ids"] == BLOCKED_ROW_ORDER
    assert ledger["resolved_row_package_count"] == 0
    assert ledger["procurement_blocker_count"] == 6
    assert ledger["formal_scan_plan_allowed_after_procurement"] is False
    assert "No row-ribbon-realization-package was produced." in ledger[
        "explicit_non_claims"
    ]

    rows = ledger["row_procurement_records"]
    assert [row["family_id"] for row in rows] == BLOCKED_ROW_ORDER
    for row in rows:
        assert row["grocery_status"] == "PROCUREMENT_BLOCKED"
        assert row["terminal_artifact_kind"] == "row-procurement-blocker"
        assert row["terminal_artifact_hash"].startswith("sha256:")
        assert row["resolved_package_hash"] is None


def test_su2_family_payloads_are_input_skeletons_not_formal_snapshots() -> None:
    payload_names = {
        "rank3-ising": "rank3-ising-principal-su2-level2-category-payload-v1.json",
        "rank3-psu2-5": "rank3-psu2-5-principal-adjoint-su2-level5-category-payload-v1.json",
        "rank4-psu2-7": "rank4-psu2-7-principal-adjoint-su2-level7-category-payload-v1.json",
        "rank5-su2-4": "rank5-su2-4-principal-su2-level4-category-payload-v1.json",
        "rank5-psu2-9": "rank5-psu2-9-principal-adjoint-su2-level9-category-payload-v1.json",
    }
    expected_labels = {
        "rank3-ising": [0, 1, 2],
        "rank3-psu2-5": [0, 2, 4],
        "rank4-psu2-7": [0, 2, 4, 6],
        "rank5-su2-4": [0, 1, 2, 3, 4],
        "rank5-psu2-9": [0, 2, 4, 6, 8],
    }

    for family_id, name in payload_names.items():
        payload = load_procurement(name)
        assert payload["family_id"] == family_id
        assert payload["payload_kind"] == "principal_su2k_category_input_skeleton"
        assert payload["formal_snapshot_produced"] is False
        assert payload["formal_row_resolution_allowed"] is False
        assert payload["certificates"]["producer_exact_coherence"]["status"] == "MISSING"
        assert payload["certificates"]["consumer_runtime_coherence"]["status"] == "MISSING"
        assert payload["certificates"]["ribbon_pivotal_compatibility"]["status"] == "MISSING"
        assert [simple["label"] for simple in payload["simples"]] == expected_labels[
            family_id
        ]
        assert payload["field_embedding"]["galois_branches_materialized"] is False
        assert payload["pairing"]["fusion_pairing_invertibility_checked"] is False


def test_ising_payload_does_not_promote_all_sigma_backend() -> None:
    payload = load_procurement("rank3-ising-principal-su2-level2-category-payload-v1.json")
    blocker = load_procurement("rank3-ising-row-procurement-blocker-v1.json")

    assert payload["all_sigma_backend_is_formal_evidence"] is False
    assert payload["convention_cross_check_only"]["status"] == "pass"
    assert blocker["row_ribbon_realization_package_produced"] is False
    assert any("all-sigma" in item for item in blocker["missing_evidence"])
    assert any("No row-complete" in item for item in blocker["why_this_is_not_a_resolved_row"])


def test_psu3_procurement_blocker_records_source_acquisition_gap() -> None:
    blocker = load_procurement("rank5-psu3-4-row-procurement-blocker-v1.json")

    assert blocker["status"] == "PROCUREMENT_BLOCKED_NO_REPO_LOCAL_PSU3_FR_SOURCE"
    assert blocker["partial_payload"] is None
    assert blocker["source_acquisition_gap"] == {
        "psu3_fr_payload": "MISSING",
        "multiplicity_two_basis_gauge": "MISSING",
        "pairing_convention": "MISSING",
    }
    assert any("multiplicity-two" in item for item in blocker["missing_evidence"])


def test_v11_catalog_is_terminal_procurement_blocked_and_scan_closed() -> None:
    catalog = load_out("low-rank-ribbon-realization-catalog-v11.json")
    readiness = load_out("formal-low-rank-scan-readiness-v11.json")

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PROCUREMENT_BLOCKED
    assert catalog["procurement_status"] == "TERMINAL_PROCUREMENT_BLOCKED"
    assert catalog["resolved_row_count"] == 8
    assert catalog["blocked_row_count"] == 6
    assert catalog["blocked_family_ids"] == BLOCKED_ROW_ORDER
    assert catalog["formal_scan_plan_allowed"] is False
    assert catalog["ribbon_denominator_by_rank"] == {}
    assert readiness["scan_plan_generation_allowed"] is False
    assert readiness["formal_scan_plan_id"] is None

    blocked_rows = [
        row
        for row in catalog["families"]
        if row["family_id"] in BLOCKED_ROW_ORDER
    ]
    for row in blocked_rows:
        assert row["procurement_status"] == "PROCUREMENT_BLOCKED"
        assert row["procurement_blocker_hash"].startswith("sha256:")
        assert row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"


def test_procurement_blocked_catalog_cannot_be_rebranded_as_established() -> None:
    catalog = load_out("low-rank-ribbon-realization-catalog-v11.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_procurement_blocked_catalog_cannot_authorize_scan_plan() -> None:
    catalog = load_out("low-rank-ribbon-realization-catalog-v11.json")
    catalog["formal_scan_plan_allowed"] = True

    with pytest.raises(FoundationSafetyError, match="cannot allow scan plans"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_consistent_procurement_artifacts() -> None:
    artifacts = MODULE.build_all()
    ledger = artifacts["low-rank-step2-grocery-procurement-v1.json"]
    catalog = artifacts["low-rank-ribbon-realization-catalog-v11.json"]
    readiness = artifacts["formal-low-rank-scan-readiness-v11.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert ledger["status"] == "STEP2_GROCERY_PROCUREMENT_COMPLETE_PROCUREMENT_BLOCKED"
    assert catalog["status"] == RIBBON_CATALOG_PROCUREMENT_BLOCKED
    assert catalog["grocery_procurement_ledger_hash"] == ledger["content_hash"]
    assert readiness["classification_catalog_hash"] == catalog["content_hash"]
    assert ledger["procurement_blocker_count"] == 6
