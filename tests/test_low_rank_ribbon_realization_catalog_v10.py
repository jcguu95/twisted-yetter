import importlib.util
import json
from pathlib import Path

import pytest

from twisted_yetter.foundation_safety import (
    RIBBON_CATALOG_ESTABLISHED,
    RIBBON_CATALOG_PARTIAL,
    FoundationSafetyError,
    validate_low_rank_ribbon_catalog,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_ribbon_realization_catalog_v10.py"
SPEC = importlib.util.spec_from_file_location("low_rank_ribbon_catalog_v10", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_json(name: str) -> dict:
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def test_checked_in_v10_catalog_keeps_nonpointed_rows_blocked() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v10.json")
    readiness = load_json("formal-low-rank-scan-readiness-v10.json")

    validate_low_rank_ribbon_catalog(catalog)

    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 8
    assert catalog["blocked_row_count"] == 6
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
    assert readiness["blocked_step_status"][
        "implementation_order_step_6_scan_plan_generator"
    ] == "NOT_STARTED_BLOCKED_BY_PARTIAL_CATALOG"
    assert readiness["blocked_step_status"]["implementation_order_step_7_controls"] == (
        "NOT_STARTED_BLOCKED_BY_NO_FORMAL_SCAN_PLAN"
    )


def test_rank3_ising_blocker_does_not_upgrade_su2_2_local_backend() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v10.json")
    row = {item["family_id"]: item for item in catalog["families"]}["rank3-ising"]
    backend = catalog["nonpointed_blocker_ledger"]["local_backend_scope_audit"]

    assert row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
    assert row["formal_admission_allowed"] is False
    assert "rank3-ising:existing-su2-2-rf-local-backend-not-full-ribbon-category" in row[
        "blocker_ids"
    ]
    assert "rank3-ising:requires-explicit-ribbon-multiplicity-denominator" in row[
        "blocker_ids"
    ]
    assert any("sixteen Ising ribbon realization snapshots" in item for item in row["missing_evidence"])
    assert backend["artifact_id"] == "su2-2-rf-local-backend-v1"
    assert backend["unsafe_as_rank3_ising_full_category_snapshot"] is True
    assert "fixed-label all-sigma braid closures" in backend["scope"]
    assert "mixed simple labels" in backend["not_scope"]


def test_nonpointed_blockers_include_q6j_and_basis_gauge_requirements() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v10.json")
    rows = {item["family_id"]: item for item in catalog["families"]}

    for family_id in ["rank3-psu2-5", "rank4-psu2-7", "rank5-psu2-9"]:
        row = rows[family_id]
        assert row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
        assert any("q6j" in item for item in row["blocker_ids"])
        assert any("q6j" in item for item in row["missing_evidence"])

    psu3 = rows["rank5-psu3-4"]
    assert any("multiplicity-two" in item for item in psu3["blocker_ids"])
    assert any("basis" in item for item in psu3["missing_evidence"])


def test_v10_catalog_cannot_be_labeled_established() -> None:
    catalog = load_json("low-rank-ribbon-realization-catalog-v10.json")
    catalog["status"] = RIBBON_CATALOG_ESTABLISHED

    with pytest.raises(FoundationSafetyError, match="blocked rows"):
        validate_low_rank_ribbon_catalog(catalog)


def test_generator_builds_valid_v10_partial_catalog() -> None:
    artifacts = MODULE.build_all()
    catalog = artifacts["low-rank-ribbon-realization-catalog-v10.json"]
    readiness = artifacts["formal-low-rank-scan-readiness-v10.json"]

    validate_low_rank_ribbon_catalog(catalog)
    assert catalog["status"] == RIBBON_CATALOG_PARTIAL
    assert catalog["resolved_row_count"] == 8
    assert catalog["blocked_row_count"] == 6
    assert readiness["scan_plan_generation_allowed"] is False
