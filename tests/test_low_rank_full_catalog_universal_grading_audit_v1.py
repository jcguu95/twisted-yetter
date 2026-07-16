import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_full_catalog_universal_grading_audit_v1.py"
SPEC = importlib.util.spec_from_file_location("full_catalog_universal_grading_audit_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_audit() -> dict:
    return json.loads(
        (OUT / "low-rank-full-catalog-universal-grading-audit-v1.json").read_text(
            encoding="utf-8"
        )
    )


def rows_by_family(audit: dict) -> dict[str, dict]:
    return {row["family_id"]: row for row in audit["row_audits"]}


def test_full_catalog_audit_separates_resolved_nontrivial_from_growth_targets() -> None:
    audit = load_audit()

    assert audit["status"] == "FULL_CATALOG_UNIVERSAL_GRADING_AUDIT_COMPLETE_WITH_ONE_UNKNOWN"
    assert audit["blocked_nontrivial_growth_target_family_ids"] == [
        "rank3-ising",
        "rank5-su2-4",
    ]
    assert audit["explicit_next_growth_targets"] == ["rank3-ising", "rank5-su2-4"]
    assert audit["unknown_universal_group_family_ids"] == ["rank5-psu3-4"]
    assert audit["explicit_unknowns_not_ignored"] == ["rank5-psu3-4"]
    assert audit["scan_plan_status"] == "NOT_AUTHORIZED_BY_THIS_AUDIT"
    assert audit["classification_status"] == "NOT_ESTABLISHED_BY_THIS_AUDIT"


def test_full_catalog_includes_all_resolved_nontrivial_rows() -> None:
    audit = load_audit()

    assert audit["resolved_nontrivial_family_ids"] == [
        "rank2-cyclic-z2",
        "rank3-cyclic-z3",
        "rank4-pointed-z4",
        "rank4-pointed-z2xz2",
        "rank4-semion-times-fibonacci",
        "rank5-su5-1",
    ]
    rows = rows_by_family(audit)
    assert rows["rank2-cyclic-z2"]["universal_group"] == "Z2"
    assert rows["rank3-cyclic-z3"]["universal_group"] == "Z3"
    assert rows["rank4-pointed-z4"]["universal_group"] == "Z4"
    assert rows["rank4-pointed-z2xz2"]["universal_group"] == "Z2xZ2"
    assert rows["rank4-semion-times-fibonacci"]["universal_group"] == "Z2"
    assert rows["rank5-su5-1"]["universal_group"] == "Z5"


def test_full_catalog_trivial_rows_are_ignored_only_for_nontrivial_character_scan() -> None:
    audit = load_audit()

    assert audit["formal_trivial_universal_group_family_ids"] == [
        "rank2-fibonacci-yang-lee",
        "rank3-psu2-5",
        "rank4-fibxfib",
        "rank4-psu2-7",
        "rank5-psu2-9",
    ]
    assert audit["trivial_rows_are_ignored_for_nontrivial_universal_character_scan"] == (
        audit["formal_trivial_universal_group_family_ids"]
    )
    assert any("Trivial rows are ignored only" in item for item in audit["explicit_non_claims"])


def test_unknown_psu3_is_not_treated_as_trivial() -> None:
    rows = rows_by_family(load_audit())
    psu3 = rows["rank5-psu3-4"]

    assert psu3["universal_group"] == "UNKNOWN"
    assert psu3["scan_relevance"] == "UNKNOWN_UNTIL_FUSION_TABLE_AUDIT"
    assert psu3["catalog_row_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"


def test_generator_rebuilds_full_catalog_audit_shape() -> None:
    artifacts = MODULE.build_all()
    audit = artifacts["low-rank-full-catalog-universal-grading-audit-v1.json"]

    assert audit["blocked_nontrivial_growth_target_family_ids"] == [
        "rank3-ising",
        "rank5-su2-4",
    ]
    assert audit["unknown_universal_group_family_ids"] == ["rank5-psu3-4"]
    assert len(audit["row_audits"]) == 14
