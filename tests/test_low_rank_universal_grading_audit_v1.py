import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_low_rank_universal_grading_audit_v1.py"
SPEC = importlib.util.spec_from_file_location("low_rank_universal_grading_audit_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_audit() -> dict:
    return json.loads(
        (OUT / "low-rank-universal-grading-audit-v1.json").read_text(encoding="utf-8")
    )


def rows_by_family(audit: dict) -> dict[str, dict]:
    return {row["family_id"]: row for row in audit["row_audits"]}


def test_universal_grading_audit_triages_blocked_rows() -> None:
    audit = load_audit()

    assert audit["status"] == "UNIVERSAL_GRADING_AUDIT_COMPLETE_WITH_ONE_BLOCKER"
    assert audit["formal_nontrivial_universal_group_family_ids"] == [
        "rank3-ising",
        "rank5-su2-4",
    ]
    assert audit["formal_trivial_universal_group_family_ids"] == [
        "rank3-psu2-5",
        "rank4-psu2-7",
        "rank5-psu2-9",
    ]
    assert audit["universal_grading_audit_blocked_family_ids"] == ["rank5-psu3-4"]
    assert audit["scan_plan_status"] == "NOT_AUTHORIZED_BY_THIS_AUDIT"
    assert audit["classification_status"] == "NOT_ESTABLISHED_BY_THIS_AUDIT"


def test_ising_and_su2_4_have_z2_universal_grading() -> None:
    rows = rows_by_family(load_audit())

    for family_id, adjoint, odd_component in [
        ("rank3-ising", [0, 2], [1]),
        ("rank5-su2-4", [0, 2, 4], [1, 3]),
    ]:
        row = rows[family_id]
        assert row["status"] == "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL"
        assert row["computed"]["universal_group"] == "Z2"
        assert row["computed"]["nontrivial_character_count"] == 1
        assert row["computed"]["adjoint_component"] == adjoint
        assert row["computed"]["universal_grading_components"] == [adjoint, odd_component]
        assert row["scan_relevance"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST"
        assert row["formal_ribbon_realization_status"] == "NOT_PRODUCED_BY_THIS_AUDIT"


def test_psu2_adjoint_rows_are_formally_trivial_for_universal_characters() -> None:
    rows = rows_by_family(load_audit())
    expected_labels = {
        "rank3-psu2-5": [0, 2, 4],
        "rank4-psu2-7": [0, 2, 4, 6],
        "rank5-psu2-9": [0, 2, 4, 6, 8],
    }

    for family_id, labels in expected_labels.items():
        row = rows[family_id]
        assert row["status"] == "UNIVERSAL_GRADING_FORMALLY_DERIVED_TRIVIAL"
        assert row["computed"]["universal_group"] == "trivial"
        assert row["computed"]["nontrivial_character_count"] == 0
        assert row["computed"]["adjoint_component"] == labels
        assert row["computed"]["universal_grading_components"] == [labels]
        assert row["scan_relevance"] == "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS"
        assert row["formal_ribbon_realization_status"] == "NOT_PRODUCED_BY_THIS_AUDIT"


def test_psu3_is_not_decided_by_adjoint_name_alone() -> None:
    rows = rows_by_family(load_audit())
    psu3 = rows["rank5-psu3-4"]

    assert psu3["status"] == "UNIVERSAL_GRADING_AUDIT_BLOCKED_NO_REPO_LOCAL_FUSION_TABLE"
    assert psu3["computed"] is None
    assert psu3["scan_relevance"] == "UNKNOWN_UNTIL_FUSION_TABLE_AUDIT"
    assert "not promote the name '_ad'" in psu3["blocked_reason"]
    assert any("does not prove PSU(3)_4" in item for item in psu3["explicit_non_claims"])


def test_generator_rebuilds_same_triage_shape() -> None:
    artifacts = MODULE.build_all()
    audit = artifacts["low-rank-universal-grading-audit-v1.json"]

    assert audit["formal_nontrivial_universal_group_family_ids"] == [
        "rank3-ising",
        "rank5-su2-4",
    ]
    assert audit["formal_trivial_universal_group_family_ids"] == [
        "rank3-psu2-5",
        "rank4-psu2-7",
        "rank5-psu2-9",
    ]
    assert audit["universal_grading_audit_blocked_family_ids"] == ["rank5-psu3-4"]
