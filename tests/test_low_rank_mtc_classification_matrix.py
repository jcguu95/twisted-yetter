import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments/scripts/build_low_rank_mtc_classification_matrix.py"
SPEC = importlib.util.spec_from_file_location("low_rank_mtc_matrix", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def test_matrix_scope_and_universal_groups() -> None:
    matrix = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)
    rows = {row["family_id"]: row for row in matrix["families"]}

    assert {entry["rank"] for entry in matrix["coverage_by_rank"]} == set(range(2, 6))
    assert "ALL_PREMODULAR_FUSION_CATEGORIES_UP_TO_BRAIDED_EQUIVALENCE" == next(
        entry["proved_scope"]
        for entry in matrix["coverage_by_rank"]
        if entry["rank"] == 5
    )
    assert rows["rank5-su5-1"]["universal_grading_group"] == "Z5"
    assert not rows["rank5-psu2-9"]["character_twist_eligible"]
    assert not rows["rank5-psu3-4"]["character_twist_eligible"]
    assert rows["rank5-psu3-4"]["fusion_multiplicity_max"] == 2


def test_braided_counts_and_ribbon_gap_are_loud() -> None:
    matrix = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)
    rows = {row["family_id"]: row for row in matrix["families"]}

    totals = {entry["rank"]: entry for entry in matrix["coverage_by_rank"]}
    assert [totals[rank]["modular_braided_class_count"] for rank in range(2, 6)] == [6, 16, 33, 22]
    assert rows["rank5-su2-4"]["modular_braided_class_count"] == 4
    assert rows["rank5-su2-4"]["spherical_structures_per_braided_class"] == 2
    joined = " ".join(matrix["open_gaps"]).lower()
    assert "braided-equivalence" in joined
    assert "ribbon-equivalence" in joined
    notice = matrix["top_notice"].lower()
    assert "braided equivalence" in notice and "ribbon-equivalence" in notice


def test_modular_family_counts_match_rank_totals() -> None:
    matrix = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)
    totals = {entry["rank"]: entry["modular_braided_class_count"] for entry in matrix["coverage_by_rank"]}
    for rank, expected in totals.items():
        assert sum(row["modular_braided_class_count"] for row in matrix["families"] if row["rank"] == rank) == expected


def test_checked_in_artifact_matches_curated_rows() -> None:
    artifact_path = ROOT / "experiments/results/mtc-classification/low-rank-mtc-classification-matrix-v1.json"
    artifact = json.loads(artifact_path.read_text(encoding="utf-8"))
    rebuilt = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)

    assert artifact["schema"] == rebuilt["schema"]
    assert artifact["coverage_by_rank"] == rebuilt["coverage_by_rank"]
    assert artifact["families"] == rebuilt["families"]
    assert artifact["twist_candidate_family_ids"] == rebuilt["twist_candidate_family_ids"]
