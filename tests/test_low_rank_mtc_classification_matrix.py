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

    assert {entry["rank"] for entry in matrix["coverage_by_rank"]} == set(range(2, 8))
    assert "EXACT_MODULAR_RIBBON_REALIZATION_COUNT_UNKNOWN" == next(
        entry["general_nonunitary_status"]
        for entry in matrix["coverage_by_rank"]
        if entry["rank"] == 5
    )
    assert rows["rank5-su5-1"]["universal_grading_group"] == "Z5"
    assert rows["rank6-ising-x-z2"]["universal_grading_group"] == "Z2xZ2"
    assert rows["rank7-so7-2"]["universal_grading_group"] == "Z2"
    assert not rows["rank5-psu2-9"]["character_twist_eligible"]
    assert not rows["rank5-psu3-4"]["character_twist_eligible"]
    assert rows["rank5-psu3-4"]["fusion_multiplicity_max"] == 2


def test_metaplectic_counts_and_open_gaps_are_loud() -> None:
    matrix = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)
    rows = {row["family_id"]: row for row in matrix["families"]}

    for family_id in ("rank5-su2-4", "rank6-so5-2", "rank7-so7-2"):
        assert rows[family_id]["realization_count"] == 4
    joined = " ".join(matrix["open_gaps"]).lower()
    assert "rank 5" in joined and "unknown" in joined
    assert "ranks 6 and 7" in joined and "weakly integral" in joined
    notice = matrix["top_notice"].lower()
    assert "do not interpret" in notice and "exhaustive list" in notice


def test_known_examples_are_not_promoted_to_classification() -> None:
    matrix = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)
    known_examples = [
        row for row in matrix["families"]
        if row["realization_status"] == "KNOWN_EXAMPLE_NOT_EXHAUSTIVE_CLASSIFICATION"
    ]

    assert {row["family_id"] for row in known_examples} == {
        "rank6-su2-5-known-outside-weak-scope",
        "rank7-su2-6-known-outside-weak-scope",
    }
    assert all("not evidence" in row["scope"] for row in known_examples)


def test_checked_in_artifact_matches_curated_rows() -> None:
    artifact_path = ROOT / "experiments/results/mtc-classification/low-rank-mtc-classification-matrix-v1.json"
    artifact = json.loads(artifact_path.read_text(encoding="utf-8"))
    rebuilt = MODULE.build_matrix(MODULE.DEFAULT_SOURCES, MODULE.DEFAULT_FAMILIES)

    assert artifact["schema"] == rebuilt["schema"]
    assert artifact["coverage_by_rank"] == rebuilt["coverage_by_rank"]
    assert artifact["families"] == rebuilt["families"]
    assert artifact["twist_candidate_family_ids"] == rebuilt["twist_candidate_family_ids"]
