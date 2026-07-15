import json
from pathlib import Path


ARTIFACT = Path(
    "experiments/results/akbulut-yasui/"
    "figure21-right-su2-2-untwisted-projector-sweep-v1.json"
)


def load_artifact():
    return json.loads(ARTIFACT.read_text())


def test_figure21_su2_2_projector_sweep_counts_every_untwisted_sector():
    artifact = load_artifact()
    assert artifact["status"] == (
        "PROJECTOR_SELECTION_CONTROLS_PASS_FULL_RT_VALUE_NOT_COMPUTED"
    )
    sweep = artifact["sector_sweep"]
    assert sweep["total_sector_count"] == 3**11 == 177147
    assert sweep["zero_sector_count"] == 90477
    assert sweep["surviving_sector_count"] == 86670
    assert sum(sweep["rank_distribution"].values()) == 177147
    assert sweep["rank_distribution"]["8192"] == 162


def test_figure21_su2_2_minimal_projector_controls_are_exact():
    artifact = load_artifact()
    assert artifact["character_twist"] == "untwisted"
    assert artifact["puncture_count"] == 29
    assert artifact["all_unit_control"]["vacuum_rank"] == 1
    assert artifact["all_unit_control"]["projected_value"] == [1.0, 0.0]
    assert artifact["exact_zero_control"]["labels"]["black"] == 1
    assert artifact["exact_zero_control"]["vacuum_rank"] == 0
    assert artifact["exact_zero_control"]["projected_value"] == [0.0, 0.0]


def test_figure21_su2_2_collective_survivor_is_not_falsely_pruned():
    artifact = load_artifact()
    survivor = artifact["collective_survivor_control"]
    assert survivor["labels"]["green"] == 1
    assert survivor["vacuum_rank"] == 2
    assert survivor["expanded_term_count"] == 2
    assert len(set(survivor["expanded_term_hashes"])) == 2
    assert survivor["expanded_projection_vertex_counts"] == [28, 28]
    assert survivor["expanded_inclusion_vertex_counts"] == [28, 28]
    assert artifact["full_untwisted_kirby_color_value"]["status"] == "BLOCKED"
