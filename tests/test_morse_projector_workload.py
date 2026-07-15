import pytest

from experiments.sage.morse_projector_workload import (
    annotate_ranked_path_shards,
    balanced_path_ranges,
    build_projector_path_workload,
    evaluation_run_identity,
    validate_projector_path_workload,
)


def _workload(rank=8192, shards=16):
    return build_projector_path_workload(
        category_id="control-category",
        category_projector_data_hash="category-data-hash",
        sector_labels={"A": 1, "B": 2},
        component_order=("A", "B"),
        projector_id="special-red",
        ordered_puncture_word=(
            {
                "cut_id": "cut-0",
                "component": "A",
                "variance": "label",
                "oriented_label": 1,
            },
            {
                "cut_id": "cut-1",
                "component": "B",
                "variance": "dual",
                "oriented_label": 2,
            },
        ),
        path_basis_rank=rank,
        shard_count=shards,
    )


def test_balanced_path_ranges_cover_rank_exactly():
    ranges = balanced_path_ranges(8192, 16)
    assert ranges[0] == (0, 512)
    assert ranges[-1] == (7680, 8192)
    assert all(stop - start == 512 for start, stop in ranges)


def test_semantic_workload_is_geometry_independent_and_validated():
    workload = _workload()
    validate_projector_path_workload(workload)
    assert "lowering_hash" not in workload["semantic_identity"]
    assert "crossing" not in workload["semantic_identity"]
    assert workload["shard_count"] == 16


def test_evaluation_identity_changes_without_invalidating_semantic_workload():
    workload = _workload()
    before = evaluation_run_identity(
        workload,
        input_hash="input",
        lowering_hash="lowering-before",
        evaluator_hash="evaluator-before",
    )
    after = evaluation_run_identity(
        workload,
        input_hash="input",
        lowering_hash="lowering-after",
        evaluator_hash="evaluator-after",
    )
    assert before["semantic_workload_hash"] == after["semantic_workload_hash"]
    assert before["evaluation_run_hash"] != after["evaluation_run_hash"]


def test_workload_validation_rejects_gaps():
    workload = _workload(rank=4, shards=2)
    workload["shards"][1]["path_start"] = 3
    with pytest.raises(ValueError, match="overlap or leave a gap"):
        validate_projector_path_workload(workload)


def test_ranked_shards_sample_all_cost_quantiles_before_easy_first_remainder():
    workload = _workload(rank=16, shards=8)
    annotate_ranked_path_shards(
        workload,
        path_costs=range(16),
        calibration_width=4,
        estimator={"name": "monotone-control"},
    )
    calibration = workload["ranking"]["calibration_shard_indices"]
    assert calibration == [1, 3, 5, 7]
    assert workload["ranking"]["dispatch_shard_indices"][:4] == calibration
    assert sorted(workload["ranking"]["dispatch_shard_indices"]) == list(range(8))
    assert workload["shards"][7]["estimated_cost_max"] == 15


def test_rank_annotations_do_not_change_semantic_workload_hash():
    workload = _workload(rank=4, shards=2)
    semantic_hash = workload["semantic_workload_hash"]
    annotate_ranked_path_shards(
        workload,
        path_costs=(4, 3, 2, 1),
        calibration_width=1,
        estimator={"name": "reverse-control"},
    )
    validate_projector_path_workload(workload)
    assert workload["semantic_workload_hash"] == semantic_hash
