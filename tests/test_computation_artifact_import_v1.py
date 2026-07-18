from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.computation_artifact_import_v1 import (
    BLOCKED_STATUS,
    EXPECTED_CHUNK_ARTIFACTS,
    EXPECTED_ROWS,
    EXPECTED_TOTAL_SECTORS,
    KNOWN_BLOCKERS,
    RUNTIME_STATUS,
    build_computation_import_runtime,
    canonical_hash,
    validate_computation_import_runtime,
)


@pytest.fixture(scope="module")
def runtime() -> dict[str, object]:
    return build_computation_import_runtime()


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_runtime_rehashes_all_rows_chunks_and_denominators(
    runtime: dict[str, object],
) -> None:
    validate_computation_import_runtime(runtime)

    batch = runtime["figure21_structural_batch"]
    assert runtime["status"] == RUNTIME_STATUS
    assert batch["row_count"] == len(EXPECTED_ROWS) == 15
    assert batch["chunk_artifact_count"] == EXPECTED_CHUNK_ARTIFACTS
    assert batch["observed_total_sector_count"] == EXPECTED_TOTAL_SECTORS


def test_exact_and_structural_admission_routes_remain_disjoint(
    runtime: dict[str, object],
) -> None:
    exact = runtime["exact_control"]
    batch = runtime["figure21_structural_batch"]
    admission = runtime["admission"]

    assert exact["source_clean"] is True
    assert exact["arithmetic_mode"] == "EXACT_RATIONAL"
    assert exact["r11_semantic_binding"] is True
    assert exact["exact_value"] == {"numerator": 101, "denominator": 450}
    assert batch["arithmetic_mode"] == "ROUNDED_COMPLEX"
    assert batch["concrete_r11_semantic_binding"] is False
    assert admission["figure21_disposition"] == BLOCKED_STATUS
    assert admission["figure21_exact_value_admitted"] is False


def test_every_row_has_unique_snapshot_and_complete_distributions(
    runtime: dict[str, object],
) -> None:
    rows = runtime["figure21_structural_batch"]["rows"]
    snapshots = set()
    category_data = set()

    for row in rows:
        rank, expected = EXPECTED_ROWS[row["realization_id"]]
        assert row["rank"] == rank
        assert row["expected_sector_count"] == expected
        assert row["observed_sector_count"] == expected
        assert sum(row["value_distribution"].values()) == expected
        assert sum(row["status_distribution"].values()) == expected
        assert sum(row["projector_rank_distribution"].values()) == expected
        snapshots.add(row["snapshot"]["content_hash"])
        category_data.add(row["snapshot"]["category_data_hash"])
    assert len(snapshots) == len(rows)
    assert len(category_data) == len(rows)


def test_every_aggregate_chunk_partition_is_contiguous(
    runtime: dict[str, object],
) -> None:
    rows = runtime["figure21_structural_batch"]["rows"]
    checked = 0
    for row in rows:
        if row["source_kind"] != "aggregate":
            assert row["chunk_count"] == 0
            assert row["chunk_records"] == []
            continue
        previous_end = 0
        for chunk_id, chunk in enumerate(row["chunk_records"]):
            assert chunk["chunk_id"] == chunk_id
            assert chunk["start_sector_id"] == previous_end
            assert chunk["sector_count"] == (
                chunk["end_sector_id_exclusive"]
                - chunk["start_sector_id"]
            )
            previous_end = chunk["end_sector_id_exclusive"]
            checked += 1
        assert previous_end == row["expected_sector_count"]
    assert checked == EXPECTED_CHUNK_ARTIFACTS


def test_all_snapshot_certificates_are_hash_bound(
    runtime: dict[str, object],
) -> None:
    rows = runtime["figure21_structural_batch"]["rows"]
    for row in rows:
        snapshot = row["snapshot"]
        assert snapshot["structural_check_count"] == 9
        assert set(snapshot["certificate_hashes"]) == {
            "producer_exact_coherence",
            "consumer_runtime_coherence",
            "ribbon_pivotal_compatibility",
        }
        assert row["source_snapshot_content_hash"] == (
            snapshot["content_hash"]
        )
        assert row["source_category_data_hash"] == (
            snapshot["category_data_hash"]
        )


def test_stale_runtime_hash_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["status"] = "CHANGED_WITHOUT_REHASH"
    with pytest.raises(ValueError, match="content hash is stale"):
        validate_computation_import_runtime(mutation)


def test_manifest_alias_or_rebinding_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["manifest_file_sha256"] = "sha256:" + "1" * 64
    rehash(mutation)
    with pytest.raises(ValueError, match="manifest binding"):
        validate_computation_import_runtime(mutation)


def test_dirty_source_cannot_masquerade_as_exact(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["exact_control"]["source_clean"] = False
    rehash(mutation)
    with pytest.raises(ValueError, match="exact-control admission"):
        validate_computation_import_runtime(mutation)


def test_structural_batch_cannot_be_promoted_by_status_edit(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["admission"]["figure21_exact_value_admitted"] = True
    mutation["admission"]["figure21_disposition"] = (
        "ADMITTED_EXACT_INVARIANT_VALUE"
    )
    rehash(mutation)
    with pytest.raises(ValueError, match="exact-admission blockers"):
        validate_computation_import_runtime(mutation)


def test_missing_blocker_cannot_be_hidden(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["admission"]["blockers"].pop()
    rehash(mutation)
    with pytest.raises(ValueError, match="exact-admission blockers"):
        validate_computation_import_runtime(mutation)
    assert tuple(runtime["admission"]["blockers"]) == KNOWN_BLOCKERS


def test_missing_chunk_cannot_aggregate_complete(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    row = next(
        item
        for item in mutation["figure21_structural_batch"]["rows"]
        if item["source_kind"] == "aggregate"
    )
    row["chunk_records"].pop()
    rehash(mutation)
    with pytest.raises(ValueError, match="chunk denominator"):
        validate_computation_import_runtime(mutation)


def test_overlapping_chunk_range_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    row = next(
        item
        for item in mutation["figure21_structural_batch"]["rows"]
        if item["source_kind"] == "aggregate"
    )
    row["chunk_records"][1]["start_sector_id"] -= 1
    row["chunk_records"][1]["sector_count"] += 1
    rehash(mutation)
    with pytest.raises(ValueError, match="chunk range/hash"):
        validate_computation_import_runtime(mutation)


def test_category_snapshot_rebinding_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    row = mutation["figure21_structural_batch"]["rows"][0]
    row["source_category_data_hash"] = "sha256:" + "2" * 64
    rehash(mutation)
    with pytest.raises(ValueError, match="source/snapshot binding"):
        validate_computation_import_runtime(mutation)


def test_draft_diagram_cannot_be_self_declared_certified(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["figure21_identity"][
        "diagram_certified_against_printed_source"
    ] = True
    rehash(mutation)
    with pytest.raises(ValueError, match="draft blocker"):
        validate_computation_import_runtime(mutation)


def test_unsealed_evaluator_and_missing_h2_cannot_be_self_upgraded(
    runtime: dict[str, object],
) -> None:
    evaluator = deepcopy(runtime)
    evaluator["figure21_structural_batch"][
        "evaluator_source_closure_sealed"
    ] = True
    rehash(evaluator)
    with pytest.raises(ValueError, match="structural boundary"):
        validate_computation_import_runtime(evaluator)

    comparison = deepcopy(runtime)
    comparison["comparison_import"]["marked_h2_comparison_ready"] = True
    rehash(comparison)
    with pytest.raises(ValueError, match="comparison boundary"):
        validate_computation_import_runtime(comparison)
