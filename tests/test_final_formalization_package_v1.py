from __future__ import annotations

from copy import deepcopy

import pytest

from twisted_yetter.computation_artifact_import_v1 import KNOWN_BLOCKERS
from twisted_yetter.final_formalization_package_v1 import (
    ROADMAP_STATUS,
    RUNTIME_STATUS,
    build_final_formalization_runtime,
    canonical_hash,
    validate_final_formalization_runtime,
)


@pytest.fixture(scope="module")
def runtime() -> dict[str, object]:
    return build_final_formalization_runtime()


def rehash(payload: dict[str, object]) -> None:
    payload["content_hash"] = canonical_hash(payload)


def test_complete_historical_denominator_replays(
    runtime: dict[str, object],
) -> None:
    validate_final_formalization_runtime(runtime)
    audit = runtime["milestone_audit"]

    assert runtime["status"] == RUNTIME_STATUS
    assert runtime["roadmap_status"] == ROADMAP_STATUS
    assert audit["artifact_count"] == 11
    assert audit["historical_source_file_replay_count"] == 231
    assert sum(
        artifact["source_file_count"] for artifact in audit["artifacts"]
    ) == 231
    assert all(
        source["status"] == "PASS_HISTORICAL_GIT_REPLAY"
        for artifact in audit["artifacts"]
        for source in artifact["source_replays"]
    )


def test_reference_ledgers_and_external_byte_boundary_are_explicit(
    runtime: dict[str, object],
) -> None:
    references = runtime["reference_audit"]
    external = runtime["external_source_capture_boundary"]

    assert references["ledger_count"] == 8
    assert references["reference_record_count"] == 25
    assert external["capture_metadata_occurrence_count"] == 9
    assert external["source_byte_complete_archive"] is False
    assert all(
        capture["required_for_r13_replay"] is False
        for capture in external["capture_metadata"]
    )


def test_trusted_inputs_are_visible_and_inherited_duplicates_are_preserved(
    runtime: dict[str, object],
) -> None:
    audit = runtime["trusted_input_audit"]

    assert audit["occurrence_count"] == 30
    assert audit["unique_count"] == 25
    inherited = [
        entry
        for entry in audit["catalog"]
        if any(origin["inherited"] for origin in entry["origins"])
    ]
    assert len(inherited) == 5
    assert all(len(entry["origins"]) == 2 for entry in inherited)


def test_all_predecessor_nonclaims_are_preserved_verbatim(
    runtime: dict[str, object],
) -> None:
    audit = runtime["predecessor_nonclaim_audit"]

    assert audit["nonclaim_count"] == 64
    assert [row["milestone_id"] for row in audit["by_milestone"]] == [
        "R0",
        "R1",
        "R2_R4",
        "R5",
        "R6",
        "R7",
        "R8",
        "R9",
        "R10",
        "R11",
        "R12",
    ]


def test_terminal_route_and_concrete_claims_remain_distinct(
    runtime: dict[str, object],
) -> None:
    boundary = runtime["terminal_boundary"]

    assert boundary["formalization_route_terminal"] is True
    assert boundary["r11_conditional_invariant_established"] is True
    assert boundary["r12_exact_control_admitted"] is True
    assert boundary["figure21_structural_row_count"] == 15
    assert boundary["figure21_structural_denominators_complete"] is True
    assert boundary["figure21_terminal_blockers"] == list(KNOWN_BLOCKERS)


@pytest.mark.parametrize(
    "field",
    [
        "figure21_exact_value_admitted",
        "figure21_marked_comparison_admitted",
        "crane_yetter_identification_established",
        "all_imported_category_identities_reproved",
        "source_byte_complete_archive",
        "ctl_claim_admitted",
    ],
)
def test_forbidden_promotions_fail_closed(
    runtime: dict[str, object],
    field: str,
) -> None:
    mutation = deepcopy(runtime)
    mutation["terminal_boundary"][field] = True
    rehash(mutation)

    with pytest.raises(ValueError, match="forbidden promotion"):
        validate_final_formalization_runtime(mutation)


def test_stale_runtime_hash_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["status"] = "EDITED_WITHOUT_REHASH"

    with pytest.raises(ValueError, match="content hash is stale"):
        validate_final_formalization_runtime(mutation)


def test_missing_or_duplicate_milestone_cannot_hide(
    runtime: dict[str, object],
) -> None:
    missing = deepcopy(runtime)
    missing["milestone_audit"]["artifacts"].pop()
    missing["milestone_audit"]["artifact_count"] = 10
    rehash(missing)
    with pytest.raises(ValueError, match="milestone denominator"):
        validate_final_formalization_runtime(missing)

    duplicate = deepcopy(runtime)
    duplicate["milestone_audit"]["artifacts"][-1] = deepcopy(
        duplicate["milestone_audit"]["artifacts"][-2]
    )
    rehash(duplicate)
    with pytest.raises(ValueError, match="frozen historical replay"):
        validate_final_formalization_runtime(duplicate)


def test_source_replay_mutation_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    source = mutation["milestone_audit"]["artifacts"][0]["source_replays"][0]
    source["sha256"] = "sha256:" + "0" * 64
    rehash(mutation)

    with pytest.raises(ValueError, match="frozen historical replay"):
        validate_final_formalization_runtime(mutation)


def test_hidden_trusted_input_or_nonclaim_fails_closed(
    runtime: dict[str, object],
) -> None:
    hidden_input = deepcopy(runtime)
    hidden_input["trusted_input_audit"]["catalog"].pop()
    hidden_input["trusted_input_audit"]["unique_count"] = 24
    rehash(hidden_input)
    with pytest.raises(ValueError, match="trusted-input denominator"):
        validate_final_formalization_runtime(hidden_input)

    hidden_nonclaim = deepcopy(runtime)
    hidden_nonclaim["predecessor_nonclaim_audit"][
        "by_milestone"
    ][0]["nonclaims"].pop()
    hidden_nonclaim["predecessor_nonclaim_audit"]["nonclaim_count"] = 63
    rehash(hidden_nonclaim)
    with pytest.raises(ValueError, match="non-claim denominator"):
        validate_final_formalization_runtime(hidden_nonclaim)


def test_missing_figure21_blocker_fails_closed(
    runtime: dict[str, object],
) -> None:
    mutation = deepcopy(runtime)
    mutation["terminal_boundary"]["figure21_terminal_blockers"].pop()
    rehash(mutation)

    with pytest.raises(ValueError, match="blocker denominator"):
        validate_final_formalization_runtime(mutation)


def test_r13_nonclaims_include_ctl_and_crane_yetter_boundaries(
    runtime: dict[str, object],
) -> None:
    nonclaims = "\n".join(runtime["explicit_non_claims"])

    assert len(runtime["explicit_non_claims"]) == 10
    assert "Crane-Yetter state sum" in nonclaims
    assert "exact Figure 21 invariant value" in nonclaims
    assert "byte-complete archive" in nonclaims
    assert "does not create or admit a CTL" in nonclaims
