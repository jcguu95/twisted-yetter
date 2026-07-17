from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))
SCRIPT = (
    REPO_ROOT
    / "experiments/scripts/"
    "build_figure21_pointed_ordinary_normalization_audit_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "figure21_pointed_ordinary_normalization_audit_v1",
    SCRIPT,
)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

NormalizationAuditError = MODULE.NormalizationAuditError
build_audit = MODULE.build_audit
content_hash = MODULE._content_hash


def _mutated_rank23(tmp_path: Path, mutate) -> Path:
    source = (
        REPO_ROOT
        / "experiments/results/akbulut-yasui/"
        "figure21-rank2-rank3-standard-comparison-v1.json"
    )
    payload = json.loads(source.read_text())
    mutate(payload)
    output = tmp_path / source.name
    output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return output


def test_all_pointed_rows_match_after_independent_ordinary_calibration() -> None:
    payload = build_audit()
    assert payload["status"] == (
        "PASS_ALL_15_POINTED_ROWS_MATCH_AFTER_INDEPENDENT_"
        "ORDINARY_AGGREGATE_NORMALIZATION"
    )
    assert payload["row_count"] == 15
    assert payload["normalized_distribution_match_count"] == 15
    assert payload["nonidentity_presentation_correction_count"] == 2
    rows = {row["realization_id"]: row for row in payload["rows"]}
    for realization_id in (
        "rank2-cyclic-z2-semion-minus",
        "rank2-cyclic-z2-semion-plus",
    ):
        calibration = rows[realization_id]["ordinary_kirby_aggregate_calibration"]
        assert calibration["figure21_raw_ordinary_aggregate"]["canonical_key"] == "-32+0i"
        assert calibration["standard_raw_ordinary_aggregate"]["canonical_key"] == "+32+0i"
        assert calibration["presentation_correction_on_figure21"]["canonical_key"] == "-1+0i"
        assert rows[realization_id][
            "normalized_figure21_minus_standard_distribution"
        ] == {}


def test_non_semion_rows_need_no_presentation_correction() -> None:
    payload = build_audit()
    for row in payload["rows"]:
        if row["rank"] == 2:
            continue
        correction = row["ordinary_kirby_aggregate_calibration"][
            "presentation_correction_on_figure21"
        ]
        assert correction["canonical_key"] == "+1+0i"


def test_same_ordinary_sum_but_corrupted_distribution_fails_closed(
    tmp_path: Path,
) -> None:
    def mutate(payload):
        row = next(
            row
            for row in payload["rows"]
            if row["realization_id"] == "rank2-cyclic-z2-semion-plus"
        )
        distribution = row["figure21_nonzero_value_distribution"]
        distribution["+0+1i"] += 1
        distribution["+0-1i"] += 1
        distribution["+1+0i"] -= 1
        distribution["-1+0i"] -= 1

    path = _mutated_rank23(tmp_path, mutate)
    with pytest.raises(
        NormalizationAuditError,
        match="ordinary aggregate calibration does not fix the full distribution",
    ):
        build_audit({"rank2_rank3": path})


def test_stale_snapshot_hash_fails_closed(tmp_path: Path) -> None:
    def mutate(payload):
        payload["rows"][0]["snapshot_content_hash"] = "sha256:stale"

    path = _mutated_rank23(tmp_path, mutate)
    with pytest.raises(NormalizationAuditError, match="stale snapshot content hash"):
        build_audit({"rank2_rank3": path})


def test_checked_in_normalization_artifact_is_content_addressed_and_clean() -> None:
    path = (
        REPO_ROOT
        / "experiments/results/akbulut-yasui/"
        "figure21-pointed-ordinary-normalization-audit-v1.json"
    )
    payload = json.loads(path.read_text())
    recorded_hash = payload.pop("content_hash")
    assert content_hash(payload) == recorded_hash
    assert payload["git_dirty_before_output_write"] is False
    assert all(row["sha256"].startswith("sha256:") for row in payload["inputs"])
