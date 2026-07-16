#!/usr/bin/env python3
"""Compare completed rank-5 Figure 21 pointed aggregates to the standard side."""

from __future__ import annotations

from datetime import UTC, datetime
import json
from pathlib import Path
import platform
import subprocess
import time

from experiments.scripts.build_figure21_rank4_standard_comparison_v1 import (
    CANONICAL_DECIMALS,
    FIGURE21_CHUNK_ROOT,
    OUTPUT as _RANK4_OUTPUT,
    REPO_ROOT,
    _canonical_distribution,
    _content_hash,
    _distribution_diff,
    _load_snapshot,
    _nonzero_distribution,
    _standard_distribution,
)
from experiments.sage.pointed_premodular_categories import SnapshotPointedModularCategory
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import _load_standard


OUTPUT = _RANK4_OUTPUT.with_name("figure21-rank5-standard-comparison-v1.json")
RANK5_REALIZATION_IDS = (
    "rank5-su5-1-s2",
    "rank5-su5-1-s1",
)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def generate() -> dict[str, object]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    standard = _load_standard()
    rows: list[dict[str, object]] = []
    for realization_id in RANK5_REALIZATION_IDS:
        aggregate_path = FIGURE21_CHUNK_ROOT / realization_id / "aggregate.json"
        if not aggregate_path.exists():
            rows.append(
                {
                    "realization_id": realization_id,
                    "status": "PENDING_MISSING_FIGURE21_AGGREGATE",
                    "aggregate_path": str(aggregate_path.relative_to(REPO_ROOT)),
                }
            )
            continue
        aggregate = json.loads(aggregate_path.read_text())
        snapshot = _load_snapshot(realization_id)
        category = SnapshotPointedModularCategory(snapshot)
        standard_result = _standard_distribution(category, standard)
        figure21_nonzero = _canonical_distribution(
            _nonzero_distribution(aggregate["value_distribution"])
        )
        standard_value_distribution = _canonical_distribution(
            standard_result["value_distribution"]
        )
        standard_result["value_distribution_raw"] = standard_result["value_distribution"]
        standard_result["value_distribution"] = standard_value_distribution
        diff = _distribution_diff(figure21_nonzero, standard_value_distribution)
        rows.append(
            {
                "realization_id": realization_id,
                "family_id": aggregate["family_id"],
                "rank": aggregate["rank"],
                "status": (
                    "PASS_FIGURE21_NONZERO_MATCHES_STANDARD"
                    if not diff
                    else "PASS_COMPUTED_DIFFERENT_DISTRIBUTION"
                ),
                "figure21_aggregate_path": str(aggregate_path.relative_to(REPO_ROOT)),
                "snapshot_content_hash": aggregate["snapshot_content_hash"],
                "category_data_hash": aggregate["category_data_hash"],
                "figure21_status": aggregate["status"],
                "figure21_sector_count": aggregate["observed_sector_count"],
                "figure21_projector_rank_distribution": aggregate[
                    "projector_rank_distribution"
                ],
                "figure21_nonzero_sector_count": sum(figure21_nonzero.values()),
                "standard_sector_count": standard_result["sector_count"],
                "nonzero_sector_count_matches_standard": (
                    sum(figure21_nonzero.values()) == standard_result["sector_count"]
                ),
                "figure21_nonzero_value_distribution": dict(sorted(figure21_nonzero.items())),
                "comparison_canonical_decimals": CANONICAL_DECIMALS,
                "standard_cp2_9cpbar": standard_result,
                "figure21_nonzero_minus_standard_distribution": diff,
            }
        )
    completed = [
        row for row in rows if not str(row["status"]).startswith("PENDING_")
    ]
    matching = [
        row for row in rows if row["status"] == "PASS_FIGURE21_NONZERO_MATCHES_STANDARD"
    ]
    differing = [
        row for row in rows if row["status"] == "PASS_COMPUTED_DIFFERENT_DISTRIBUTION"
    ]
    pending = [row for row in rows if str(row["status"]).startswith("PENDING_")]
    if pending:
        status = "PARTIAL_RANK5_STANDARD_COMPARISON_PENDING_AGGREGATES"
    elif differing:
        status = "PASS_RANK5_STANDARD_COMPARISON_WITH_DIFFERENCES"
    else:
        status = "PASS_RANK5_STANDARD_COMPARISON_ALL_MATCH"
    finished = datetime.now(UTC)
    payload = {
        "schema": "twisted-yetter.figure21-rank5-standard-comparison.v1",
        "status": status,
        "mathematical_status": "COMPUTED_COMPARISON_NOT_H2_CERTIFIED_EXOTIC_CLAIM",
        "generator_script": (
            "experiments/scripts/build_figure21_rank5_standard_comparison_v1.py"
        ),
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "figure21_aggregate_root": str(FIGURE21_CHUNK_ROOT.relative_to(REPO_ROOT)),
            "standard": {
                "path": "experiments/inputs/standard/e1-cp2-sum-9barcp2-morse-v1.json",
                "manifold": standard["source"]["manifold"],
                "signature": standard["source"]["signature"],
                "component_count": standard["source"]["component_count"],
                "framings": standard["source"]["framings"],
            },
        },
        "rank": 5,
        "row_count": len(rows),
        "completed_row_count": len(completed),
        "matching_row_count": len(matching),
        "differing_row_count": len(differing),
        "pending_row_count": len(pending),
        "comparison_rule": (
            "Compare the nonzero Figure 21 projector distribution against the "
            "split CP2#9CPbar fixed-label distribution."
        ),
        "rows": rows,
        "claim_boundary": (
            "This is a computed distribution comparison for rank-5 pointed "
            "modular rows. It is not a certified exoticness theorem because "
            "the H2 coordinate comparison remains outside this artifact."
        ),
        "non_claims": [
            "This does not certify that Figure 21 is exotic.",
            "This does not include non-pointed categories.",
            "Pending rows are not silently treated as matches.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> None:
    result = generate()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(OUTPUT)


if __name__ == "__main__":
    main()
