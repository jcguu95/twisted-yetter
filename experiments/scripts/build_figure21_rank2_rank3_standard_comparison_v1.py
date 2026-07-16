#!/usr/bin/env python3
"""Compare completed rank-2/3 Figure 21 pointed distributions to the standard side."""

from __future__ import annotations

from datetime import UTC, datetime
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any

from experiments.sage.pointed_premodular_categories import SnapshotPointedModularCategory
from experiments.scripts.build_figure21_rank4_standard_comparison_v1 import (
    CANONICAL_DECIMALS,
    FIGURE21_CHUNK_ROOT,
    REPO_ROOT,
    _canonical_distribution,
    _content_hash,
    _distribution_diff,
    _load_snapshot,
    _nonzero_distribution,
    _standard_distribution,
)
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    _load_standard,
)


PREFIX_SWEEP_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-vs-standard-pointed-modular-sweep-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-rank2-rank3-standard-comparison-v1.json"
)
REALIZATION_IDS = (
    "rank2-cyclic-z2-semion-minus",
    "rank2-cyclic-z2-semion-plus",
    "rank3-cyclic-z3-minus",
    "rank3-cyclic-z3-plus",
)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _load_prefix_rows() -> dict[str, dict[str, Any]]:
    payload = json.loads(PREFIX_SWEEP_PATH.read_text())
    return {row["realization_id"]: row for row in payload["rows"]}


def _figure21_distribution(realization_id: str, prefix_rows: dict[str, dict[str, Any]]) -> dict[str, int]:
    if realization_id.startswith("rank2-"):
        return prefix_rows[realization_id]["figure21_right"]["value_distribution"]
    aggregate_path = FIGURE21_CHUNK_ROOT / realization_id / "aggregate.json"
    aggregate = json.loads(aggregate_path.read_text())
    return aggregate["value_distribution"]


def generate() -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    standard = _load_standard()
    prefix_rows = _load_prefix_rows()
    rows = []
    for realization_id in REALIZATION_IDS:
        prefix_row = prefix_rows[realization_id]
        snapshot = _load_snapshot(realization_id)
        category = SnapshotPointedModularCategory(snapshot)
        figure21_distribution = _canonical_distribution(
            _nonzero_distribution(_figure21_distribution(realization_id, prefix_rows))
        )
        standard_result = _standard_distribution(category, standard)
        standard_distribution = _canonical_distribution(standard_result["value_distribution"])
        standard_result["value_distribution_raw"] = standard_result["value_distribution"]
        standard_result["value_distribution"] = standard_distribution
        diff = _distribution_diff(figure21_distribution, standard_distribution)
        rows.append(
            {
                "realization_id": realization_id,
                "family_id": prefix_row["family_id"],
                "rank": prefix_row["rank"],
                "status": (
                    "PASS_FIGURE21_NONZERO_MATCHES_STANDARD"
                    if not diff
                    else "PASS_COMPUTED_DIFFERENT_DISTRIBUTION"
                ),
                "figure21_source": (
                    "PREFIX_FULL_SWEEP"
                    if realization_id.startswith("rank2-")
                    else "CHUNK_AGGREGATE"
                ),
                "figure21_nonzero_value_distribution": figure21_distribution,
                "standard_cp2_9cpbar": standard_result,
                "figure21_nonzero_minus_standard_distribution": diff,
                "comparison_canonical_decimals": CANONICAL_DECIMALS,
                "snapshot_content_hash": snapshot.get("content_hash"),
                "category_data_hash": prefix_row["category_data_hash"],
                "nonzero_sector_count_matches_standard": (
                    sum(figure21_distribution.values()) == standard_result["sector_count"]
                ),
            }
        )
    matching = [
        row for row in rows if row["status"] == "PASS_FIGURE21_NONZERO_MATCHES_STANDARD"
    ]
    differing = [
        row for row in rows if row["status"] == "PASS_COMPUTED_DIFFERENT_DISTRIBUTION"
    ]
    status = (
        "PASS_RANK2_RANK3_STANDARD_COMPARISON_ALL_MATCH"
        if not differing
        else "PASS_RANK2_RANK3_STANDARD_COMPARISON_WITH_DIFFERENCES"
    )
    finished = datetime.now(UTC)
    payload = {
        "schema": "twisted-yetter.figure21-rank2-rank3-standard-comparison.v1",
        "status": status,
        "mathematical_status": "COMPUTED_COMPARISON_NOT_H2_CERTIFIED_EXOTIC_CLAIM",
        "generator_script": (
            "experiments/scripts/build_figure21_rank2_rank3_standard_comparison_v1.py"
        ),
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "prefix_sweep": str(PREFIX_SWEEP_PATH.relative_to(REPO_ROOT)),
            "figure21_aggregate_root": str(FIGURE21_CHUNK_ROOT.relative_to(REPO_ROOT)),
            "standard": {
                "path": "experiments/inputs/standard/e1-cp2-sum-9barcp2-morse-v1.json",
                "manifold": standard["source"]["manifold"],
                "signature": standard["source"]["signature"],
                "component_count": standard["source"]["component_count"],
                "framings": standard["source"]["framings"],
            },
        },
        "comparison_rule": (
            "Compare the nonzero Figure 21 projector distribution against the "
            "split CP2#9CPbar fixed-label distribution, with no H2 coordinate "
            "identification beyond the same category labels."
        ),
        "row_count": len(rows),
        "matching_row_count": len(matching),
        "differing_row_count": len(differing),
        "rows": rows,
        "claim_boundary": (
            "This is a same-label computed distribution comparison for rank-2 "
            "and rank-3 pointed modular rows. It is not a certified exoticness "
            "theorem because the H2 coordinate comparison remains outside this artifact."
        ),
        "non_claims": [
            "This does not certify that Figure 21 is exotic.",
            "This does not certify equality or inequality under a marked H2 identification.",
            "This does not include rank-4 or rank-5 rows.",
            "This does not include non-pointed categories.",
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
