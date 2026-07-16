#!/usr/bin/env python3
"""Compare completed rank-4 Figure 21 pointed aggregates to the standard side."""

from __future__ import annotations

from collections import Counter
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any

from experiments.sage.pointed_premodular_categories import SnapshotPointedModularCategory
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    _complex_from_key,
    _complex_key,
    _load_standard,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
SNAPSHOT_ROOT = (
    REPO_ROOT
    / "experiments/results/foundation-v2-safety-substrate/ribbon-realization-snapshots"
)
FIGURE21_CHUNK_ROOT = (
    REPO_ROOT / "experiments/results/akbulut-yasui/figure21-pointed-chunks-v1"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-rank4-standard-comparison-v1.json"
)

RANK4_REALIZATION_IDS = (
    "rank4-pointed-z4-k1",
    "rank4-pointed-z4-k3",
    "rank4-pointed-z4-k5",
    "rank4-pointed-z4-k7",
    "rank4-pointed-z2xz2-q002",
    "rank4-pointed-z2xz2-q013",
    "rank4-pointed-z2xz2-q112",
    "rank4-pointed-z2xz2-q222",
    "rank4-pointed-z2xz2-q233",
)
CANONICAL_DECIMALS = 9


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _load_snapshot(realization_id: str) -> dict[str, Any]:
    path = SNAPSHOT_ROOT / f"{realization_id}-snapshot-v1.json"
    if not path.exists():
        raise FileNotFoundError(path)
    snapshot = json.loads(path.read_text())
    if snapshot.get("realization_id") != realization_id:
        raise ValueError(f"snapshot realization mismatch for {realization_id}")
    return snapshot


def _standard_distribution(
    category: SnapshotPointedModularCategory,
    standard: dict[str, Any],
) -> dict[str, Any]:
    total = len(category.labels) ** len(standard["component_order"])
    distribution: Counter[str] = Counter({"+1+0i": 1})
    for component in standard["component_order"]:
        local = Counter(
            _complex_key(complex(category.twist(label)) ** standard["framings"][component])
            for label in category.labels
        )
        next_distribution: Counter[str] = Counter()
        for left_key, left_count in distribution.items():
            left = _complex_from_key(left_key)
            for right_key, right_count in local.items():
                right = _complex_from_key(right_key)
                next_distribution[_complex_key(left * right)] += left_count * right_count
        distribution = next_distribution
    value_distribution = dict(sorted(distribution.items()))
    return {
        "status": "FULL_CLOSED_FORM_DISTRIBUTION",
        "backend": "SPLIT_UNLINK_CLOSED_FORM_FIXED_LABELS",
        "sector_count": total,
        "full_sector_count": total,
        "value_distribution": value_distribution,
        "records_sha256": _sha256_bytes(
            json.dumps(
                value_distribution,
                sort_keys=True,
                separators=(",", ":"),
            ).encode()
        ),
    }


def _nonzero_distribution(distribution: dict[str, int]) -> dict[str, int]:
    return {key: value for key, value in distribution.items() if key != "+0+0i"}


def _canonical_key(key: str) -> str:
    value = _complex_from_key(key)
    real = 0.0 if abs(value.real) < 10 ** (-CANONICAL_DECIMALS) else round(value.real, CANONICAL_DECIMALS)
    imag = 0.0 if abs(value.imag) < 10 ** (-CANONICAL_DECIMALS) else round(value.imag, CANONICAL_DECIMALS)
    return f"{real:+.{CANONICAL_DECIMALS}g}{imag:+.{CANONICAL_DECIMALS}g}i"


def _canonical_distribution(distribution: dict[str, int]) -> dict[str, int]:
    counter: Counter[str] = Counter()
    for key, value in distribution.items():
        counter[_canonical_key(key)] += int(value)
    return dict(sorted(counter.items()))


def _distribution_diff(left: dict[str, int], right: dict[str, int]) -> dict[str, int]:
    left = _canonical_distribution(left)
    right = _canonical_distribution(right)
    keys = sorted(set(left) | set(right))
    return {
        key: int(left.get(key, 0)) - int(right.get(key, 0))
        for key in keys
        if int(left.get(key, 0)) != int(right.get(key, 0))
    }


def generate() -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    standard = _load_standard()
    rows = []
    for realization_id in RANK4_REALIZATION_IDS:
        aggregate_path = FIGURE21_CHUNK_ROOT / realization_id / "aggregate.json"
        if not aggregate_path.exists():
            rows.append(
                {
                    "realization_id": realization_id,
                    "status": "BLOCKED_MISSING_FIGURE21_AGGREGATE",
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
        projector_rank_distribution = aggregate.get("projector_rank_distribution", {})
        expected_nonzero = int(projector_rank_distribution.get("1", 0))
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
                "figure21_projector_rank_distribution": projector_rank_distribution,
                "figure21_nonzero_sector_count": sum(figure21_nonzero.values()),
                "standard_sector_count": standard_result["sector_count"],
                "nonzero_sector_count_matches_standard": (
                    sum(figure21_nonzero.values()) == standard_result["sector_count"]
                    and expected_nonzero == standard_result["sector_count"]
                ),
                "figure21_nonzero_value_distribution": dict(sorted(figure21_nonzero.items())),
                "comparison_canonical_decimals": CANONICAL_DECIMALS,
                "standard_cp2_9cpbar": standard_result,
                "figure21_nonzero_minus_standard_distribution": diff,
            }
        )
    terminal_rows = [
        row
        for row in rows
        if row["status"]
        in {
            "PASS_FIGURE21_NONZERO_MATCHES_STANDARD",
            "PASS_COMPUTED_DIFFERENT_DISTRIBUTION",
        }
    ]
    matching_rows = [
        row
        for row in rows
        if row["status"] == "PASS_FIGURE21_NONZERO_MATCHES_STANDARD"
    ]
    differing_rows = [
        row
        for row in rows
        if row["status"] == "PASS_COMPUTED_DIFFERENT_DISTRIBUTION"
    ]
    blocked_rows = [row for row in rows if row not in terminal_rows]
    if blocked_rows:
        status = "TERMINAL_BLOCKED_MISSING_RANK4_INPUT"
    elif differing_rows:
        status = "PASS_RANK4_STANDARD_COMPARISON_WITH_DIFFERENCES"
    else:
        status = "PASS_RANK4_STANDARD_COMPARISON_ALL_MATCH"
    finished = datetime.now(UTC)
    return {
        "schema": "twisted-yetter.figure21-rank4-standard-comparison.v1",
        "status": status,
        "mathematical_status": "COMPUTED_COMPARISON_NOT_H2_CERTIFIED_EXOTIC_CLAIM",
        "generator_script": (
            "experiments/scripts/build_figure21_rank4_standard_comparison_v1.py"
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
            "snapshot_root": str(SNAPSHOT_ROOT.relative_to(REPO_ROOT)),
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
            "split CP2#9CPbar fixed-label distribution. The zero Figure 21 "
            "projector sectors are excluded from this equality check."
        ),
        "rank": 4,
        "row_count": len(rows),
        "matching_row_count": len(matching_rows),
        "differing_row_count": len(differing_rows),
        "blocked_row_count": len(blocked_rows),
        "rows": rows,
        "claim_boundary": (
            "This compares computed rank-4 pointed modular distributions for "
            "the current Figure 21 transcription and the split standard "
            "CP2#9CPbar presentation. It is not a certified exoticness theorem "
            "because the H2 coordinate comparison is still not certified."
        ),
        "non_claims": [
            "This does not certify that Figure 21 is exotic.",
            "This does not certify equality or inequality under a marked H2 identification.",
            "This does not include rank-5 rows.",
            "This does not include non-pointed categories.",
        ],
    }


def main() -> None:
    result = generate()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(OUTPUT)


if __name__ == "__main__":
    main()
