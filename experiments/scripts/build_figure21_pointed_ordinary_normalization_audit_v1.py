#!/usr/bin/env python3
"""Calibrate Figure 21 pointed presentation normalization from ordinary sums."""

from __future__ import annotations

from collections import Counter
from datetime import UTC, datetime
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any, Mapping

from experiments.sage.pointed_premodular_categories import (
    SnapshotPointedModularCategory,
)
from experiments.scripts.build_figure21_rank4_standard_comparison_v1 import (
    REPO_ROOT,
    _canonical_distribution,
    _distribution_diff,
    _load_snapshot,
)
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    _complex_from_key,
    _complex_key,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-pointed-ordinary-normalization-audit-v1.json"
)
COMPARISON_PATHS = {
    "rank2_rank3": (
        "experiments/results/akbulut-yasui/"
        "figure21-rank2-rank3-standard-comparison-v1.json"
    ),
    "rank4": (
        "experiments/results/akbulut-yasui/"
        "figure21-rank4-standard-comparison-v1.json"
    ),
    "rank5": (
        "experiments/results/akbulut-yasui/"
        "figure21-rank5-standard-comparison-v1.json"
    ),
}
EXPECTED_ROW_COUNTS = {
    "rank2_rank3": 4,
    "rank4": 9,
    "rank5": 2,
}
TOLERANCE = 1e-8


class NormalizationAuditError(ValueError):
    """Raised when ordinary calibration cannot safely normalize a comparison."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise NormalizationAuditError(message)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _sha256(path: Path) -> str:
    return f"sha256:{hashlib.sha256(path.read_bytes()).hexdigest()}"


def _content_hash(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _complex_json(value: complex) -> dict[str, Any]:
    value = complex(value)
    return {
        "real": repr(float(value.real)),
        "imag": repr(float(value.imag)),
        "abs": repr(float(abs(value))),
        "canonical_key": _complex_key(value),
    }


def _distribution_sum(distribution: Mapping[str, int]) -> complex:
    return sum(
        (
            _complex_from_key(key) * int(count)
            for key, count in distribution.items()
        ),
        start=0.0 + 0.0j,
    )


def _multiply_distribution(
    distribution: Mapping[str, int],
    scalar: complex,
) -> dict[str, int]:
    result: Counter[str] = Counter()
    for key, count in distribution.items():
        result[_complex_key(_complex_from_key(key) * scalar)] += int(count)
    return _canonical_distribution(dict(result))


def _load_comparison(
    key: str,
    overrides: Mapping[str, Path] | None,
) -> tuple[Path, dict[str, Any]]:
    path = (
        overrides[key]
        if overrides and key in overrides
        else REPO_ROOT / COMPARISON_PATHS[key]
    )
    _require(path.is_file(), f"missing comparison input: {path}")
    payload = json.loads(path.read_text())
    _require(
        payload.get("row_count") == EXPECTED_ROW_COUNTS[key],
        f"{path.name}: comparison row denominator changed",
    )
    return path, payload


def _snapshot_for_row(
    row: Mapping[str, Any],
) -> tuple[dict[str, Any], SnapshotPointedModularCategory]:
    realization_id = str(row["realization_id"])
    snapshot = _load_snapshot(realization_id)
    _require(
        snapshot.get("content_hash") == row.get("snapshot_content_hash"),
        f"{realization_id}: stale snapshot content hash",
    )
    _require(
        snapshot.get("category_data_hash") == row.get("category_data_hash"),
        f"{realization_id}: stale category data hash",
    )
    category = SnapshotPointedModularCategory(snapshot)
    _require(
        all(
            abs(complex(category.dimension(label)) - 1.0) <= TOLERANCE
            for label in category.labels
        ),
        f"{realization_id}: ordinary unweighted sum is only valid for pointed dimensions one",
    )
    return snapshot, category


def _audit_row(row: Mapping[str, Any]) -> dict[str, Any]:
    realization_id = str(row["realization_id"])
    snapshot, category = _snapshot_for_row(row)
    figure21 = _canonical_distribution(
        dict(row["figure21_nonzero_value_distribution"])
    )
    standard = _canonical_distribution(
        dict(row["standard_cp2_9cpbar"]["value_distribution"])
    )
    _require(
        sum(figure21.values()) == sum(standard.values()),
        f"{realization_id}: fixed-label sector denominators differ",
    )

    figure21_ordinary = _distribution_sum(figure21)
    standard_ordinary = _distribution_sum(standard)
    _require(
        abs(figure21_ordinary) > TOLERANCE,
        f"{realization_id}: Figure 21 ordinary aggregate is zero; calibration is unsafe",
    )
    _require(
        abs(standard_ordinary) > TOLERANCE,
        f"{realization_id}: standard ordinary aggregate is zero; calibration is unsafe",
    )
    correction = standard_ordinary / figure21_ordinary
    _require(
        abs(abs(correction) - 1.0) <= TOLERANCE,
        f"{realization_id}: ordinary calibration is not a unit presentation scalar",
    )

    normalized = _multiply_distribution(figure21, correction)
    normalized_diff = _distribution_diff(normalized, standard)
    _require(
        not normalized_diff,
        (
            f"{realization_id}: ordinary aggregate calibration does not fix "
            "the full distribution"
        ),
    )
    raw_diff = _distribution_diff(figure21, standard)
    return {
        "realization_id": realization_id,
        "family_id": row["family_id"],
        "rank": row["rank"],
        "status": "PASS_INDEPENDENT_ORDINARY_CALIBRATION_AND_FULL_DISTRIBUTION_MATCH",
        "pointed_dimension_check": {
            "label_count": len(category.labels),
            "all_quantum_dimensions_equal_one": True,
        },
        "snapshot": {
            "content_hash": snapshot["content_hash"],
            "category_data_hash": snapshot["category_data_hash"],
        },
        "raw_figure21_nonzero_value_distribution": figure21,
        "raw_standard_nonzero_value_distribution": standard,
        "raw_figure21_minus_standard_distribution": raw_diff,
        "ordinary_kirby_aggregate_calibration": {
            "calibration_input": (
                "The unweighted sum of all fixed-label amplitudes. This equals "
                "the ordinary Kirby-color graph evaluation here because every "
                "simple object in the validated pointed snapshots has dimension one."
            ),
            "figure21_raw_ordinary_aggregate": _complex_json(figure21_ordinary),
            "standard_raw_ordinary_aggregate": _complex_json(standard_ordinary),
            "presentation_correction_on_figure21": _complex_json(correction),
            "correction_derived_before_distribution_comparison": True,
            "distribution_bucket_alignment_not_used_to_choose_correction": True,
        },
        "normalized_figure21_nonzero_value_distribution": normalized,
        "normalized_figure21_minus_standard_distribution": normalized_diff,
    }


def build_audit(
    overrides: Mapping[str, Path] | None = None,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    dirty_before = bool(_git("status", "--short"))
    loaded = {
        key: _load_comparison(key, overrides)
        for key in COMPARISON_PATHS
    }
    rows = [
        _audit_row(row)
        for key in COMPARISON_PATHS
        for row in loaded[key][1]["rows"]
    ]
    _require(len(rows) == 15, "pointed Figure 21 realization denominator is not 15")
    nonidentity = [
        row
        for row in rows
        if row["ordinary_kirby_aggregate_calibration"][
            "presentation_correction_on_figure21"
        ]["canonical_key"]
        != "+1+0i"
    ]
    _require(
        {
            row["realization_id"]
            for row in nonidentity
        }
        == {
            "rank2-cyclic-z2-semion-minus",
            "rank2-cyclic-z2-semion-plus",
        },
        "nonidentity presentation-correction denominator changed",
    )
    _require(
        all(
            row["ordinary_kirby_aggregate_calibration"][
                "presentation_correction_on_figure21"
            ]["canonical_key"]
            == "-1+0i"
            for row in nonidentity
        ),
        "semion presentation correction is no longer exactly -1",
    )

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.figure21-pointed-ordinary-normalization-audit.v1",
        "status": (
            "PASS_ALL_15_POINTED_ROWS_MATCH_AFTER_INDEPENDENT_"
            "ORDINARY_AGGREGATE_NORMALIZATION"
        ),
        "mathematical_status": (
            "ESTABLISHED_COMPUTATIONAL_PRESENTATION_NORMALIZATION_"
            "NOT_H2_MARKED_POINTWISE_THEOREM"
        ),
        "top_notice": (
            "The previous two semion -1 differences are raw presentation-level "
            "graph-normalization differences. For each pointed row, this artifact "
            "derives one correction using only the ordinary Kirby-color aggregate "
            "and then independently checks the complete fixed-label distribution. "
            "It does not construct an H2 marking or prove a general MTC normalization theorem."
        ),
        "generator_script": (
            "experiments/scripts/"
            "build_figure21_pointed_ordinary_normalization_audit_v1.py"
        ),
        "reproduce_command": (
            "python experiments/scripts/"
            "build_figure21_pointed_ordinary_normalization_audit_v1.py"
        ),
        "started_at_utc": started.isoformat(),
        "finished_at_utc": datetime.now(UTC).isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty_before_output_write": dirty_before,
        "python_version": platform.python_version(),
        "tolerance": TOLERANCE,
        "inputs": [
            {
                "role": key,
                "path": str(path.relative_to(REPO_ROOT)),
                "sha256": _sha256(path),
                "schema": payload.get("schema"),
                "status": payload.get("status"),
            }
            for key, (path, payload) in loaded.items()
        ],
        "calibration_rule": {
            "scope": "POINTED_CATEGORIES_WITH_ALL_QUANTUM_DIMENSIONS_ONE",
            "figure21_raw_ordinary_aggregate": (
                "S_F21(C)=sum_l A_F21,C^raw(l)"
            ),
            "standard_raw_ordinary_aggregate": (
                "S_std(C)=sum_l A_std,C^raw(l)"
            ),
            "presentation_correction": "nu_C=S_std(C)/S_F21(C)",
            "normalized_amplitude": (
                "A_F21,C^normalized(l)=nu_C*A_F21,C^raw(l)"
            ),
            "non_circularity": (
                "nu_C is determined from the single ordinary aggregate before "
                "the full value-distribution buckets are compared. A preserved-"
                "aggregate corrupted distribution is a required negative test."
            ),
        },
        "row_count": len(rows),
        "normalized_distribution_match_count": len(rows),
        "nonidentity_presentation_correction_count": len(nonidentity),
        "nonidentity_presentation_correction_realization_ids": [
            row["realization_id"] for row in nonidentity
        ],
        "rows": rows,
        "explicit_non_claims": [
            "This does not erase or rewrite the historical raw graph evaluations.",
            "This does not certify the Figure 21 source transcription against the printed diagram.",
            "This does not provide a Figure 21 H2 coordinate map.",
            "This does not prove pointwise equality for every alpha.",
            "This pointed dimension-one calibration is not a general MTC normalization theorem.",
            "This does not establish a premodular formula or premodular exotic comparison.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> int:
    payload = build_audit()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    )
    print(OUTPUT)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
