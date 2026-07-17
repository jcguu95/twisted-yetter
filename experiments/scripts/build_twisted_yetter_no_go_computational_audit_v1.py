#!/usr/bin/env python3
"""Audit completed MTC comparisons against the candidate stable no-go theorem."""

from __future__ import annotations

from datetime import UTC, datetime
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    REPO_ROOT
    / "experiments/results/theory/"
    "twisted-yetter-stable-no-go-computational-audit-v1.json"
)

PATHS = {
    "figure21_batch": "experiments/results/akbulut-yasui/figure21-pointed-batch-result-v1.json",
    "figure21_rank23": "experiments/results/akbulut-yasui/figure21-rank2-rank3-standard-comparison-v1.json",
    "figure21_rank4": "experiments/results/akbulut-yasui/figure21-rank4-standard-comparison-v1.json",
    "figure21_rank5": "experiments/results/akbulut-yasui/figure21-rank5-standard-comparison-v1.json",
    "figure21_budgeted_sweep": "experiments/results/akbulut-yasui/figure21-vs-standard-pointed-modular-sweep-v1.json",
    "figure21_untwisted_su22": "experiments/results/akbulut-yasui/figure21-right-su2-2-untwisted-framed-evaluation-v1.json",
    "figure21_semion_backend": "experiments/results/akbulut-yasui/figure21-right-rank2-semion-modular-evaluation-v1.json",
    "figure21_bad_framing": "experiments/results/akbulut-yasui/figure21-right-su2-2-blackboard-framing-omission-run-v1.json",
    "figure21_premodular": "experiments/results/akbulut-yasui/figure21-right-pointed-premodular-projector-controls-v1.json",
    "figure21_hard_barrier": "experiments/results/akbulut-yasui/figure21-right-su2-2-sector95378-runtime-barrier-v1.json",
    "figure21_terminal_package": "experiments/results/akbulut-yasui/current-low-rank-figure21-terminal-package-v1.json",
    "akbulut_su22_untwisted": "experiments/results/akbulut/figure1-e1-su2-2-untwisted-comparison-v1.json",
    "akbulut_su22_sampled": "experiments/results/akbulut/figure1-e1-su2-2-sampled-twists-comparison-v1.json",
    "akbulut_su23_untwisted": "experiments/results/akbulut/figure1-e1-su2-3-untwisted-chunked-comparison-v2.json",
    "akbulut_su23_twisted": "experiments/results/akbulut/figure1-e1-su2-3-twisted-x-chunked-comparison-v1.json",
    "yasui_figure2_su2": "experiments/results/yasui/figure2-cp2-a1-r1-su2k-untwisted-check-v1.json",
    "yasui_figure2_su32": "experiments/results/yasui/figure2-cp2-a1-r1-su3-2-anyonwiki-h2-character-check-v1.json",
    "yasui_figure2_dic12": "experiments/results/yasui/figure2-cp2-a1-r1-dic12-omega0-range-combined-aggregate-v1.json",
    "yasui_a1_su22": "experiments/results/yasui/figure3-a1-r1-normalized-su2-2-all-alpha-raw-comparison-v3.json",
    "yasui_a1_su23": "experiments/results/yasui/figure3-a1-r1-normalized-su2-3-all-alpha-raw-comparison-v2.json",
    "yasui_a1_su24": "experiments/results/yasui/figure3-a1-r1-normalized-su2-4-all-alpha-raw-comparison-v3.json",
    "yasui_a1_su26": "experiments/results/yasui/figure3-a1-r1-normalized-su2-6-all-alpha-raw-comparison-v2.json",
    "yasui_a1_su28": "experiments/results/yasui/figure3-a1-r1-normalized-su2-8-all-alpha-raw-comparison-v3.json",
    "yasui_a1_su32": "experiments/results/yasui/figure3-a1-su3-2-yasui-vs-split-coordinate-comparison-v1.json",
    "yasui_a1_da4": "experiments/results/yasui/figure3-a1-r1-normalized-da4-omega0-untwisted-singleton-aggregate-check-v1.json",
    "yasui_a1_da4_twist": "experiments/results/yasui/figure3-a1-r1-normalized-da4-c3w1-twisted-component-a-singleton-aggregate-v1.json",
    "yasui_a1_da4_split": "experiments/results/yasui/figure3-a1-standard-split-unlink-da4-c3w1-character-scan-v1.json",
    "yasui_a1_dic12": "experiments/results/yasui/figure3-a1-r1-normalized-dic12-witness-g-component-a-twist-compact-trace-manifest-v1.json",
    "yasui_a3_su22": "experiments/results/yasui/figure3-a3-su2-2-all-alpha-chunked-comparison-v1.json",
    "yasui_a3_su23": "experiments/results/yasui/figure3-a3-su2-3-all-alpha-chunked-comparison-v1.json",
    "yasui_a3_su24": "experiments/results/yasui/figure3-a3-su2-4-all-alpha-chunked-comparison-v1.json",
    "yasui_a3_su26": "experiments/results/yasui/figure3-a3-su2-6-all-alpha-chunked-comparison-v1.json",
    "gompf_e1_su22": "experiments/results/gompf-stipsicz/figure815-e1-su2-2-b-minus1-direct-aggregate-v1.json",
    "history_correction": "ctl-dogfood/lab-notes/2026-07-15-yasui-character-twist-history-correction.json",
}

COMPARISON_FILE_DISPOSITIONS = {
    "experiments/results/akbulut-yasui/figure21-rank2-rank3-standard-comparison-v1.json": "RETAINED",
    "experiments/results/akbulut-yasui/figure21-rank4-standard-comparison-v1.json": "RETAINED",
    "experiments/results/akbulut-yasui/figure21-rank5-standard-comparison-v1.json": "RETAINED",
    "experiments/results/akbulut/figure1-e1-su2-2-sampled-twists-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/akbulut/figure1-e1-su2-2-untwisted-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/akbulut/figure1-e1-su2-3-twisted-x-chunked-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/akbulut/figure1-e1-su2-3-untwisted-chunked-comparison-v2.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure2-cp2-a1-su2-2-tham511-comparison-v1.json": "BLOCKED",
    "experiments/results/yasui/figure2-cp2-a1-su2-2-tham511-r1-a15-curl-comparison-v1.json": "NEEDS_REVIEW",
    "experiments/results/yasui/figure3-a1-other-mtc-comparison-v1.json": "BLOCKED",
    "experiments/results/yasui/figure3-a1-r1-normalized-su2-2-all-alpha-raw-comparison-v3.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a1-r1-normalized-su2-3-all-alpha-raw-comparison-v2.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a1-r1-normalized-su2-3-untwisted-raw-comparison-v2.json": "DUPLICATE_SUBSET",
    "experiments/results/yasui/figure3-a1-r1-normalized-su2-4-all-alpha-raw-comparison-v3.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a1-r1-normalized-su2-6-all-alpha-raw-comparison-v2.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a1-r1-normalized-su2-8-all-alpha-raw-comparison-v3.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a1-r1-normalized-su3-2-anyonwiki-convention-comparison-v1.json": "IMPLEMENTATION_CONVENTION_CONTROL",
    "experiments/results/yasui/figure3-a1-standard-comparison-su2-2-v1.json": "SKIPPED_LEGACY_DIAGNOSTIC",
    "experiments/results/yasui/figure3-a1-su3-2-yasui-vs-split-coordinate-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a3-su2-2-all-alpha-chunked-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a3-su2-3-all-alpha-chunked-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a3-su2-3-untwisted-chunked-comparison-v1.json": "DUPLICATE_SUBSET",
    "experiments/results/yasui/figure3-a3-su2-4-all-alpha-chunked-comparison-v1.json": "RETAINED_CONTROL",
    "experiments/results/yasui/figure3-a3-su2-6-all-alpha-chunked-comparison-v1.json": "RETAINED_CONTROL",
}

EXPECTED_DOWNGRADED_COMPARISON_STATUSES = {
    "BLOCKED": {"blocked", "blocked-yasui-braid-payload-not-admitted"},
    "NEEDS_REVIEW": {"needs-review"},
    "DUPLICATE_SUBSET": {"pass"},
    "IMPLEMENTATION_CONVENTION_CONTROL": {"pass_with_convention_warning"},
    "SKIPPED_LEGACY_DIAGNOSTIC": {"skipped-legacy-jones-diagnostic"},
}


class AuditError(ValueError):
    """Raised when a pinned artifact no longer supports the declared result."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return f"sha256:{digest.hexdigest()}"


def _content_hash(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _resolve(key: str, overrides: Mapping[str, Path] | None) -> Path:
    if overrides and key in overrides:
        return overrides[key]
    return REPO_ROOT / PATHS[key]


def _load(key: str, overrides: Mapping[str, Path] | None) -> tuple[Path, dict[str, Any]]:
    path = _resolve(key, overrides)
    _require(path.is_file(), f"missing audit input: {path}")
    return path, json.loads(path.read_text())


def _ref(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    try:
        relative = str(path.relative_to(REPO_ROOT))
    except ValueError:
        relative = str(path)
    return {
        "path": relative,
        "sha256": _sha256(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def _comparison_inventory_entry(
    path: Path, disposition: str
) -> dict[str, str | None]:
    _require(path.is_file(), f"missing classified comparison artifact: {path}")
    payload = json.loads(path.read_text())
    expected_statuses = EXPECTED_DOWNGRADED_COMPARISON_STATUSES.get(disposition)
    if expected_statuses is not None:
        _require(
            payload.get("status") in expected_statuses,
            (
                f"comparison disposition {disposition} is inconsistent with "
                f"status {payload.get('status')!r}: {path}"
            ),
        )
    try:
        display_path = str(path.relative_to(REPO_ROOT))
    except ValueError:
        display_path = str(path)
    return {
        "path": display_path,
        "disposition": disposition,
        "sha256": _sha256(path),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def _decimal(value: Any) -> Decimal:
    return Decimal(str(value))


def _assert_numeric_pass(payload: dict[str, Any], *, expected_rows: int) -> None:
    _require(payload.get("status") == "pass", "numeric comparison status is not pass")
    rows = payload.get("rows", [])
    _require(len(rows) == expected_rows, f"expected {expected_rows} rows, got {len(rows)}")
    tolerance = _decimal(payload["tolerance"])
    _require(
        _decimal(payload["max_abs_difference"]) <= tolerance,
        "max_abs_difference exceeds tolerance",
    )
    _require(
        all(row.get("close_under_tolerance") is True for row in rows),
        "a numeric comparison row is not close_under_tolerance",
    )


def _comparison_inventory() -> list[dict[str, str | None]]:
    discovered: set[str] = set()
    for directory in (
        REPO_ROOT / "experiments/results/akbulut-yasui",
        REPO_ROOT / "experiments/results/akbulut",
        REPO_ROOT / "experiments/results/yasui",
    ):
        for path in directory.glob("*comparison*.json"):
            discovered.add(str(path.relative_to(REPO_ROOT)))
    classified = set(COMPARISON_FILE_DISPOSITIONS)
    missing = sorted(discovered - classified)
    stale = sorted(classified - discovered)
    _require(not missing, f"unclassified comparison artifacts: {missing}")
    _require(not stale, f"classified comparison artifacts no longer present: {stale}")
    retained = {
        path
        for path, disposition in COMPARISON_FILE_DISPOSITIONS.items()
        if disposition in {"RETAINED", "RETAINED_CONTROL"}
    }
    _require(
        retained <= set(PATHS.values()),
        (
            "retained comparison artifacts lack field-level validators: "
            f"{sorted(retained - set(PATHS.values()))}"
        ),
    )
    return [
        _comparison_inventory_entry(
            REPO_ROOT / path, COMPARISON_FILE_DISPOSITIONS[path]
        )
        for path in sorted(classified)
    ]


def build_audit(
    overrides: Mapping[str, Path] | None = None,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()

    loaded = {key: _load(key, overrides) for key in PATHS}
    payloads = {key: pair[1] for key, pair in loaded.items()}

    batch = payloads["figure21_batch"]
    rank23 = payloads["figure21_rank23"]
    rank4 = payloads["figure21_rank4"]
    rank5 = payloads["figure21_rank5"]
    _require(
        batch.get("status") == "PASS_POINTED_FIGURE21_BATCH_COMPLETE",
        "Figure 21 pointed batch is not complete",
    )
    _require(batch.get("row_count") == 15, "Figure 21 pointed denominator is not 15")
    _require(
        rank23.get("status")
        == "PASS_RANK2_RANK3_STANDARD_COMPARISON_ALL_MATCH_PHASE_ALIGNED",
        "rank 2/3 final comparison status changed",
    )
    _require(rank23.get("row_count") == 4, "rank 2/3 row count changed")
    _require(rank23.get("matching_row_count") == 2, "rank 2/3 raw match count changed")
    _require(rank23.get("differing_row_count") == 2, "rank 2 raw discrepancy disappeared")
    _require(
        rank23.get("phase_aligned_matching_row_count") == 4,
        "rank 2/3 phase-aligned count changed",
    )
    rank23_rows = {row["realization_id"]: row for row in rank23["rows"]}
    semion_ids = {
        "rank2-cyclic-z2-semion-minus",
        "rank2-cyclic-z2-semion-plus",
    }
    for realization_id in semion_ids:
        row = rank23_rows[realization_id]
        _require(
            row["figure21_nonzero_minus_standard_distribution"]
            == {"+1+0i": -32, "-1+0i": 32},
            f"unexpected raw semion distribution difference: {realization_id}",
        )
        _require(
            row["phase_alignment"]["phase_multiplier_on_figure21_values"] == "-1+0i",
            f"unexpected semion alignment phase: {realization_id}",
        )
    _require(
        rank4.get("status") == "PASS_RANK4_STANDARD_COMPARISON_ALL_MATCH"
        and rank4.get("matching_row_count") == 9,
        "rank 4 comparison is no longer a 9-row exact match",
    )
    _require(
        rank5.get("status") == "PASS_RANK5_STANDARD_COMPARISON_ALL_MATCH"
        and rank5.get("matching_row_count") == 2,
        "rank 5 comparison is no longer a 2-row exact match",
    )

    untwisted = payloads["figure21_untwisted_su22"]
    _require(untwisted["result"]["match"] == "YES", "Figure 21 SU(2)_2 no longer matches")
    _require(
        untwisted["result"]["absolute_difference"]
        <= untwisted["result"]["match_tolerance"],
        "Figure 21 SU(2)_2 residual exceeds tolerance",
    )
    semion_backend = payloads["figure21_semion_backend"]
    _require(
        semion_backend.get("status")
        == "PASS_FIGURE21_RANK2_SEMION_MODULAR_FULL_SECTOR_EVALUATION",
        "semion modular shortcut control no longer passes",
    )
    for branch in ("minus", "plus"):
        row = semion_backend["results"][branch]
        _require(row["sector_count"] == 2048, f"{branch} semion sector count changed")
        _require(
            row["all_modular_values_equal_pointed_values"] is True
            and row["max_modular_pointed_abs_error"] == 0.0,
            f"{branch} semion modular/pointed backend mismatch",
        )

    ak_su22 = payloads["akbulut_su22_untwisted"]
    _require(
        ak_su22.get("status") == "pass"
        and _decimal(ak_su22["abs_difference"]) <= _decimal(ak_su22["tolerance"]),
        "Akbulut Figure 1 SU(2)_2 untwisted comparison failed",
    )
    ak_samples = payloads["akbulut_su22_sampled"]
    _require(
        ak_samples.get("status") == "pass"
        and ak_samples.get("row_count") == 22
        and ak_samples.get("mismatch_count") == 0,
        "Akbulut Figure 1 SU(2)_2 sampled comparison changed",
    )
    for key in ("akbulut_su23_untwisted", "akbulut_su23_twisted"):
        value = payloads[key]
        _require(
            value.get("status") == "pass"
            and value.get("aggregation_scope") == "full"
            and _decimal(value["abs_difference"]) <= _decimal(value["tolerance"]),
            f"{key} is not a complete passing comparison",
        )

    figure2_su2 = payloads["yasui_figure2_su2"]
    _require(
        figure2_su2.get("status") == "pass" and len(figure2_su2.get("rows", [])) == 2,
        "Yasui Figure 2 SU(2) control changed",
    )
    _require(
        all(row["normalized_matches_unknot_plus_one"] for row in figure2_su2["rows"]),
        "Yasui Figure 2 SU(2) row mismatch",
    )
    figure2_su32 = payloads["yasui_figure2_su32"]
    _require(
        figure2_su32.get("status") == "pass_with_convention_warning",
        "Yasui Figure 2 SU(3)_2 convention status changed",
    )
    character_rows = figure2_su32["rows"][0]["character_rows"]
    _require(
        len(character_rows) == 3
        and all(row["normalized_matches_standard"] for row in character_rows),
        "Yasui Figure 2 SU(3)_2 H2-character comparison changed",
    )
    figure2_dic12 = payloads["yasui_figure2_dic12"]
    _require(
        figure2_dic12.get("status") == "pass"
        and len(figure2_dic12.get("yasui_rows", [])) == 4
        and all(
            row["matches_standard_at_1e_minus_7"]
            for row in figure2_dic12["yasui_rows"]
        ),
        "Yasui Figure 2 D(Dic_12) comparison changed",
    )

    a1_keys = ("yasui_a1_su22", "yasui_a1_su23", "yasui_a1_su24", "yasui_a1_su26", "yasui_a1_su28")
    for key in a1_keys:
        _assert_numeric_pass(payloads[key], expected_rows=8)
    a3_keys = ("yasui_a3_su22", "yasui_a3_su23", "yasui_a3_su24", "yasui_a3_su26")
    for key in a3_keys:
        _assert_numeric_pass(payloads[key], expected_rows=8)

    a1_su32 = payloads["yasui_a1_su32"]
    _require(
        a1_su32.get("status") == "pass"
        and a1_su32["summary"]["row_count"] == 27
        and a1_su32["summary"]["mapped_nonmatching_count"] == 0
        and a1_su32["summary"]["direct_same_tuple_nonmatching_count"] == 18,
        "Yasui a=1 SU(3)_2 coordinate comparison changed",
    )
    da4 = payloads["yasui_a1_da4"]
    _require(
        da4.get("status") == "pass"
        and da4["standard_split_unlink_comparison"]["status"] == "pass"
        and da4["completed_count"] == da4["sector_total_expected"] == 2744,
        "Yasui a=1 D(A4) untwisted aggregate changed",
    )
    da4_twist = payloads["yasui_a1_da4_twist"]
    da4_split = payloads["yasui_a1_da4_split"]
    _require(
        da4_twist.get("status") == "pass"
        and len(da4_twist.get("rows", [])) == 2744
        and da4_split.get("status") == "no-nonbaseline-character-found",
        "Yasui a=1 D(A4)c3w1 witness evidence changed",
    )
    dic12 = payloads["yasui_a1_dic12"]
    _require(
        dic12.get("status") == "pass"
        and dic12["mathematical_summary"]["verdict"]
        == "twisted_matches_expected_nonbaseline_split_signal",
        "Yasui a=1 D(Dic_12) witness evidence changed",
    )
    history = payloads["history_correction"]
    _require(
        history.get("status") == "ESTABLISHED_NUMERIC_REINTERPRETATION",
        "current Yasui correction ledger status changed",
    )

    gompf = payloads["gompf_e1_su22"]
    _require(
        gompf.get("status") == "pass"
        and gompf["checks"]["contiguous_complete_sector_coverage"] is True
        and gompf["checks"]["matches_expected"] is True,
        "Gompf-Stipsicz E(1) control changed",
    )

    bad_framing = payloads["figure21_bad_framing"]
    _require(
        bad_framing.get("status") == "SUPERSEDED_RESOURCE_UNSAFE"
        and bad_framing["result"]["match"] == "NO",
        "known Figure 21 framing-bug artifact lost its unsafe marker",
    )
    premodular = payloads["figure21_premodular"]
    _require(
        premodular.get("status") == "PASS_POINTED_PREMODULAR_FIXED_SECTOR_CONTROLS",
        "premodular fixed-sector control status changed",
    )
    hard_barrier = payloads["figure21_hard_barrier"]
    _require(
        hard_barrier.get("status") == "ESTABLISHED_CURRENT_BACKEND_RUNTIME_BARRIER",
        "nonpointed Figure 21 runtime blocker status changed",
    )
    budgeted_sweep = payloads["figure21_budgeted_sweep"]
    _require(
        budgeted_sweep.get("status")
        == "PASS_POINTED_MODULAR_FIGURE21_STANDARD_SWEEP_WITH_BUDGETED_PREFIXES"
        and budgeted_sweep.get("row_count") == 15
        and budgeted_sweep.get("full_row_count") == 2
        and budgeted_sweep.get("budgeted_prefix_row_count") == 13,
        "historical Figure 21 budgeted sweep changed",
    )

    comparison_inventory = _comparison_inventory()
    exact_pointed_rows = (
        rank23["matching_row_count"]
        + rank4["matching_row_count"]
        + rank5["matching_row_count"]
    )
    _require(exact_pointed_rows == 13, "pointed raw exact-match count is not 13")

    evidence_groups = [
        {
            "id": "figure21-pointed-rank2-5",
            "target_role": "ONLY_CURRENT_EXOTIC_TARGET",
            "category_scope": "15 pointed modular realizations, ranks 2-5",
            "comparison_unit": "nonzero fixed-label value distribution",
            "declared_units": 15,
            "result": "13_RAW_EXACT_AND_2_PHASE_ALIGNED",
            "theorem_compatibility": "COMPATIBLE_BUT_NOT_MARKED_POINTWISE_VERIFICATION",
            "caveat": (
                "The two rank-2 semion rows have a raw global -1 discrepancy. "
                "No certified H2 coordinate map or proof of this normalization phase exists."
            ),
            "artifacts": [
                _ref(*loaded[key])
                for key in (
                    "figure21_batch",
                    "figure21_rank23",
                    "figure21_rank4",
                    "figure21_rank5",
                )
            ],
        },
        {
            "id": "figure21-su2-2-untwisted",
            "target_role": "ONLY_CURRENT_EXOTIC_TARGET_UNTWISTED_CONTROL",
            "category_scope": "SU(2)_2",
            "comparison_unit": "complete untwisted scalar",
            "declared_units": 1,
            "result": "NUMERIC_MATCH_WITHIN_2_7E_MINUS_12",
            "theorem_compatibility": "SUPPORTS_ALPHA_ZERO_SPECIALIZATION_ONLY",
            "artifacts": [_ref(*loaded["figure21_untwisted_su22"])],
        },
        {
            "id": "akbulut-figure1-controls",
            "target_role": "HISTORICAL_PRESENTATION_CONTROL_NOT_CURRENT_CERTIFIED_EXOTIC_TARGET",
            "category_scope": "SU(2)_2 and SU(2)_3",
            "comparison_unit": "22 sampled SU(2)_2 twists plus full SU(2)_3 alpha=0 and X-twist",
            "declared_units": 24,
            "result": "ALL_DECLARED_COMPARISONS_MATCH_TOLERANCE",
            "theorem_compatibility": "COMPATIBLE_CONTROL",
            "artifacts": [
                _ref(*loaded[key])
                for key in (
                    "akbulut_su22_untwisted",
                    "akbulut_su22_sampled",
                    "akbulut_su23_untwisted",
                    "akbulut_su23_twisted",
                )
            ],
        },
        {
            "id": "yasui-figure2-cp2-controls",
            "target_role": "STANDARD_MANIFOLD_PRESENTATION_CONTROL",
            "category_scope": "SU(2)_2, SU(2)_4, SU(3)_2, D(Dic_12)",
            "comparison_unit": "declared alpha rows",
            "declared_units": 9,
            "result": "ALL_DECLARED_COMPARISONS_MATCH_TOLERANCE",
            "theorem_compatibility": "COMPATIBLE_CONTROL_WITH_SU3_CONVENTION_WARNING",
            "artifacts": [
                _ref(*loaded[key])
                for key in (
                    "yasui_figure2_su2",
                    "yasui_figure2_su32",
                    "yasui_figure2_dic12",
                )
            ],
        },
        {
            "id": "yasui-figure3-a1-controls",
            "target_role": "PRESENTATION_CONTROL_NOT_CURRENT_CERTIFIED_EXOTIC_TARGET",
            "category_scope": "five SU(2)_k levels, SU(3)_2, D(A4), D(A4)c3w1, D(Dic_12)",
            "comparison_unit": "40 SU(2) rows, 27 mapped SU(3)_2 rows, and three scalar/witness checks",
            "declared_units": 70,
            "result": "ALL_RETAINED_ROWS_MATCH_AFTER_RECORDED_COORDINATE_OR_WITNESS_RULE",
            "theorem_compatibility": "COMPATIBLE_CONTROL",
            "artifacts": [
                _ref(*loaded[key])
                for key in (
                    *a1_keys,
                    "yasui_a1_su32",
                    "yasui_a1_da4",
                    "yasui_a1_da4_twist",
                    "yasui_a1_da4_split",
                    "yasui_a1_dic12",
                    "history_correction",
                )
            ],
        },
        {
            "id": "yasui-figure3-a3-controls",
            "target_role": "PRESENTATION_CONTROL_NOT_CURRENT_CERTIFIED_EXOTIC_TARGET",
            "category_scope": "SU(2)_2, SU(2)_3, SU(2)_4, SU(2)_6",
            "comparison_unit": "all eight alpha rows at each level",
            "declared_units": 32,
            "result": "ALL_DECLARED_COMPARISONS_MATCH_TOLERANCE",
            "theorem_compatibility": "COMPATIBLE_CONTROL",
            "artifacts": [_ref(*loaded[key]) for key in a3_keys],
        },
        {
            "id": "gompf-stipsicz-e1-control",
            "target_role": "STANDARD_MANIFOLD_IMPLEMENTATION_CONTROL",
            "category_scope": "SU(2)_2",
            "comparison_unit": "complete alpha=0 aggregate",
            "declared_units": 1,
            "result": "MATCHES_EXPECTED",
            "theorem_compatibility": "IMPLEMENTATION_CONTROL_ONLY",
            "artifacts": [_ref(*loaded["gompf_e1_su22"])],
        },
    ]

    excluded_or_downgraded = [
        {
            "id": "figure21-semion-modular-vs-pointed-backend",
            "disposition": "IMPLEMENTATION_CROSSCHECK_NOT_TOPOLOGICAL_PAIR_COMPARISON",
            "detail": "Both branches agree sector by sector on 4096 total fixed-label sectors.",
            "artifact": _ref(*loaded["figure21_semion_backend"]),
        },
        {
            "id": "figure21-budgeted-prefix-sweep",
            "disposition": "SUPERSEDED_PARTIAL_CHECKPOINT_NOT_THEOREM_EVIDENCE",
            "detail": (
                "Only 2 of 15 rows were full evaluations; 13 were budgeted prefixes, "
                "and the run recorded a dirty worktree. Complete rank 2-5 comparison "
                "artifacts supersede it."
            ),
            "artifact": _ref(*loaded["figure21_budgeted_sweep"]),
        },
        {
            "id": "figure21-premodular",
            "disposition": "OUT_OF_THEOREM_DENOMINATOR_FIXED_SECTOR_CONTROLS_ONLY",
            "detail": "No full premodular invariant or exotic-vs-standard comparison was computed.",
            "artifact": _ref(*loaded["figure21_premodular"]),
        },
        {
            "id": "figure21-nonpointed-twisted-su2-2",
            "disposition": "INCOMPLETE_RUNTIME_BARRIER_NO_VALUE",
            "detail": "Hard sectors remain unevaluated; this cannot support or contradict the theorem.",
            "artifact": _ref(*loaded["figure21_hard_barrier"]),
        },
        {
            "id": "figure21-missing-framing-run",
            "disposition": "REJECTED_HISTORICAL_RESULT_KNOWN_FRAMING_BUG",
            "detail": "The nonmatch is caused by omitted total framings and is unsafe as invariant evidence.",
            "artifact": _ref(*loaded["figure21_bad_framing"]),
        },
        {
            "id": "figure21-target-certification",
            "disposition": "BLOCKED_NO_CERTIFIED_H2_MAP_OR_SOURCE_TRANSCRIPTION",
            "detail": "The terminal package remains explicit about both target-certification blockers.",
            "artifact": _ref(*loaded["figure21_terminal_package"]),
        },
    ]

    conditional_theorem = {
        "theorem_id": "conditional-marked-stable-no-go-for-total-twisted-yetter",
        "status": "CONDITIONAL_PROPOSITION_NOT_YET_ESTABLISHED_AS_PROJECT_THEOREM",
        "statement": (
            "Let C be a ribbon fusion category, let A be a finite subgroup of "
            "Aut_tensor(Id_C), and let Z_C(M,alpha) be the homologically twisted "
            "Yetter invariant. Let M and N be closed connected oriented smooth simply "
            "connected 4-manifolds, and let f:H2(M;Z)->H2(N;Z) be an integral "
            "intersection-form isometry. If the marked connected-sum formula holds "
            "with the chosen normalization, the ordinary stabilization scalar "
            "Z_C(S2xS2,0)/Z_C(S4,0) is nonzero, and the marked stable-realization "
            "argument applies, then Z_C(M,alpha)=Z_C(N,(f tensor id_A)(alpha)) "
            "for every alpha in H2(M;A)."
        ),
        "statement_zh_tw": (
            "若 twisted Yetter 的 marked connected-sum 公式、非零穩定化因子與 "
            "marked stable realization 三項前提都成立，則任何兩個具有同構整數交叉形式的"
            "閉、定向、單連通光滑四維流形，其完整 twisted Yetter 函數在由該交叉形式"
            "同構搬運 H2 係數後完全相同。"
        ),
        "proof_route": [
            "Wall gives an unmarked stable diffeomorphism between M and N.",
            "Ruberman-Strle Theorem 2.1 realizes the correction automorphism after one additional S2xS2, producing the prescribed map f direct-sum identity.",
            "Diffeomorphism invariance equates the two stabilized marked invariants.",
            "Marked connected-sum multiplicativity expresses both sides using the same stabilization scalar.",
            "Nonvanishing permits cancellation of that common scalar.",
        ],
        "proof_obligations": [
            {
                "id": "marked-stable-realization",
                "status": "ARGUMENT_SUPPLIED_AWAITING_4_MANIFOLD_EXPERT_REVIEW",
            },
            {
                "id": "marked-connected-sum-normalization",
                "status": "NOT_FORMALIZED_FOR_YETTER_BACKGROUND_THEORY",
            },
            {
                "id": "nonzero-stabilization-factor",
                "status": "SUPPORTED_FOR_ORDINARY_CYK_BY_REUTTER_NOT_YET_NORMALIZATION_BRIDGED",
            },
        ],
    }

    computational_theorem = {
        "theorem_id": "frozen-computation-denominator-compatibility-theorem",
        "status": "ESTABLISHED_MACHINE_CHECKED_STATEMENT_ABOUT_RETAINED_ARTIFACTS",
        "statement": (
            "For the frozen artifact denominator enumerated by this audit, every retained "
            "completed MTC presentation comparison satisfies its recorded tolerance, "
            "coordinate map, witness rule, or explicitly disclosed output-phase alignment. "
            "No retained artifact is a certified counterexample to the conditional marked "
            "stable no-go proposition. On the sole current exotic target, Figure 21, the "
            "strongest result is only distribution-level compatibility: 13 pointed rows "
            "match raw, two semion rows match only after a global -1 output phase, and no "
            "H2-marked pointwise comparison is certified."
        ),
        "statement_zh_tw": (
            "在本 audit 明列並凍結的既有計算範圍內，所有保留的完整 MTC "
            "presentation comparisons 都通過各自記錄的誤差、座標搬運、witness 或明示"
            "的整體 phase 規則；沒有任何一份保留資料構成上述條件式 no-go 命題的"
            "已認證反例。唯一真正的 exotic target Figure 21 目前只能說：13 個 pointed "
            "rows 原始 distribution 完全相同，2 個 semion rows 要乘整體 -1 才相同，"
            "而且尚無 H2-marked pointwise comparison。"
        ),
        "machine_checked_counts": {
            "retained_evidence_group_count": len(evidence_groups),
            "figure21_pointed_realization_count": 15,
            "figure21_raw_exact_pointed_rows": exact_pointed_rows,
            "figure21_phase_only_pointed_rows": 2,
            "figure21_certified_h2_marked_pointwise_rows": 0,
            "certified_counterexample_count": 0,
            "declared_control_comparison_units_excluding_figure21_distributions": sum(
                group["declared_units"] for group in evidence_groups[1:]
            ),
        },
    }

    finished = datetime.now(UTC)
    result = {
        "schema": "twisted-yetter.stable-no-go-computational-audit.v1",
        "status": "PASS_COMPATIBLE_WITH_EXPLICIT_FIGURE21_NORMALIZATION_DISCREPANCY",
        "mathematical_status": (
            "COMPUTATIONAL_THEOREM_ESTABLISHED_CONDITIONAL_MATHEMATICAL_THEOREM_OPEN"
        ),
        "generator_script": (
            "experiments/scripts/build_twisted_yetter_no_go_computational_audit_v1.py"
        ),
        "reproduce_command": (
            "python experiments/scripts/"
            "build_twisted_yetter_no_go_computational_audit_v1.py"
        ),
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty_before_output_write": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "scope": {
            "only_current_exotic_target": "Akbulut-Yasui 2008 Figure 21 / E3prime",
            "figure21_input_status": "DRAFT_USER_TRANSCRIPTION_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM",
            "figure21_evaluator_scope": "MODULAR_SHORTCUT_ONLY_FOR_TRACTABLE_EXOTIC_RUNS",
            "premodular_exotic_status": "NOT_COMPUTABLE_WITH_CURRENT_BACKEND",
            "comparison_denominator_rule": (
                "Retain completed repo-local MTC presentation comparisons; classify all "
                "top-level comparison-named artifacts in the Akbulut-Yasui, Akbulut, and "
                "Yasui result roots; exclude incomplete, superseded, known-bad, premodular, "
                "and implementation-only artifacts from theorem support."
            ),
        },
        "conditional_mathematical_theorem": conditional_theorem,
        "established_computational_theorem": computational_theorem,
        "evidence_groups": evidence_groups,
        "comparison_file_inventory": comparison_inventory,
        "excluded_or_downgraded": excluded_or_downgraded,
        "source_anchors": [
            {
                "ref": "ref:yetter-hepth-9311082",
                "locator": "Proposition 4; Theorem 8; Proposition 12",
                "use": "coefficient group, twisted-state-sum invariance, and SU(2) surgery/state-sum relation",
            },
            {
                "ref": "ref:ruberman-strle-2210-16260",
                "locator": "Theorem 2.1",
                "use": "one-stable realization of a prescribed intersection-form automorphism",
            },
            {
                "ref": "ref:reutter-2001-02288",
                "locator": "Proposition 3.2; Theorem 3.5; Example 3.6",
                "use": "ordinary semisimple-TQFT connected sums and invertible S2xS2 value",
            },
        ],
        "exact_non_claims": [
            "The conditional mathematical theorem is not yet an established theorem.",
            "The computations do not prove marked connected-sum multiplicativity for the homologically twisted theory.",
            "The computations do not replace expert review of the marked stable-realization argument.",
            "The Figure 21 source transcription is not certified against the printed diagram.",
            "There is no certified H2 coordinate map for Figure 21 versus CP2#9(-CP2).",
            "The two rank-2 Figure 21 semion rows have an unresolved raw global -1 discrepancy.",
            "Distribution equality is weaker than pointwise equality under an H2 marking.",
            "No completed nonpointed twisted MTC Figure 21 comparison is included.",
            "No full premodular Figure 21 invariant is currently computable.",
            "This does not establish a no-go theorem for manifolds with boundary, non-simply-connected manifolds, or other background fields.",
        ],
    }
    result["content_hash"] = _content_hash(result)
    return result


def main() -> None:
    result = build_audit()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    )
    print(OUTPUT)


if __name__ == "__main__":
    main()
