#!/usr/bin/env python3
"""Sweep resolved pointed modular snapshots on Figure 21 and standard E(1)."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import UTC, datetime
from itertools import product
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import time
from typing import Any

from experiments.sage.pointed_premodular_categories import (
    SnapshotPointedModularCategory,
)
from experiments.sage.ribbon_graph_evaluator import (
    PointedVacuumProjectorEvaluator,
    RibbonGraphEvaluator,
)
from experiments.scripts.special_dotted_morphism import (
    build_vacuum_coupon_graph,
    compile_projected_morphism,
    stable_json_hash,
)


REPO_ROOT = Path(__file__).resolve().parents[2]
SNAPSHOT_ROOT = (
    REPO_ROOT
    / "experiments/results/foundation-v2-safety-substrate/"
    "ribbon-realization-snapshots"
)
FIGURE21_INPUT = (
    REPO_ROOT
    / "experiments/inputs/akbulut-yasui/figure21-right-morse-draft-v1.json"
)
STANDARD_INPUT = (
    REPO_ROOT / "experiments/inputs/standard/e1-cp2-sum-9barcp2-morse-v1.json"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-vs-standard-pointed-modular-sweep-v1.json"
)
EXPECTED_FIGURE21_INPUT_SHA256 = (
    "b6f8459547a7cec415eb6c70acb89a40c37ab4cabd364330206685d8e579cbc5"
)
EXPECTED_FIGURE21_GRAPH_HASH = (
    "sha256:f66f1ef64661c432c389b6c1db726de605055ea0cabe74005fa649ebbd32a26c"
)
TOLERANCE = 1e-10


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_path(path: Path) -> str:
    return _sha256_bytes(path.read_bytes())


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _complex_key(value: complex) -> str:
    value = complex(value)
    real = 0.0 if abs(value.real) < TOLERANCE else round(value.real, 12)
    imag = 0.0 if abs(value.imag) < TOLERANCE else round(value.imag, 12)
    return f"{real:+.12g}{imag:+.12g}i"


def _complex_from_key(key: str) -> complex:
    text = key.removesuffix("i")
    split_at = max(text.rfind("+", 1), text.rfind("-", 1))
    return complex(float(text[:split_at]), float(text[split_at:]))


def _load_figure21() -> dict[str, Any]:
    source_bytes = FIGURE21_INPUT.read_bytes()
    input_sha256 = _sha256_bytes(source_bytes)
    if input_sha256 != EXPECTED_FIGURE21_INPUT_SHA256:
        raise ValueError("Figure 21 input hash changed")
    source = json.loads(source_bytes)
    forms = tuple(source["forms"])
    ir = compile_projected_morphism(
        forms,
        component_by_piece=source["component_by_piece"],
        special_components=source["special_components"],
        component_order=source["component_order"],
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    if graph["graph_hash"] != EXPECTED_FIGURE21_GRAPH_HASH:
        raise ValueError("Figure 21 coupon graph hash changed")
    ordinary = tuple(
        component for component in source["component_order"] if component != "red"
    )
    return {
        "source": source,
        "forms": forms,
        "ir": ir,
        "graph": graph,
        "ordinary": ordinary,
        "input_sha256": input_sha256,
    }


def _load_standard() -> dict[str, Any]:
    source = json.loads(STANDARD_INPUT.read_text())
    forms = tuple(source["forms"])
    component_order = tuple(f"U{index}" for index in range(source["component_count"]))
    component_by_piece = {component: component for component in component_order}
    framings = {
        component: int(source["framings"][index])
        for index, component in enumerate(component_order)
    }
    return {
        "source": source,
        "forms": forms,
        "component_order": component_order,
        "component_by_piece": component_by_piece,
        "framings": framings,
    }


def _pointed_snapshots() -> list[dict[str, Any]]:
    snapshots = []
    for path in sorted(SNAPSHOT_ROOT.glob("*-snapshot-v1.json")):
        snapshot = json.loads(path.read_text())
        data = snapshot.get("category_data", {})
        dimensions = data.get("dimensions", {})
        if (
            snapshot.get("status") == "RESOLVED_RIBBON_REALIZATION"
            and dimensions
            and set(dimensions.values()) == {"1"}
        ):
            snapshots.append(
                {
                    "path": path,
                    "payload": snapshot,
                    "rank": len(data["labels"]),
                    "realization_id": snapshot["realization_id"],
                }
            )
    return sorted(
        snapshots,
        key=lambda item: (item["rank"], item["payload"]["family_id"], item["realization_id"]),
    )


def _labels_from_id(labels: tuple[Any, ...], sector_id: int, width: int) -> tuple[Any, ...]:
    radix = len(labels)
    digits = [labels[0]] * width
    value = sector_id
    for index in range(width - 1, -1, -1):
        value, digit = divmod(value, radix)
        digits[index] = labels[digit]
    return tuple(digits)


def _distribution(records: list[complex]) -> dict[str, int]:
    return dict(sorted(Counter(_complex_key(value) for value in records).items()))


def _is_full_status(status: str) -> bool:
    return status in {"FULL", "FULL_CLOSED_FORM_DISTRIBUTION"}


def _run_figure21(
    category: SnapshotPointedModularCategory,
    context: dict[str, Any],
    *,
    max_sectors: int,
    modular_cross_check_sectors: int,
) -> dict[str, Any]:
    total = len(category.labels) ** len(context["ordinary"])
    count = min(total, max_sectors)
    pointed = PointedVacuumProjectorEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    modular = RibbonGraphEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    values = []
    status_counter: Counter[str] = Counter()
    rank_counter: Counter[str] = Counter()
    max_error = 0.0
    first_mismatch = None
    started = time.perf_counter()
    for sector_id in range(count):
        labels_tuple = _labels_from_id(category.labels, sector_id, len(context["ordinary"]))
        labels = dict(zip(context["ordinary"], labels_tuple, strict=True))
        pointed_value, pointed_stats = pointed.fixed_label_value(context["graph"], labels)
        if sector_id < modular_cross_check_sectors:
            modular_value, _modular_stats = modular.fixed_label_value(context["graph"], labels)
            error = abs(modular_value - pointed_value)
            if error > max_error:
                max_error = error
            if error > TOLERANCE:
                first_mismatch = {
                    "sector_id": sector_id,
                    "abs_error": error,
                    "modular_value": _complex_key(modular_value),
                    "pointed_value": _complex_key(pointed_value),
                    "reason": "MODULAR_POINTED_MISMATCH_FAIL_CLOSED",
                }
                break
        values.append(pointed_value)
        status_counter[pointed_stats["status"]] += 1
        rank_counter[str(pointed_stats["projector_rank"])] += 1
    return {
        "status": (
            "FAILED_MODULAR_CROSS_CHECK"
            if first_mismatch is not None
            else ("FULL" if len(values) == total else "PREFIX_BUDGETED")
        ),
        "sector_count": len(values),
        "full_sector_count": total,
        "elapsed_seconds": time.perf_counter() - started,
        "backend": "POINTED_GRAPH_PROJECTOR",
        "modular_cross_check": (
            {
                "enabled": True,
                "sector_count": min(count, modular_cross_check_sectors),
                "max_abs_error": max_error,
                "status": "FAIL" if first_mismatch is not None else "PASS",
                "first_mismatch": first_mismatch,
            }
        ),
        "pointed_status_distribution": dict(sorted(status_counter.items())),
        "projector_rank_distribution": dict(sorted(rank_counter.items())),
        "value_distribution": _distribution(values),
        "records_sha256": _sha256_bytes(
            json.dumps(
                [_complex_key(value) for value in values],
                sort_keys=True,
                separators=(",", ":"),
            ).encode()
        ),
    }


def _run_standard(
    category: SnapshotPointedModularCategory,
    context: dict[str, Any],
    *,
    max_sectors: int,
) -> dict[str, Any]:
    total = len(category.labels) ** len(context["component_order"])
    started = time.perf_counter()
    distribution: Counter[str] = Counter({"+1+0i": 1})
    for component in context["component_order"]:
        local = Counter(
            _complex_key(complex(category.twist(label)) ** context["framings"][component])
            for label in category.labels
        )
        next_distribution: Counter[str] = Counter()
        for left_key, left_count in distribution.items():
            left = _complex_from_key(left_key)
            for right_key, right_count in local.items():
                right = _complex_from_key(right_key)
                next_distribution[_complex_key(left * right)] += left_count * right_count
        distribution = next_distribution
    return {
        "status": "FULL_CLOSED_FORM_DISTRIBUTION",
        "sector_count": total,
        "full_sector_count": total,
        "elapsed_seconds": time.perf_counter() - started,
        "backend": "SPLIT_UNLINK_CLOSED_FORM_FIXED_LABELS",
        "value_distribution": dict(sorted(distribution.items())),
        "records_sha256": _sha256_bytes(
            json.dumps(
                dict(sorted(distribution.items())),
                sort_keys=True,
                separators=(",", ":"),
            ).encode()
        ),
    }


def generate(
    *,
    max_figure21_sectors: int,
    max_standard_sectors: int,
    modular_cross_check_sectors: int,
    max_rank: int | None,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    figure21 = _load_figure21()
    standard = _load_standard()
    rows = []
    for item in _pointed_snapshots():
        if max_rank is not None and item["rank"] > max_rank:
            continue
        snapshot = item["payload"]
        category = SnapshotPointedModularCategory(snapshot)
        row_started = time.perf_counter()
        figure21_result = _run_figure21(
            category,
            figure21,
            max_sectors=max_figure21_sectors,
            modular_cross_check_sectors=modular_cross_check_sectors,
        )
        standard_result = _run_standard(
            category,
            standard,
            max_sectors=max_standard_sectors,
        )
        rows.append(
            {
                "realization_id": item["realization_id"],
                "family_id": snapshot["family_id"],
                "rank": item["rank"],
                "snapshot_path": str(item["path"].relative_to(REPO_ROOT)),
                "snapshot_content_hash": snapshot["content_hash"],
                "category_data_hash": snapshot["category_data_hash"],
                "figure21_right": figure21_result,
                "standard_cp2_9cpbar": standard_result,
                "elapsed_seconds": time.perf_counter() - row_started,
            }
        )
    full_rows = [
        row
        for row in rows
        if _is_full_status(row["figure21_right"]["status"])
        and _is_full_status(row["standard_cp2_9cpbar"]["status"])
    ]
    status = (
        "PASS_POINTED_MODULAR_FIGURE21_STANDARD_SWEEP_ALL_FULL"
        if len(full_rows) == len(rows)
        else "PASS_POINTED_MODULAR_FIGURE21_STANDARD_SWEEP_WITH_BUDGETED_PREFIXES"
    )
    finished = datetime.now(UTC)
    return {
        "schema": "twisted-yetter.figure21-standard-pointed-modular-sweep.v1",
        "status": status,
        "mathematical_status": "EVALUATOR_SWEEP_NOT_EXOTIC_COMPARISON_CLAIM",
        "generator_script": (
            "experiments/scripts/run_figure21_standard_pointed_modular_sweep_v1.py"
        ),
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "figure21": {
                "path": str(FIGURE21_INPUT.relative_to(REPO_ROOT)),
                "sha256": figure21["input_sha256"],
                "projected_ir_hash": stable_json_hash(figure21["ir"]),
                "coupon_graph_hash": figure21["graph"]["graph_hash"],
                "ordinary_component_order": list(figure21["ordinary"]),
                "source_status": figure21["source"]["status"],
            },
            "standard": {
                "path": str(STANDARD_INPUT.relative_to(REPO_ROOT)),
                "sha256": _sha256_path(STANDARD_INPUT),
                "manifold": standard["source"]["manifold"],
                "signature": standard["source"]["signature"],
                "component_count": standard["source"]["component_count"],
                "framings": standard["source"]["framings"],
            },
        },
        "budgets": {
            "max_figure21_sectors_per_category": max_figure21_sectors,
            "max_standard_sectors_per_category": max_standard_sectors,
            "modular_cross_check_sectors_per_category": modular_cross_check_sectors,
            "max_rank": max_rank,
        },
        "row_count": len(rows),
        "full_row_count": len(full_rows),
        "budgeted_prefix_row_count": len(rows) - len(full_rows),
        "rows": rows,
        "claim_boundary": (
            "This evaluates fixed-label pointed modular sectors on Figure 21 "
            "right and the split CP2#9CPbar standard presentation. It does not "
            "identify the H2 character-coordinate map between the two sides."
        ),
        "non_claims": [
            "This is not a formal low-rank scan aggregate.",
            "This is not an exotic-vs-standard separation or no-separation theorem.",
            "Budgeted prefix rows are not complete category evaluations.",
            "Nonpointed resolved rows are not included in this pointed sweep.",
            "The Figure 21 transcription remains draft unless separately certified against the paper."
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--max-figure21-sectors", type=int, default=2_048)
    parser.add_argument("--max-standard-sectors", type=int, default=200_000)
    parser.add_argument("--modular-cross-check-sectors", type=int, default=16)
    parser.add_argument("--max-rank", type=int, default=None)
    args = parser.parse_args()
    result = generate(
        max_figure21_sectors=args.max_figure21_sectors,
        max_standard_sectors=args.max_standard_sectors,
        modular_cross_check_sectors=args.modular_cross_check_sectors,
        max_rank=args.max_rank,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
