#!/usr/bin/env python3
"""Probe the next non-pointed partial-scan row until the executable surface blocks."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import stable_content_hash, validate_formal_evidence  # noqa: E402
from twisted_yetter.link_diagram import LinkDiagram  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
TOY_DIR = REPO_ROOT / "experiments" / "inputs" / "toy-diagrams"
RULE = OUT_DIR / "low-rank-nontrivial-partial-scan-rule-v1.json"
POINTED_BENCHMARK = OUT_DIR / "low-rank-pointed-partial-scan-benchmark-v1.json"

PRODUCT_FAMILY = "rank4-semion-times-fibonacci"
TOY_DIAGRAMS = [
    TOY_DIR / "s4-empty.json",
    TOY_DIR / "cp2-plus-one-framed-unknot.json",
    TOY_DIR / "hopf-link.json",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def file_sha256_id(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def with_hash(payload: dict[str, Any]) -> dict[str, Any]:
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {"path": str(path.relative_to(REPO_ROOT)), "sha256": file_sha256_id(path)}
    if payload is not None:
        record["content_hash"] = payload.get("content_hash", stable_content_hash(payload))
        record["status"] = payload["status"]
    return record


def row_disposition(rule: dict[str, Any], family_id: str) -> dict[str, Any]:
    rows = {item["family_id"]: item for item in rule["row_dispositions"]}
    return rows[family_id]


def product_snapshot_paths() -> list[Path]:
    return sorted(SNAPSHOT_DIR.glob(f"{PRODUCT_FAMILY}-*.json"))


def is_atomic_root_expression(value: str) -> bool:
    if value in {"1", "-1", "i", "-i"}:
        return True
    if value.startswith("zeta") and "*" not in value and "+" not in value and "-" not in value[1:]:
        return True
    return False


def product_surface_observations(snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    twist_expressions = sorted(
        {
            value
            for snapshot in snapshots
            for value in snapshot["category_data"]["twists"].values()
            if not is_atomic_root_expression(value)
        }
    )
    noninteger_dimension_expressions = sorted(
        {
            value
            for snapshot in snapshots
            for value in snapshot["category_data"]["dimensions"].values()
            if value not in {"1", "-1"}
        }
    )
    factorwise_f_r_snapshots = [
        snapshot["realization_id"]
        for snapshot in snapshots
        if snapshot["category_data"]["f_symbols"].get("construction")
        == "factorwise tensor product of pinned factor F-symbols"
        and snapshot["category_data"]["r_symbols"].get("construction")
        == "factorwise tensor product of pinned factor R-symbols"
    ]
    return {
        "snapshot_count": len(snapshots),
        "validated_snapshot_count": len(snapshots),
        "labels_per_snapshot": sorted({len(snapshot["category_data"]["labels"]) for snapshot in snapshots}),
        "product_type_values": sorted({snapshot["category_data"]["product_type"] for snapshot in snapshots}),
        "non_atomic_twist_expressions": twist_expressions,
        "noninteger_dimension_expressions": noninteger_dimension_expressions,
        "factorwise_f_r_construction_snapshot_count": len(factorwise_f_r_snapshots),
    }


def build_probe(*, started_at_utc: str) -> dict[str, Any]:
    t0 = time.perf_counter()
    rule = load_json(RULE)
    pointed = load_json(POINTED_BENCHMARK)
    snapshot_paths = product_snapshot_paths()
    snapshots = [load_json(path) for path in snapshot_paths]
    for snapshot in snapshots:
        validate_formal_evidence(snapshot)
        if snapshot["family_id"] != PRODUCT_FAMILY:
            raise RuntimeError(f"unexpected product snapshot family: {snapshot['family_id']}")
    diagrams = [(path, LinkDiagram.from_json(load_json(path))) for path in TOY_DIAGRAMS]
    disposition = row_disposition(rule, PRODUCT_FAMILY)
    if disposition["disposition"] != "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED":
        raise RuntimeError(f"{PRODUCT_FAMILY} is not admitted by the partial rule")

    observations = product_surface_observations(snapshots)
    blockers = [
        {
            "blocker_id": "product-row-formal-worker-not-implemented",
            "status": "BLOCKS_SCAN_EXECUTION",
            "why_it_blocks": (
                "The next admitted row is non-pointed. The current runnable benchmark "
                "only has a pointed-sector toy evaluator, so using it here would silently "
                "drop non-pointed fusion, dimensions, and factorwise F/R semantics."
            ),
            "required_fix": (
                "Implement a product-category scan worker that either expands the pinned "
                "factorwise F/R data into executable tables or proves and uses a checked "
                "factorwise Deligne-product evaluation path."
            ),
        },
        {
            "blocker_id": "composite-field-expression-runtime-not-implemented",
            "status": "BLOCKS_EXACT_PRODUCT_RUNTIME",
            "why_it_blocks": (
                "The product snapshots contain composite expressions such as "
                "(i)*(zeta10^4) and Fibonacci/Yang-Lee dimension expressions. "
                "The pointed exact-root runner only supports one atomic cyclotomic root "
                "at a time."
            ),
            "required_fix": (
                "Add a fail-closed exact expression layer for the composite field "
                "Q(i, zeta10, u), or a separately certified numeric consumer profile."
            ),
        },
        {
            "blocker_id": "universal-character-projection-for-product-labels-not-bound-to-worker",
            "status": "BLOCKS_FORMAL_CASE_GENERATION",
            "why_it_blocks": (
                "The nontrivial universal character lives on the semion factor of labels "
                "like 1|x. A formal worker must pin this projection explicitly instead "
                "of inferring it from label strings."
            ),
            "required_fix": (
                "Add a character-assignment contract for Deligne product labels and make "
                "worker startup revalidate the pinned projection hash."
            ),
        },
    ]
    elapsed_ms = (time.perf_counter() - t0) * 1000
    checks = {
        "partial_rule_admits_product_family": True,
        "all_product_snapshots_validate_as_formal_category_evidence": len(snapshots) == 8,
        "toy_diagrams_load": len(diagrams) == 3,
        "pointed_benchmark_completed_before_product_probe": pointed["status"]
        == "PASS_POINTED_TOY_BENCHMARK_FAST",
        "no_product_scan_case_result_produced": True,
        "bottleneck_recorded_fail_closed": True,
    }
    if not all(checks.values()):
        raise RuntimeError(f"product surface probe checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-product-partial-scan-surface-probe.v1",
            "status": "BLOCKED_PRODUCT_ROW_EXECUTABLE_SURFACE_NOT_READY",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/probe_low_rank_product_partial_scan_surface_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/probe_low_rank_product_partial_scan_surface_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "claim_level": "runtime-surface-probe-preformal",
            "source_status": "bottleneck-artifact-not-formal-scan-evidence",
            "probe_id": "low-rank-product-partial-scan-surface-probe-v1",
            "after_artifact": artifact_record(POINTED_BENCHMARK, pointed),
            "input_artifacts": {
                "partial_scan_rule": artifact_record(RULE, rule),
                "snapshots": [
                    artifact_record(path, snapshot)
                    for path, snapshot in zip(snapshot_paths, snapshots, strict=True)
                ],
                "diagrams": [artifact_record(path) for path, _ in diagrams],
            },
            "scope": {
                "family_id": PRODUCT_FAMILY,
                "row_disposition": disposition,
                "snapshot_count": len(snapshots),
                "diagram_ids": [diagram.diagram_id for _, diagram in diagrams],
                "formal_partial_scan_plan_used": False,
                "formal_scan_case_result_produced": False,
            },
            "probe_runtime": {
                "elapsed_ms": elapsed_ms,
                "snapshots_validated": len(snapshots),
                "toy_diagrams_loaded": len(diagrams),
            },
            "surface_observations": observations,
            "terminal_bottleneck": {
                "bottleneck_kind": "IMPLEMENTATION_GAP_NOT_CATEGORY_DATA_GAP",
                "blocked_stage": "next_admitted_non_pointed_product_row_execution",
                "blockers": blockers,
            },
            "checks": checks,
            "explicit_non_claims": [
                "This probe artifact is not a partial_scan_plan.",
                "This probe artifact is not a scan_case_result.",
                "This probe artifact is not a scan_aggregate.",
                "This probe artifact does not claim no signal.",
                "This probe artifact does not invalidate the product row snapshots.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-product-partial-scan-surface-probe-v1.json": build_probe(
            started_at_utc=started_at_utc
        )
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    artifacts = build_all()
    if args.write:
        for name, payload in artifacts.items():
            write_json(OUT_DIR / name, payload)
    else:
        print(json.dumps(artifacts, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
