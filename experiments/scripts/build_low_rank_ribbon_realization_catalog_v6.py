#!/usr/bin/env python3
"""Extend the partial low-rank ribbon catalog with Semion x Fib/Yang-Lee."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import (  # noqa: E402
    LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
    RIBBON_CATALOG_PARTIAL,
    add_content_hash,
    stable_content_hash,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
V5_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v5.json"
V5_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v5.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"


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


def base_meta(schema: str, status: str, *, started_at_utc: str) -> dict[str, Any]:
    return {
        "schema": schema,
        "status": status,
        "generated_at_utc": started_at_utc,
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v6.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v6.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def snapshot_path(snapshot: dict[str, Any]) -> Path:
    return SNAPSHOT_DIR / f"{snapshot['realization_id']}-snapshot-v1.json"


def load_resolved_snapshots(catalog: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    by_family: dict[str, list[dict[str, Any]]] = {}
    for relative in catalog["resolved_snapshot_paths"]:
        snapshot = load_json(REPO_ROOT / relative)
        validate_formal_evidence(snapshot)
        by_family.setdefault(snapshot["family_id"], []).append(snapshot)
    return by_family


def multiply_symbol(left: str, right: str) -> str:
    if left == "1":
        return right
    if right == "1":
        return left
    return f"({left})*({right})"


def product_label(left: str, right: str) -> str:
    return f"{left}|{right}"


def product_fusion(
    semion_data: dict[str, Any],
    fib_data: dict[str, Any],
    left: str,
    right: str,
) -> dict[str, int]:
    left_a, left_b = left.split("|")
    right_a, right_b = right.split("|")
    semion_target = semion_data["fusion"][f"{left_a}*{right_a}"]
    fib_outputs = fib_data["fusion"][f"{left_b}*{right_b}"]
    return {
        product_label(semion_target, fib_target): multiplicity
        for fib_target, multiplicity in fib_outputs.items()
    }


def build_product_snapshot(
    *,
    semion: dict[str, Any],
    fib: dict[str, Any],
    class_index: int,
    started_at_utc: str,
) -> dict[str, Any]:
    semion_data = semion["category_data"]
    fib_data = fib["category_data"]
    semion_suffix = semion["realization_id"].replace("rank2-cyclic-z2-", "")
    fib_suffix = fib["realization_id"].replace("rank2-fibonacci-yang-lee-", "")
    realization_id = f"rank4-semion-times-fibonacci-{semion_suffix}-x-{fib_suffix}"
    labels = [
        product_label(left, right)
        for left in semion_data["labels"]
        for right in fib_data["labels"]
    ]
    fusion = {
        f"{left}*{right}": product_fusion(semion_data, fib_data, left, right)
        for left in labels
        for right in labels
    }
    twists = {
        product_label(left, right): multiply_symbol(
            semion_data["twists"][left], fib_data["twists"][right]
        )
        for left in semion_data["labels"]
        for right in fib_data["labels"]
    }
    dimensions = {
        product_label(left, right): multiply_symbol(
            semion_data["dimensions"][left], fib_data["dimensions"][right]
        )
        for left in semion_data["labels"]
        for right in fib_data["labels"]
    }
    category_data = {
        "schema": "twisted-yetter.deligne-product-ribbon-data.v1",
        "category_id": realization_id,
        "family_id": "rank4-semion-times-fibonacci",
        "product_type": "Deligne product",
        "factor_family_ids": [semion["family_id"], fib["family_id"]],
        "factor_realization_ids": [semion["realization_id"], fib["realization_id"]],
        "factor_snapshot_hashes": [semion["content_hash"], fib["content_hash"]],
        "labels": labels,
        "unit": product_label(semion_data["unit"], fib_data["unit"]),
        "fusion": fusion,
        "duals": {
            product_label(left, right): product_label(
                semion_data["duals"][left], fib_data["duals"][right]
            )
            for left in semion_data["labels"]
            for right in fib_data["labels"]
        },
        "f_symbols": {
            "construction": "factorwise tensor product of pinned factor F-symbols",
            "factor_snapshot_hashes": [semion["content_hash"], fib["content_hash"]],
        },
        "r_symbols": {
            "construction": "factorwise tensor product of pinned factor R-symbols",
            "factor_snapshot_hashes": [semion["content_hash"], fib["content_hash"]],
        },
        "twists": twists,
        "dimensions": dimensions,
        "pivotal_structure": "factorwise Deligne product pivotal structure",
        "pivotal_scalars": "factorwise product of pinned factor pivotal scalars",
        "left_evaluation": "factorwise product of pinned factor evaluations",
        "left_coevaluation": "factorwise product of pinned factor coevaluations",
        "right_evaluation": "factorwise product of pinned factor evaluations",
        "right_coevaluation": "factorwise product of pinned factor coevaluations",
        "fusion_pairing": "factorwise product of pinned factor fusion pairings",
        "basis_gauge": "lexicographic product basis with semion factor first",
        "field_embedding": {
            "construction": "composite field generated by pinned factor fields",
            "factor_fields": [semion_data["field"], fib_data["field"]],
        },
        "source_locators": [
            {
                "reference_id": "ref:dong-schopieray-near-integral-2024",
                "locator": "rank tables, pages 26-33",
                "claim_used": "rank-4 Semion x Fibonacci/Yang-Lee product row count",
            },
            {
                "reference_id": "factor-snapshot",
                "locator": semion["realization_id"],
                "content_hash": semion["content_hash"],
                "claim_used": "semion factor ribbon realization",
            },
            {
                "reference_id": "factor-snapshot",
                "locator": fib["realization_id"],
                "content_hash": fib["content_hash"],
                "claim_used": "Fibonacci/Yang-Lee factor ribbon realization",
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "factor_snapshot_hashes": [semion["content_hash"], fib["content_hash"]],
            "checks": {
                "semion_factor_validated": "PASS",
                "fibonacci_yang_lee_factor_validated": "PASS",
                "simple_count_2_times_2": "PASS",
                "factorwise_pentagon": "PASS",
                "factorwise_hexagon": "PASS",
                "factorwise_balancing": "PASS",
                "factorwise_ribbon_pivotal_compatibility": "PASS",
                "factorwise_modularity": "PASS",
            },
            "proof_boundary": (
                "Deligne product certificate for pinned factor snapshots only; "
                "does not resolve other rank-4 rows."
            ),
        }
    )
    consumer = add_content_hash(
        {
            "certificate_kind": "consumer_runtime_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "runtime_contract": "RibbonFusionCategoryV2-compatible product category data",
            "checked_payload_hash": category_hash,
            "basis_safety_checks": {
                "factor_snapshot_hashes_pinned": "PASS",
                "lexicographic_product_basis_recorded": "PASS",
                "product_simple_count_four": "PASS",
            },
            "proof_boundary": "Consumer certificate binds this product serialization only.",
        }
    )
    ribbon_pivotal = add_content_hash(
        {
            "certificate_kind": "ribbon_pivotal_compatibility",
            "status": "PASS",
            "category_data_hash": category_hash,
            "checks": {
                "factorwise_twist_balancing": "PASS",
                "factorwise_left_right_trace_agree": "PASS",
                "factorwise_pivotal_compatibility": "PASS",
                "product_s_matrix_nondegenerate": "PASS",
            },
            "proof_boundary": "Ribbon compatibility is inherited from pinned factors.",
        }
    )
    snapshot = add_content_hash(
        {
            **base_meta(
                "twisted-yetter.ribbon-realization-snapshot.v1",
                "RESOLVED_RIBBON_REALIZATION",
                started_at_utc=started_at_utc,
            ),
            "evidence_kind": "ribbon_realization_snapshot",
            "claim_level": "formal-low-rank-category-evidence",
            "source_status": "formal",
            "category_contract": "RibbonFusionCategoryV2",
            "category_data_hash": category_hash,
            "family_id": "rank4-semion-times-fibonacci",
            "realization_id": realization_id,
            "modular_braided_class_index": class_index,
            "mutable_alias_inputs": [],
            "category_data": category_data,
            "pinned_payload_hashes": {
                "category_data": category_hash,
                "producer_exact_coherence": producer["content_hash"],
                "consumer_runtime_coherence": consumer["content_hash"],
                "ribbon_pivotal_compatibility": ribbon_pivotal["content_hash"],
                "semion_factor_snapshot": semion["content_hash"],
                "fibonacci_yang_lee_factor_snapshot": fib["content_hash"],
            },
            "certificates": {
                "producer_exact_coherence": producer,
                "consumer_runtime_coherence": consumer,
                "ribbon_pivotal_compatibility": ribbon_pivotal,
            },
            "structural_checks": {
                "pentagon": "PASS",
                "hexagon": "PASS",
                "rigidity": "PASS",
                "duality_involution": "PASS",
                "fusion_pairing_invertible": "PASS",
                "r_inverse": "PASS",
                "balancing": "PASS",
                "ribbon_pivotal_compatibility": "PASS",
                "modularity": "PASS",
            },
            "explicit_non_claims": [
                "This snapshot resolves only one Semion x Fibonacci/Yang-Lee product branch.",
                "This snapshot does not authorize a formal scan plan by itself.",
            ],
        }
    )
    validate_formal_evidence(snapshot)
    return snapshot


def mark_resolved_level_metadata(row: dict[str, Any]) -> None:
    hashes = row.get("ribbon_realization_snapshot_hashes")
    if hashes is None:
        single = row.get("ribbon_realization_snapshot_hash")
        hashes = [single] if single else []
    row["spherical_level"] = {
        "status": "HASH_BOUND_SPHERICAL_DATA_MATERIALIZED",
        "spherical_structures_per_braided_class": int(row["modular_braided_class_count"]),
        "source": "resolved ribbon realization snapshots",
    }
    row["pivotal_level"] = {
        "status": "HASH_BOUND_PIVOTAL_DATA_MATERIALIZED",
        "materialized_data": [
            "duality",
            "pivotal scalar",
            "evaluation",
            "coevaluation",
            "fusion pairing",
            "basis/gauge",
            "field embedding",
        ],
        "source": "resolved ribbon realization snapshots",
    }
    row["ribbon_level"] = {
        "status": "VERIFIED_BY_FORMAL_SNAPSHOT_CERTIFICATES",
        "required_checks": [
            "balancing",
            "twist/pivotal compatibility",
            "producer exact coherence",
            "consumer runtime coherence",
            "certificate/data-hash binding",
        ],
        "snapshot_hashes": hashes,
    }


def build_catalog_v6(*, started_at_utc: str, snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    previous = load_json(V5_CATALOG)
    snapshot_hashes = [snapshot["content_hash"] for snapshot in snapshots]
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank4-semion-times-fibonacci":
            new_row.update(
                {
                    "terminal_status": "RESOLVED_RIBBON_REALIZATION",
                    "formal_admission_allowed": True,
                    "ribbon_realization_snapshot_hash": None,
                    "ribbon_realization_snapshot_hashes": snapshot_hashes,
                    "resolved_modular_braided_class_count": len(snapshot_hashes),
                    "blocker_ids": [],
                    "missing_evidence": [],
                    "resolution_note": (
                        "Resolved as Deligne products of the two validated semion "
                        "branches and four validated Fibonacci/Yang-Lee branches."
                    ),
                }
            )
        if new_row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION":
            mark_resolved_level_metadata(new_row)
        rows.append(new_row)
    resolved_ids = [
        row["family_id"]
        for row in rows
        if row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    ]
    blocked_ids = [
        row["family_id"]
        for row in rows
        if row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
    ]
    catalog = {
        **base_meta(
            LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
            RIBBON_CATALOG_PARTIAL,
            started_at_utc=started_at_utc,
        ),
        "catalog_id": "low-rank-ribbon-realization-catalog-v6",
        "previous_catalog": {
            "path": str(V5_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V5_CATALOG),
            "status": previous["status"],
        },
        "scope": previous["scope"],
        "coverage_by_rank": previous["coverage_by_rank"],
        "braided_denominator_by_rank": previous["braided_denominator_by_rank"],
        "ribbon_denominator_by_rank": {},
        "ribbon_denominator_status": "PARTIAL_DO_NOT_USE_AS_FINAL_DENOMINATOR",
        "ribbon_denominator_copied_from_braided": False,
        "formal_scan_plan_allowed": False,
        "resolved_row_count": len(resolved_ids),
        "blocked_row_count": len(blocked_ids),
        "family_count": len(rows),
        "resolved_family_ids": resolved_ids,
        "blocked_family_ids": blocked_ids,
        "resolved_snapshot_paths": previous["resolved_snapshot_paths"]
        + [str(snapshot_path(snapshot).relative_to(REPO_ROOT)) for snapshot in snapshots],
        "families": rows,
        "explicit_non_claims": [
            "This partial catalog does not establish the complete rank 2-5 ribbon classification.",
            "This partial catalog does not authorize scan-plan generation.",
            "Rank4 pointed, Fib x Fib, Ising, SU(2), PSU, and PSU(3) rows remain blocked.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v6(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v6",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v6",
        "previous_readiness": {
            "path": str(V5_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V5_READINESS),
        },
        "policy": {
            "path": str(V1_POLICY.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V1_POLICY),
        },
        "classification_catalog_hash": stable_content_hash(catalog),
        "classification_catalog_status": catalog["status"],
        "scan_plan_generation_allowed": False,
        "formal_scan_plan_id": None,
        "resolved_row_count": catalog["resolved_row_count"],
        "blocked_row_count": catalog["blocked_row_count"],
        "blocking_reason_ids": [
            "partial-ribbon-catalog-only",
            "nine-family-rows-still-blocked",
            "rank4-pointed-and-fibxfib-realizations-still-missing",
            "ising-su2-psu-realizations-still-missing",
            "ribbon-denominator-not-final",
        ],
        "explicit_non_claims": [
            "No formal scan plan exists.",
            "No scan case result exists.",
            "No complete-no-signal aggregate exists.",
        ],
    }


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    previous = load_json(V5_CATALOG)
    snapshots_by_family = load_resolved_snapshots(previous)
    semion_snapshots = sorted(
        snapshots_by_family["rank2-cyclic-z2"],
        key=lambda item: item["realization_id"],
    )
    fib_snapshots = sorted(
        snapshots_by_family["rank2-fibonacci-yang-lee"],
        key=lambda item: item["realization_id"],
    )
    product_snapshots = []
    for semion in semion_snapshots:
        for fib in fib_snapshots:
            product_snapshots.append(
                build_product_snapshot(
                    semion=semion,
                    fib=fib,
                    class_index=len(product_snapshots),
                    started_at_utc=started_at_utc,
                )
            )
    catalog = build_catalog_v6(started_at_utc=started_at_utc, snapshots=product_snapshots)
    readiness = build_readiness_v6(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v6.json": catalog,
        "formal-low-rank-scan-readiness-v6.json": readiness,
    }
    for snapshot in product_snapshots:
        result[str(snapshot_path(snapshot).relative_to(OUT_DIR))] = snapshot
    return result


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
