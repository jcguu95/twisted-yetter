#!/usr/bin/env python3
"""Record precise blockers for the remaining non-pointed low-rank rows."""

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
    stable_content_hash,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
V9_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v9.json"
V9_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v9.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"
SU2_2_RF_LOCAL = REPO_ROOT / "experiments" / "results" / "local-piece" / "su2-2-rf-local-backend-v1.json"

REMAINING_NONPOINTED_BLOCKERS: dict[str, dict[str, Any]] = {
    "rank3-ising": {
        "additional_blocker_ids": [
            "rank3-ising:existing-su2-2-rf-local-backend-not-full-ribbon-category",
            "rank3-ising:requires-explicit-ribbon-multiplicity-denominator",
            "rank3-ising:requires-full-mixed-label-pentagon-hexagon-checker",
        ],
        "additional_missing_evidence": [
            "sixteen Ising ribbon realization snapshots if the recorded two spherical structures per braided class survive the audit",
            "full mixed-label F/R/twist/pivotal/evaluation/coevaluation data in one gauge",
            "machine checker for pentagon and both hexagon equations, not only all-sigma braid closures",
            "negative controls for mirror, pivotal sign, sigma basis order, and stale SU(2)_2 local backend reuse",
        ],
        "blocker_note": (
            "The checked-in SU(2)_2 R/F local backend is useful convention evidence "
            "but explicitly scoped to fixed all-sigma braid closures; it is not a "
            "full Ising RibbonFusionCategoryV2 realization."
        ),
        "known_local_backend": "su2-2-rf-local-backend-v1",
    },
    "rank3-psu2-5": {
        "additional_blocker_ids": [
            "rank3-psu2-5:requires-source-backed-q6j-symbols",
            "rank3-psu2-5:requires-galois-branch-and-pivotal-audit",
        ],
        "additional_missing_evidence": [
            "rank-3 adjoint SU(2) level-5 F/R data with field embedding and source locator",
            "exact q6j or equivalent symbolic producer certificate for all fusion channels",
            "independent balancing and ribbon/pivotal compatibility checks for every branch",
        ],
        "blocker_note": "No repo-local full adjoint SU(2)_5 realization or q6j certificate is currently available.",
    },
    "rank4-psu2-7": {
        "additional_blocker_ids": [
            "rank4-psu2-7:requires-source-backed-q6j-symbols",
            "rank4-psu2-7:requires-galois-branch-and-pivotal-audit",
        ],
        "additional_missing_evidence": [
            "rank-4 adjoint SU(2) level-7 F/R data with field embedding and source locator",
            "exact q6j or equivalent symbolic producer certificate for all fusion channels",
            "independent balancing and ribbon/pivotal compatibility checks for every branch",
        ],
        "blocker_note": "No repo-local full adjoint SU(2)_7 realization or q6j certificate is currently available.",
    },
    "rank5-su2-4": {
        "additional_blocker_ids": [
            "rank5-su2-4:rep-s3-extension-explicit-branching-needed",
            "rank5-su2-4:two-spherical-structures-per-braided-class-must-not-collapse",
        ],
        "additional_missing_evidence": [
            "explicit Rep(S3)^omega extension data for each gamma branch",
            "two spherical/ribbon refinements per braided class, if confirmed by the audit, recorded as separate snapshot hashes",
            "producer and consumer certificates that distinguish pivotal sign changes from braided equivalence",
        ],
        "blocker_note": "The row records multiple spherical structures; choosing one representative would undercount ribbon realizations.",
    },
    "rank5-psu2-9": {
        "additional_blocker_ids": [
            "rank5-psu2-9:requires-source-backed-q6j-symbols",
            "rank5-psu2-9:requires-galois-branch-and-pivotal-audit",
        ],
        "additional_missing_evidence": [
            "rank-5 adjoint SU(2) level-9 F/R data with field embedding and source locator",
            "exact q6j or equivalent symbolic producer certificate for all fusion channels",
            "independent balancing and ribbon/pivotal compatibility checks for every branch",
        ],
        "blocker_note": "No repo-local full adjoint SU(2)_9 realization or q6j certificate is currently available.",
    },
    "rank5-psu3-4": {
        "additional_blocker_ids": [
            "rank5-psu3-4:requires-source-backed-psu3-fr-symbols",
            "rank5-psu3-4:multiplicity-two-fusion-spaces-require-explicit-basis-gauge",
        ],
        "additional_missing_evidence": [
            "rank-5 PSU(3)_4 F/R data with source locator and field embedding",
            "explicit multiplicity-two fusion-space basis and pairing convention",
            "producer and runtime coherence certificates that check basis order and gauge changes fail closed",
        ],
        "blocker_note": "This row has fusion multiplicity max 2, so summary modular data is especially unsafe as computation input.",
    },
}


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
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v10.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v10.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def merge_unique(existing: list[str], additions: list[str]) -> list[str]:
    result = list(existing)
    for item in additions:
        if item not in result:
            result.append(item)
    return result


def local_backend_summary() -> dict[str, Any]:
    payload = load_json(SU2_2_RF_LOCAL)
    exact = payload["exact_output"]
    return {
        "artifact_id": "su2-2-rf-local-backend-v1",
        "path": str(SU2_2_RF_LOCAL.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(SU2_2_RF_LOCAL),
        "status": payload["status"],
        "exact_status": exact["status"],
        "claim_level": exact["claim_level"],
        "scope": exact["scope"],
        "not_scope": exact["not_scope"],
        "unsafe_as_rank3_ising_full_category_snapshot": True,
        "safe_use_in_this_ledger": "convention cross-check and blocker evidence only",
    }


def build_catalog_v10(*, started_at_utc: str) -> dict[str, Any]:
    previous = load_json(V9_CATALOG)
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        blocker = REMAINING_NONPOINTED_BLOCKERS.get(row["family_id"])
        if blocker is not None:
            new_row["blocker_ids"] = merge_unique(
                list(new_row["blocker_ids"]),
                blocker["additional_blocker_ids"],
            )
            new_row["missing_evidence"] = merge_unique(
                list(new_row["missing_evidence"]),
                blocker["additional_missing_evidence"],
            )
            new_row["formal_admission_allowed"] = False
            new_row["terminal_status"] = "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
            new_row["nonpointed_blocker_note"] = blocker["blocker_note"]
            if "known_local_backend" in blocker:
                new_row["known_local_backend"] = blocker["known_local_backend"]
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
        "catalog_id": "low-rank-ribbon-realization-catalog-v10",
        "previous_catalog": {
            "path": str(V9_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V9_CATALOG),
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
        "resolved_snapshot_paths": previous["resolved_snapshot_paths"],
        "nonpointed_blocker_ledger": {
            "status": "NONPOINTED_ROWS_BLOCK_FORMAL_SCAN_PLAN",
            "local_backend_scope_audit": local_backend_summary(),
            "remaining_blocked_family_ids": sorted(REMAINING_NONPOINTED_BLOCKERS),
            "step_6_scan_plan_generator_status": "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG",
            "step_7_controls_status": "BLOCKED_NO_FORMAL_SCAN_PLAN",
        },
        "families": rows,
        "explicit_non_claims": [
            "This partial catalog does not establish the complete rank 2-5 ribbon classification.",
            "This partial catalog does not authorize scan-plan generation.",
            "The existing SU(2)_2 local R/F backend is not a full Ising category realization.",
            "No non-pointed row is resolved by this blocker refinement.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v10(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v10",
            "BLOCKED_NONPOINTED_RIBBON_ROWS_REMAIN",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v10",
        "previous_readiness": {
            "path": str(V9_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V9_READINESS),
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
            "six-nonpointed-family-rows-still-blocked",
            "ising-full-category-realization-not-materialized",
            "psu-su-q6j-and-basis-gauge-data-not-materialized",
            "ribbon-denominator-not-final",
        ],
        "blocked_step_status": {
            "implementation_order_step_4_materialize_catalog": "BLOCKED_SIX_NONPOINTED_ROWS_REMAIN",
            "implementation_order_step_5_category_coherence_certificates": "BLOCKED_FOR_NONPOINTED_ROWS",
            "implementation_order_step_6_scan_plan_generator": "NOT_STARTED_BLOCKED_BY_PARTIAL_CATALOG",
            "implementation_order_step_7_controls": "NOT_STARTED_BLOCKED_BY_NO_FORMAL_SCAN_PLAN",
        },
        "explicit_non_claims": [
            "No formal scan plan exists.",
            "No control scan was run under formal scan semantics.",
            "No scan case result exists.",
            "No complete-no-signal aggregate exists.",
        ],
    }


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    catalog = build_catalog_v10(started_at_utc=started_at_utc)
    readiness = build_readiness_v10(started_at_utc=started_at_utc, catalog=catalog)
    return {
        "low-rank-ribbon-realization-catalog-v10.json": catalog,
        "formal-low-rank-scan-readiness-v10.json": readiness,
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
