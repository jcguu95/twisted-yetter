#!/usr/bin/env python3
"""Summarize nontrivial low-rank category-growth status after strict validation."""

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

from twisted_yetter.foundation_safety import stable_content_hash  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
GROWN_DIR = OUT_DIR / "grown-category-data"
CERT_DIR = OUT_DIR / "grown-category-certificates"
BRANCH_DIR = OUT_DIR / "grown-category-branches"
FULL_AUDIT = OUT_DIR / "low-rank-full-catalog-universal-grading-audit-v1.json"

GROWTH_TARGETS = {
    "rank3-ising": {
        "export": GROWN_DIR / "rank3-ising-principal-su2-level2-category-data-export-v1.json",
        "certificate": CERT_DIR / "rank3-ising-principal-su2-level2-strict-export-validation-v1.json",
        "galois_branch_export": BRANCH_DIR / "rank3-ising-su2-level2-galois-branch-candidates-v1.json",
        "galois_branch_certificate": BRANCH_DIR / "rank3-ising-su2-level2-galois-branch-candidates-validation-v1.json",
        "status": "GALOIS_BRANCH_CANDIDATES_STRICTLY_VALIDATED_NOT_ROW_COMPLETE",
        "remaining_growth": [
            "identify which candidate Galois branches correspond to the eight braided Ising classes",
            "materialize mirror/reverse equivalence conventions explicitly",
            "decide and materialize ribbon/pivotal lifts for each braided branch",
            "produce row-complete producer/runtime/ribbon certificates for every lift",
            "derive the row ribbon denominator without copying the braided denominator",
        ],
    },
    "rank5-su2-4": {
        "export": GROWN_DIR / "rank5-su2-4-principal-su2-level4-category-data-export-v1.json",
        "certificate": CERT_DIR / "rank5-su2-4-principal-su2-level4-strict-export-validation-v1.json",
        "galois_branch_export": BRANCH_DIR / "rank5-su2-4-su2-level4-galois-branch-candidates-v1.json",
        "galois_branch_certificate": BRANCH_DIR / "rank5-su2-4-su2-level4-galois-branch-candidates-validation-v1.json",
        "status": "GALOIS_BRANCH_CANDIDATES_STRICTLY_VALIDATED_EXTENSION_BRANCHES_MISSING",
        "remaining_growth": [
            "identify which SU(2)_4 Galois candidates correspond to the four braided family classes",
            "materialize Rep(S3)^omega / gamma extension branches",
            "separate the spherical/ribbon refinements by snapshot hash",
            "produce row-complete producer/runtime/ribbon certificates for every branch",
            "derive the row ribbon denominator without copying the braided denominator",
        ],
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


def with_hash(payload: dict[str, Any]) -> dict[str, Any]:
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def base_meta(schema: str, status: str, *, started_at_utc: str) -> dict[str, Any]:
    return {
        "schema": schema,
        "status": status,
        "generated_at_utc": started_at_utc,
        "generator_script": "experiments/scripts/build_low_rank_nontrivial_growth_status_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_nontrivial_growth_status_v1.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def artifact_record(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
        "content_hash": payload["content_hash"],
        "status": payload["status"],
    }


def target_record(family_id: str) -> dict[str, Any]:
    spec = GROWTH_TARGETS[family_id]
    export = load_json(spec["export"])
    cert = load_json(spec["certificate"])
    branch_export = load_json(spec["galois_branch_export"])
    branch_cert = load_json(spec["galois_branch_certificate"])
    if cert["validated_export"]["content_hash"] != export["content_hash"]:
        raise RuntimeError(f"{family_id} validation certificate is not bound to export")
    if cert["status"] != "PASS_STRICT_PRINCIPAL_EXPORT_REVALIDATION":
        raise RuntimeError(f"{family_id} strict validation did not pass")
    if branch_cert["validated_export"]["content_hash"] != branch_export["content_hash"]:
        raise RuntimeError(f"{family_id} Galois branch certificate is not bound to export")
    if branch_cert["status"] != "PASS_STRICT_GALOIS_BRANCH_CANDIDATE_REVALIDATION":
        raise RuntimeError(f"{family_id} Galois branch validation did not pass")
    return {
        "family_id": family_id,
        "growth_status": spec["status"],
        "principal_export": artifact_record(spec["export"], export),
        "strict_validation_certificate": artifact_record(spec["certificate"], cert),
        "galois_branch_candidate_export": artifact_record(
            spec["galois_branch_export"], branch_export
        ),
        "galois_branch_candidate_certificate": artifact_record(
            spec["galois_branch_certificate"], branch_cert
        ),
        "principal_checked_entry_counts": cert["checked_entry_counts"],
        "galois_checked_entry_counts": branch_cert["checked_entry_counts"],
        "galois_candidate_branch_count": branch_export["candidate_branch_count"],
        "galois_powers": branch_export["galois_powers"],
        "formal_row_resolution_allowed": False,
        "formal_ribbon_realization_snapshot_produced": False,
        "remaining_growth": spec["remaining_growth"],
    }


def build_status(*, started_at_utc: str) -> dict[str, Any]:
    full_audit = load_json(FULL_AUDIT)
    targets = [target_record(family_id) for family_id in full_audit["explicit_next_growth_targets"]]
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-nontrivial-growth-status.v1",
                "GALOIS_BRANCH_CANDIDATES_STRICTLY_VALIDATED_REMAINING_BRANCHES_BLOCKED",
                started_at_utc=started_at_utc,
            ),
            "growth_status_id": "low-rank-nontrivial-growth-status-v1",
            "input_artifacts": {
                "full_catalog_universal_grading_audit": artifact_record(FULL_AUDIT, full_audit),
            },
            "growth_target_family_ids": full_audit["explicit_next_growth_targets"],
            "growth_targets": targets,
            "trivial_rows_not_grown_for_nontrivial_universal_character_scan": (
                full_audit["trivial_rows_are_ignored_for_nontrivial_universal_character_scan"]
            ),
            "unknown_rows_not_ignored": full_audit["explicit_unknowns_not_ignored"],
            "row_complete_growth_target_family_ids": [],
            "still_blocked_growth_target_family_ids": full_audit["explicit_next_growth_targets"],
            "scan_plan_status": "NOT_AUTHORIZED_BY_THIS_STATUS",
            "classification_status": "NOT_ESTABLISHED_BY_THIS_STATUS",
            "explicit_non_claims": [
                "Strict principal and Galois candidate validation is not row-complete ribbon realization evidence.",
                "No growth target is resolved as a full family row by this status artifact.",
                "No formal scan plan is authorized.",
                "Galois candidate branch payloads do not establish pivotal/ribbon lift completeness.",
                "Trivial rows are ignored only for nontrivial universal-character twist growth.",
                "Unknown rows are not treated as trivial.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "low-rank-nontrivial-growth-status-v1.json": build_status(started_at_utc=utc_now())
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
