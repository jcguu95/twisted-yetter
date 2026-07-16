#!/usr/bin/env python3
"""Materialize the nontrivial universal-character partial scan admission rule."""

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
    stable_content_hash,
    validate_formal_admission_policy,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
POLICY_V1 = OUT_DIR / "formal-admission-policy-v1.json"
CATALOG_V11 = OUT_DIR / "low-rank-ribbon-realization-catalog-v11.json"
UNIVERSAL_AUDIT = OUT_DIR / "low-rank-full-catalog-universal-grading-audit-v1.json"


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


def artifact_record(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
        "content_hash": payload.get("content_hash", stable_content_hash(payload)),
        "status": payload["status"],
    }


def row_map(audit: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["family_id"]: row for row in audit["row_audits"]}


def build_rule(*, started_at_utc: str) -> dict[str, Any]:
    policy = load_json(POLICY_V1)
    catalog = load_json(CATALOG_V11)
    audit = load_json(UNIVERSAL_AUDIT)
    validate_formal_admission_policy(policy)

    dispositions = audit["nontrivial_universal_character_scan_dispositions"]
    admitted = dispositions["admit_resolved_nontrivial_family_ids"]
    excluded = dispositions["exclude_blocked_nontrivial_family_ids"]
    discarded = dispositions["discard_trivial_family_ids"]
    unknown = dispositions["exclude_unknown_not_discarded_family_ids"]

    rows = row_map(audit)
    row_dispositions = []
    for family_id in audit["row_order"]:
        row = rows[family_id]
        row_dispositions.append(
            {
                "family_id": family_id,
                "catalog_row_status": row["catalog_row_status"],
                "universal_group": row["universal_group"],
                "nontrivial_character_count": row["nontrivial_character_count"],
                "scan_relevance": row["scan_relevance"],
                "disposition": row["nontrivial_character_scan_disposition"],
                "row_audit_hash": row["content_hash"],
            }
        )

    checks = {
        "policy_allows_partial_scan_plan_kind": "partial_scan_plan"
        in policy["formal_evidence_kind_allowlist"],
        "policy_allows_partial_scan_aggregate_kind": "partial_scan_aggregate"
        in policy["formal_evidence_kind_allowlist"],
        "admitted_subset_nonempty": bool(admitted),
        "blocked_nontrivial_rows_explicit": excluded == ["rank3-ising", "rank5-su2-4"],
        "trivial_rows_marked_discarded": discarded
        == [
            "rank2-fibonacci-yang-lee",
            "rank3-psu2-5",
            "rank4-fibxfib",
            "rank4-psu2-7",
            "rank5-psu2-9",
        ],
        "unknown_rows_not_discarded": unknown == ["rank5-psu3-4"],
        "full_scan_claim_forbidden": True,
        "no_scan_plan_emitted_by_this_rule": True,
    }
    if not all(checks.values()):
        raise RuntimeError(f"partial scan rule checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-nontrivial-partial-scan-rule.v1",
            "status": "NONTRIVIAL_PARTIAL_SCAN_RULE_ACTIVE_NO_SCAN_RUN",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_low_rank_nontrivial_partial_scan_rule_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_low_rank_nontrivial_partial_scan_rule_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "rule_id": "low-rank-nontrivial-partial-scan-rule-v1",
            "input_artifacts": {
                "formal_admission_policy": artifact_record(POLICY_V1, policy),
                "catalog_v11": artifact_record(CATALOG_V11, catalog),
                "universal_grading_audit": artifact_record(UNIVERSAL_AUDIT, audit),
            },
            "scan_scope": "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET",
            "formal_partial_scan_plan_allowed_if_validator_accepts": True,
            "formal_partial_scan_plan_emitted": False,
            "formal_partial_scan_aggregate_allowed_if_cases_complete": True,
            "formal_full_scan_plan_allowed": False,
            "formal_full_scan_complete_claim_allowed": False,
            "full_rank_2_5_ribbon_classification_claim_allowed": False,
            "admitted_resolved_nontrivial_family_ids": admitted,
            "excluded_blocked_nontrivial_family_ids": excluded,
            "discarded_trivial_universal_group_family_ids": discarded,
            "unknown_universal_group_family_ids": unknown,
            "trivial_rows_disposition": (
                "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
            ),
            "unknown_rows_disposition": "EXCLUDED_NOT_DISCARDED",
            "row_dispositions": row_dispositions,
            "checks": checks,
            "explicit_non_claims": [
                "This rule artifact is not a scan plan.",
                "This rule artifact runs no controls and no target scans.",
                "Partial scan completion under this rule is not FORMAL_LOW_RANK_SCAN_COMPLETE.",
                "Discarded trivial rows are discarded only for nontrivial universal-character twists.",
                "Unknown universal-group rows are excluded from the partial subset but not treated as trivial.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-nontrivial-partial-scan-rule-v1.json": build_rule(
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
