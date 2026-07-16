#!/usr/bin/env python3
"""Audit universal grading groups for every v11 low-rank family row."""

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
CATALOG_V11 = OUT_DIR / "low-rank-ribbon-realization-catalog-v11.json"
BLOCKED_AUDIT = OUT_DIR / "low-rank-universal-grading-audit-v1.json"

ROW_ORDER = [
    "rank2-cyclic-z2",
    "rank2-fibonacci-yang-lee",
    "rank3-cyclic-z3",
    "rank3-ising",
    "rank3-psu2-5",
    "rank4-pointed-z4",
    "rank4-pointed-z2xz2",
    "rank4-semion-times-fibonacci",
    "rank4-fibxfib",
    "rank4-psu2-7",
    "rank5-su2-4",
    "rank5-psu2-9",
    "rank5-su5-1",
    "rank5-psu3-4",
]

FULL_CATALOG_POLICIES = {
    "rank2-cyclic-z2": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL",
        "universal_group": "Z2",
        "method": "pointed metric group universal grading equals underlying group",
        "nontrivial_character_count": 1,
        "scan_relevance": "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST",
        "nontrivial_character_scan_disposition": "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED",
    },
    "rank2-fibonacci-yang-lee": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_TRIVIAL",
        "universal_group": "trivial",
        "method": "adjoint rank-2 Fibonacci/Yang-Lee fusion rule audit",
        "nontrivial_character_count": 0,
        "scan_relevance": "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS",
        "nontrivial_character_scan_disposition": (
            "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
        ),
    },
    "rank3-cyclic-z3": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL",
        "universal_group": "Z3",
        "method": "pointed metric group universal grading equals underlying group",
        "nontrivial_character_count": 2,
        "scan_relevance": "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST",
        "nontrivial_character_scan_disposition": "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED",
    },
    "rank4-pointed-z4": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL",
        "universal_group": "Z4",
        "method": "pointed metric group universal grading equals underlying group",
        "nontrivial_character_count": 3,
        "scan_relevance": "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST",
        "nontrivial_character_scan_disposition": "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED",
    },
    "rank4-pointed-z2xz2": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL",
        "universal_group": "Z2xZ2",
        "method": "pointed metric group universal grading equals underlying group",
        "nontrivial_character_count": 3,
        "scan_relevance": "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST",
        "nontrivial_character_scan_disposition": "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED",
    },
    "rank4-semion-times-fibonacci": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL",
        "universal_group": "Z2",
        "method": "Deligne product universal grading from semion Z2 factor times Fibonacci/Yang-Lee trivial factor",
        "nontrivial_character_count": 1,
        "scan_relevance": "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST",
        "nontrivial_character_scan_disposition": "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED",
    },
    "rank4-fibxfib": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_TRIVIAL",
        "universal_group": "trivial",
        "method": "Deligne product of two trivial Fibonacci/Yang-Lee universal gradings",
        "nontrivial_character_count": 0,
        "scan_relevance": "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS",
        "nontrivial_character_scan_disposition": (
            "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
        ),
    },
    "rank5-su5-1": {
        "status": "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL",
        "universal_group": "Z5",
        "method": "pointed metric group universal grading equals underlying group",
        "nontrivial_character_count": 4,
        "scan_relevance": "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST",
        "nontrivial_character_scan_disposition": "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED",
    },
}

BLOCKED_ROW_SCAN_DISPOSITIONS = {
    "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST": "EXCLUDED_BLOCKED_RIBBON_REALIZATION",
    "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS": (
        "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
    ),
    "UNKNOWN_UNTIL_FUSION_TABLE_AUDIT": "EXCLUDED_NOT_DISCARDED",
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
        "generator_script": "experiments/scripts/build_low_rank_full_catalog_universal_grading_audit_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_full_catalog_universal_grading_audit_v1.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
    }
    if payload is not None:
        record["content_hash"] = payload.get("content_hash", stable_content_hash(payload))
        record["status"] = payload["status"]
    return record


def blocked_audit_rows() -> dict[str, dict[str, Any]]:
    blocked = load_json(BLOCKED_AUDIT)
    return {row["family_id"]: row for row in blocked["row_audits"]}


def row_audit(
    row: dict[str, Any],
    *,
    blocked_rows: dict[str, dict[str, Any]],
    started_at_utc: str,
) -> dict[str, Any]:
    family_id = row["family_id"]
    if family_id in blocked_rows:
        source = blocked_rows[family_id]
        return with_hash(
            {
                **base_meta(
                    "twisted-yetter.low-rank-full-catalog-row-universal-grading-audit.v1",
                    source["status"],
                    started_at_utc=started_at_utc,
                ),
                "family_id": family_id,
                "family": row["family"],
                "rank": row["rank"],
                "catalog_row_status": row["terminal_status"],
                "modular_braided_class_count": row["modular_braided_class_count"],
                "audit_source": "blocked-row-universal-grading-audit-v1",
                "source_row_audit_hash": source["content_hash"],
                "universal_group": (
                    source["computed"]["universal_group"]
                    if source.get("computed") is not None
                    else "UNKNOWN"
                ),
                "nontrivial_character_count": (
                    source["computed"]["nontrivial_character_count"]
                    if source.get("computed") is not None
                    else None
                ),
                "scan_relevance": source["scan_relevance"],
                "nontrivial_character_scan_disposition": BLOCKED_ROW_SCAN_DISPOSITIONS[
                    source["scan_relevance"]
                ],
                "formal_ribbon_realization_status": row["terminal_status"],
                "explicit_non_claims": [
                    "This row audit does not change the ribbon realization status.",
                    "This row audit does not authorize scan-plan generation.",
                ],
            }
        )

    policy = FULL_CATALOG_POLICIES[family_id]
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-full-catalog-row-universal-grading-audit.v1",
                policy["status"],
                started_at_utc=started_at_utc,
            ),
            "family_id": family_id,
            "family": row["family"],
            "rank": row["rank"],
            "catalog_row_status": row["terminal_status"],
            "modular_braided_class_count": row["modular_braided_class_count"],
            "audit_source": "catalog-family-structure-and-existing-resolved-snapshots",
            "derivation_method": policy["method"],
            "universal_group": policy["universal_group"],
            "nontrivial_character_count": policy["nontrivial_character_count"],
            "scan_relevance": policy["scan_relevance"],
            "nontrivial_character_scan_disposition": policy[
                "nontrivial_character_scan_disposition"
            ],
            "formal_ribbon_realization_status": row["terminal_status"],
            "resolved_snapshot_hashes": row.get("ribbon_realization_snapshot_hashes", []),
            "explicit_non_claims": [
                "This row audit records universal grading only.",
                "This row audit does not authorize scan-plan generation.",
            ],
        }
    )


def build_audit(*, started_at_utc: str) -> dict[str, Any]:
    catalog = load_json(CATALOG_V11)
    blocked = load_json(BLOCKED_AUDIT)
    rows = {row["family_id"]: row for row in catalog["families"]}
    if list(rows) != ROW_ORDER:
        raise RuntimeError("catalog row order changed; update full-catalog audit")
    blocked_rows = blocked_audit_rows()
    row_audits = [
        row_audit(rows[family_id], blocked_rows=blocked_rows, started_at_utc=started_at_utc)
        for family_id in ROW_ORDER
    ]
    nontrivial = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST"
    ]
    trivial = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS"
    ]
    unknown = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "UNKNOWN_UNTIL_FUSION_TABLE_AUDIT"
    ]
    blocked_nontrivial = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST"
        and row["catalog_row_status"] != "RESOLVED_RIBBON_REALIZATION"
    ]
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-full-catalog-universal-grading-audit.v1",
                "FULL_CATALOG_UNIVERSAL_GRADING_AUDIT_COMPLETE_WITH_ONE_UNKNOWN",
                started_at_utc=started_at_utc,
            ),
            "audit_id": "low-rank-full-catalog-universal-grading-audit-v1",
            "input_artifacts": {
                "catalog_v11": artifact_record(CATALOG_V11, catalog),
                "blocked_row_universal_grading_audit": artifact_record(BLOCKED_AUDIT, blocked),
            },
            "row_order": ROW_ORDER,
            "row_audits": row_audits,
            "formal_nontrivial_universal_group_family_ids": nontrivial,
            "formal_trivial_universal_group_family_ids": trivial,
            "unknown_universal_group_family_ids": unknown,
            "blocked_nontrivial_growth_target_family_ids": blocked_nontrivial,
            "resolved_nontrivial_family_ids": [
                row["family_id"]
                for row in row_audits
                if row["scan_relevance"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST"
                and row["catalog_row_status"] == "RESOLVED_RIBBON_REALIZATION"
            ],
            "trivial_rows_are_ignored_for_nontrivial_universal_character_scan": trivial,
            "discarded_trivial_universal_group_family_ids": trivial,
            "explicit_next_growth_targets": blocked_nontrivial,
            "explicit_unknowns_not_ignored": unknown,
            "nontrivial_universal_character_scan_dispositions": {
                "admit_resolved_nontrivial_family_ids": [
                    row["family_id"]
                    for row in row_audits
                    if row["nontrivial_character_scan_disposition"]
                    == "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED"
                    and row["catalog_row_status"] == "RESOLVED_RIBBON_REALIZATION"
                ],
                "exclude_blocked_nontrivial_family_ids": blocked_nontrivial,
                "discard_trivial_family_ids": trivial,
                "exclude_unknown_not_discarded_family_ids": unknown,
            },
            "scan_plan_status": "NOT_AUTHORIZED_BY_THIS_AUDIT",
            "classification_status": "NOT_ESTABLISHED_BY_THIS_AUDIT",
            "explicit_non_claims": [
                "This audit does not establish the low-rank ribbon classification.",
                "This audit does not produce new ribbon_realization_snapshot artifacts.",
                "This audit does not authorize scan-plan generation.",
                "Trivial rows are ignored only for nontrivial universal-character twists.",
                "Unknown rows are not treated as trivial.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-full-catalog-universal-grading-audit-v1.json": build_audit(
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
