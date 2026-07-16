#!/usr/bin/env python3
"""Build the terminal package for the current low-rank / Figure 21 work."""

from __future__ import annotations

import argparse
from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
POINTED_BATCH_PATH = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/figure21-pointed-batch-result-v1.json"
)
NONTRIVIAL_RULE_PATH = (
    REPO_ROOT
    / "experiments/results/foundation-v2-safety-substrate/"
    "low-rank-nontrivial-partial-scan-rule-v1.json"
)
TARGET_READINESS_PATH = (
    REPO_ROOT
    / "experiments/results/foundation-v2-safety-substrate/"
    "low-rank-partial-target-readiness-probe-v1.json"
)
GROCERY_ROOT = (
    REPO_ROOT / "experiments/results/foundation-v2-safety-substrate/grocery-procurement"
)
OUTPUT = (
    REPO_ROOT
    / "experiments/results/akbulut-yasui/"
    "current-low-rank-figure21-terminal-package-v1.json"
)

POINTED_FAMILIES = {
    "rank2-cyclic-z2",
    "rank3-cyclic-z3",
    "rank4-pointed-z4",
    "rank4-pointed-z2xz2",
    "rank5-su5-1",
}
NONPOINTED_BLOCKER_PATHS = {
    "rank3-ising": GROCERY_ROOT / "rank3-ising-row-procurement-blocker-v1.json",
    "rank5-su2-4": GROCERY_ROOT / "rank5-su2-4-row-procurement-blocker-v1.json",
    "rank5-psu3-4": GROCERY_ROOT / "rank5-psu3-4-row-procurement-blocker-v1.json",
}


def _git(*args: str) -> str:
    try:
        return subprocess.run(
            ["git", *args],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        if args == ("rev-parse", "HEAD"):
            return os.environ.get("TWISTED_YETTER_GIT_COMMIT", "REMOTE_GIT_UNAVAILABLE")
        if args == ("status", "--porcelain"):
            return os.environ.get("TWISTED_YETTER_GIT_DIRTY", "REMOTE_GIT_UNAVAILABLE")
        raise


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def _sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def _content_hash(payload: Any) -> str:
    data = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(data).hexdigest()}"


def _rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _artifact_ref(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    if payload is None:
        payload = _load_json(path)
    return {
        "path": _rel(path),
        "sha256": _sha256_path(path),
        "content_hash": payload.get("content_hash") or payload.get("content_sha256"),
        "schema": payload.get("schema"),
        "status": payload.get("status"),
    }


def _nonpointed_summary(rule: dict[str, Any]) -> dict[str, Any]:
    rows = rule.get("row_dispositions", [])
    blocked_or_unknown = []
    discarded_trivial = []
    resolved_deferred = []
    all_terminal_rows = []
    for row in rows:
        family_id = row["family_id"]
        disposition = row.get("disposition")
        entry = {
            "family_id": family_id,
            "universal_group": row.get("universal_group"),
            "nontrivial_character_count": row.get("nontrivial_character_count"),
            "catalog_row_status": row.get("catalog_row_status"),
            "disposition": disposition,
            "scan_relevance": row.get("scan_relevance"),
            "row_audit_hash": row.get("row_audit_hash"),
        }
        if disposition == "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN":
            entry["terminal_status"] = (
                "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
            )
            discarded_trivial.append(entry)
        elif family_id in POINTED_FAMILIES:
            entry["terminal_status"] = "HANDLED_BY_POINTED_FIGURE21_BATCH_SCOPE"
        elif disposition == "ADMIT_IF_RIBBON_SNAPSHOT_RESOLVED":
            entry["terminal_status"] = (
                "RESOLVED_NONPOINTED_ROW_DEFERRED_TO_NONPOINTED_WORKER_PREFLIGHT"
            )
            resolved_deferred.append(entry)
        elif family_id in NONPOINTED_BLOCKER_PATHS:
            blocker_path = NONPOINTED_BLOCKER_PATHS[family_id]
            blocker = _load_json(blocker_path)
            blocker_status = blocker.get("status", "PROCUREMENT_BLOCKED")
            entry["terminal_status"] = f"TERMINAL_BLOCKED_NONPOINTED_ROW_{blocker_status}"
            entry["blocker_artifact"] = _artifact_ref(blocker_path, blocker)
            entry["missing_evidence"] = blocker.get("missing_evidence", [])
            blocked_or_unknown.append(entry)
        else:
            entry["terminal_status"] = "TERMINAL_BLOCKED_NONPOINTED_ROW_UNCLASSIFIED"
            blocked_or_unknown.append(entry)
        all_terminal_rows.append(entry)

    expected_blockers = set(NONPOINTED_BLOCKER_PATHS)
    observed_blockers = {
        row["family_id"]
        for row in blocked_or_unknown
        if row["family_id"] in expected_blockers
    }
    missing_expected_blockers = sorted(expected_blockers - observed_blockers)
    return {
        "status": (
            "TERMINAL_BLOCKED_NONPOINTED_ROWS_PRESENT"
            if blocked_or_unknown
            else "RESOLVED_AND_ADDED_TO_NEXT_BATCH"
        ),
        "rule_artifact_status": rule.get("status"),
        "admitted_resolved_nontrivial_family_ids": rule.get(
            "admitted_resolved_nontrivial_family_ids", []
        ),
        "blocked_or_unknown_rows": blocked_or_unknown,
        "discarded_trivial_universal_group_rows": discarded_trivial,
        "resolved_deferred_nonpointed_rows": resolved_deferred,
        "missing_expected_blocker_rows": missing_expected_blockers,
        "all_rows": all_terminal_rows,
        "non_claims": [
            "Trivial universal-group rows are discarded only for nontrivial-character scans.",
            "Unknown universal-group rows are excluded-not-discarded.",
            "Resolved nonpointed rows are not included in the first pointed paid batch unless they pass a separate worker preflight.",
        ],
    }


def _target_readiness_summary(target: dict[str, Any]) -> dict[str, Any]:
    probe = target.get("readiness_probe", {})
    ready = (
        target.get("status") == "TARGET_COMPARISON_READY"
        or (
            probe.get("certified_exotic_input_ready")
            and probe.get("target_manifold_catalog_ready")
            and probe.get("worker_dispatch_allowed")
        )
    )
    if ready:
        status = "TARGET_COMPARISON_READY"
    else:
        status = "TERMINAL_BLOCKED_TARGET_CERTIFICATION_MISSING"
    return {
        "status": status,
        "source_status": target.get("source_status"),
        "readiness_probe": probe,
        "blocked_reason_ids": target.get("blocked_reason_ids", []),
        "next_required_work": target.get("next_required_work", []),
        "fail_closed_checks": target.get("fail_closed_checks", {}),
        "non_claims": target.get("explicit_non_claims", []),
    }


def build_package(
    *,
    pointed_batch_path: Path,
    nontrivial_rule_path: Path,
    target_readiness_path: Path,
) -> dict[str, Any]:
    started = datetime.now(UTC)
    clock = time.perf_counter()
    pointed = _load_json(pointed_batch_path)
    rule = _load_json(nontrivial_rule_path)
    target = _load_json(target_readiness_path)

    nonpointed = _nonpointed_summary(rule)
    target_summary = _target_readiness_summary(target)
    explicit_blockers = []
    if pointed.get("status") != "PASS_POINTED_FIGURE21_BATCH_COMPLETE":
        explicit_blockers.append(
            {
                "line": "figure21_pointed_batch",
                "status": pointed.get("status"),
                "blockers": pointed.get("blockers", []),
            }
        )
    if nonpointed["blocked_or_unknown_rows"]:
        explicit_blockers.append(
            {
                "line": "nonpointed_unresolved_rows",
                "status": nonpointed["status"],
                "blockers": nonpointed["blocked_or_unknown_rows"],
            }
        )
    if target_summary["status"] != "TARGET_COMPARISON_READY":
        explicit_blockers.append(
            {
                "line": "exotic_vs_standard_comparison_readiness",
                "status": target_summary["status"],
                "blockers": target_summary.get("blocked_reason_ids", []),
            }
        )

    consistency_failures = []
    if nonpointed.get("missing_expected_blocker_rows"):
        consistency_failures.append("missing_expected_nonpointed_blocker_rows")
    if pointed.get("status") not in {
        "PASS_POINTED_FIGURE21_BATCH_COMPLETE",
        "TERMINAL_BLOCKED_REMOTE_CAPACITY_NOT_PROVIDED",
        "TERMINAL_BLOCKED_POINTED_BATCH_INCOMPLETE",
    }:
        consistency_failures.append("unknown_pointed_batch_status")
    if target_summary["status"] not in {
        "TARGET_COMPARISON_READY",
        "TERMINAL_BLOCKED_TARGET_CERTIFICATION_MISSING",
    }:
        consistency_failures.append("unknown_target_readiness_status")

    if consistency_failures:
        status = "FAIL_INCONSISTENT_TERMINAL_STATE"
    elif explicit_blockers:
        status = "TERMINAL_WITH_EXPLICIT_BLOCKERS"
    else:
        status = "PASS_ALL_IN_SCOPE_TERMINAL"

    finished = datetime.now(UTC)
    payload = {
        "schema": "twisted-yetter.current-low-rank-figure21-terminal-package.v1",
        "status": status,
        "mathematical_status": "TERMINAL_PACKAGE_NOT_CTL_THEOREM_CLAIM",
        "generator_script": "experiments/scripts/build_current_low_rank_figure21_terminal_package_v1.py",
        "started_at_utc": started.isoformat(),
        "finished_at_utc": finished.isoformat(),
        "elapsed_seconds": time.perf_counter() - clock,
        "repo_root": str(REPO_ROOT),
        "git_commit": _git("rev-parse", "HEAD"),
        "git_dirty": bool(_git("status", "--porcelain")),
        "python_version": platform.python_version(),
        "inputs": {
            "pointed_batch_result": _artifact_ref(pointed_batch_path, pointed),
            "nontrivial_partial_scan_rule": _artifact_ref(nontrivial_rule_path, rule),
            "target_readiness_probe": _artifact_ref(target_readiness_path, target),
        },
        "lines": {
            "figure21_pointed_batch": {
                "status": pointed.get("status"),
                "artifact": _artifact_ref(pointed_batch_path, pointed),
                "row_count": pointed.get("row_count"),
                "complete_row_count": pointed.get("complete_row_count"),
                "blocked_row_count": pointed.get("blocked_row_count"),
                "blockers": pointed.get("blockers", []),
            },
            "nonpointed_unresolved_rows": nonpointed,
            "exotic_vs_standard_comparison_readiness": target_summary,
        },
        "explicit_blockers": explicit_blockers,
        "consistency_failures": consistency_failures,
        "exact_non_claims": [
            "This does not complete all rank 2-5 MTC/ribbon scans.",
            "This does not resolve all nonpointed rows.",
            "This does not prove no signal.",
            "This does not compare Figure 21 to the standard side without H2 certification.",
            "This does not claim Figure 21 is or is not exotic.",
            "This does not make a CTL final theorem claim.",
        ],
    }
    payload["content_hash"] = _content_hash(payload)
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pointed-batch", type=Path, default=POINTED_BATCH_PATH)
    parser.add_argument("--nontrivial-rule", type=Path, default=NONTRIVIAL_RULE_PATH)
    parser.add_argument("--target-readiness", type=Path, default=TARGET_READINESS_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    result = build_package(
        pointed_batch_path=args.pointed_batch,
        nontrivial_rule_path=args.nontrivial_rule,
        target_readiness_path=args.target_readiness,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
