#!/usr/bin/env python3
"""Propagate the Ising terminal blocker to the low-rank catalog route."""

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
ISING_SOURCE_DECISION = OUT_DIR / "ising-formal-map-source-decision-v1.json"
CATALOG_V11 = OUT_DIR / "low-rank-ribbon-realization-catalog-v11.json"
COMPLETION_RUN = OUT_DIR / "low-rank-completion-run-v1.json"
STEP6 = OUT_DIR / "formal-low-rank-scan-plan-generation-attempt-v1.json"
STEP7 = OUT_DIR / "formal-low-rank-control-scan-attempt-v1.json"
STEP8 = OUT_DIR / "formal-low-rank-target-scan-attempt-v1.json"
STEP9 = OUT_DIR / "formal-low-rank-scan-aggregate-attempt-v1.json"


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
        "content_hash": payload["content_hash"],
        "status": payload["status"],
    }


def family_status_counts(catalog: dict[str, Any]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for family in catalog["families"]:
        status = family["terminal_status"]
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def family_record(catalog: dict[str, Any], family_id: str) -> dict[str, Any]:
    for family in catalog["families"]:
        if family["family_id"] == family_id:
            return family
    raise RuntimeError(f"missing family in catalog: {family_id}")


def build_terminal_blocker(*, started_at_utc: str) -> dict[str, Any]:
    ising_decision = load_json(ISING_SOURCE_DECISION)
    catalog = load_json(CATALOG_V11)
    completion_run = load_json(COMPLETION_RUN)
    step6 = load_json(STEP6)
    step7 = load_json(STEP7)
    step8 = load_json(STEP8)
    step9 = load_json(STEP9)

    if ising_decision["status"] != "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER":
        raise RuntimeError("Ising source decision is not terminal-blocked")
    if catalog["status"] not in {
        "PARTIAL_RIBBON_REFINEMENT_PROGRESS",
        "PROCUREMENT_BLOCKED_RIBBON_REFINEMENT_PROGRESS",
        "PROCUREMENT_BLOCKED_RIBBON_REFINEMENT_INCOMPLETE",
    }:
        raise RuntimeError("catalog v11 is not in an expected non-established state")

    ising_family = family_record(catalog, "rank3-ising")
    blocker = ising_decision["terminal_blocker"]
    gate_statuses = {
        "scan_plan_generation": step6["status"],
        "control_scan": step7["status"],
        "target_scan": step8["status"],
        "scan_aggregate": step9["status"],
    }
    classification_blocker_body = {
        "blocker_id": "low-rank-ribbon-classification-terminal-blocked-v2",
        "terminal_status": "LOW_RANK_RIBBON_CLASSIFICATION_TERMINAL_BLOCKED",
        "primary_blocking_family_id": "rank3-ising",
        "primary_blocker_hash": blocker["blocker_hash"],
        "primary_blocker_status": ising_decision["status"],
        "catalog_id": catalog["catalog_id"],
        "catalog_hash": catalog["content_hash"],
        "catalog_established": False,
        "formal_scan_plan_allowed": False,
        "aggregate_allowed": False,
        "scan_complete_claim_allowed": False,
        "no_signal_claim_allowed": False,
        "reason": (
            "rank3-ising is terminal-blocked for current repo-local row-complete "
            "snapshot production because no formal SU(2)_2 eval/coeval map source "
            "or branch-pinned derivation is available."
        ),
    }
    classification_blocker = {
        **classification_blocker_body,
        "classification_blocker_hash": stable_content_hash(classification_blocker_body),
    }

    checks = {
        "ising_terminal_blocker_pinned": blocker["blocker_hash"].startswith("sha256:"),
        "ising_family_present_in_catalog": ising_family["family_id"] == "rank3-ising",
        "catalog_not_established": catalog["status"]
        != "LOW_RANK_RIBBON_CLASSIFICATION_ESTABLISHED",
        "catalog_has_blocked_rows": int(catalog["blocked_row_count"]) > 0,
        "scan_plan_generation_blocked": step6["status"]
        == "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG",
        "control_scan_blocked": step7["status"] == "BLOCKED_NO_FORMAL_SCAN_PLAN",
        "target_scan_blocked": step8["status"]
        == "BLOCKED_NO_FORMAL_SCAN_PLAN_OR_CONTROL_PASS",
        "aggregate_blocked": step9["status"]
        == "BLOCKED_NO_SCAN_CASE_RESULTS_OR_DENOMINATOR_CERTIFICATE",
        "scan_complete_claim_disallowed": classification_blocker["scan_complete_claim_allowed"]
        is False,
        "no_signal_claim_disallowed": classification_blocker["no_signal_claim_allowed"]
        is False,
    }
    if not all(checks.values()):
        raise RuntimeError(f"low-rank terminal blocker checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-ribbon-classification-terminal-blocked.v2",
            "status": "LOW_RANK_RIBBON_CLASSIFICATION_TERMINAL_BLOCKED",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_low_rank_ribbon_classification_terminal_blocked_v2.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_low_rank_ribbon_classification_terminal_blocked_v2.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "terminal_blocker_id": "low-rank-ribbon-classification-terminal-blocked-v2",
            "formal_terminal_result": "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED",
            "classification_blocker": classification_blocker,
            "input_artifacts": {
                "ising_formal_map_source_decision": artifact_record(
                    ISING_SOURCE_DECISION, ising_decision
                ),
                "catalog_v11": artifact_record(CATALOG_V11, catalog),
                "completion_run": artifact_record(COMPLETION_RUN, completion_run),
                "scan_plan_generation_attempt": artifact_record(STEP6, step6),
                "control_scan_attempt": artifact_record(STEP7, step7),
                "target_scan_attempt": artifact_record(STEP8, step8),
                "scan_aggregate_attempt": artifact_record(STEP9, step9),
            },
            "checks": checks,
            "catalog_state": {
                "catalog_id": catalog["catalog_id"],
                "catalog_status": catalog["status"],
                "catalog_established": False,
                "family_status_counts": family_status_counts(catalog),
                "blocked_family_ids": catalog["blocked_family_ids"],
                "primary_blocked_family_id": "rank3-ising",
                "primary_blocker_hash": blocker["blocker_hash"],
            },
            "scan_route_state": {
                "formal_scan_plan_allowed": False,
                "formal_controls_allowed": False,
                "formal_targets_allowed": False,
                "formal_aggregate_allowed": False,
                "final_scan_complete_claim_allowed": False,
                "no_signal_claim_allowed": False,
                "gate_statuses": gate_statuses,
            },
            "terminal_explanation": [
                "The formal low-rank scan route cannot start because the rank 2-5 ribbon catalog is not established.",
                "The catalog cannot be established because rank3-ising has a current repo-local terminal blocker for formal map source support.",
                "This terminal result is a blocker, not a completed scan and not a no-signal theorem.",
            ],
            "allowed_future_unblockers": [
                "add a hash-bound formal SU(2)_2 evaluation/coevaluation derivation or exporter",
                "pin square-root branches for every Ising candidate pivotal dimension",
                "certify Ising q-6j path-basis pairing convention",
                "supersede the Ising terminal blocker with resolved ribbon_realization_snapshot artifacts",
                "then regenerate the low-rank catalog and scan gates",
            ],
            "explicit_non_claims": [
                "This artifact does not claim LOW_RANK_RIBBON_CLASSIFICATION_ESTABLISHED.",
                "This artifact does not claim FORMAL_LOW_RANK_SCAN_COMPLETE.",
                "This artifact does not claim no signal.",
                "This artifact does not claim a TCY no-go theorem.",
                "This artifact does not claim the mathematical Ising row is impossible.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "low-rank-ribbon-classification-terminal-blocked-v2.json": build_terminal_blocker(
            started_at_utc=utc_now()
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
