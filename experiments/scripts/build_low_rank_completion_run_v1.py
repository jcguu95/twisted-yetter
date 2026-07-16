#!/usr/bin/env python3
"""Build the terminal end-to-end completion-run artifacts.

This script does not pretend to solve the remaining non-pointed ribbon rows.
It records the end-to-end outcome for the current repository state: the run is
terminal-blocked before scan planning because six non-pointed rows still lack
formal ribbon realization snapshots and bound coherence certificates.
"""

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
    RIBBON_CATALOG_PARTIAL,
    stable_content_hash,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
CATALOG_V10 = OUT_DIR / "low-rank-ribbon-realization-catalog-v10.json"
READINESS_V10 = OUT_DIR / "formal-low-rank-scan-readiness-v10.json"
STEP6_ATTEMPT = OUT_DIR / "formal-low-rank-scan-plan-generation-attempt-v1.json"
STEP7_ATTEMPT = OUT_DIR / "formal-low-rank-control-scan-attempt-v1.json"
STEP8_ATTEMPT = OUT_DIR / "formal-low-rank-target-scan-attempt-v1.json"
STEP9_ATTEMPT = OUT_DIR / "formal-low-rank-scan-aggregate-attempt-v1.json"
RIBBON_SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"

BLOCKED_ROW_ORDER = [
    "rank3-ising",
    "rank3-psu2-5",
    "rank4-psu2-7",
    "rank5-su2-4",
    "rank5-psu2-9",
    "rank5-psu3-4",
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


def content_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    return stable_content_hash(body)


def with_hash(payload: dict[str, Any]) -> dict[str, Any]:
    result = dict(payload)
    result["content_hash"] = content_hash(result)
    return result


def base_meta(schema: str, status: str, *, started_at_utc: str) -> dict[str, Any]:
    return {
        "schema": schema,
        "status": status,
        "generated_at_utc": started_at_utc,
        "generator_script": "experiments/scripts/build_low_rank_completion_run_v1.py",
        "reproduce_command": "python3 experiments/scripts/build_low_rank_completion_run_v1.py --write",
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


def snapshot_inventory() -> dict[str, Any]:
    paths = sorted(RIBBON_SNAPSHOT_DIR.glob("*.json"))
    blocked_hits = {
        family_id: [
            str(path.relative_to(REPO_ROOT))
            for path in paths
            if path.name.startswith(f"{family_id}-")
        ]
        for family_id in BLOCKED_ROW_ORDER
    }
    return {
        "snapshot_dir": str(RIBBON_SNAPSHOT_DIR.relative_to(REPO_ROOT)),
        "total_snapshot_file_count": len(paths),
        "blocked_family_snapshot_paths": blocked_hits,
        "blocked_family_snapshot_count": {
            family_id: len(paths_for_family)
            for family_id, paths_for_family in blocked_hits.items()
        },
    }


def row_resolution_record(row: dict[str, Any], inventory: dict[str, Any]) -> dict[str, Any]:
    family_id = row["family_id"]
    required_checks = [
        "ribbon_realization_snapshot",
        "producer_exact_or_symbolic_coherence_certificate",
        "runtime_consumer_coherence_certificate",
        "ribbon_pivotal_compatibility_certificate",
        "explicit_ribbon_denominator_contribution",
    ]
    if family_id == "rank3-ising":
        attempted_resolution = [
            "inspected v10 blocker row and known SU(2)_2 local backend scope",
            "checked ribbon snapshot inventory for rank3-ising snapshots",
            "rejected reuse of all-sigma local backend as full mixed-label RibbonFusionCategoryV2 evidence",
        ]
    elif family_id in {"rank3-psu2-5", "rank4-psu2-7", "rank5-psu2-9"}:
        attempted_resolution = [
            "inspected v10 blocker row",
            "checked ribbon snapshot inventory for family snapshots",
            "rejected category-name or historical SU(2)_k control output as q6j-backed ribbon realization evidence",
        ]
    elif family_id == "rank5-su2-4":
        attempted_resolution = [
            "inspected v10 blocker row",
            "checked ribbon snapshot inventory for rank5-su2-4 snapshots",
            "rejected collapsing multiple spherical/ribbon branches to one representative",
        ]
    else:
        attempted_resolution = [
            "inspected v10 blocker row",
            "checked ribbon snapshot inventory for rank5-psu3-4 snapshots",
            "rejected summary fusion data without multiplicity-two basis/gauge/pairing certificates",
        ]
    return {
        "family_id": family_id,
        "rank": row["rank"],
        "modular_braided_class_count": row["modular_braided_class_count"],
        "terminal_status": "TERMINAL_BLOCKED_RIBBON_REFINEMENT_INCOMPLETE",
        "formal_admission_allowed": False,
        "attempted_resolution": attempted_resolution,
        "required_evidence": required_checks,
        "blocked_by": row["blocker_ids"],
        "missing_evidence": row["missing_evidence"],
        "snapshot_inventory_count": inventory["blocked_family_snapshot_count"][family_id],
        "snapshot_inventory_paths": inventory["blocked_family_snapshot_paths"][family_id],
        "terminal_condition": (
            "No formal scan route may start until this row has content-addressed "
            "ribbon realization snapshots and all required certificates, or this "
            "terminal blocker is explicitly superseded by a later resolved row artifact."
        ),
    }


def build_run_ledger(
    *,
    started_at_utc: str,
    catalog: dict[str, Any],
    readiness: dict[str, Any],
    step6: dict[str, Any],
    step7: dict[str, Any],
    step8: dict[str, Any],
    step9: dict[str, Any],
    row_records: list[dict[str, Any]],
    inventory: dict[str, Any],
) -> dict[str, Any]:
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-completion-run.v1",
                "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED",
                started_at_utc=started_at_utc,
            ),
            "run_id": "low-rank-completion-run-v1",
            "terminal_result_kind": "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED",
            "input_artifacts": {
                "catalog": artifact_record(CATALOG_V10, catalog),
                "readiness": artifact_record(READINESS_V10, readiness),
                "step6_scan_plan_generation_attempt": artifact_record(STEP6_ATTEMPT, step6),
                "step7_control_scan_attempt": artifact_record(STEP7_ATTEMPT, step7),
                "step8_target_scan_attempt": artifact_record(STEP8_ATTEMPT, step8),
                "step9_aggregate_attempt": artifact_record(STEP9_ATTEMPT, step9),
            },
            "starting_state": {
                "catalog_status": catalog["status"],
                "resolved_row_count": catalog["resolved_row_count"],
                "blocked_row_count": catalog["blocked_row_count"],
                "blocked_family_ids": catalog["blocked_family_ids"],
                "formal_scan_plan_allowed": catalog["formal_scan_plan_allowed"],
                "scan_plan_generation_allowed": readiness["scan_plan_generation_allowed"],
                "formal_scan_plan_produced": step6["formal_scan_plan_produced"],
                "formal_control_results_produced": step7["formal_scan_case_results_produced"],
                "formal_target_scan_results_produced": step8["formal_target_scan_results_produced"],
                "formal_scan_aggregate_produced": step9["formal_scan_aggregate_produced"],
            },
            "snapshot_inventory": inventory,
            "row_resolution_order": BLOCKED_ROW_ORDER,
            "row_resolution_records": row_records,
            "final_claims_admission_state": "PAUSED_FOR_USER_REVIEW",
            "next_allowed_action": (
                "Review terminal-blocked candidate and proposed final CTL wording; "
                "do not admit final classification or scan claims before review."
            ),
            "explicit_non_claims": [
                "This run does not establish the rank 2-5 ribbon classification.",
                "This run does not produce a formal scan plan.",
                "This run does not run formal controls or target scans.",
                "This run does not produce a formal scan aggregate.",
                "This run does not claim no-signal.",
            ],
        }
    )


def build_terminal_blocker(
    *,
    started_at_utc: str,
    run_ledger: dict[str, Any],
    row_records: list[dict[str, Any]],
) -> dict[str, Any]:
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-ribbon-classification-terminal-blocked.v1",
                "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED",
                started_at_utc=started_at_utc,
            ),
            "blocker_id": "low-rank-ribbon-classification-terminal-blocked-v1",
            "run_ledger_hash": run_ledger["content_hash"],
            "terminal_blocked_family_ids": BLOCKED_ROW_ORDER,
            "terminal_blocked_row_count": len(BLOCKED_ROW_ORDER),
            "resolved_row_count_at_stop": run_ledger["starting_state"]["resolved_row_count"],
            "blocked_row_count_at_stop": run_ledger["starting_state"]["blocked_row_count"],
            "formal_scan_route_status": "STOPPED_BEFORE_SCAN_PLAN",
            "blocked_rows": row_records,
            "would_be_unblock_conditions": [
                "All six rows receive content-addressed ribbon_realization_snapshot artifacts.",
                "Each snapshot passes producer exact/symbolic coherence, runtime consumer coherence, and ribbon/pivotal compatibility checks.",
                "The established catalog independently derives ribbon denominators and is accepted by validate_low_rank_ribbon_catalog.",
            ],
            "proposed_ctl_claim_kind": "terminal_blocker_not_scan_complete",
            "explicit_non_claims": [
                "Not LOW_RANK_RIBBON_CLASSIFICATION_ESTABLISHED.",
                "Not FORMAL_LOW_RANK_SCAN_COMPLETE.",
                "Not a no-signal result.",
                "Not a TCY no-go theorem.",
            ],
        }
    )


def build_review_package(
    *,
    started_at_utc: str,
    run_ledger: dict[str, Any],
    terminal_blocker: dict[str, Any],
) -> dict[str, Any]:
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-final-claim-review-package.v1",
                "READY_FOR_USER_REVIEW_BEFORE_FINAL_CLAIMS",
                started_at_utc=started_at_utc,
            ),
            "review_package_id": "low-rank-final-claim-review-package-v1",
            "run_ledger_hash": run_ledger["content_hash"],
            "terminal_blocker_hash": terminal_blocker["content_hash"],
            "review_required_before_admission": True,
            "final_claims_admitted": False,
            "proposed_final_ctl_claims": [
                {
                    "logical_id": "claim:low-rank-ribbon-classification-terminal-blocked",
                    "status": "PROPOSED_NOT_ADMITTED",
                    "claim": (
                        "The current end-to-end low-rank ribbon scan run is terminal-blocked "
                        "before formal scan planning because six non-pointed rows lack "
                        "formal ribbon realization snapshots and bound coherence certificates."
                    ),
                }
            ],
            "claims_explicitly_not_proposed": [
                "LOW_RANK_RIBBON_CLASSIFICATION_ESTABLISHED",
                "FORMAL_LOW_RANK_SCAN_COMPLETE",
                "complete-no-signal-under-frozen-plan",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    catalog = load_json(CATALOG_V10)
    readiness = load_json(READINESS_V10)
    step6 = load_json(STEP6_ATTEMPT)
    step7 = load_json(STEP7_ATTEMPT)
    step8 = load_json(STEP8_ATTEMPT)
    step9 = load_json(STEP9_ATTEMPT)

    validate_low_rank_ribbon_catalog(catalog)
    if catalog["status"] != RIBBON_CATALOG_PARTIAL:
        raise RuntimeError("completion run v1 expects the v10 catalog to remain partial")
    if catalog["blocked_family_ids"] != BLOCKED_ROW_ORDER:
        raise RuntimeError("blocked family order changed; update completion run explicitly")

    rows = {row["family_id"]: row for row in catalog["families"]}
    inventory = snapshot_inventory()
    row_records = [row_resolution_record(rows[family_id], inventory) for family_id in BLOCKED_ROW_ORDER]
    run_ledger = build_run_ledger(
        started_at_utc=started_at_utc,
        catalog=catalog,
        readiness=readiness,
        step6=step6,
        step7=step7,
        step8=step8,
        step9=step9,
        row_records=row_records,
        inventory=inventory,
    )
    terminal_blocker = build_terminal_blocker(
        started_at_utc=started_at_utc,
        run_ledger=run_ledger,
        row_records=row_records,
    )
    review_package = build_review_package(
        started_at_utc=started_at_utc,
        run_ledger=run_ledger,
        terminal_blocker=terminal_blocker,
    )
    return {
        "low-rank-completion-run-v1.json": run_ledger,
        "low-rank-ribbon-classification-terminal-blocked-v1.json": terminal_blocker,
        "low-rank-final-claim-review-package-v1.json": review_package,
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
