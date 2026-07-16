#!/usr/bin/env python3
"""Materialize the Step 2 input-attempt ledger for blocked low-rank rows.

Step 2 is where formal category inputs must be produced.  This pass records
what is actually available in the repository today, without promoting partial
or principal-branch data to complete ribbon-row evidence.
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
    stable_content_hash,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
CATALOG_V10 = OUT_DIR / "low-rank-ribbon-realization-catalog-v10.json"
TERMINAL_BLOCKER = OUT_DIR / "low-rank-ribbon-classification-terminal-blocked-v1.json"
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
SU2_2_LOCAL_BACKEND = REPO_ROOT / "experiments" / "results" / "local-piece" / "su2-2-rf-local-backend-v1.json"
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
        "generator_script": "experiments/scripts/build_low_rank_step2_input_materialization_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_step2_input_materialization_v1.py --write"
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


def snapshot_paths_for(family_id: str) -> list[str]:
    return [
        str(path.relative_to(REPO_ROOT))
        for path in sorted(RIBBON_SNAPSHOT_DIR.glob(f"{family_id}-*.json"))
    ]


def input_attempt_for(row: dict[str, Any]) -> dict[str, Any]:
    family_id = row["family_id"]
    base = {
        "family_id": family_id,
        "rank": row["rank"],
        "modular_braided_class_count": row["modular_braided_class_count"],
        "row_terminal_status_before_step2": row["terminal_status"],
        "formal_row_resolution_after_step2": "NOT_RESOLVED",
        "formal_admission_allowed": False,
        "existing_snapshot_paths": snapshot_paths_for(family_id),
        "required_outputs": [
            "content-addressed ribbon_realization_snapshot artifacts for every branch",
            "producer exact/symbolic coherence certificates bound to category_data_hash",
            "runtime consumer coherence certificates bound to the same category_data_hash",
            "ribbon/pivotal compatibility certificates",
            "independently derived ribbon denominator contribution",
        ],
    }
    if family_id == "rank3-ising":
        return {
            **base,
            "materialization_status": "PARTIAL_LOCAL_BRANCH_DATA_AVAILABLE_NOT_ROW_RESOLVED",
            "available_inputs": [
                artifact_record(SU2_2_LOCAL_BACKEND, load_json(SU2_2_LOCAL_BACKEND)),
                artifact_record(SU2K_EVALUATOR),
            ],
            "available_input_scope": [
                "SU(2)_2 local R/F all-sigma backend exists as convention evidence only",
                "SU(2)_k fusion-braid evaluator exposes principal-branch q6j/F/R machinery",
            ],
            "why_not_resolved": [
                "no rank3-ising ribbon realization snapshot files exist",
                "no complete branch enumeration for the 8 braided classes exists",
                "possible 16 ribbon realizations are not materialized or denominator-certified",
                "local all-sigma backend is not full mixed-label RibbonFusionCategoryV2 input",
            ],
        }
    if family_id in {"rank3-psu2-5", "rank4-psu2-7", "rank5-psu2-9"}:
        level_by_family = {
            "rank3-psu2-5": 5,
            "rank4-psu2-7": 7,
            "rank5-psu2-9": 9,
        }
        return {
            **base,
            "materialization_status": "PRINCIPAL_SU2K_Q6J_BACKEND_AVAILABLE_NOT_ROW_RESOLVED",
            "available_inputs": [artifact_record(SU2K_EVALUATOR)],
            "available_input_scope": [
                f"SU(2)_{level_by_family[family_id]} principal-branch q6j/F/R machinery is available through the evaluator code",
                "the evaluator is a braid-closure backend, not a row-complete ribbon realization catalog",
            ],
            "why_not_resolved": [
                f"no {family_id} ribbon realization snapshot files exist",
                "Galois/branch and pivotal audits are not materialized",
                "no per-branch category_data_hash or coherence certificate exists",
                "family row denominator cannot be replaced by a principal-branch backend",
            ],
        }
    if family_id == "rank5-su2-4":
        return {
            **base,
            "materialization_status": "PRINCIPAL_SU2K_BACKEND_AVAILABLE_EXTENSION_BRANCHES_NOT_RESOLVED",
            "available_inputs": [artifact_record(SU2K_EVALUATOR)],
            "available_input_scope": [
                "SU(2)_4 principal-branch fusion-braid machinery is available through the evaluator code"
            ],
            "why_not_resolved": [
                "no rank5-su2-4 ribbon realization snapshot files exist",
                "Rep(S3)^omega extension/gamma branches are not materialized",
                "multiple spherical/ribbon refinements are not separated by snapshot hashes",
                "principal SU(2)_4 backend cannot stand in for all row branches",
            ],
        }
    return {
        **base,
        "materialization_status": "NO_REPO_LOCAL_PSU3_FR_INPUT_AVAILABLE",
        "available_inputs": [],
        "available_input_scope": [],
        "why_not_resolved": [
            "no rank5-psu3-4 ribbon realization snapshot files exist",
            "no PSU(3)_4 F/R source-backed payload exists in the repository",
            "multiplicity-two fusion-space basis/gauge/pairing convention is absent",
            "no producer/runtime coherence certificate exists",
        ],
    }


def build_step2_materialization(*, started_at_utc: str) -> dict[str, Any]:
    catalog = load_json(CATALOG_V10)
    terminal_blocker = load_json(TERMINAL_BLOCKER)
    validate_low_rank_ribbon_catalog(catalog)
    if catalog["blocked_family_ids"] != BLOCKED_ROW_ORDER:
        raise RuntimeError("blocked row order changed; update step2 materialization explicitly")
    rows = {row["family_id"]: row for row in catalog["families"]}
    attempts = [input_attempt_for(rows[family_id]) for family_id in BLOCKED_ROW_ORDER]
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-step2-input-materialization.v1",
                "STEP2_INPUT_MATERIALIZATION_COMPLETE_TERMINAL_BLOCKED",
                started_at_utc=started_at_utc,
            ),
            "materialization_id": "low-rank-step2-input-materialization-v1",
            "step": "implementation_order_step_2_resolve_the_6_blocked_rows",
            "terminal_result_kind": "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED",
            "input_artifacts": {
                "catalog": artifact_record(CATALOG_V10, catalog),
                "terminal_blocker": artifact_record(TERMINAL_BLOCKER, terminal_blocker),
            },
            "blocked_family_ids": BLOCKED_ROW_ORDER,
            "attempts": attempts,
            "resolved_row_count_after_step2": 0,
            "terminal_blocked_row_count_after_step2": len(BLOCKED_ROW_ORDER),
            "formal_scan_plan_allowed_after_step2": False,
            "step2_completion_semantics": (
                "Step 2 is complete for the current run as a materialization pass: "
                "each blocked row was inspected for repo-local inputs, and none has "
                "enough formal snapshots/certificates to become resolved."
            ),
            "explicit_non_claims": [
                "No blocked row is resolved by this Step 2 pass.",
                "No principal-branch SU(2)_k backend is promoted to a row-complete ribbon catalog.",
                "No all-sigma Ising backend is promoted to full mixed-label category evidence.",
                "No formal scan plan is authorized.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-step2-input-materialization-v1.json": build_step2_materialization(
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
