#!/usr/bin/env python3
"""Build the fail-closed artifact for formal scan step 8.

Step 8 runs admitted target/exotic scan cases only after a formal scan plan and
formal controls exist.  With steps 6 and 7 blocked, the correct output is a
hash-bound blocked target-scan attempt.
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
STEP6_ATTEMPT = OUT_DIR / "formal-low-rank-scan-plan-generation-attempt-v1.json"
STEP7_ATTEMPT = OUT_DIR / "formal-low-rank-control-scan-attempt-v1.json"
STEP6_7_GATE = OUT_DIR / "formal-low-rank-step6-7-gate-v1.json"


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
        "generator_script": "experiments/scripts/build_formal_low_rank_scan_step8_gate_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_formal_low_rank_scan_step8_gate_v1.py --write"
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


def build_target_scan_attempt(*, started_at_utc: str) -> dict[str, Any]:
    catalog = load_json(CATALOG_V10)
    step6 = load_json(STEP6_ATTEMPT)
    step7 = load_json(STEP7_ATTEMPT)
    step6_7 = load_json(STEP6_7_GATE)
    validate_low_rank_ribbon_catalog(catalog)

    if step6.get("formal_scan_plan_produced") is not False:
        raise RuntimeError("step 8 gate expects step 6 to be blocked")
    if step7.get("formal_scan_case_results_produced") is not False:
        raise RuntimeError("step 8 gate expects step 7 controls to be blocked")

    return with_hash(
        {
            **base_meta(
                "twisted-yetter.formal-low-rank-target-scan-attempt.v1",
                "BLOCKED_NO_FORMAL_SCAN_PLAN_OR_CONTROL_PASS",
                started_at_utc=started_at_utc,
            ),
            "attempt_id": "formal-low-rank-target-scan-attempt-v1",
            "step": "implementation_order_step_8_admitted_exotic_target_scan_cases",
            "evidence_kind": "blocked_target_scan_attempt",
            "claim_level": "not-formal-scan-evidence",
            "source_status": "blocked",
            "input_artifacts": {
                "catalog": {
                    "path": str(CATALOG_V10.relative_to(REPO_ROOT)),
                    "sha256": file_sha256_id(CATALOG_V10),
                    "content_hash": stable_content_hash(catalog),
                    "status": catalog["status"],
                    "resolved_row_count": catalog["resolved_row_count"],
                    "blocked_row_count": catalog["blocked_row_count"],
                },
                "step6_scan_plan_generation_attempt": artifact_record(STEP6_ATTEMPT, step6),
                "step7_control_scan_attempt": artifact_record(STEP7_ATTEMPT, step7),
                "step6_7_gate": artifact_record(STEP6_7_GATE, step6_7),
            },
            "blocked_reason_ids": [
                "no-formal-scan-plan",
                "no-formal-control-pass",
                "catalog-remains-partial",
                "six-nonpointed-family-rows-still-blocked",
                "no-scan-case-ids-to-dispatch",
                "worker-cannot-revalidate-missing-pinned-scan-plan",
            ],
            "admitted_target_set_status": "NOT_ENUMERATED_NO_FORMAL_SCAN_PLAN",
            "admitted_target_scan_case_ids": [],
            "target_scan_case_results": [],
            "worker_jobs_dispatched": 0,
            "worker_revalidation_possible": False,
            "formal_target_scan_results_produced": False,
            "formal_scan_aggregate_candidate": None,
            "fail_closed_checks": {
                "no_target_cases_without_scan_plan": "PASS",
                "no_worker_dispatch_without_pinned_hashes": "PASS",
                "no_result_cache_written": "PASS",
                "no_target_scan_result_emitted": "PASS",
                "no_scan_aggregate_candidate": "PASS",
            },
            "explicit_non_claims": [
                "No admitted exotic or target scan case was enumerated.",
                "No target scan worker was dispatched.",
                "No target scan case result exists.",
                "No scan aggregate or no-signal claim is supported.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "formal-low-rank-target-scan-attempt-v1.json": build_target_scan_attempt(
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
