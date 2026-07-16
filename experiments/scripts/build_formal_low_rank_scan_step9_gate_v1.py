#!/usr/bin/env python3
"""Build the fail-closed artifact for formal scan step 9.

Step 9 may aggregate formal scan case results only when the enumerator
certificate proves complete denominator coverage.  With no formal scan plan and
no target scan case results, the correct output is a hash-bound blocked
aggregate attempt, not a formal scan aggregate.
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
STEP8_ATTEMPT = OUT_DIR / "formal-low-rank-target-scan-attempt-v1.json"


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
        "generator_script": "experiments/scripts/build_formal_low_rank_scan_step9_gate_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_formal_low_rank_scan_step9_gate_v1.py --write"
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


def build_scan_aggregate_attempt(*, started_at_utc: str) -> dict[str, Any]:
    catalog = load_json(CATALOG_V10)
    step6 = load_json(STEP6_ATTEMPT)
    step7 = load_json(STEP7_ATTEMPT)
    step8 = load_json(STEP8_ATTEMPT)
    validate_low_rank_ribbon_catalog(catalog)

    if step6.get("formal_scan_plan_produced") is not False:
        raise RuntimeError("step 9 gate expects step 6 to be blocked")
    if step7.get("formal_scan_case_results_produced") is not False:
        raise RuntimeError("step 9 gate expects step 7 controls to be blocked")
    if step8.get("formal_target_scan_results_produced") is not False:
        raise RuntimeError("step 9 gate expects step 8 targets to be blocked")
    if step8.get("target_scan_case_results") != []:
        raise RuntimeError("step 9 gate expects no target scan case results")

    return with_hash(
        {
            **base_meta(
                "twisted-yetter.formal-low-rank-scan-aggregate-attempt.v1",
                "BLOCKED_NO_SCAN_CASE_RESULTS_OR_DENOMINATOR_CERTIFICATE",
                started_at_utc=started_at_utc,
            ),
            "attempt_id": "formal-low-rank-scan-aggregate-attempt-v1",
            "step": "implementation_order_step_9_scan_aggregate_and_admission_validator",
            "evidence_kind": "blocked_scan_aggregate_attempt",
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
                "step8_target_scan_attempt": artifact_record(STEP8_ATTEMPT, step8),
            },
            "blocked_reason_ids": [
                "no-formal-scan-plan",
                "no-formal-control-pass",
                "no-target-scan-case-results",
                "no-enumerator-complete-denominator-certificate",
                "catalog-remains-partial",
                "six-nonpointed-family-rows-still-blocked",
            ],
            "scan_case_result_count": 0,
            "scan_case_result_hashes": [],
            "expected_case_count": None,
            "actual_case_count": 0,
            "enumerator_certificate": {
                "status": "MISSING_NO_FORMAL_SCAN_PLAN",
                "content_hash": None,
                "complete_denominator_coverage": False,
            },
            "formal_scan_aggregate_produced": False,
            "formal_scan_aggregate_id": None,
            "formal_scan_aggregate_hash": None,
            "admission_validator_route": {
                "validator": "twisted_yetter.foundation_safety.validate_formal_evidence",
                "formal_scan_aggregate_candidate": None,
                "result": "NOT_RUN_NO_AGGREGATE_CANDIDATE",
                "reason": "No scan aggregate payload is emitted when scan case results and denominator certificate are absent.",
            },
            "would_be_formal_schema": "twisted-yetter.formal-low-rank-scan-aggregate.v1",
            "fail_closed_checks": {
                "no_aggregate_without_scan_case_results": "PASS",
                "no_complete_claim_without_denominator_certificate": "PASS",
                "no_no_signal_claim_emitted": "PASS",
                "no_formal_scan_aggregate_payload_emitted": "PASS",
                "admission_validator_not_given_empty_alias": "PASS",
            },
            "explicit_non_claims": [
                "This artifact is not a formal scan aggregate.",
                "No complete denominator certificate exists.",
                "No complete-no-signal aggregate is supported.",
                "No FORMAL_LOW_RANK_SCAN_COMPLETE claim is supported.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "formal-low-rank-scan-aggregate-attempt-v1.json": build_scan_aggregate_attempt(
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
