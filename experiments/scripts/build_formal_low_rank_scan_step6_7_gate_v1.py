#!/usr/bin/env python3
"""Build fail-closed artifacts for formal scan steps 6 and 7.

Step 6 may generate a formal scan plan only from an established low-rank ribbon
catalog.  Step 7 may run controls only from a formal scan plan.  With the v10
catalog still partial, the correct output is a hash-bound blocked attempt.
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
    RIBBON_CATALOG_ESTABLISHED,
    add_content_hash,
    stable_content_hash,
    validate_formal_admission_policy,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
CATALOG_V10 = OUT_DIR / "low-rank-ribbon-realization-catalog-v10.json"
READINESS_V10 = OUT_DIR / "formal-low-rank-scan-readiness-v10.json"
POLICY_V1 = OUT_DIR / "formal-admission-policy-v1.json"

CONTROL_TARGETS = [
    {
        "control_id": "s4-empty",
        "target": "S4",
        "purpose": "empty closed 4-manifold normalization control",
    },
    {
        "control_id": "cp2-plus-one-framed-unknot",
        "target": "CP2",
        "purpose": "positive one-framed unknot control",
    },
    {
        "control_id": "s2xs2-hopf-zero-framed",
        "target": "S2xS2",
        "purpose": "zero-framed Hopf control",
    },
    {
        "control_id": "unlink-and-hopf-link-controls",
        "target": "unlink/Hopf",
        "purpose": "link-level ordinary RT sanity controls",
    },
    {
        "control_id": "alpha0-ordinary-invariant",
        "target": "alpha=0",
        "purpose": "ordinary invariant comparison under the same pinned scan plan",
    },
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


def base_meta(schema: str, status: str, *, started_at_utc: str) -> dict[str, Any]:
    return {
        "schema": schema,
        "status": status,
        "generated_at_utc": started_at_utc,
        "generator_script": "experiments/scripts/build_formal_low_rank_scan_step6_7_gate_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_formal_low_rank_scan_step6_7_gate_v1.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def build_scan_plan_attempt(
    *,
    started_at_utc: str,
    catalog: dict[str, Any],
    readiness: dict[str, Any],
    policy: dict[str, Any],
) -> dict[str, Any]:
    validate_formal_admission_policy(policy)
    validate_low_rank_ribbon_catalog(catalog)

    blocked_reasons = []
    if catalog["status"] != RIBBON_CATALOG_ESTABLISHED:
        blocked_reasons.append("catalog-status-is-not-established")
    if catalog.get("formal_scan_plan_allowed") is not True:
        blocked_reasons.append("catalog-formal-scan-plan-allowed-is-false")
    if readiness.get("scan_plan_generation_allowed") is not True:
        blocked_reasons.append("readiness-scan-plan-generation-allowed-is-false")
    if catalog.get("blocked_row_count") != 0:
        blocked_reasons.append("catalog-has-blocked-family-rows")
    if catalog.get("ribbon_denominator_by_rank") in ({}, None):
        blocked_reasons.append("ribbon-denominator-is-not-final")

    if not blocked_reasons:
        raise RuntimeError("unexpected established catalog; this v1 gate only records blocked attempts")

    return add_content_hash(
        {
            **base_meta(
                "twisted-yetter.formal-low-rank-scan-plan-generation-attempt.v1",
                "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG",
                started_at_utc=started_at_utc,
            ),
            "attempt_id": "formal-low-rank-scan-plan-generation-attempt-v1",
            "step": "implementation_order_step_6_scan_plan_generator",
            "evidence_kind": "blocked_scan_plan_generation_attempt",
            "claim_level": "not-formal-scan-evidence",
            "source_status": "blocked",
            "input_artifacts": {
                "catalog": {
                    "path": str(CATALOG_V10.relative_to(REPO_ROOT)),
                    "sha256": file_sha256_id(CATALOG_V10),
                    "content_hash": stable_content_hash(catalog),
                    "status": catalog["status"],
                },
                "readiness_artifact": {
                    "path": str(READINESS_V10.relative_to(REPO_ROOT)),
                    "sha256": file_sha256_id(READINESS_V10),
                    "content_hash": stable_content_hash(readiness),
                    "status": readiness["status"],
                },
                "policy": {
                    "path": str(POLICY_V1.relative_to(REPO_ROOT)),
                    "sha256": file_sha256_id(POLICY_V1),
                    "content_hash": stable_content_hash(policy),
                    "status": policy["policy_status"],
                },
            },
            "blocked_reason_ids": blocked_reasons,
            "resolved_row_count": catalog["resolved_row_count"],
            "blocked_row_count": catalog["blocked_row_count"],
            "blocked_family_ids": catalog["blocked_family_ids"],
            "formal_scan_plan_produced": False,
            "formal_scan_plan_id": None,
            "formal_scan_plan_hash": None,
            "scan_case_ids": [],
            "would_be_formal_schema": "twisted-yetter.formal-low-rank-scan-plan.v1",
            "fail_closed_checks": {
                "partial_catalog_rejected": "PASS",
                "no_mutable_alias_plan_emitted": "PASS",
                "no_scan_case_ids_emitted": "PASS",
                "no_formal_evidence_route_opened": "PASS",
            },
            "explicit_non_claims": [
                "This artifact is not a formal scan plan.",
                "No scan case id is admitted.",
                "No low-rank no-signal result follows from this blocked attempt.",
            ],
        }
    )


def build_control_attempt(
    *,
    started_at_utc: str,
    scan_plan_attempt: dict[str, Any],
) -> dict[str, Any]:
    if scan_plan_attempt.get("formal_scan_plan_produced") is not False:
        raise RuntimeError("control gate expects the step 6 attempt to be blocked")
    return add_content_hash(
        {
            **base_meta(
                "twisted-yetter.formal-low-rank-control-scan-attempt.v1",
                "BLOCKED_NO_FORMAL_SCAN_PLAN",
                started_at_utc=started_at_utc,
            ),
            "attempt_id": "formal-low-rank-control-scan-attempt-v1",
            "step": "implementation_order_step_7_controls",
            "evidence_kind": "blocked_control_scan_attempt",
            "claim_level": "not-formal-scan-evidence",
            "source_status": "blocked",
            "scan_plan_generation_attempt_hash": scan_plan_attempt["content_hash"],
            "required_formal_scan_plan_hash": None,
            "control_targets": CONTROL_TARGETS,
            "control_case_results": [],
            "formal_scan_case_results_produced": False,
            "alpha0_control_status": "NOT_RUN_NO_FORMAL_SCAN_PLAN",
            "ordinary_control_status": "NOT_RUN_NO_FORMAL_SCAN_PLAN",
            "blocked_reason_ids": [
                "step6-produced-no-formal-scan-plan",
                "worker-revalidation-has-no-pinned-scan-plan",
                "control-targets-cannot-bind-category-manifold-character-hashes",
            ],
            "fail_closed_checks": {
                "s4_not_run_without_plan": "PASS",
                "cp2_not_run_without_plan": "PASS",
                "s2xs2_not_run_without_plan": "PASS",
                "unlink_hopf_not_run_without_plan": "PASS",
                "alpha0_not_run_without_plan": "PASS",
                "no_scan_case_result_emitted": "PASS",
            },
            "explicit_non_claims": [
                "No S4/CP2/S2xS2/unlink/Hopf/alpha=0 control was run under formal scan semantics.",
                "This artifact is not a scan case result.",
                "This artifact does not test detector correctness.",
            ],
        }
    )


def build_gate_summary(
    *,
    started_at_utc: str,
    scan_plan_attempt: dict[str, Any],
    control_attempt: dict[str, Any],
) -> dict[str, Any]:
    return add_content_hash(
        {
            **base_meta(
                "twisted-yetter.formal-low-rank-step6-7-gate.v1",
                "STEP6_7_FAIL_CLOSED_COMPLETE",
                started_at_utc=started_at_utc,
            ),
            "gate_id": "formal-low-rank-step6-7-gate-v1",
            "completion_semantics": (
                "Step 6 and step 7 are complete only as fail-closed gates under "
                "the current partial catalog. They did not produce a scan plan, "
                "control case result, scan aggregate, or no-signal claim."
            ),
            "scan_plan_generation_attempt_hash": scan_plan_attempt["content_hash"],
            "control_scan_attempt_hash": control_attempt["content_hash"],
            "step_status": {
                "implementation_order_step_6_scan_plan_generator": "COMPLETE_FAIL_CLOSED_BLOCKED",
                "implementation_order_step_7_controls": "COMPLETE_FAIL_CLOSED_BLOCKED",
            },
            "formal_outputs": {
                "scan_plan": None,
                "scan_case_results": [],
                "scan_aggregate": None,
            },
            "blocked_reason_ids": sorted(
                set(scan_plan_attempt["blocked_reason_ids"] + control_attempt["blocked_reason_ids"])
            ),
            "explicit_non_claims": [
                "LOW_RANK_RIBBON_CLASSIFICATION_ESTABLISHED is still not claimed.",
                "FORMAL_LOW_RANK_SCAN_COMPLETE is still not claimed.",
                "No formal control scan was run.",
                "No no-signal conclusion is supported.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    catalog = load_json(CATALOG_V10)
    readiness = load_json(READINESS_V10)
    policy = load_json(POLICY_V1)
    scan_plan_attempt = build_scan_plan_attempt(
        started_at_utc=started_at_utc,
        catalog=catalog,
        readiness=readiness,
        policy=policy,
    )
    control_attempt = build_control_attempt(
        started_at_utc=started_at_utc,
        scan_plan_attempt=scan_plan_attempt,
    )
    summary = build_gate_summary(
        started_at_utc=started_at_utc,
        scan_plan_attempt=scan_plan_attempt,
        control_attempt=control_attempt,
    )
    return {
        "formal-low-rank-scan-plan-generation-attempt-v1.json": scan_plan_attempt,
        "formal-low-rank-control-scan-attempt-v1.json": control_attempt,
        "formal-low-rank-step6-7-gate-v1.json": summary,
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
