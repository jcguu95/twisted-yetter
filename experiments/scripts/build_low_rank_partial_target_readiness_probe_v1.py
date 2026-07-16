#!/usr/bin/env python3
"""Probe whether the formal partial toy scan can advance to target scans."""

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

from twisted_yetter.foundation_safety import stable_content_hash, validate_formal_evidence  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
PARTIAL_TOY_AGGREGATE = OUT_DIR / "formal-low-rank-partial-toy-scan-aggregate-v1.json"
PARTIAL_TOY_PLAN = OUT_DIR / "formal-low-rank-partial-toy-scan-plan-v1.json"
N70 = REPO_ROOT / "experiments" / "inputs" / "exotic-pairs" / "n70-exotic-input-certification.json"
N93 = REPO_ROOT / "experiments" / "inputs" / "exotic-pairs" / "n93-data-blocker.json"
N65 = REPO_ROOT / "experiments" / "results" / "exotic-input-scout" / "n65-exotic-input-scout.json"


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
    record = {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
        "status": payload["status"],
    }
    if payload.get("content_hash"):
        record["content_hash"] = payload["content_hash"]
    else:
        record["content_hash"] = stable_content_hash(payload)
    return record


def nested_exact_output(payload: dict[str, Any]) -> dict[str, Any]:
    exact = payload.get("exact_output")
    return exact if isinstance(exact, dict) else {}


def build_probe(*, started_at_utc: str) -> dict[str, Any]:
    aggregate = load_json(PARTIAL_TOY_AGGREGATE)
    plan = load_json(PARTIAL_TOY_PLAN)
    n70 = load_json(N70)
    n93 = load_json(N93)
    n65 = load_json(N65)
    validate_formal_evidence(aggregate)
    validate_formal_evidence(plan)

    n70_exact = nested_exact_output(n70)
    n65_exact = nested_exact_output(n65)
    if n70_exact.get("n80_exotic_computation_route_allowed") is not False:
        raise RuntimeError("probe expected n70 to block n80")
    if n65_exact.get("any_machine_readable_exotic_input") is not False:
        raise RuntimeError("probe expected n65 to have no machine-readable exotic input")

    return with_hash(
        {
            "schema": "twisted-yetter.low-rank-partial-target-readiness-probe.v1",
            "status": "BLOCKED_NO_CERTIFIED_TARGET_INPUT_FOR_PARTIAL_SCAN",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_low_rank_partial_target_readiness_probe_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_low_rank_partial_target_readiness_probe_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "evidence_kind": "blocked_partial_target_scan_readiness_probe",
            "claim_level": "not-formal-scan-evidence",
            "source_status": "blocked",
            "input_artifacts": {
                "formal_partial_toy_scan_plan": artifact_record(PARTIAL_TOY_PLAN, plan),
                "formal_partial_toy_scan_aggregate": artifact_record(
                    PARTIAL_TOY_AGGREGATE, aggregate
                ),
                "n70_exotic_input_certification": artifact_record(N70, n70),
                "n93_data_blocker": artifact_record(N93, n93),
                "n65_exotic_input_scout": artifact_record(N65, n65),
            },
            "readiness_probe": {
                "formal_partial_toy_scan_aggregate_complete": True,
                "target_manifold_catalog_ready": False,
                "certified_exotic_input_ready": False,
                "worker_dispatch_allowed": False,
                "target_scan_case_results_produced": False,
            },
            "blocked_reason_ids": [
                "n70-blocked-no-certified-input",
                "missing-machine-readable-exotic-kirby-diagrams",
                "missing-h2-homeomorphism-marking-certificate",
                "no-admitted-target-manifold-catalog",
                "partial-toy-aggregate-cannot-substitute-target-scan",
            ],
            "next_required_work": [
                "certify one machine-readable target or exotic-pair input",
                "pin target manifold catalog and character assignments",
                "prove evaluator support for that target beyond the current toy diagrams",
                "generate a new partial target scan plan only after those hashes exist",
            ],
            "fail_closed_checks": {
                "toy_aggregate_not_promoted_to_target_scan": "PASS",
                "n70_blocks_n80_route": "PASS",
                "no_target_case_ids_emitted": "PASS",
                "no_target_worker_dispatched": "PASS",
                "no_no_signal_claim": "PASS",
            },
            "explicit_non_claims": [
                "This probe is not a formal scan plan.",
                "This probe is not a scan_case_result.",
                "This probe is not a scan_aggregate.",
                "This probe does not claim no signal.",
                "This probe does not certify any exotic or target manifold input.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    return {
        "low-rank-partial-target-readiness-probe-v1.json": build_probe(
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
