#!/usr/bin/env python3
"""Build a formal partial toy scan plan, chunk results, and aggregate.

The scope is intentionally narrow: admitted nontrivial universal-character rows
that already have toy workers, over the three checked-in toy diagrams.  This is
not the final low-rank scan and not a no-signal claim.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import (  # noqa: E402
    add_content_hash,
    stable_content_hash,
    validate_formal_evidence,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
TOY_DIR = REPO_ROOT / "experiments" / "inputs" / "toy-diagrams"
RULE = OUT_DIR / "low-rank-nontrivial-partial-scan-rule-v1.json"
CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v11.json"
UNIVERSAL_AUDIT = OUT_DIR / "low-rank-full-catalog-universal-grading-audit-v1.json"
POLICY = OUT_DIR / "formal-admission-policy-v1.json"
POINTED_BENCHMARK = OUT_DIR / "low-rank-pointed-partial-scan-benchmark-v1.json"
PRODUCT_BENCHMARK = OUT_DIR / "low-rank-product-partial-scan-benchmark-v1.json"

POINTED_RUNNER = REPO_ROOT / "experiments" / "scripts" / "run_low_rank_pointed_partial_scan_benchmark_v1.py"
PRODUCT_RUNNER = REPO_ROOT / "experiments" / "scripts" / "run_low_rank_product_partial_scan_benchmark_v1.py"
THIS_SCRIPT = REPO_ROOT / "experiments" / "scripts" / "build_low_rank_partial_toy_scan_v1.py"


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


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {"path": str(path.relative_to(REPO_ROOT)), "sha256": file_sha256_id(path)}
    if payload is not None:
        record["content_hash"] = payload.get("content_hash", stable_content_hash(payload))
        record["status"] = payload["status"]
    return record


def load_script_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec is not None and spec.loader is not None
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sha_section(payload: dict[str, Any]) -> str:
    return stable_content_hash(payload)


def snapshot_records_for_family(family_ids: set[str]) -> list[dict[str, Any]]:
    records = []
    for path in sorted(SNAPSHOT_DIR.glob("*.json")):
        snapshot = load_json(path)
        if snapshot.get("family_id") in family_ids:
            validate_formal_evidence(snapshot)
            records.append(
                {
                    "family_id": snapshot["family_id"],
                    "realization_id": snapshot["realization_id"],
                    "content_hash": snapshot["content_hash"],
                    "path": str(path.relative_to(REPO_ROOT)),
                    "file_sha256": file_sha256_id(path),
                }
            )
    return records


def toy_diagram_records() -> list[dict[str, str]]:
    paths = [
        TOY_DIR / "s4-empty.json",
        TOY_DIR / "cp2-plus-one-framed-unknot.json",
        TOY_DIR / "hopf-link.json",
    ]
    return [
        {
            "path": str(path.relative_to(REPO_ROOT)),
            "file_sha256": file_sha256_id(path),
            "diagram_id": load_json(path)["diagram_id"],
        }
        for path in paths
    ]


def make_sections(rule: dict[str, Any]) -> dict[str, dict[str, Any]]:
    admitted = set(rule["admitted_resolved_nontrivial_family_ids"])
    pointed = admitted - {"rank4-semion-times-fibonacci"}
    sections = {
        "category_subset_catalog": {
            "schema": "twisted-yetter.partial-toy-category-subset-catalog.v1",
            "scan_scope": "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET",
            "family_ids": sorted(admitted),
            "snapshot_records": snapshot_records_for_family(admitted),
        },
        "manifold_catalog": {
            "schema": "twisted-yetter.partial-toy-manifold-catalog.v1",
            "scan_target_scope": "toy-diagrams-only",
            "diagrams": toy_diagram_records(),
        },
        "character_assignment_catalog": {
            "schema": "twisted-yetter.partial-toy-character-assignment-catalog.v1",
            "pointed_family_ids": sorted(pointed),
            "product_family_ids": ["rank4-semion-times-fibonacci"],
            "assignment_policy": {
                "pointed": "all characters of the pointed universal group recorded by each runner",
                "product": "Z2 characters pinned by Semion-factor-first projection contract",
            },
        },
        "evaluator_profile": {
            "schema": "twisted-yetter.partial-toy-evaluator-profile.v1",
            "profiles": [
                {
                    "profile_id": "pointed-toy-linking-matrix",
                    "runner": str(POINTED_RUNNER.relative_to(REPO_ROOT)),
                    "runner_sha256": file_sha256_id(POINTED_RUNNER),
                    "family_ids": sorted(pointed),
                },
                {
                    "profile_id": "semion-times-fib-product-toy-channel-trace",
                    "runner": str(PRODUCT_RUNNER.relative_to(REPO_ROOT)),
                    "runner_sha256": file_sha256_id(PRODUCT_RUNNER),
                    "family_ids": ["rank4-semion-times-fibonacci"],
                    "limits": [
                        "toy diagrams with at most two components",
                        "not a general planar RT recoupling evaluator",
                    ],
                },
            ],
        },
        "numeric_policy": {
            "schema": "twisted-yetter.partial-toy-numeric-policy.v1",
            "pointed": "exact sparse roots of unity per pointed runner",
            "product": "exact sparse integer zeta20 bookkeeping for current product snapshots",
            "floating_point_allowed": False,
        },
        "execution_semantics": {
            "schema": "twisted-yetter.partial-toy-execution-semantics.v1",
            "chunking": [
                "one formal chunk for all admitted pointed toy cases",
                "one formal chunk for rank4-semion-times-fibonacci toy cases",
            ],
            "worker_revalidates_hashes": True,
            "resume_policy": "rerun whole toy chunk; no mutable cache accepted as evidence",
        },
        "exclusion_ledger": {
            "schema": "twisted-yetter.partial-toy-exclusion-ledger.v1",
            "excluded_blocked_family_ids": rule["excluded_blocked_nontrivial_family_ids"],
            "discarded_trivial_universal_group_family_ids": (
                rule["discarded_trivial_universal_group_family_ids"]
            ),
            "unknown_universal_group_family_ids": rule["unknown_universal_group_family_ids"],
            "trivial_rows_disposition": (
                "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
            ),
            "unknown_rows_disposition": "EXCLUDED_NOT_DISCARDED",
        },
    }
    return sections


def make_plan(
    *,
    started_at_utc: str,
    rule: dict[str, Any],
    catalog: dict[str, Any],
    universal_audit: dict[str, Any],
    sections: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    case_ids = [
        "partial-toy-pointed-chunk-v1",
        "partial-toy-product-semion-times-fib-chunk-v1",
    ]
    plan = add_content_hash(
        {
            "schema": "twisted-yetter.formal-low-rank-partial-toy-scan-plan.v1",
            "evidence_kind": "partial_scan_plan",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "status": "FORMAL_PARTIAL_TOY_SCAN_PLAN_ADMITTED_SCOPE",
            "generated_at_utc": started_at_utc,
            "generator_script": str(THIS_SCRIPT.relative_to(REPO_ROOT)),
            "reproduce_command": (
                "python3 experiments/scripts/build_low_rank_partial_toy_scan_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "scan_scope": "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET",
            "toy_scope_notice": "Only the three checked-in toy diagrams are in this plan.",
            "partial_scan_complete_claim_allowed": True,
            "full_scan_complete_claim_allowed": False,
            "audit_snapshot_state": "current-pinned",
            "audit_snapshot_hash": rule["content_hash"],
            "classification_catalog_hash": catalog["content_hash"],
            "universal_grading_audit_hash": universal_audit["content_hash"],
            "pinned_hashes": {
                key: sha_section(value) for key, value in sections.items()
            },
            "pinned_sections": sections,
            "admitted_family_ids": rule["admitted_resolved_nontrivial_family_ids"],
            "excluded_blocked_family_ids": rule["excluded_blocked_nontrivial_family_ids"],
            "discarded_trivial_universal_group_family_ids": (
                rule["discarded_trivial_universal_group_family_ids"]
            ),
            "unknown_universal_group_family_ids": rule["unknown_universal_group_family_ids"],
            "trivial_rows_disposition": (
                "DISCARDED_TRIVIAL_UNIVERSAL_GROUP_FOR_NONTRIVIAL_CHARACTER_SCAN"
            ),
            "unknown_rows_disposition": "EXCLUDED_NOT_DISCARDED",
            "scan_case_ids": case_ids,
            "explicit_non_claims": [
                "This plan is not a full rank 2-5 scan plan.",
                "This plan does not include rank3-ising or rank5-su2-4.",
                "This plan does not include rank5-psu3-4.",
                "This plan covers toy diagrams only.",
            ],
        }
    )
    validate_formal_evidence(plan)
    return plan


def stable_case_results_hash(benchmark: dict[str, Any]) -> str:
    return stable_content_hash(
        {
            "benchmark_id": benchmark["benchmark_id"],
            "scope": benchmark["scope"],
            "case_results": benchmark["case_results"],
        }
    )


def run_worker_chunk(
    *,
    chunk_id: str,
    plan: dict[str, Any],
    runner_module: Any,
    expected_status: str,
    expected_case_count: int,
    started_at_utc: str,
    input_hashes: dict[str, str],
) -> dict[str, Any]:
    t0 = time.perf_counter()
    benchmark = next(iter(runner_module.build_all().values()))
    elapsed_ms = (time.perf_counter() - t0) * 1000
    if benchmark["status"] != expected_status:
        raise RuntimeError(f"{chunk_id} status mismatch: {benchmark['status']}")
    if benchmark["timing"]["case_count"] != expected_case_count:
        raise RuntimeError(f"{chunk_id} case count mismatch")
    if any(not value.startswith("sha256:") for value in input_hashes.values()):
        raise RuntimeError(f"{chunk_id} has non-sha input hash")
    result = add_content_hash(
        {
            "schema": "twisted-yetter.formal-low-rank-partial-toy-scan-case-result.v1",
            "evidence_kind": "scan_case_result",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "status": "PASS_FORMAL_PARTIAL_TOY_SCAN_CHUNK",
            "generated_at_utc": started_at_utc,
            "generator_script": str(THIS_SCRIPT.relative_to(REPO_ROOT)),
            "scan_plan_hash": plan["content_hash"],
            "scan_case_id": chunk_id,
            "worker_revalidated_hashes": True,
            "input_hashes": input_hashes,
            "chunk_status": "PASS",
            "subcase_count": expected_case_count,
            "elapsed_ms_decimal": format(elapsed_ms, ".17g"),
            "result_hashes": {
                "benchmark_payload": benchmark["content_hash"],
                "stable_case_results": stable_case_results_hash(benchmark),
            },
            "result_summary": {
                "benchmark_status": benchmark["status"],
                "benchmark_id": benchmark["benchmark_id"],
                "case_count": benchmark["timing"]["case_count"],
                "max_case_id": benchmark["timing"]["max_case_id"],
            },
            "explicit_non_claims": [
                "This chunk is only a partial toy scan result.",
                "This chunk is not a full low-rank scan result.",
            ],
        }
    )
    validate_formal_evidence(result)
    return result


def make_aggregate(
    *,
    started_at_utc: str,
    plan: dict[str, Any],
    rule: dict[str, Any],
    pointed_case: dict[str, Any],
    product_case: dict[str, Any],
) -> dict[str, Any]:
    case_hashes = [pointed_case["content_hash"], product_case["content_hash"]]
    aggregate = add_content_hash(
        {
            "schema": "twisted-yetter.formal-low-rank-partial-toy-scan-aggregate.v1",
            "evidence_kind": "partial_scan_aggregate",
            "claim_level": "formal-low-rank-scan-evidence",
            "source_status": "formal",
            "status": "FORMAL_PARTIAL_TOY_SCAN_AGGREGATE_COMPLETE",
            "generated_at_utc": started_at_utc,
            "generator_script": str(THIS_SCRIPT.relative_to(REPO_ROOT)),
            "scan_scope": "NONTRIVIAL_UNIVERSAL_CHARACTER_ADMITTED_SUBSET",
            "toy_scope_notice": "Only the three checked-in toy diagrams are aggregated.",
            "partial_scan_complete_claim_allowed": True,
            "full_scan_complete_claim_allowed": False,
            "scan_plan_hash": plan["content_hash"],
            "enumerator_certificate": {
                "status": "PASS_PARTIAL_DENOMINATOR",
                "expected_chunk_case_ids": plan["scan_case_ids"],
                "actual_chunk_case_ids": [
                    pointed_case["scan_case_id"],
                    product_case["scan_case_id"],
                ],
                "expected_subcase_count": 347,
                "actual_subcase_count": (
                    pointed_case["subcase_count"] + product_case["subcase_count"]
                ),
                "coverage_boundary": (
                    "admitted nontrivial universal-character toy chunks only"
                ),
            },
            "expected_case_count": 2,
            "actual_case_count": 2,
            "scan_case_result_hashes": case_hashes,
            "scan_case_result_statuses": {
                pointed_case["scan_case_id"]: pointed_case["chunk_status"],
                product_case["scan_case_id"]: product_case["chunk_status"],
            },
            "excluded_blocked_family_ids": rule["excluded_blocked_nontrivial_family_ids"],
            "discarded_trivial_universal_group_family_ids": (
                rule["discarded_trivial_universal_group_family_ids"]
            ),
            "unknown_universal_group_family_ids": rule["unknown_universal_group_family_ids"],
            "aggregate_claim": "partial-toy-scan-complete-for-admitted-subset",
            "explicit_non_claims": [
                "This aggregate does not claim complete-no-signal.",
                "This aggregate does not claim FORMAL_LOW_RANK_SCAN_COMPLETE.",
                "This aggregate does not cover rank3-ising, rank5-su2-4, or rank5-psu3-4.",
                "This aggregate does not cover target exotic manifolds.",
            ],
        }
    )
    validate_formal_evidence(aggregate)
    return aggregate


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    rule = load_json(RULE)
    catalog = load_json(CATALOG)
    universal_audit = load_json(UNIVERSAL_AUDIT)
    policy = load_json(POLICY)
    existing_pointed = load_json(POINTED_BENCHMARK)
    existing_product = load_json(PRODUCT_BENCHMARK)
    sections = make_sections(rule)
    plan = make_plan(
        started_at_utc=started_at_utc,
        rule=rule,
        catalog=catalog,
        universal_audit=universal_audit,
        sections=sections,
    )
    pointed_module = load_script_module(POINTED_RUNNER, "formal_partial_toy_pointed_runner_v1")
    product_module = load_script_module(PRODUCT_RUNNER, "formal_partial_toy_product_runner_v1")
    common_hashes = {
        "scan_plan": plan["content_hash"],
        "partial_scan_rule": rule["content_hash"],
        "category_subset_catalog": plan["pinned_hashes"]["category_subset_catalog"],
        "manifold_catalog": plan["pinned_hashes"]["manifold_catalog"],
        "character_assignment_catalog": plan["pinned_hashes"]["character_assignment_catalog"],
        "evaluator_profile": plan["pinned_hashes"]["evaluator_profile"],
        "numeric_policy": plan["pinned_hashes"]["numeric_policy"],
        "execution_semantics": plan["pinned_hashes"]["execution_semantics"],
        "exclusion_ledger": plan["pinned_hashes"]["exclusion_ledger"],
        "formal_policy": policy.get("content_hash", stable_content_hash(policy)),
    }
    pointed_case = run_worker_chunk(
        chunk_id="partial-toy-pointed-chunk-v1",
        plan=plan,
        runner_module=pointed_module,
        expected_status="PASS_POINTED_TOY_BENCHMARK_FAST",
        expected_case_count=291,
        started_at_utc=started_at_utc,
        input_hashes={
            **common_hashes,
            "worker_runner": file_sha256_id(POINTED_RUNNER),
            "previous_benchmark_artifact": existing_pointed["content_hash"],
        },
    )
    product_case = run_worker_chunk(
        chunk_id="partial-toy-product-semion-times-fib-chunk-v1",
        plan=plan,
        runner_module=product_module,
        expected_status="PASS_PRODUCT_TOY_BENCHMARK_FAST",
        expected_case_count=56,
        started_at_utc=started_at_utc,
        input_hashes={
            **common_hashes,
            "worker_runner": file_sha256_id(PRODUCT_RUNNER),
            "previous_benchmark_artifact": existing_product["content_hash"],
        },
    )
    aggregate = make_aggregate(
        started_at_utc=started_at_utc,
        plan=plan,
        rule=rule,
        pointed_case=pointed_case,
        product_case=product_case,
    )
    return {
        "formal-low-rank-partial-toy-scan-plan-v1.json": plan,
        "formal-low-rank-partial-toy-scan-case-pointed-v1.json": pointed_case,
        "formal-low-rank-partial-toy-scan-case-product-v1.json": product_case,
        "formal-low-rank-partial-toy-scan-aggregate-v1.json": aggregate,
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
