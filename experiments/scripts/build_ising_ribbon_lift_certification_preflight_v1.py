#!/usr/bin/env python3
"""Fail-closed preflight for certifying Ising ribbon-lift candidate payloads."""

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
CANDIDATE_PAYLOADS = OUT_DIR / "ising-ribbon-lift-candidate-payloads-v1.json"
NUMERIC_PIVOTAL_PROFILE = (
    REPO_ROOT / "experiments" / "inputs" / "category-pivotal" / "su2-k-standard-pivotal-v1.json"
)
FOUNDATION_SAFETY = REPO_ROOT / "src" / "twisted_yetter" / "foundation_safety.py"


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


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
    }
    if payload is not None:
        record["content_hash"] = payload["content_hash"]
        record["status"] = payload["status"]
    return record


def required_formal_checks() -> dict[str, str]:
    return {
        "category_contract": "RibbonFusionCategoryV2",
        "category_data_hash": "REQUIRED_SHA256",
        "producer_exact_coherence": "PASS_REQUIRED",
        "consumer_runtime_coherence": "PASS_REQUIRED",
        "ribbon_pivotal_compatibility_certificate": "PASS_REQUIRED",
        "pentagon": "PASS_REQUIRED",
        "hexagon": "PASS_REQUIRED",
        "rigidity": "PASS_REQUIRED",
        "duality_involution": "PASS_REQUIRED",
        "fusion_pairing_invertible": "PASS_REQUIRED",
        "r_inverse": "PASS_REQUIRED",
        "balancing": "PASS_REQUIRED",
        "ribbon_pivotal_compatibility_structural_check": "PASS_REQUIRED",
    }


def candidate_preflight_record(payload: dict[str, Any]) -> dict[str, Any]:
    pivotal = payload["candidate_pivotal_data"]
    category = payload["category_payload"]
    checks = {
        "candidate_payload_hash_present": isinstance(
            payload.get("candidate_payload_hash"), str
        )
        and payload["candidate_payload_hash"].startswith("sha256:"),
        "source_branch_hash_present": isinstance(payload.get("source_branch_data_hash"), str)
        and payload["source_branch_data_hash"].startswith("sha256:"),
        "f_r_twist_fusion_payload_present": bool(
            category.get("f_symbols")
            and category.get("r_symbols")
            and category.get("twists")
            and category.get("fusion")
        ),
        "evaluation_coevaluation_maps_materialized": pivotal.get(
            "evaluation_coevaluation_status"
        )
        == "MATERIALIZED",
        "fusion_pairing_certified": pivotal.get("pairing_status")
        == "FORMALLY_CERTIFIED_FOR_ROW_COMPLETION",
        "producer_exact_certificate_passed": payload.get(
            "producer_exact_certificate_status"
        )
        == "PASS",
        "runtime_consumer_certificate_passed": payload.get(
            "runtime_consumer_certificate_status"
        )
        == "PASS",
        "ribbon_pivotal_certificate_passed": payload.get(
            "ribbon_pivotal_certificate_status"
        )
        == "PASS",
        "formal_snapshot_produced": payload.get(
            "formal_ribbon_realization_snapshot_produced"
        )
        is True,
    }
    missing = [
        key
        for key, value in checks.items()
        if value is not True
    ]
    status = (
        "READY_FOR_FORMAL_SNAPSHOT_PROMOTION"
        if not missing
        else "BLOCKED_MISSING_FORMAL_PIVOTAL_RIBBON_EVIDENCE"
    )
    record_body = {
        "slot_id": payload["slot_id"],
        "braided_class_id": payload["braided_class_id"],
        "candidate_payload_hash": payload["candidate_payload_hash"],
        "source_branch_id": payload["source_branch_id"],
        "source_branch_data_hash": payload["source_branch_data_hash"],
        "spherical_lift_label": payload["spherical_lift_label"],
        "preflight_status": status,
        "checks": checks,
        "missing_requirements": missing,
        "blocking_summary": (
            "Candidate payload has F/R/twist/fusion data but lacks formal "
            "evaluation/coevaluation maps, certified fusion pairing, and "
            "producer/runtime/ribbon-pivotal certificates."
            if missing
            else "All formal promotion preflight checks passed."
        ),
        "formal_snapshot_hash": None,
    }
    return {
        **record_body,
        "preflight_record_hash": stable_content_hash(record_body),
    }


def build_preflight(*, started_at_utc: str) -> dict[str, Any]:
    payload_set = load_json(CANDIDATE_PAYLOADS)
    numeric_profile = load_json(NUMERIC_PIVOTAL_PROFILE)

    if payload_set["status"] != (
        "ISING_RIBBON_LIFT_CANDIDATE_PAYLOADS_MATERIALIZED_NOT_CERTIFIED"
    ):
        raise RuntimeError("Ising candidate payload set is not in the expected state")
    if payload_set["candidate_payload_count"] != 16:
        raise RuntimeError("Ising candidate payload set does not contain 16 payloads")

    records = [
        candidate_preflight_record(payload)
        for payload in payload_set["candidate_payloads"]
    ]
    blocked = [
        record
        for record in records
        if record["preflight_status"] != "READY_FOR_FORMAL_SNAPSHOT_PROMOTION"
    ]
    checks = {
        "input_candidate_payload_set_hash_bound": payload_set["content_hash"].startswith(
            "sha256:"
        ),
        "candidate_payload_count_is_16": len(records) == 16,
        "preflight_record_hashes_are_unique": len(
            {record["preflight_record_hash"] for record in records}
        )
        == len(records),
        "no_payload_ready_for_snapshot_promotion": len(blocked) == len(records),
        "all_payloads_block_on_eval_coeval_maps": all(
            "evaluation_coevaluation_maps_materialized"
            in record["missing_requirements"]
            for record in records
        ),
        "all_payloads_block_on_pairing_certificate": all(
            "fusion_pairing_certified" in record["missing_requirements"]
            for record in records
        ),
        "all_payloads_block_on_three_certificates": all(
            {
                "producer_exact_certificate_passed",
                "runtime_consumer_certificate_passed",
                "ribbon_pivotal_certificate_passed",
            }.issubset(set(record["missing_requirements"]))
            for record in records
        ),
        "numeric_pivotal_profile_is_not_formal_certificate": numeric_profile["status"]
        == "SUPPORTED_FOR_NUMERIC_MORSE_CONTROLS"
        and numeric_profile["pivotal_structure"]["mathematical_status"]
        == "NUMERIC_CONTROL_PROFILE_NOT_FORMAL_CERTIFICATE",
    }
    if not all(checks.values()):
        raise RuntimeError(f"Ising certification preflight checks failed: {checks}")

    status = (
        "ISING_RIBBON_LIFT_CERTIFICATES_PASSING_SNAPSHOTS_READY"
        if not blocked
        else "ISING_RIBBON_LIFT_CERTIFICATION_BLOCKED"
    )

    return with_hash(
        {
            "schema": "twisted-yetter.ising-ribbon-lift-certification-preflight.v1",
            "status": status,
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_ising_ribbon_lift_certification_preflight_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_ising_ribbon_lift_certification_preflight_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "preflight_id": "ising-ribbon-lift-certification-preflight-v1",
            "family_id": "rank3-ising",
            "input_artifacts": {
                "candidate_payload_set": artifact_record(
                    CANDIDATE_PAYLOADS, payload_set
                ),
                "numeric_pivotal_profile_reference": {
                    **artifact_record(NUMERIC_PIVOTAL_PROFILE),
                    "status": numeric_profile["status"],
                    "formal_certificate": False,
                    "reason": "Numeric Morse control profile is useful convention evidence, but not a producer/runtime/ribbon-pivotal formal certificate.",
                },
                "formal_admission_validator": artifact_record(FOUNDATION_SAFETY),
            },
            "formal_snapshot_promotion_requirements": required_formal_checks(),
            "checks": checks,
            "candidate_payload_count": len(records),
            "ready_for_snapshot_promotion_count": len(records) - len(blocked),
            "blocked_payload_count": len(blocked),
            "formal_snapshot_count": 0,
            "row_complete_status": "NOT_ROW_COMPLETE",
            "formal_scan_plan_allowed": False,
            "preflight_records": records,
            "blocking_requirements_summary": [
                "evaluation/coevaluation maps are not materialized in candidate payloads",
                "fusion pairings are not formally certified for row completion",
                "producer exact/symbolic coherence certificates are missing",
                "runtime consumer coherence certificates are missing",
                "ribbon/pivotal compatibility certificates are missing",
                "candidate payloads have not been promoted to ribbon_realization_snapshot artifacts",
            ],
            "remaining_growth": [
                "derive or materialize evaluation and coevaluation maps in the pinned SU(2)_2 Galois branch gauge",
                "certify fusion pairing invertibility in the pinned basis/gauge",
                "run exact/symbolic producer coherence checks",
                "run runtime consumer coherence checks",
                "run twist/balancing/ribbon-pivotal compatibility checks",
                "promote only passing records to formal ribbon_realization_snapshot artifacts",
            ],
            "explicit_non_claims": [
                "This preflight does not establish Ising row-complete ribbon classification.",
                "This preflight does not produce ribbon_realization_snapshot formal evidence.",
                "This preflight does not authorize scan-plan generation.",
                "The recorded numeric SU(2)_k pivotal profile is not used as a formal certificate.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "ising-ribbon-lift-certification-preflight-v1.json": build_preflight(
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
