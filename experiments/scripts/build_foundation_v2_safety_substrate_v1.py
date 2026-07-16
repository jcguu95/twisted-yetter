#!/usr/bin/env python3
"""Materialize v1 fail-closed safety artifacts for low-rank ribbon scans."""

from __future__ import annotations

import argparse
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
    EVIDENCE_KIND_ALLOWLIST,
    EXPECTED_MODULAR_BRAIDED_COUNTS,
    FORMAL_ADMISSION_POLICY_SCHEMA,
    FORMAL_SCAN_READINESS_SCHEMA,
    FOUNDATION_STATUS,
    LOW_RANK_RIBBON_CATALOG_SCHEMA,
    REJECTED_SOURCE_STATUSES,
    RIBBON_CATALOG_BLOCKED,
    stable_content_hash,
    validate_formal_admission_policy,
    validate_formal_scan_readiness,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
LOW_RANK_MATRIX_PATH = (
    REPO_ROOT
    / "experiments"
    / "results"
    / "mtc-classification"
    / "low-rank-mtc-classification-matrix-v1.json"
)
LOW_RANK_FAMILIES_PATH = (
    REPO_ROOT
    / "experiments"
    / "inputs"
    / "mtc-classification"
    / "low-rank-mtc-families-v1.json"
)
PRIMARY_SOURCES_PATH = (
    REPO_ROOT
    / "experiments"
    / "inputs"
    / "references"
    / "low-rank-mtc-classification-primary-sources-v1.json"
)
V0_ARTIFACTS = (
    "blocker-coverage-matrix-v0.json",
    "blocker-registry-v0.json",
    "formal-admission-policy-v0.json",
    "historical-claim-audit-seed-v0.json",
    "known-execution-surface-inventory-v0.json",
    "review-input-bundle-v0.json",
)


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


def sha256_id(path: Path) -> str:
    import hashlib

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
        "generator_script": "experiments/scripts/build_foundation_v2_safety_substrate_v1.py",
        "reproduce_command": "python3 experiments/scripts/build_foundation_v2_safety_substrate_v1.py --write",
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {
            "python": platform.python_version(),
        },
    }


def build_policy(*, started_at_utc: str) -> dict[str, Any]:
    v0_inputs = []
    for name in V0_ARTIFACTS:
        path = OUT_DIR / name
        v0_inputs.append(
            {
                "path": str(path.relative_to(REPO_ROOT)),
                "sha256": sha256_id(path),
            }
        )
    policy = {
        **base_meta(
            FORMAL_ADMISSION_POLICY_SCHEMA,
            "FOUNDATION_ESTABLISHED_POLICY_ARTIFACT",
            started_at_utc=started_at_utc,
        ),
        "policy_id": "low-rank-ribbon-foundation-v2-formal-admission-policy-v1",
        "foundation_status": FOUNDATION_STATUS,
        "policy_status": "ACTIVE_FAIL_CLOSED",
        "formal_scan_status": "BLOCKED_UNTIL_LOW_RANK_RIBBON_CATALOG_ESTABLISHED",
        "partial_scan_status": (
            "AUTHORIZED_ONLY_FOR_VALIDATED_NONTRIVIAL_UNIVERSAL_CHARACTER_SUBSETS"
        ),
        "formal_evidence_kind_allowlist": list(EVIDENCE_KIND_ALLOWLIST),
        "policy_flags": {
            "derived_readiness_only": True,
            "mutable_aliases_are_not_formal_evidence": True,
            "formal_evidence_requires_content_hash": True,
            "classification_must_be_ribbon_level": True,
            "formula_preflight_is_not_formal_evidence": True,
            "braided_denominator_is_not_ribbon_denominator": True,
            "ctl_claims_require_admission_validator": True,
            "partial_scan_complete_claims_are_not_full_scan_claims": True,
            "trivial_universal_group_rows_discarded_for_nontrivial_character_scan": True,
            "unknown_universal_group_rows_cannot_be_silently_discarded": True,
        },
        "required_pinned_hash_fields": {
            "ribbon_realization_snapshot": [
                "content_hash",
                "category_data_hash",
                "producer_exact_coherence",
                "consumer_runtime_coherence",
                "ribbon_pivotal_compatibility",
            ],
            "scan_plan": [
                "content_hash",
                "audit_snapshot_hash",
                "classification_catalog_hash",
                "category_catalog",
                "manifold_catalog",
                "character_assignment_catalog",
                "evaluator_profile",
                "numeric_policy",
                "execution_semantics",
            ],
            "partial_scan_plan": [
                "content_hash",
                "audit_snapshot_hash",
                "classification_catalog_hash",
                "universal_grading_audit_hash",
                "category_subset_catalog",
                "manifold_catalog",
                "character_assignment_catalog",
                "evaluator_profile",
                "numeric_policy",
                "execution_semantics",
                "exclusion_ledger",
            ],
            "scan_case_result": [
                "content_hash",
                "scan_plan_hash",
                "scan_case_id",
                "input_hashes",
                "worker_revalidated_hashes",
            ],
            "scan_aggregate": [
                "content_hash",
                "scan_plan_hash",
                "enumerator_certificate",
                "expected_case_count",
                "actual_case_count",
            ],
            "partial_scan_aggregate": [
                "content_hash",
                "scan_plan_hash",
                "enumerator_certificate",
                "expected_case_count",
                "actual_case_count",
                "excluded_blocked_family_ids",
                "discarded_trivial_universal_group_family_ids",
            ],
        },
        "rejected_source_statuses": list(REJECTED_SOURCE_STATUSES),
        "allowed_formal_claim_levels": [
            "formal-low-rank-category-evidence",
            "formal-low-rank-scan-evidence",
        ],
        "explicit_non_claims": [
            "This policy does not establish any rank 2-5 ribbon refinement.",
            "This policy does not authorize any formal scan plan while the catalog is blocked.",
            "This policy only allows partial subset scans when their excluded rows are explicit.",
            "This policy does not turn formula preflight, candidate, or legacy FR-only outputs into evidence.",
        ],
        "v0_seed_inputs": v0_inputs,
    }
    validate_formal_admission_policy(policy)
    return policy


def build_resource_safety_ledger(*, started_at_utc: str) -> dict[str, Any]:
    entries = [
        resource_entry(
            resource_id="resource:twisted-yetter:category-input:historical-da4-fr-only-no-pivotal",
            path="experiments/inputs/category-pivotal/historical-da4-fr-only-no-pivotal-v1.json",
            safety_status="unsafe_for_formal_low_rank_scan",
            rationale="Historical FR-only fixture intentionally lacks explicit pivotal data.",
            safe_scopes=["negative control for missing-pivotal rejection"],
            unsafe_scopes=[
                "formal ribbon realization",
                "formal low-rank scan category input",
                "source of pivotal, spherical, or ribbon structure",
            ],
        ),
        resource_entry(
            resource_id="resource:twisted-yetter:policy:provisional-formula-policy",
            path="experiments/results/provisional-formula-policy/n30-policy-certificate.json",
            safety_status="policy_reference_not_formal_scan_evidence",
            rationale="n30 allows provisional formula experiments but rejects theorem-level claims.",
            safe_scopes=["policy citation for provisional formula boundaries"],
            unsafe_scopes=[
                "formal scan evidence",
                "closed 4D invariant claim",
                "low-rank no-signal conclusion",
            ],
        ),
        resource_entry(
            resource_id="resource:twisted-yetter:result:yasui-da4-c3w1-preflight",
            path="experiments/results/yasui/figure3-a1-r1-normalized-da4-c3w1-twisted-component-a-preflight-v1.json",
            safety_status="formula_preflight_not_formal_evidence",
            rationale="Preflight output may guide debugging but cannot satisfy formal scan admission.",
            safe_scopes=["debugging and archaeology"],
            unsafe_scopes=[
                "formal scan case result",
                "complete-no-signal aggregate",
                "CTL claim evidence for low-rank classification",
            ],
        ),
        resource_entry(
            resource_id="resource:twisted-yetter:script:su2-2-braid-oracle",
            path="experiments/sage/su2_2_braid_oracle.sage.py",
            safety_status="legacy_oracle_not_authorized_for_formal_scan",
            rationale="Legacy oracle scripts are execution surfaces, not admission gates.",
            safe_scopes=["historical comparison after explicit resource safety review"],
            unsafe_scopes=[
                "backend-neutral formal scan runner",
                "independent ribbon coherence certificate",
                "CTL-admissible formal evidence by itself",
            ],
        ),
    ]
    return {
        **base_meta(
            "twisted-yetter.foundation-safety.resource-safety-ledger.v1",
            "FOUNDATION_RESOURCE_SAFETY_LEDGER_ACTIVE",
            started_at_utc=started_at_utc,
        ),
        "ledger_id": "low-rank-ribbon-foundation-v2-resource-safety-ledger-v1",
        "resource_count": len(entries),
        "formal_low_rank_scan_allowed_by_default": False,
        "entries": entries,
    }


def resource_entry(
    *,
    resource_id: str,
    path: str,
    safety_status: str,
    rationale: str,
    safe_scopes: list[str],
    unsafe_scopes: list[str],
) -> dict[str, Any]:
    full = REPO_ROOT / path
    return {
        "resource_id": resource_id,
        "path": path,
        "exists_at_generation": full.exists(),
        "sha256": sha256_id(full) if full.exists() else None,
        "safety_status": safety_status,
        "formal_low_rank_scan_allowed": False,
        "safe_scopes": safe_scopes,
        "unsafe_scopes": unsafe_scopes,
        "rationale": rationale,
    }


def build_audit_ledger(*, started_at_utc: str) -> dict[str, Any]:
    primary = load_json(PRIMARY_SOURCES_PATH)
    rows = []
    for ref in primary["references"]:
        rows.append(
            {
                "reference_id": ref["reference_id"],
                "title": ref["title"],
                "source_snapshot_sha256": f"sha256:{ref['snapshot']['sha256']}",
                "locator_count": len(ref["locators"]),
                "locators": ref["locators"],
                "ribbon_refinement_role": source_role(ref["reference_id"]),
                "formal_ribbon_realization_sufficiency": "INSUFFICIENT_BY_ITSELF",
            }
        )
    return {
        **base_meta(
            "twisted-yetter.low-rank-ribbon-audit-ledger.v1",
            "AUDIT_LEDGER_READY_RIBBON_REFINEMENT_NOT_COMPLETE",
            started_at_utc=started_at_utc,
        ),
        "ledger_id": "low-rank-ribbon-refinement-audit-ledger-v1",
        "scope": "Rank 2-5 modular braided classes; ribbon/pivotal refinement audit.",
        "input_artifacts": [
            {
                "path": str(PRIMARY_SOURCES_PATH.relative_to(REPO_ROOT)),
                "sha256": sha256_id(PRIMARY_SOURCES_PATH),
            },
            {
                "path": str(LOW_RANK_MATRIX_PATH.relative_to(REPO_ROOT)),
                "sha256": sha256_id(LOW_RANK_MATRIX_PATH),
            },
        ],
        "reference_count": len(rows),
        "references": rows,
        "audit_conclusion": {
            "braided_scope_currently_supported": True,
            "ribbon_realization_catalog_complete": False,
            "reason": "Primary sources delimit braided scope but do not provide hash-bound realization snapshots for every row.",
        },
    }


def source_role(reference_id: str) -> str:
    if reference_id == "ref:rsw-low-rank-umtc-2009":
        return "rank_at_most_4_unitary_ribbon_source_partial_scope"
    if reference_id == "ref:dong-schopieray-near-integral-2024":
        return "rank_at_most_6_braided_source_explicit_pivotal_spherical_gap"
    if reference_id == "ref:bnrw-rank5-2016":
        return "rank_5_grothendieck_source_not_braided_or_ribbon_denominator"
    return "supporting_rank_5_premodular_source_not_formal_ribbon_catalog"


def build_catalog(*, started_at_utc: str) -> dict[str, Any]:
    matrix = load_json(LOW_RANK_MATRIX_PATH)
    families_input = load_json(LOW_RANK_FAMILIES_PATH)
    rows = [catalog_row(row) for row in matrix["families"]]
    catalog = {
        **base_meta(
            LOW_RANK_RIBBON_CATALOG_SCHEMA,
            RIBBON_CATALOG_BLOCKED,
            started_at_utc=started_at_utc,
        ),
        "catalog_id": "low-rank-ribbon-realization-catalog-v1",
        "scope": {
            "rank_min": 2,
            "rank_max": 5,
            "rank_6_or_higher_in_scope": False,
            "equivalence_target": "ribbon/pivotal refinements of modular braided classes",
        },
        "input_artifacts": [
            {
                "path": str(LOW_RANK_MATRIX_PATH.relative_to(REPO_ROOT)),
                "sha256": sha256_id(LOW_RANK_MATRIX_PATH),
            },
            {
                "path": str(LOW_RANK_FAMILIES_PATH.relative_to(REPO_ROOT)),
                "sha256": sha256_id(LOW_RANK_FAMILIES_PATH),
            },
        ],
        "coverage_by_rank": matrix["coverage_by_rank"],
        "braided_denominator_by_rank": EXPECTED_MODULAR_BRAIDED_COUNTS,
        "ribbon_denominator_by_rank": {},
        "ribbon_denominator_status": "NOT_DERIVED_DO_NOT_USE_BRAIDED_DENOMINATOR",
        "ribbon_denominator_copied_from_braided": False,
        "formal_scan_plan_allowed": False,
        "resolved_row_count": 0,
        "blocked_row_count": len(rows),
        "family_count": len(rows),
        "families": rows,
        "family_input_status": families_input["status"],
        "explicit_non_claims": [
            "No row is admitted as a formal ribbon realization snapshot.",
            "The braided denominator is not a ribbon denominator.",
            "This catalog blocks formal scan-plan generation.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def catalog_row(row: dict[str, Any]) -> dict[str, Any]:
    family_id = row["family_id"]
    return {
        "family_id": family_id,
        "rank": row["rank"],
        "family": row["family"],
        "modular_braided_class_count": row["modular_braided_class_count"],
        "fusion_multiplicity_max": row["fusion_multiplicity_max"],
        "reference_id": row["reference_id"],
        "fusion_level": {
            "status": "LITERATURE_BACKED_FUSION_FAMILY",
            "source_reference_id": row["reference_id"],
        },
        "braided_level": {
            "status": "MODULAR_BRAIDED_CLASSES_ENUMERATED",
            "equivalence": "braided",
            "class_count": row["modular_braided_class_count"],
            "source_reference_id": row["reference_id"],
        },
        "spherical_level": {
            "status": (
                "PARTIAL_SPHERICAL_MULTIPLICITY_RECORDED_NOT_REALIZATION_SNAPSHOT"
                if "spherical_structures_per_braided_class" in row
                else "NOT_AUDITED"
            ),
            "spherical_structures_per_braided_class": row.get(
                "spherical_structures_per_braided_class"
            ),
        },
        "pivotal_level": {
            "status": "NOT_MATERIALIZED_AS_HASH_BOUND_PIVOTAL_DATA",
            "required_data": [
                "duality",
                "pivotal scalar",
                "evaluation",
                "coevaluation",
                "fusion pairing",
                "basis/gauge",
                "field embedding",
            ],
        },
        "ribbon_level": {
            "status": "NOT_VERIFIED",
            "required_checks": [
                "balancing",
                "twist/pivotal compatibility",
                "producer exact coherence",
                "consumer runtime coherence",
                "certificate/data-hash binding",
            ],
        },
        "terminal_status": "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE",
        "formal_admission_allowed": False,
        "ribbon_realization_snapshot_hash": None,
        "blocker_ids": [
            f"{family_id}:missing-ribbon-realization-snapshot",
            f"{family_id}:missing-hash-bound-full-coherence-certificate",
            f"{family_id}:missing-independent-ribbon-compatibility-check",
        ],
        "missing_evidence": [
            "content-addressed F/R/twist/duality/pivotal/pairing realization",
            "exact or symbolic producer coherence certificate",
            "runtime consumer certificate bound to the same category_data_hash",
            "explicit ribbon condition / balancing compatibility certificate",
        ],
    }


def build_readiness(
    *,
    started_at_utc: str,
    policy: dict[str, Any],
    catalog: dict[str, Any],
    audit: dict[str, Any],
) -> dict[str, Any]:
    readiness = {
        **base_meta(
            FORMAL_SCAN_READINESS_SCHEMA,
            "BLOCKED_NO_ESTABLISHED_RIBBON_CATALOG",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v1",
        "foundation_status": FOUNDATION_STATUS,
        "policy_hash": stable_content_hash(policy),
        "audit_ledger_hash": stable_content_hash(audit),
        "classification_catalog_hash": stable_content_hash(catalog),
        "classification_catalog_status": catalog["status"],
        "scan_plan_generation_allowed": False,
        "formal_scan_plan_id": None,
        "blocking_reason_ids": [
            "low-rank-ribbon-catalog-status-blocked",
            "ribbon-denominator-not-derived",
            "zero-ribbon-realization-snapshots-admitted",
        ],
        "control_requirements_before_future_scan": [
            "S4 empty control",
            "CP2 one-framed unknot control",
            "S2xS2 Hopf zero-framed control",
            "unlink/Hopf link controls",
            "alpha=0 ordinary invariant control",
        ],
        "explicit_non_claims": [
            "No toy/control formal scan has been run under this readiness artifact.",
            "No exotic or target scan case is admitted.",
            "No complete-no-signal aggregate exists.",
        ],
    }
    validate_formal_scan_readiness(readiness, catalog=catalog)
    return readiness


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    policy = build_policy(started_at_utc=started_at_utc)
    resources = build_resource_safety_ledger(started_at_utc=started_at_utc)
    audit = build_audit_ledger(started_at_utc=started_at_utc)
    catalog = build_catalog(started_at_utc=started_at_utc)
    readiness = build_readiness(
        started_at_utc=started_at_utc,
        policy=policy,
        catalog=catalog,
        audit=audit,
    )
    return {
        "formal-admission-policy-v1.json": policy,
        "resource-safety-ledger-v1.json": resources,
        "low-rank-ribbon-audit-ledger-v1.json": audit,
        "low-rank-ribbon-realization-catalog-v1.json": catalog,
        "formal-low-rank-scan-readiness-v1.json": readiness,
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
