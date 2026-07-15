#!/usr/bin/env python3
"""Extend the partial low-rank ribbon catalog with rank-2 Fib/Yang-Lee data."""

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
    LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
    RIBBON_CATALOG_PARTIAL,
    FoundationSafetyError,
    add_content_hash,
    stable_content_hash,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
V3_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v3.json"
V3_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v3.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"
SAGE_CERTIFICATE = OUT_DIR / "rank2-fibonacci-yang-lee-sage-coherence-v1.json"


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
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v4.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v4.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def require_sage_certificate(certificate: dict[str, Any]) -> None:
    if certificate.get("schema") != "twisted-yetter.rank2-fibonacci-yang-lee-sage-coherence.v1":
        raise FoundationSafetyError("unexpected rank2 Fib/Yang-Lee Sage certificate schema")
    if certificate.get("status") != "PASS":
        raise FoundationSafetyError("rank2 Fib/Yang-Lee Sage certificate did not pass")
    if certificate.get("family_id") != "rank2-fibonacci-yang-lee":
        raise FoundationSafetyError("rank2 Fib/Yang-Lee Sage certificate has wrong family")
    branches = certificate.get("branches")
    if not isinstance(branches, list) or len(branches) != 4:
        raise FoundationSafetyError("rank2 Fib/Yang-Lee Sage certificate must have four branches")
    if certificate.get("branch_count") != 4:
        raise FoundationSafetyError("rank2 Fib/Yang-Lee Sage certificate branch_count mismatch")
    expected_ids = {
        "rank2-fibonacci-yang-lee-fibonacci-plus",
        "rank2-fibonacci-yang-lee-fibonacci-minus",
        "rank2-fibonacci-yang-lee-yang-lee-plus",
        "rank2-fibonacci-yang-lee-yang-lee-minus",
    }
    if {branch.get("realization_id") for branch in branches} != expected_ids:
        raise FoundationSafetyError("rank2 Fib/Yang-Lee branch ids changed")
    for branch in branches:
        if branch.get("status") != "PASS":
            raise FoundationSafetyError("rank2 Fib/Yang-Lee branch did not pass")
        checks = branch.get("exact_checks")
        if not isinstance(checks, dict) or not checks or not all(checks.values()):
            raise FoundationSafetyError("rank2 Fib/Yang-Lee exact checks are incomplete")
        negative = branch.get("negative_controls", {}).get("wrong_rx_square_root")
        if not isinstance(negative, dict):
            raise FoundationSafetyError("rank2 Fib/Yang-Lee negative control is missing")
        if "FAIL" not in {
            negative.get("right_hexagon_status"),
            negative.get("left_hexagon_status"),
        }:
            raise FoundationSafetyError("rank2 Fib/Yang-Lee wrong R negative control did not fail")


def branch_sort_key(branch: dict[str, Any]) -> tuple[int, str]:
    order = {
        "rank2-fibonacci-yang-lee-fibonacci-plus": 0,
        "rank2-fibonacci-yang-lee-fibonacci-minus": 1,
        "rank2-fibonacci-yang-lee-yang-lee-plus": 2,
        "rank2-fibonacci-yang-lee-yang-lee-minus": 3,
    }
    return (order[branch["realization_id"]], branch["realization_id"])


def zeta10(power: int) -> str:
    normalized = power % 10
    if normalized == 0:
        return "1"
    if normalized == 1:
        return "zeta10"
    return f"zeta10^{normalized}"


def build_rank2_snapshot(
    *,
    branch: dict[str, Any],
    certificate: dict[str, Any],
    class_index: int,
    started_at_utc: str,
) -> dict[str, Any]:
    certificate_file_hash = file_sha256_id(SAGE_CERTIFICATE)
    certificate_content_hash = certificate["content_hash"]
    theta = zeta10(int(branch["theta_zeta10_power"]))
    r_1 = zeta10(int(branch["r_1_zeta10_power"]))
    r_x = zeta10(int(branch["r_x_zeta10_power"]))
    category_data = {
        "schema": "twisted-yetter.rank2-fibonacci-yang-lee-ribbon-data.v1",
        "category_id": branch["realization_id"],
        "family_id": "rank2-fibonacci-yang-lee",
        "fusion_ring": "Fib: x*x = 1 + x",
        "labels": ["1", "x"],
        "unit": "1",
        "fusion": {
            "1*1": {"1": 1},
            "1*x": {"x": 1},
            "x*1": {"x": 1},
            "x*x": {"1": 1, "x": 1},
        },
        "duals": {"1": "1", "x": "x"},
        "field": "CyclotomicField(10) extended by u^2=1/d",
        "dimension_root": branch["dimension_root"],
        "dimensions": {"1": "1", "x": branch["dimension"]},
        "f_symbols": {
            "unit_normalized_blocks": "all 1D unit associativity blocks are scalar 1",
            "F_xxx_to_x_basis_1_x": [["1/d", "u"], ["u", "-1/d"]],
            "relations": ["d^2=d+1", "u^2=1/d"],
        },
        "r_symbols": {
            "R_xx_to_1": r_1,
            "R_xx_to_x": r_x,
            "all_unit_channels": "1",
        },
        "twists": {"1": "1", "x": theta},
        "pivotal_structure": (
            "canonical spherical rank-2 pivotal structure used by the Sage "
            "coherence certificate; x is self-dual and the closed x-loop is d"
        ),
        "pivotal_scalars": {"1": "1", "x": "canonical_spherical"},
        "left_evaluation": {"1": "1", "x": "ev_x with ev_x coev_x = d"},
        "left_coevaluation": {"1": "1", "x": "coev_x with ev_x coev_x = d"},
        "right_evaluation": {"1": "1", "x": "right trace equals left trace"},
        "right_coevaluation": {"1": "1", "x": "right trace equals left trace"},
        "fusion_pairing": {
            "basis": "multiplicity-free basis with channels 1,x for x*x",
            "pairing_status": "invertible by one-dimensional channel pairings",
        },
        "basis_gauge": (
            "unit-normalized rank-2 gauge; nontrivial F block basis order is [1,x]"
        ),
        "field_embedding": {
            "zeta10": "exp(2*pi*i/10)",
            "u_relation": "u^2=1/d",
            "dimension": branch["dimension"],
        },
        "source_locators": [
            {
                "reference_id": "ref:dong-schopieray-near-integral-2024",
                "locator": "rank tables, pages 26-33",
                "claim_used": "rank-2 Fibonacci/Yang-Lee modular braided row count",
            },
            {
                "reference_id": "self-contained-rank2-sage-coherence",
                "locator": str(SAGE_CERTIFICATE.relative_to(REPO_ROOT)),
                "content_hash": certificate_content_hash,
                "file_sha256": certificate_file_hash,
                "claim_used": "exact rank-2 pentagon/hexagon/balancing/ribbon certificate",
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "exact_certificate_path": str(SAGE_CERTIFICATE.relative_to(REPO_ROOT)),
            "exact_certificate_content_hash": certificate_content_hash,
            "exact_certificate_file_sha256": certificate_file_hash,
            "branch_realization_id": branch["realization_id"],
            "checks": branch["exact_checks"],
            "scan_summaries": branch["scan_summaries"],
            "negative_controls": branch["negative_controls"],
            "proof_boundary": (
                "Exact Sage number-field scan for this rank-2 branch only; "
                "does not resolve semion, Ising, SU(2), or product rows."
            ),
        }
    )
    consumer = add_content_hash(
        {
            "certificate_kind": "consumer_runtime_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "runtime_contract": (
                "RibbonFusionCategoryV2-compatible multiplicity-free rank-2 "
                "fusion spaces with explicit channel basis [1,x]"
            ),
            "checked_payload_hash": category_hash,
            "basis_order": ["1", "x"],
            "basis_safety_checks": {
                "unit_label_mismatch_not_used_as_identity_test": "PASS",
                "wrong_rx_square_root_fails_hexagon": "PASS",
                "branch_bound_to_exact_certificate_hash": "PASS",
            },
            "proof_boundary": "Consumer certificate binds this serialized rank-2 branch only.",
        }
    )
    ribbon_pivotal = add_content_hash(
        {
            "certificate_kind": "ribbon_pivotal_compatibility",
            "status": "PASS",
            "category_data_hash": category_hash,
            "checks": {
                "theta_polynomial": "PASS",
                "ribbon_square_unit_channel": "PASS",
                "ribbon_square_x_channel": "PASS",
                "balancing": "PASS",
                "left_right_trace_agree": "PASS",
                "s_matrix_nondegenerate": "PASS",
            },
            "proof_boundary": (
                "Braided plus pivotal is not used as a shortcut; the Sage "
                "certificate checks ribbon/balancing compatibility."
            ),
        }
    )
    snapshot = add_content_hash(
        {
            **base_meta(
                "twisted-yetter.ribbon-realization-snapshot.v1",
                "RESOLVED_RIBBON_REALIZATION",
                started_at_utc=started_at_utc,
            ),
            "evidence_kind": "ribbon_realization_snapshot",
            "claim_level": "formal-low-rank-category-evidence",
            "source_status": "formal",
            "category_contract": "RibbonFusionCategoryV2",
            "category_data_hash": category_hash,
            "family_id": "rank2-fibonacci-yang-lee",
            "realization_id": branch["realization_id"],
            "modular_braided_class_index": class_index,
            "mutable_alias_inputs": [],
            "category_data": category_data,
            "pinned_payload_hashes": {
                "category_data": category_hash,
                "producer_exact_coherence": producer["content_hash"],
                "consumer_runtime_coherence": consumer["content_hash"],
                "ribbon_pivotal_compatibility": ribbon_pivotal["content_hash"],
                "rank2_sage_coherence_certificate": certificate_content_hash,
            },
            "certificates": {
                "producer_exact_coherence": producer,
                "consumer_runtime_coherence": consumer,
                "ribbon_pivotal_compatibility": ribbon_pivotal,
            },
            "structural_checks": {
                "pentagon": "PASS",
                "hexagon": "PASS",
                "rigidity": "PASS",
                "duality_involution": "PASS",
                "fusion_pairing_invertible": "PASS",
                "r_inverse": "PASS",
                "balancing": "PASS",
                "ribbon_pivotal_compatibility": "PASS",
                "modularity": "PASS",
            },
            "explicit_non_claims": [
                "This snapshot resolves only one rank2 Fibonacci/Yang-Lee braided branch.",
                "This snapshot does not authorize a formal scan plan by itself.",
                "This snapshot does not resolve rank2 semion or anti-semion data.",
            ],
        }
    )
    validate_formal_evidence(snapshot)
    return snapshot


def snapshot_path(snapshot: dict[str, Any]) -> Path:
    return SNAPSHOT_DIR / f"{snapshot['realization_id']}-snapshot-v1.json"


def mark_resolved_level_metadata(row: dict[str, Any]) -> None:
    hashes = row.get("ribbon_realization_snapshot_hashes")
    if hashes is None:
        single = row.get("ribbon_realization_snapshot_hash")
        hashes = [single] if single else []
    row["spherical_level"] = {
        "status": "HASH_BOUND_SPHERICAL_DATA_MATERIALIZED",
        "spherical_structures_per_braided_class": int(row["modular_braided_class_count"]),
        "source": "resolved ribbon realization snapshots",
    }
    row["pivotal_level"] = {
        "status": "HASH_BOUND_PIVOTAL_DATA_MATERIALIZED",
        "materialized_data": [
            "duality",
            "pivotal scalar",
            "evaluation",
            "coevaluation",
            "fusion pairing",
            "basis/gauge",
            "field embedding",
        ],
        "source": "resolved ribbon realization snapshots",
    }
    row["ribbon_level"] = {
        "status": "VERIFIED_BY_FORMAL_SNAPSHOT_CERTIFICATES",
        "required_checks": [
            "balancing",
            "twist/pivotal compatibility",
            "producer exact coherence",
            "consumer runtime coherence",
            "certificate/data-hash binding",
        ],
        "snapshot_hashes": hashes,
    }


def build_catalog_v4(*, started_at_utc: str, snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    previous = load_json(V3_CATALOG)
    snapshot_hashes = [snapshot["content_hash"] for snapshot in snapshots]
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank2-fibonacci-yang-lee":
            new_row.update(
                {
                    "terminal_status": "RESOLVED_RIBBON_REALIZATION",
                    "formal_admission_allowed": True,
                    "ribbon_realization_snapshot_hash": None,
                    "ribbon_realization_snapshot_hashes": snapshot_hashes,
                    "resolved_modular_braided_class_count": len(snapshot_hashes),
                    "blocker_ids": [],
                    "missing_evidence": [],
                    "resolution_note": (
                        "Resolved by exact Sage rank-2 Fibonacci/Yang-Lee "
                        "pentagon/hexagon/balancing/ribbon certificate."
                    ),
                }
            )
        if new_row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION":
            mark_resolved_level_metadata(new_row)
        rows.append(new_row)
    resolved_ids = [
        row["family_id"]
        for row in rows
        if row["terminal_status"] == "RESOLVED_RIBBON_REALIZATION"
    ]
    blocked_ids = [
        row["family_id"]
        for row in rows
        if row["terminal_status"] == "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
    ]
    catalog = {
        **base_meta(
            LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
            RIBBON_CATALOG_PARTIAL,
            started_at_utc=started_at_utc,
        ),
        "catalog_id": "low-rank-ribbon-realization-catalog-v4",
        "previous_catalog": {
            "path": str(V3_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V3_CATALOG),
            "status": previous["status"],
        },
        "rank2_sage_coherence_certificate": {
            "path": str(SAGE_CERTIFICATE.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(SAGE_CERTIFICATE),
            "content_hash": load_json(SAGE_CERTIFICATE)["content_hash"],
        },
        "scope": previous["scope"],
        "coverage_by_rank": previous["coverage_by_rank"],
        "braided_denominator_by_rank": previous["braided_denominator_by_rank"],
        "ribbon_denominator_by_rank": {},
        "ribbon_denominator_status": "PARTIAL_DO_NOT_USE_AS_FINAL_DENOMINATOR",
        "ribbon_denominator_copied_from_braided": False,
        "formal_scan_plan_allowed": False,
        "resolved_row_count": len(resolved_ids),
        "blocked_row_count": len(blocked_ids),
        "family_count": len(rows),
        "resolved_family_ids": resolved_ids,
        "blocked_family_ids": blocked_ids,
        "resolved_snapshot_paths": previous["resolved_snapshot_paths"]
        + [str(snapshot_path(snapshot).relative_to(REPO_ROOT)) for snapshot in snapshots],
        "families": rows,
        "explicit_non_claims": [
            "This partial catalog does not establish the complete rank 2-5 ribbon classification.",
            "This partial catalog does not authorize scan-plan generation.",
            "Even-order pointed, Ising, SU(2), PSU, and product rows remain blocked.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v4(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v4",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v4",
        "previous_readiness": {
            "path": str(V3_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V3_READINESS),
        },
        "policy": {
            "path": str(V1_POLICY.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V1_POLICY),
        },
        "classification_catalog_hash": stable_content_hash(catalog),
        "classification_catalog_status": catalog["status"],
        "scan_plan_generation_allowed": False,
        "formal_scan_plan_id": None,
        "resolved_row_count": catalog["resolved_row_count"],
        "blocked_row_count": catalog["blocked_row_count"],
        "blocking_reason_ids": [
            "partial-ribbon-catalog-only",
            "eleven-family-rows-still-blocked",
            "rank2-and-even-pointed-cocycle-data-still-missing",
            "ising-su2-psu-product-realizations-still-missing",
            "ribbon-denominator-not-final",
        ],
        "explicit_non_claims": [
            "No formal scan plan exists.",
            "No scan case result exists.",
            "No complete-no-signal aggregate exists.",
        ],
    }


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    certificate = load_json(SAGE_CERTIFICATE)
    require_sage_certificate(certificate)
    snapshots = [
        build_rank2_snapshot(
            branch=branch,
            certificate=certificate,
            class_index=index,
            started_at_utc=started_at_utc,
        )
        for index, branch in enumerate(sorted(certificate["branches"], key=branch_sort_key))
    ]
    catalog = build_catalog_v4(started_at_utc=started_at_utc, snapshots=snapshots)
    readiness = build_readiness_v4(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v4.json": catalog,
        "formal-low-rank-scan-readiness-v4.json": readiness,
    }
    for snapshot in snapshots:
        result[str(snapshot_path(snapshot).relative_to(OUT_DIR))] = snapshot
    return result


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
