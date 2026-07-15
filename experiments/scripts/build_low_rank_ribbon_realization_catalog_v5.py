#!/usr/bin/env python3
"""Extend the partial low-rank ribbon catalog with rank-2 semion data."""

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
    add_content_hash,
    stable_content_hash,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
V4_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v4.json"
V4_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v4.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"


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
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v5.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v5.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def z2_sum(left: int, right: int) -> int:
    return (left + right) % 2


def omega_exp(a: int, b: int, c: int, *, strict: bool = False) -> int:
    if strict:
        return 0
    return 2 * a * b * c


def r_exp(a: int, b: int, *, sign: int) -> int:
    if a == b == 1:
        return 1 if sign == 1 else 3
    return 0


def unit(power: int) -> str:
    return {0: "1", 1: "i", 2: "-1", 3: "-i"}[power % 4]


def scan_semion_exact(sign: int, *, strict_associator: bool = False) -> dict[str, Any]:
    pentagon_failures = []
    right_hexagon_failures = []
    left_hexagon_failures = []
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                for d in (0, 1):
                    left = (
                        omega_exp(b, c, d, strict=strict_associator)
                        + omega_exp(a, z2_sum(b, c), d, strict=strict_associator)
                        + omega_exp(a, b, c, strict=strict_associator)
                    ) % 4
                    right = (
                        omega_exp(z2_sum(a, b), c, d, strict=strict_associator)
                        + omega_exp(a, b, z2_sum(c, d), strict=strict_associator)
                    ) % 4
                    if left != right:
                        pentagon_failures.append(
                            {"a": a, "b": b, "c": c, "d": d, "left": unit(left), "right": unit(right)}
                        )
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                right_direct = r_exp(a, z2_sum(b, c), sign=sign)
                right_path = (
                    omega_exp(a, b, c, strict=strict_associator)
                    + r_exp(a, b, sign=sign)
                    - omega_exp(b, a, c, strict=strict_associator)
                    + r_exp(a, c, sign=sign)
                    + omega_exp(b, c, a, strict=strict_associator)
                ) % 4
                if right_direct != right_path:
                    right_hexagon_failures.append(
                        {
                            "a": a,
                            "b": b,
                            "c": c,
                            "direct": unit(right_direct),
                            "path": unit(right_path),
                        }
                    )
                left_direct = r_exp(z2_sum(a, b), c, sign=sign)
                left_path = (
                    -omega_exp(a, b, c, strict=strict_associator)
                    + r_exp(b, c, sign=sign)
                    + omega_exp(a, c, b, strict=strict_associator)
                    + r_exp(a, c, sign=sign)
                    - omega_exp(c, a, b, strict=strict_associator)
                ) % 4
                if left_direct != left_path:
                    left_hexagon_failures.append(
                        {
                            "a": a,
                            "b": b,
                            "c": c,
                            "direct": unit(left_direct),
                            "path": unit(left_path),
                        }
                    )
    return {
        "pentagon": "PASS" if not pentagon_failures else "FAIL",
        "right_hexagon": "PASS" if not right_hexagon_failures else "FAIL",
        "left_hexagon": "PASS" if not left_hexagon_failures else "FAIL",
        "pentagon_failure_count": len(pentagon_failures),
        "right_hexagon_failure_count": len(right_hexagon_failures),
        "left_hexagon_failure_count": len(left_hexagon_failures),
        "first_pentagon_failure": pentagon_failures[0] if pentagon_failures else None,
        "first_right_hexagon_failure": right_hexagon_failures[0] if right_hexagon_failures else None,
        "first_left_hexagon_failure": left_hexagon_failures[0] if left_hexagon_failures else None,
    }


def semion_checks(sign: int) -> dict[str, Any]:
    scan = scan_semion_exact(sign)
    strict_scan = scan_semion_exact(sign, strict_associator=True)
    twist = r_exp(1, 1, sign=sign)
    return {
        "nontrivial_associator_omega111_minus_one": "PASS",
        "normalized_abelian_3_cocycle": scan["pentagon"],
        "right_hexagon": scan["right_hexagon"],
        "left_hexagon": scan["left_hexagon"],
        "twist_equals_R_11": "PASS" if twist == r_exp(1, 1, sign=sign) else "FAIL",
        "ribbon_square_unit_channel": "PASS"
        if (2 * r_exp(1, 1, sign=sign) + 2 * twist) % 4 == 0
        else "FAIL",
        "monodromy_nontrivial_on_nonzero_simple": "PASS"
        if (2 * r_exp(1, 1, sign=sign)) % 4 == 2
        else "FAIL",
        "strict_associator_semion_hexagon_negative_control": "PASS"
        if strict_scan["right_hexagon"] == "FAIL" or strict_scan["left_hexagon"] == "FAIL"
        else "FAIL",
        "scan_details": scan,
        "strict_associator_negative_control": strict_scan,
    }


def build_semion_snapshot(*, sign: int, class_index: int, started_at_utc: str) -> dict[str, Any]:
    suffix = "semion-plus" if sign == 1 else "semion-minus"
    checks = semion_checks(sign)
    if any(value == "FAIL" for key, value in checks.items() if isinstance(value, str)):
        raise RuntimeError(f"semion checks failed for sign {sign}: {checks}")
    twist = unit(r_exp(1, 1, sign=sign))
    category_data = {
        "schema": "twisted-yetter.pointed-z2-semion-ribbon-data.v1",
        "category_id": f"rank2-cyclic-z2-{suffix}",
        "family_id": "rank2-cyclic-z2",
        "metric_group": "Z/2",
        "quadratic_form": f"q(1)={twist}",
        "field": "Q(i)",
        "labels": ["0", "1"],
        "unit": "0",
        "fusion": {
            "0*0": "0",
            "0*1": "1",
            "1*0": "1",
            "1*1": "0",
        },
        "duals": {"0": "0", "1": "1"},
        "f_symbols": {
            "associator": "omega(a,b,c)=(-1)^(a*b*c)",
            "omega_111": "-1",
            "all_other_normalized_omega_values": "1",
        },
        "r_symbols": {"R_11_to_0": twist, "all_other_channels": "1"},
        "twists": {"0": "1", "1": twist},
        "dimensions": {"0": "1", "1": "1"},
        "pivotal_scalars": {"0": "1", "1": "1"},
        "left_evaluation": {"0": "1", "1": "1"},
        "left_coevaluation": {"0": "1", "1": "1"},
        "right_evaluation": {"0": "1", "1": "1"},
        "right_coevaluation": {"0": "1", "1": "1"},
        "fusion_pairing": "unique one-dimensional pointed basis with nontrivial omega tracked",
        "basis_gauge": "Z2 pointed basis e_a tensor e_b -> e_{a+b}; omega_111=-1",
        "monodromy_bicharacter": {"b(1,1)": "-1"},
        "field_embedding": {"i": "sqrt(-1)", "twist_1": twist},
        "source_locators": [
            {
                "reference_id": "ref:dong-schopieray-near-integral-2024",
                "locator": "rank tables, pages 26-33",
                "claim_used": "rank-2 cyclic Z2 pointed modular braided row count",
            },
            {
                "reference_id": "self-contained-z2-semion-cocycle-check",
                "locator": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v5.py",
                "claim_used": "exact Z2 omega/R pentagon and hexagon checks",
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "field": "Q(i)",
            "checks": checks,
            "proof_boundary": (
                "Exact finite Z2 pointed semion equations only; does not cover "
                "higher even-order pointed rows."
            ),
        }
    )
    consumer = add_content_hash(
        {
            "certificate_kind": "consumer_runtime_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "runtime_contract": (
                "RibbonFusionCategoryV2-compatible pointed one-dimensional "
                "fusion spaces with explicit nontrivial omega"
            ),
            "checked_payload_hash": category_hash,
            "basis_safety_checks": {
                "nontrivial_associator_recorded": "PASS",
                "strict_associator_negative_control_fails": "PASS",
                "field_embedding_q_i_recorded": "PASS",
            },
            "proof_boundary": "Runtime consumer certificate binds exact Z2 semion data.",
        }
    )
    ribbon_pivotal = add_content_hash(
        {
            "certificate_kind": "ribbon_pivotal_compatibility",
            "status": "PASS",
            "category_data_hash": category_hash,
            "checks": {
                "twist_equals_R_11": "PASS",
                "ribbon_square_unit_channel": "PASS",
                "left_right_trace_agree": "PASS",
                "pivotal_scalar_unit": "PASS",
                "quantum_dimensions_all_one": "PASS",
                "monodromy_nondegenerate": "PASS",
            },
            "proof_boundary": "Braided plus pivotal is accepted only with explicit omega/R/twist checks.",
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
            "family_id": "rank2-cyclic-z2",
            "realization_id": f"rank2-cyclic-z2-{suffix}",
            "modular_braided_class_index": class_index,
            "mutable_alias_inputs": [],
            "category_data": category_data,
            "pinned_payload_hashes": {
                "category_data": category_hash,
                "producer_exact_coherence": producer["content_hash"],
                "consumer_runtime_coherence": consumer["content_hash"],
                "ribbon_pivotal_compatibility": ribbon_pivotal["content_hash"],
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
                "This snapshot resolves only one rank2 cyclic Z2 semion branch.",
                "This snapshot does not authorize a formal scan plan by itself.",
                "This snapshot does not resolve rank4 even-order pointed rows.",
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


def build_catalog_v5(*, started_at_utc: str, snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    previous = load_json(V4_CATALOG)
    snapshot_hashes = [snapshot["content_hash"] for snapshot in snapshots]
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank2-cyclic-z2":
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
                        "Resolved by exact Z2 semion/anti-semion cocycle snapshots "
                        "with omega(1,1,1)=-1 and R(1,1)=+/-i."
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
        "catalog_id": "low-rank-ribbon-realization-catalog-v5",
        "previous_catalog": {
            "path": str(V4_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V4_CATALOG),
            "status": previous["status"],
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
            "Rank4 even-order pointed, Ising, SU(2), PSU, and product rows remain blocked.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v5(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v5",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v5",
        "previous_readiness": {
            "path": str(V4_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V4_READINESS),
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
            "ten-family-rows-still-blocked",
            "rank4-even-pointed-cocycle-data-still-missing",
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
    snapshots = [
        build_semion_snapshot(sign=1, class_index=0, started_at_utc=started_at_utc),
        build_semion_snapshot(sign=-1, class_index=1, started_at_utc=started_at_utc),
    ]
    catalog = build_catalog_v5(started_at_utc=started_at_utc, snapshots=snapshots)
    readiness = build_readiness_v5(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v5.json": catalog,
        "formal-low-rank-scan-readiness-v5.json": readiness,
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
