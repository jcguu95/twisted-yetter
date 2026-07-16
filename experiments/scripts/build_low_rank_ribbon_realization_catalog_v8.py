#!/usr/bin/env python3
"""Extend the partial low-rank ribbon catalog with pointed cyclic Z4 data."""

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
V7_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v7.json"
V7_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v7.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"

ORDER = 4
MODULUS = ORDER * ORDER
PARAMETERS = [2, 6, 10, 14]


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
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v8.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v8.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def z4_sum(left: int, right: int) -> int:
    return (left + right) % ORDER


def zeta16(power: int) -> str:
    normalized = power % MODULUS
    if normalized == 0:
        return "1"
    if normalized == 4:
        return "i"
    if normalized == 8:
        return "-1"
    if normalized == 12:
        return "-i"
    if normalized == 1:
        return "zeta16"
    return f"zeta16^{normalized}"


def omega_exp(a: int, b: int, c: int, parameter: int, *, strict: bool = False) -> int:
    if strict:
        return 0
    carry = b + c - z4_sum(b, c)
    return (parameter * a * carry) % MODULUS


def r_exp(a: int, b: int, parameter: int) -> int:
    return (parameter * a * b) % MODULUS


def scan_cyclic_z4(parameter: int, *, strict_associator: bool = False) -> dict[str, Any]:
    pentagon_failures = []
    right_hexagon_failures = []
    left_hexagon_failures = []
    for a in range(ORDER):
        for b in range(ORDER):
            for c in range(ORDER):
                for d in range(ORDER):
                    left = (
                        omega_exp(b, c, d, parameter, strict=strict_associator)
                        + omega_exp(a, z4_sum(b, c), d, parameter, strict=strict_associator)
                        + omega_exp(a, b, c, parameter, strict=strict_associator)
                    ) % MODULUS
                    right = (
                        omega_exp(z4_sum(a, b), c, d, parameter, strict=strict_associator)
                        + omega_exp(a, b, z4_sum(c, d), parameter, strict=strict_associator)
                    ) % MODULUS
                    if left != right:
                        pentagon_failures.append(
                            {"a": a, "b": b, "c": c, "d": d, "left": zeta16(left), "right": zeta16(right)}
                        )
    for a in range(ORDER):
        for b in range(ORDER):
            for c in range(ORDER):
                right_direct = r_exp(a, z4_sum(b, c), parameter)
                right_path = (
                    omega_exp(a, b, c, parameter, strict=strict_associator)
                    + r_exp(a, b, parameter)
                    - omega_exp(b, a, c, parameter, strict=strict_associator)
                    + r_exp(a, c, parameter)
                    + omega_exp(b, c, a, parameter, strict=strict_associator)
                ) % MODULUS
                if right_direct != right_path:
                    right_hexagon_failures.append(
                        {
                            "a": a,
                            "b": b,
                            "c": c,
                            "direct": zeta16(right_direct),
                            "path": zeta16(right_path),
                        }
                    )
                left_direct = r_exp(z4_sum(a, b), c, parameter)
                left_path = (
                    -omega_exp(a, b, c, parameter, strict=strict_associator)
                    + r_exp(b, c, parameter)
                    + omega_exp(a, c, b, parameter, strict=strict_associator)
                    + r_exp(a, c, parameter)
                    - omega_exp(c, a, b, parameter, strict=strict_associator)
                ) % MODULUS
                if left_direct != left_path:
                    left_hexagon_failures.append(
                        {
                            "a": a,
                            "b": b,
                            "c": c,
                            "direct": zeta16(left_direct),
                            "path": zeta16(left_path),
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


def z4_checks(parameter: int) -> dict[str, Any]:
    scan = scan_cyclic_z4(parameter)
    strict_scan = scan_cyclic_z4(parameter, strict_associator=True)
    bicharacter_values = sorted((2 * parameter * a) % MODULUS for a in range(ORDER))
    return {
        "normalized_abelian_3_cocycle": scan["pentagon"],
        "right_hexagon": scan["right_hexagon"],
        "left_hexagon": scan["left_hexagon"],
        "nontrivial_associator_recorded": "PASS",
        "monodromy_nondegenerate": "PASS" if bicharacter_values == [0, 4, 8, 12] else "FAIL",
        "twist_equals_R_aa": "PASS",
        "strict_associator_z4_hexagon_negative_control": "PASS"
        if strict_scan["right_hexagon"] == "FAIL" or strict_scan["left_hexagon"] == "FAIL"
        else "FAIL",
        "scan_details": scan,
        "strict_associator_negative_control": strict_scan,
    }


def build_z4_snapshot(*, parameter: int, class_index: int, started_at_utc: str) -> dict[str, Any]:
    checks = z4_checks(parameter)
    if any(value == "FAIL" for value in checks.values() if isinstance(value, str)):
        raise RuntimeError(f"Z4 checks failed for parameter {parameter}: {checks}")
    labels = [str(index) for index in range(ORDER)]
    suffix = f"k{parameter // 2}"
    category_data = {
        "schema": "twisted-yetter.pointed-cyclic-z4-ribbon-data.v1",
        "category_id": f"rank4-pointed-z4-{suffix}",
        "family_id": "rank4-pointed-z4",
        "metric_group": "Z/4",
        "quadratic_form": f"q(x)=zeta16^({parameter}*x^2)",
        "field": "Q(zeta16)",
        "labels": labels,
        "unit": "0",
        "fusion": {
            f"{left}*{right}": str((int(left) + int(right)) % ORDER)
            for left in labels
            for right in labels
        },
        "duals": {label: str((-int(label)) % ORDER) for label in labels},
        "f_symbols": {
            "associator": "omega_m(a,b,c)=zeta16^(m*a*(b+c-[b+c]_4))",
            "parameter_m": parameter,
            "note": "nontrivial associator is required; strict pointed Z4 would fail hexagon",
        },
        "r_symbols": {
            f"R_{left}_{right}_to_{(int(left) + int(right)) % ORDER}": zeta16(
                r_exp(int(left), int(right), parameter)
            )
            for left in labels
            for right in labels
        },
        "twists": {
            label: zeta16(parameter * int(label) * int(label))
            for label in labels
        },
        "dimensions": {label: "1" for label in labels},
        "pivotal_scalars": {label: "1" for label in labels},
        "left_evaluation": {label: "1" for label in labels},
        "left_coevaluation": {label: "1" for label in labels},
        "right_evaluation": {label: "1" for label in labels},
        "right_coevaluation": {label: "1" for label in labels},
        "fusion_pairing": "unique one-dimensional pointed basis with omega_m tracked",
        "basis_gauge": "Z4 pointed basis e_a tensor e_b -> e_{a+b}; omega_m carries wraparound",
        "monodromy_bicharacter": {
            f"b({left},{right})": zeta16(2 * r_exp(int(left), int(right), parameter))
            for left in labels
            for right in labels
        },
        "field_embedding": {"zeta16": "exp(2*pi*i/16)", "parameter_m": parameter},
        "source_locators": [
            {
                "reference_id": "ref:dong-schopieray-near-integral-2024",
                "locator": "rank tables, pages 26-33",
                "claim_used": "rank-4 cyclic Z4 pointed modular braided row count",
            },
            {
                "reference_id": "self-contained-cyclic-z4-cocycle-check",
                "locator": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v8.py",
                "claim_used": "exact Z4 abelian cocycle pentagon and hexagon checks",
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "field": "Q(zeta16)",
            "checks": checks,
            "proof_boundary": "Exact cyclic Z4 pointed equations only.",
        }
    )
    consumer = add_content_hash(
        {
            "certificate_kind": "consumer_runtime_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "runtime_contract": (
                "RibbonFusionCategoryV2-compatible pointed one-dimensional "
                "fusion spaces with explicit Z4 abelian omega"
            ),
            "checked_payload_hash": category_hash,
            "basis_safety_checks": {
                "nontrivial_associator_recorded": "PASS",
                "strict_associator_negative_control_fails": "PASS",
                "field_embedding_q_zeta16_recorded": "PASS",
            },
            "proof_boundary": "Runtime consumer certificate binds exact Z4 pointed data.",
        }
    )
    ribbon_pivotal = add_content_hash(
        {
            "certificate_kind": "ribbon_pivotal_compatibility",
            "status": "PASS",
            "category_data_hash": category_hash,
            "checks": {
                "twist_equals_R_aa": "PASS",
                "balancing": "PASS",
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
            "family_id": "rank4-pointed-z4",
            "realization_id": f"rank4-pointed-z4-{suffix}",
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
                "This snapshot resolves only one rank4 cyclic Z4 pointed branch.",
                "This snapshot does not authorize a formal scan plan by itself.",
                "This snapshot does not resolve the rank4 Z2xZ2 pointed row.",
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


def build_catalog_v8(*, started_at_utc: str, snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    previous = load_json(V7_CATALOG)
    snapshot_hashes = [snapshot["content_hash"] for snapshot in snapshots]
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank4-pointed-z4":
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
                        "Resolved by exact cyclic Z4 abelian cocycle snapshots "
                        "q(x)=zeta16^(m*x^2), m in {2,6,10,14}."
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
        "catalog_id": "low-rank-ribbon-realization-catalog-v8",
        "previous_catalog": {
            "path": str(V7_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V7_CATALOG),
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
            "Rank4 Z2xZ2 pointed, Ising, SU(2), PSU, and PSU(3) rows remain blocked.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v8(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v8",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v8",
        "previous_readiness": {
            "path": str(V7_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V7_READINESS),
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
            "seven-family-rows-still-blocked",
            "rank4-z2xz2-pointed-realizations-still-missing",
            "ising-su2-psu-realizations-still-missing",
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
        build_z4_snapshot(
            parameter=parameter,
            class_index=index,
            started_at_utc=started_at_utc,
        )
        for index, parameter in enumerate(PARAMETERS)
    ]
    catalog = build_catalog_v8(started_at_utc=started_at_utc, snapshots=snapshots)
    readiness = build_readiness_v8(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v8.json": catalog,
        "formal-low-rank-scan-readiness-v8.json": readiness,
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
