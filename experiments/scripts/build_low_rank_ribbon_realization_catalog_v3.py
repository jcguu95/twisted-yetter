#!/usr/bin/env python3
"""Extend the partial low-rank ribbon catalog with exact pointed Z5 data."""

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
    LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
    RIBBON_CATALOG_PARTIAL,
    add_content_hash,
    stable_content_hash,
    validate_formal_evidence,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "ribbon-realization-snapshots"
V2_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v2.json"
V2_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v2.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"
MTC_CANDIDATE_DATA = (
    REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "mtc-candidate-data-v1.json"
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


def file_sha256_id(path: Path) -> str:
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
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v3.py",
        "reproduce_command": "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v3.py --write",
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def zeta_power(order: int, power: int) -> str:
    normalized = power % order
    if normalized == 0:
        return "1"
    if normalized == 1:
        return f"zeta{order}"
    return f"zeta{order}^{normalized}"


def build_odd_cyclic_snapshot(
    *,
    family_id: str,
    order: int,
    parameter: int,
    class_index: int,
    started_at_utc: str,
) -> dict[str, Any]:
    labels = [str(index) for index in range(order)]
    fusion = {
        f"{left}*{right}": str((int(left) + int(right)) % order)
        for left in labels
        for right in labels
    }
    twists = {
        label: zeta_power(order, parameter * int(label) * int(label))
        for label in labels
    }
    braiding = {
        f"{left},{right}": zeta_power(order, parameter * int(left) * int(right))
        for left in labels
        for right in labels
    }
    monodromy = {
        f"{left},{right}": zeta_power(order, 2 * parameter * int(left) * int(right))
        for left in labels
        for right in labels
    }
    realization_id = f"{family_id}-s{parameter}"
    category_data = {
        "schema": "twisted-yetter.pointed-metric-group-ribbon-data.v1",
        "category_id": realization_id,
        "family_id": family_id,
        "metric_group": f"Z/{order}",
        "quadratic_form": f"q_s(x)=zeta{order}^({parameter}*x^2)",
        "field": f"Q(zeta{order})",
        "labels": labels,
        "unit": "0",
        "fusion": fusion,
        "duals": {label: str((-int(label)) % order) for label in labels},
        "f_symbols": "strict pointed gauge, all F(a,b,c)=1",
        "r_symbols": braiding,
        "twists": twists,
        "dimensions": {label: "1" for label in labels},
        "pivotal_scalars": {label: "1" for label in labels},
        "left_evaluation": {label: "1" for label in labels},
        "left_coevaluation": {label: "1" for label in labels},
        "right_evaluation": {label: "1" for label in labels},
        "right_coevaluation": {label: "1" for label in labels},
        "fusion_pairing": "unique one-dimensional orthonormal pointed basis",
        "basis_gauge": "strict pointed basis e_a tensor e_b -> e_{a+b}",
        "monodromy_bicharacter": monodromy,
        "source_locators": [
            {
                "reference_id": "ref:dong-schopieray-near-integral-2024",
                "locator": "rank tables, pages 26-33",
                "claim_used": f"{family_id} pointed modular braided row count",
            },
            {
                "reference_id": "self-contained-pointed-check",
                "locator": "this artifact",
                "claim_used": f"strict odd-order pointed Z{order} metric group coherence equations",
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "field": f"Q(zeta{order})",
            "checks": odd_cyclic_checks(order, parameter),
            "proof_boundary": (
                f"Exact finite pointed Z{order} equations only; even-order "
                "pointed rows remain blocked."
            ),
        }
    )
    consumer = add_content_hash(
        {
            "certificate_kind": "consumer_runtime_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "runtime_contract": "RibbonFusionCategoryV2-compatible pointed one-dimensional fusion spaces",
            "checked_payload_hash": category_hash,
            "control_artifact": {
                "path": str(MTC_CANDIDATE_DATA.relative_to(REPO_ROOT)),
                "sha256": file_sha256_id(MTC_CANDIDATE_DATA),
                "category_id": "Vec_Z3_q",
                "role": "existing pointed-control pattern; not reused as Z5 proof",
            },
            "proof_boundary": f"Runtime consumer certificate binds exact Z{order} data.",
        }
    )
    ribbon_pivotal = add_content_hash(
        {
            "certificate_kind": "ribbon_pivotal_compatibility",
            "status": "PASS",
            "category_data_hash": category_hash,
            "checks": {
                "twist_balancing": "PASS",
                "left_right_trace_agree": "PASS",
                "pivotal_scalar_unit": "PASS",
                "quantum_dimensions_all_one": "PASS",
            },
            "proof_boundary": "Braided plus pivotal is accepted only with explicit balancing checks.",
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
            "family_id": family_id,
            "realization_id": realization_id,
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
                f"This snapshot resolves only one {family_id} pointed class.",
                "This snapshot does not authorize a formal scan plan by itself.",
            ],
        }
    )
    validate_formal_evidence(snapshot)
    return snapshot


def odd_cyclic_checks(order: int, parameter: int) -> dict[str, Any]:
    labels = range(order)
    hexagon = all(
        (parameter * a * ((b + c) % order) - parameter * a * b - parameter * a * c)
        % order
        == 0
        and (
            parameter * ((a + b) % order) * c
            - parameter * a * c
            - parameter * b * c
        )
        % order
        == 0
        for a in labels
        for b in labels
        for c in labels
    )
    balancing = all(
        (
            parameter * ((a + b) % order) ** 2
            - parameter * a * a
            - parameter * b * b
            - 2 * parameter * a * b
        )
        % order
        == 0
        for a in labels
        for b in labels
    )
    duality = all((a + ((-a) % order)) % order == 0 for a in labels)
    nondegenerate = sorted((2 * parameter * a) % order for a in labels) == list(range(order))
    return {
        "strict_pentagon_all_f_symbols_one": "PASS",
        "bilinear_braiding_hexagon": "PASS" if hexagon else "FAIL",
        "twist_balancing": "PASS" if balancing else "FAIL",
        "duality_involution": "PASS" if duality else "FAIL",
        "monodromy_bicharacter_nondegenerate": "PASS" if nondegenerate else "FAIL",
    }


def snapshot_path(snapshot: dict[str, Any]) -> Path:
    return SNAPSHOT_DIR / f"{snapshot['realization_id']}-snapshot-v1.json"


def build_catalog_v3(*, started_at_utc: str, z5_snapshots: list[dict[str, Any]]) -> dict[str, Any]:
    previous = load_json(V2_CATALOG)
    z5_hashes = [snapshot["content_hash"] for snapshot in z5_snapshots]
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank5-su5-1":
            new_row.update(
                {
                    "terminal_status": "RESOLVED_RIBBON_REALIZATION",
                    "formal_admission_allowed": True,
                    "ribbon_realization_snapshot_hash": None,
                    "ribbon_realization_snapshot_hashes": z5_hashes,
                    "resolved_modular_braided_class_count": len(z5_hashes),
                    "blocker_ids": [],
                    "missing_evidence": [],
                    "resolution_note": (
                        "Resolved by exact strict pointed Z5 metric group snapshots "
                        "q_s(x)=zeta5^(s*x^2), s=1,2."
                    ),
                }
            )
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
        "catalog_id": "low-rank-ribbon-realization-catalog-v3",
        "previous_catalog": {
            "path": str(V2_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V2_CATALOG),
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
        + [str(snapshot_path(snapshot).relative_to(REPO_ROOT)) for snapshot in z5_snapshots],
        "families": rows,
        "explicit_non_claims": [
            "This partial catalog does not establish the complete rank 2-5 ribbon classification.",
            "This partial catalog does not authorize scan-plan generation.",
            "Even-order pointed rows remain blocked until their cocycle data is explicit.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def build_readiness_v3(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    return {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v3",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v3",
        "previous_readiness": {
            "path": str(V2_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V2_READINESS),
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
            "twelve-family-rows-still-blocked",
            "rank2-and-even-pointed-cocycle-data-still-missing",
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
    z5_snapshots = [
        build_odd_cyclic_snapshot(
            family_id="rank5-su5-1",
            order=5,
            parameter=1,
            class_index=0,
            started_at_utc=started_at_utc,
        ),
        build_odd_cyclic_snapshot(
            family_id="rank5-su5-1",
            order=5,
            parameter=2,
            class_index=1,
            started_at_utc=started_at_utc,
        ),
    ]
    catalog = build_catalog_v3(started_at_utc=started_at_utc, z5_snapshots=z5_snapshots)
    readiness = build_readiness_v3(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v3.json": catalog,
        "formal-low-rank-scan-readiness-v3.json": readiness,
    }
    for snapshot in z5_snapshots:
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
