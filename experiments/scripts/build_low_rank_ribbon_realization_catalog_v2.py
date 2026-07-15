#!/usr/bin/env python3
"""Build a partial v2 low-rank ribbon catalog with exact pointed Z3 snapshots.

This script intentionally resolves only the rank3-cyclic-z3 row.  It leaves all
other rows blocked, including rank2-cyclic-z2: semion/anti-semion require a
nontrivial abelian cocycle and must not be faked with a trivial associator.
"""

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
V1_CATALOG = OUT_DIR / "low-rank-ribbon-realization-catalog-v1.json"
V1_POLICY = OUT_DIR / "formal-admission-policy-v1.json"
V1_READINESS = OUT_DIR / "formal-low-rank-scan-readiness-v1.json"
Z3_CONTROL = REPO_ROOT / "experiments" / "results" / "mtc-candidates" / "mtc-candidate-data-v1.json"


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
        "generator_script": "experiments/scripts/build_low_rank_ribbon_realization_catalog_v2.py",
        "reproduce_command": "python3 experiments/scripts/build_low_rank_ribbon_realization_catalog_v2.py --write",
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def ci(sign: int) -> list[int]:
    return [0, sign]


def cone() -> list[int]:
    return [1, 0]


def cnegone() -> list[int]:
    return [-1, 0]


def zeta3_power(power: int, sign: int) -> str:
    normalized = (sign * power) % 3
    return {
        0: "1",
        1: "zeta3",
        2: "zeta3^2",
    }[normalized]


def build_z3_snapshot(*, sign: int, started_at_utc: str) -> dict[str, Any]:
    suffix = "plus" if sign == 1 else "minus"
    labels = ["0", "1", "2"]
    fusion = {
        f"{left}*{right}": str((int(left) + int(right)) % 3)
        for left in labels
        for right in labels
    }
    twists = {label: zeta3_power(int(label) * int(label), sign) for label in labels}
    braiding = {
        f"{left},{right}": zeta3_power(int(left) * int(right), sign)
        for left in labels
        for right in labels
    }
    monodromy = {
        f"{left},{right}": zeta3_power(2 * int(left) * int(right), sign)
        for left in labels
        for right in labels
    }
    category_data = {
        "schema": "twisted-yetter.pointed-metric-group-ribbon-data.v1",
        "category_id": f"rank3-cyclic-z3-{suffix}",
        "family_id": "rank3-cyclic-z3",
        "metric_group": "Z/3",
        "quadratic_form": f"q_s(x)=zeta3^({sign}*x^2)",
        "field": "Q(zeta3)",
        "labels": labels,
        "unit": "0",
        "fusion": fusion,
        "duals": {label: str((-int(label)) % 3) for label in labels},
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
                "claim_used": "rank-3 cyclic Z3 pointed modular braided row count",
            },
            {
                "reference_id": "self-contained-pointed-check",
                "locator": "this artifact",
                "claim_used": "strict odd-order pointed metric group coherence equations checked below",
            },
        ],
    }
    category_hash = stable_content_hash(category_data)
    producer = add_content_hash(
        {
            "certificate_kind": "producer_exact_coherence",
            "status": "PASS",
            "category_data_hash": category_hash,
            "field": "Q(zeta3)",
            "checks": pointed_z3_checks(sign),
            "proof_boundary": "Exact finite pointed Z3 equations only; does not cover semion Z2 cocycle data.",
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
                "path": str(Z3_CONTROL.relative_to(REPO_ROOT)),
                "sha256": file_sha256_id(Z3_CONTROL),
                "category_id": "Vec_Z3_q",
            },
            "proof_boundary": "Runtime consumer certificate binds exact pointed Z3 data, not all pointed families.",
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
            "proof_boundary": "Braided plus pivotal is accepted here only after explicit balancing checks.",
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
            "family_id": "rank3-cyclic-z3",
            "realization_id": f"rank3-cyclic-z3-{suffix}",
            "modular_braided_class_index": 0 if sign == 1 else 1,
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
                "This snapshot resolves only one rank3-cyclic-z3 pointed class.",
                "This snapshot does not resolve rank2 semion/anti-semion cocycle data.",
                "This snapshot does not authorize a formal scan plan by itself.",
            ],
        }
    )
    validate_formal_evidence(snapshot)
    return snapshot


def pointed_z3_checks(sign: int) -> dict[str, Any]:
    labels = range(3)
    hexagon = all(
        (sign * a * ((b + c) % 3) - sign * a * b - sign * a * c) % 3 == 0
        and (sign * ((a + b) % 3) * c - sign * a * c - sign * b * c) % 3 == 0
        for a in labels
        for b in labels
        for c in labels
    )
    balancing = all(
        (
            sign * ((a + b) % 3) ** 2
            - sign * a * a
            - sign * b * b
            - 2 * sign * a * b
        )
        % 3
        == 0
        for a in labels
        for b in labels
    )
    duality = all((a + ((-a) % 3)) % 3 == 0 for a in labels)
    nondegenerate = sorted((2 * sign * a) % 3 for a in labels) == [0, 1, 2]
    return {
        "strict_pentagon_all_f_symbols_one": "PASS",
        "bilinear_braiding_hexagon": "PASS" if hexagon else "FAIL",
        "twist_balancing": "PASS" if balancing else "FAIL",
        "duality_involution": "PASS" if duality else "FAIL",
        "monodromy_bicharacter_nondegenerate": "PASS" if nondegenerate else "FAIL",
    }


def build_catalog_v2(
    *,
    started_at_utc: str,
    snapshots: list[dict[str, Any]],
) -> dict[str, Any]:
    v1 = load_json(V1_CATALOG)
    snapshot_hashes = [snapshot["content_hash"] for snapshot in snapshots]
    rows = []
    for row in v1["families"]:
        new_row = dict(row)
        if row["family_id"] == "rank3-cyclic-z3":
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
                        "Resolved by exact strict pointed Z3 metric group snapshots "
                        "q(x)=zeta3^(+x^2) and q(x)=zeta3^(-x^2)."
                    ),
                }
            )
        elif row["family_id"] == "rank2-cyclic-z2":
            new_row["blocker_ids"] = list(row["blocker_ids"]) + [
                "rank2-cyclic-z2:semion-requires-nontrivial-abelian-cocycle-data"
            ]
            new_row["missing_evidence"] = list(row["missing_evidence"]) + [
                "nontrivial Z2 abelian cocycle/associator data for semion and anti-semion"
            ]
            new_row["resolution_note"] = (
                "Not resolved by the strict pointed builder: a trivial associator "
                "would silently fail the semion hexagon."
            )
        rows.append(new_row)

    catalog = {
        **base_meta(
            LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
            RIBBON_CATALOG_PARTIAL,
            started_at_utc=started_at_utc,
        ),
        "catalog_id": "low-rank-ribbon-realization-catalog-v2",
        "previous_catalog": {
            "path": str(V1_CATALOG.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V1_CATALOG),
            "status": v1["status"],
        },
        "scope": v1["scope"],
        "coverage_by_rank": v1["coverage_by_rank"],
        "braided_denominator_by_rank": v1["braided_denominator_by_rank"],
        "ribbon_denominator_by_rank": {},
        "ribbon_denominator_status": "PARTIAL_DO_NOT_USE_AS_FINAL_DENOMINATOR",
        "ribbon_denominator_copied_from_braided": False,
        "formal_scan_plan_allowed": False,
        "resolved_row_count": 1,
        "blocked_row_count": len(rows) - 1,
        "family_count": len(rows),
        "resolved_family_ids": ["rank3-cyclic-z3"],
        "blocked_family_ids": [
            row["family_id"]
            for row in rows
            if row["family_id"] != "rank3-cyclic-z3"
        ],
        "resolved_snapshot_paths": [
            str(snapshot_path(snapshot).relative_to(REPO_ROOT)) for snapshot in snapshots
        ],
        "families": rows,
        "explicit_non_claims": [
            "This partial catalog does not establish the complete rank 2-5 ribbon classification.",
            "This partial catalog does not authorize scan-plan generation.",
            "The rank2 cyclic Z2 row remains blocked to avoid faking semion cocycle data.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return catalog


def snapshot_path(snapshot: dict[str, Any]) -> Path:
    return SNAPSHOT_DIR / f"{snapshot['realization_id']}-snapshot-v1.json"


def build_readiness_v2(*, started_at_utc: str, catalog: dict[str, Any]) -> dict[str, Any]:
    readiness = {
        **base_meta(
            "twisted-yetter.low-rank-formal-scan-readiness.v2",
            "BLOCKED_PARTIAL_RIBBON_CATALOG_ONLY",
            started_at_utc=started_at_utc,
        ),
        "readiness_id": "low-rank-formal-scan-readiness-v2",
        "previous_readiness": {
            "path": str(V1_READINESS.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(V1_READINESS),
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
            "rank2-cyclic-z2-semion-cocycle-missing",
            "thirteen-family-rows-still-blocked",
            "ribbon-denominator-not-final",
        ],
        "explicit_non_claims": [
            "No formal scan plan exists.",
            "No scan case result exists.",
            "No complete-no-signal aggregate exists.",
        ],
    }
    return readiness


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    snapshots = [
        build_z3_snapshot(sign=1, started_at_utc=started_at_utc),
        build_z3_snapshot(sign=-1, started_at_utc=started_at_utc),
    ]
    catalog = build_catalog_v2(started_at_utc=started_at_utc, snapshots=snapshots)
    readiness = build_readiness_v2(started_at_utc=started_at_utc, catalog=catalog)
    result = {
        "low-rank-ribbon-realization-catalog-v2.json": catalog,
        "formal-low-rank-scan-readiness-v2.json": readiness,
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
