#!/usr/bin/env python3
"""Run the Step 2 grocery-procurement pass for blocked low-rank rows.

This script is intentionally conservative.  It materializes the repo-local
SU(2)-family input skeletons we can justify today, then records terminal row
procurement blockers for every row that still lacks row-complete ribbon
realization snapshots and certificates.
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
    LOW_RANK_RIBBON_CATALOG_SCHEMA_V2,
    RIBBON_CATALOG_PROCUREMENT_BLOCKED,
    stable_content_hash,
    validate_low_rank_ribbon_catalog,
)


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
PROCUREMENT_DIR = OUT_DIR / "grocery-procurement"
CATALOG_V10 = OUT_DIR / "low-rank-ribbon-realization-catalog-v10.json"
STEP2_MATERIALIZATION = OUT_DIR / "low-rank-step2-input-materialization-v1.json"
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
SU2_2_LOCAL_BACKEND = REPO_ROOT / "experiments" / "results" / "local-piece" / "su2-2-rf-local-backend-v1.json"

BLOCKED_ROW_ORDER = [
    "rank3-ising",
    "rank3-psu2-5",
    "rank4-psu2-7",
    "rank5-su2-4",
    "rank5-psu2-9",
    "rank5-psu3-4",
]

SU2_PAYLOAD_SPECS = {
    "rank3-ising": {
        "level": 2,
        "labels": [0, 1, 2],
        "subcategory": "full-su2-level-2",
        "payload_id": "rank3-ising-principal-su2-level2-category-payload-v1",
        "status": "PARTIAL_PRINCIPAL_SU2_2_PAYLOAD_NOT_ROW_COMPLETE",
        "blocking_summary": (
            "The full mixed-label SU(2)_2 skeleton is available, but the row still "
            "needs branch enumeration for the 8 braided classes and possible 16 "
            "ribbon lifts."
        ),
    },
    "rank3-psu2-5": {
        "level": 5,
        "labels": [0, 2, 4],
        "subcategory": "adjoint-even-labels",
        "payload_id": "rank3-psu2-5-principal-adjoint-su2-level5-category-payload-v1",
        "status": "PARTIAL_PRINCIPAL_SU2K_PAYLOAD_NOT_GALOIS_COMPLETE",
        "blocking_summary": "Principal adjoint SU(2)_5 data cannot stand in for all Galois/pivotal branches.",
    },
    "rank4-psu2-7": {
        "level": 7,
        "labels": [0, 2, 4, 6],
        "subcategory": "adjoint-even-labels",
        "payload_id": "rank4-psu2-7-principal-adjoint-su2-level7-category-payload-v1",
        "status": "PARTIAL_PRINCIPAL_SU2K_PAYLOAD_NOT_GALOIS_COMPLETE",
        "blocking_summary": "Principal adjoint SU(2)_7 data cannot stand in for all Galois/pivotal branches.",
    },
    "rank5-su2-4": {
        "level": 4,
        "labels": [0, 1, 2, 3, 4],
        "subcategory": "full-su2-level-4-principal",
        "payload_id": "rank5-su2-4-principal-su2-level4-category-payload-v1",
        "status": "PARTIAL_PRINCIPAL_SU2_4_PAYLOAD_EXTENSION_BRANCHES_MISSING",
        "blocking_summary": "Principal SU(2)_4 data does not resolve Rep(S3)^omega/gamma extension branches.",
    },
    "rank5-psu2-9": {
        "level": 9,
        "labels": [0, 2, 4, 6, 8],
        "subcategory": "adjoint-even-labels",
        "payload_id": "rank5-psu2-9-principal-adjoint-su2-level9-category-payload-v1",
        "status": "PARTIAL_PRINCIPAL_SU2K_PAYLOAD_NOT_GALOIS_COMPLETE",
        "blocking_summary": "Principal adjoint SU(2)_9 data cannot stand in for all Galois/pivotal branches.",
    },
}


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


def base_meta(schema: str, status: str, *, started_at_utc: str) -> dict[str, Any]:
    return {
        "schema": schema,
        "status": status,
        "generated_at_utc": started_at_utc,
        "generator_script": "experiments/scripts/build_low_rank_step2_grocery_procurement_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_step2_grocery_procurement_v1.py --write"
        ),
        "repo_root": str(REPO_ROOT),
        "git": {
            "commit": git_output("rev-parse", "HEAD"),
            "dirty": bool(git_output("status", "--porcelain")),
        },
        "tool_versions": {"python": platform.python_version()},
    }


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
    }
    if payload is not None:
        record["content_hash"] = payload.get("content_hash", stable_content_hash(payload))
        record["status"] = payload["status"]
    return record


def generated_record(name: str, payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "path": str((PROCUREMENT_DIR / name).relative_to(REPO_ROOT)),
        "content_hash": payload["content_hash"],
        "status": payload["status"],
    }


def su2_fusion_outputs(level: int, left: int, right: int) -> list[int]:
    lower = abs(left - right)
    upper = min(left + right, 2 * level - left - right)
    return [
        label
        for label in range(lower, upper + 1)
        if (left + right + label) % 2 == 0
    ]


def fusion_table(level: int, labels: list[int]) -> dict[str, list[int]]:
    table = {}
    label_set = set(labels)
    for left in labels:
        for right in labels:
            outputs = [
                label
                for label in su2_fusion_outputs(level, left, right)
                if label in label_set
            ]
            table[f"{left}x{right}"] = outputs
    return table


def build_su2_payload(family_id: str, *, started_at_utc: str) -> dict[str, Any]:
    spec = SU2_PAYLOAD_SPECS[family_id]
    level = int(spec["level"])
    labels = list(spec["labels"])
    payload = {
        **base_meta(
            "twisted-yetter.low-rank-step2-principal-category-payload.v1",
            spec["status"],
            started_at_utc=started_at_utc,
        ),
        "payload_id": spec["payload_id"],
        "family_id": family_id,
        "payload_kind": "principal_su2k_category_input_skeleton",
        "formal_snapshot_produced": False,
        "formal_row_resolution_allowed": False,
        "not_formal_evidence_reason": "missing row-complete branch enumeration and bound producer/runtime/ribbon certificates",
        "source_machinery": artifact_record(SU2K_EVALUATOR),
        "level": level,
        "root_order": 4 * (level + 2),
        "field_embedding": {
            "status": "FORMULA_RECORDED_NOT_BRANCH_CERTIFIED",
            "cyclotomic_root": f"A = zeta_{{{4 * (level + 2)}}}",
            "galois_branches_materialized": False,
        },
        "subcategory": spec["subcategory"],
        "simples": [{"label": label, "dual": label} for label in labels],
        "fusion": {
            "multiplicity": "multiplicity-free",
            "table": fusion_table(level, labels),
            "source_method": "SU2KBraidEvaluator.fusion_outputs",
        },
        "duals": {str(label): label for label in labels},
        "twists": {
            str(label): f"A^({label}*({label}+2))"
            for label in labels
        },
        "pivotal": {
            "status": "FORMULA_RECORDED_NOT_CERTIFIED",
            "candidate_quantum_dimension_formula": "[label+1]_q via SU2KBraidEvaluator.dimension",
            "evaluation_coevaluation_materialized": False,
        },
        "pairing": {
            "status": "NOT_CERTIFIED",
            "fusion_pairing_invertibility_checked": False,
        },
        "basis_gauge": {
            "status": "MULTIPLICITY_FREE_FUSION_PATH_BASIS_RECORDED_NOT_ROW_CERTIFIED",
            "source": "SU2KBraidEvaluator multiplicity-free fusion-path basis",
        },
        "f_symbols": {
            "status": "FORMULA_SOURCE_PINNED_NOT_EXPORTED_FOR_ALL_BRANCHES",
            "source_method": "SU2KBraidEvaluator.f_symbol",
            "q6j_source_method": "SU2KBraidEvaluator.quantum_6j",
        },
        "r_symbols": {
            "status": "FORMULA_SOURCE_PINNED_NOT_EXPORTED_FOR_ALL_BRANCHES",
            "source_method": "SU2KBraidEvaluator.r_symbol",
        },
        "certificates": {
            "producer_exact_coherence": {"status": "MISSING"},
            "consumer_runtime_coherence": {"status": "MISSING"},
            "ribbon_pivotal_compatibility": {"status": "MISSING"},
        },
        "negative_checks": {
            "wrong_branch": "NOT_RUN_NO_BRANCH_EXPORT",
            "wrong_pivotal_scalar": "NOT_RUN_NO_PIVOTAL_CERTIFICATE",
            "wrong_mirror": "NOT_RUN_NO_BRANCH_EXPORT",
            "wrong_basis_order": "NOT_RUN_NO_EXPORTED_BASIS_CERTIFICATE",
            "stale_certificate": "NOT_RUN_NO_CERTIFICATE",
        },
        "blocking_summary": spec["blocking_summary"],
    }
    if family_id == "rank3-ising":
        payload["convention_cross_check_only"] = artifact_record(
            SU2_2_LOCAL_BACKEND, load_json(SU2_2_LOCAL_BACKEND)
        )
        payload["all_sigma_backend_is_formal_evidence"] = False
    return with_hash(payload)


def blocker_for_row(
    row: dict[str, Any],
    *,
    started_at_utc: str,
    partial_payload: dict[str, Any] | None,
) -> dict[str, Any]:
    family_id = row["family_id"]
    missing = list(row["missing_evidence"])
    blocker_ids = list(row["blocker_ids"])
    status_by_family = {
        "rank3-ising": "PROCUREMENT_BLOCKED_BRANCH_ENUMERATION_INCOMPLETE",
        "rank3-psu2-5": "PROCUREMENT_BLOCKED_GALOIS_PIVOTAL_BRANCH_AUDIT_MISSING",
        "rank4-psu2-7": "PROCUREMENT_BLOCKED_GALOIS_PIVOTAL_BRANCH_AUDIT_MISSING",
        "rank5-su2-4": "PROCUREMENT_BLOCKED_EXTENSION_BRANCH_DATA_MISSING",
        "rank5-psu2-9": "PROCUREMENT_BLOCKED_GALOIS_PIVOTAL_BRANCH_AUDIT_MISSING",
        "rank5-psu3-4": "PROCUREMENT_BLOCKED_NO_REPO_LOCAL_PSU3_FR_SOURCE",
    }
    blocker = {
        **base_meta(
            "twisted-yetter.low-rank-row-procurement-blocker.v1",
            status_by_family[family_id],
            started_at_utc=started_at_utc,
        ),
        "blocker_id": f"{family_id}-row-procurement-blocker-v1",
        "family_id": family_id,
        "rank": row["rank"],
        "modular_braided_class_count": row["modular_braided_class_count"],
        "terminal_artifact_kind": "row-procurement-blocker",
        "row_terminal_status": "PROCUREMENT_BLOCKED",
        "formal_admission_allowed": False,
        "row_ribbon_realization_package_produced": False,
        "ribbon_realization_snapshot_hashes": [],
        "partial_payload": (
            {
                "path": str(
                    (
                        PROCUREMENT_DIR
                        / f"{partial_payload['payload_id']}.json"
                    ).relative_to(REPO_ROOT)
                ),
                "content_hash": partial_payload["content_hash"],
                "status": partial_payload["status"],
                "formal_snapshot_produced": partial_payload["formal_snapshot_produced"],
            }
            if partial_payload is not None
            else None
        ),
        "required_grocery_items": [
            "full simples/fusion/duals",
            "F symbols for every required branch",
            "R symbols for every required branch",
            "twists",
            "pivotal/evaluation/coevaluation",
            "fusion pairings and basis/gauge",
            "field embedding",
            "source locator or derivation artifact",
            "producer exact/symbolic coherence certificate",
            "runtime consumer coherence certificate",
            "ribbon/pivotal compatibility certificate",
        ],
        "blocker_ids": blocker_ids,
        "missing_evidence": missing,
        "procurement_attempt_result": "TERMINAL_BLOCKED_FOR_THIS_PASS",
        "why_this_is_not_a_resolved_row": [
            "No row-complete ribbon_realization_snapshot was produced.",
            "No producer/runtime/ribbon certificate triple exists for this row.",
            "No independently derived ribbon denominator contribution exists for this row.",
            "Partial payloads are explicitly marked non-formal evidence.",
        ],
    }
    if family_id == "rank5-psu3-4":
        blocker["source_acquisition_gap"] = {
            "psu3_fr_payload": "MISSING",
            "multiplicity_two_basis_gauge": "MISSING",
            "pairing_convention": "MISSING",
        }
    return with_hash(blocker)


def build_catalog_v11(
    *,
    started_at_utc: str,
    blockers: dict[str, dict[str, Any]],
    ledger_hash: str,
) -> dict[str, Any]:
    previous = load_json(CATALOG_V10)
    validate_low_rank_ribbon_catalog(previous)
    rows = []
    for row in previous["families"]:
        new_row = dict(row)
        blocker = blockers.get(row["family_id"])
        if blocker is not None:
            new_row["procurement_status"] = "PROCUREMENT_BLOCKED"
            new_row["procurement_blocker_hash"] = blocker["content_hash"]
            new_row["procurement_blocker_path"] = str(
                (PROCUREMENT_DIR / f"{blocker['blocker_id']}.json").relative_to(REPO_ROOT)
            )
            new_row["formal_admission_allowed"] = False
            new_row["terminal_status"] = "BLOCKED_RIBBON_REFINEMENT_INCOMPLETE"
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
            RIBBON_CATALOG_PROCUREMENT_BLOCKED,
            started_at_utc=started_at_utc,
        ),
        "catalog_id": "low-rank-ribbon-realization-catalog-v11",
        "previous_catalog": artifact_record(CATALOG_V10, previous),
        "grocery_procurement_ledger_hash": ledger_hash,
        "procurement_status": "TERMINAL_PROCUREMENT_BLOCKED",
        "scope": previous["scope"],
        "coverage_by_rank": previous["coverage_by_rank"],
        "braided_denominator_by_rank": previous["braided_denominator_by_rank"],
        "ribbon_denominator_by_rank": {},
        "ribbon_denominator_status": "PROCUREMENT_BLOCKED_DO_NOT_USE_AS_FINAL_DENOMINATOR",
        "ribbon_denominator_copied_from_braided": False,
        "formal_scan_plan_allowed": False,
        "resolved_row_count": len(resolved_ids),
        "blocked_row_count": len(blocked_ids),
        "family_count": len(rows),
        "resolved_family_ids": resolved_ids,
        "blocked_family_ids": blocked_ids,
        "resolved_snapshot_paths": previous["resolved_snapshot_paths"],
        "families": rows,
        "terminal_procurement_blockers": [
            {
                "family_id": family_id,
                "content_hash": blockers[family_id]["content_hash"],
                "status": blockers[family_id]["status"],
                "path": str(
                    (PROCUREMENT_DIR / f"{blockers[family_id]['blocker_id']}.json").relative_to(
                        REPO_ROOT
                    )
                ),
            }
            for family_id in BLOCKED_ROW_ORDER
        ],
        "explicit_non_claims": [
            "This procurement-blocked catalog does not establish the complete rank 2-5 ribbon classification.",
            "This procurement-blocked catalog does not authorize scan-plan generation.",
            "Partial principal SU(2)_k payloads are not row-complete ribbon realization snapshots.",
            "No formal low-rank scan aggregate or no-signal claim follows from this catalog.",
        ],
    }
    validate_low_rank_ribbon_catalog(catalog)
    return with_hash(catalog)


def build_readiness_v11(
    *,
    started_at_utc: str,
    catalog: dict[str, Any],
) -> dict[str, Any]:
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-formal-scan-readiness.v11",
                "BLOCKED_TERMINAL_PROCUREMENT_BLOCKED_CATALOG",
                started_at_utc=started_at_utc,
            ),
            "readiness_id": "low-rank-formal-scan-readiness-v11",
            "classification_catalog_hash": catalog["content_hash"],
            "classification_catalog_status": catalog["status"],
            "procurement_status": catalog["procurement_status"],
            "scan_plan_generation_allowed": False,
            "formal_scan_plan_id": None,
            "blocking_reason_ids": [
                "terminal-procurement-blocked-catalog",
                "six-row-procurement-blockers-remain",
                "ribbon-denominator-not-established",
            ],
            "explicit_non_claims": [
                "No formal scan plan exists.",
                "No controls, target scans, aggregate, or no-signal result is authorized.",
            ],
        }
    )


def build_ledger(
    *,
    started_at_utc: str,
    partial_payloads: dict[str, dict[str, Any]],
    blockers: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    materialization = load_json(STEP2_MATERIALIZATION)
    rows = []
    for family_id in BLOCKED_ROW_ORDER:
        partial = partial_payloads.get(family_id)
        blocker = blockers[family_id]
        rows.append(
            {
                "family_id": family_id,
                "grocery_status": "PROCUREMENT_BLOCKED",
                "terminal_artifact_kind": "row-procurement-blocker",
                "terminal_artifact_hash": blocker["content_hash"],
                "terminal_artifact_path": str(
                    (PROCUREMENT_DIR / f"{blocker['blocker_id']}.json").relative_to(REPO_ROOT)
                ),
                "partial_payload_hash": partial["content_hash"] if partial is not None else None,
                "resolved_package_hash": None,
            }
        )
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-step2-grocery-procurement.v1",
                "STEP2_GROCERY_PROCUREMENT_COMPLETE_PROCUREMENT_BLOCKED",
                started_at_utc=started_at_utc,
            ),
            "procurement_id": "low-rank-step2-grocery-procurement-v1",
            "step": "implementation_order_step_2_resolve_the_6_blocked_rows",
            "input_artifacts": {
                "catalog_v10": artifact_record(CATALOG_V10, load_json(CATALOG_V10)),
                "step2_materialization": artifact_record(
                    STEP2_MATERIALIZATION, materialization
                ),
                "su2k_evaluator": artifact_record(SU2K_EVALUATOR),
            },
            "blocked_family_ids": BLOCKED_ROW_ORDER,
            "row_procurement_records": rows,
            "resolved_row_package_count": 0,
            "procurement_blocker_count": len(BLOCKED_ROW_ORDER),
            "formal_scan_plan_allowed_after_procurement": False,
            "terminal_result_kind": "FORMAL_LOW_RANK_SCAN_TERMINAL_BLOCKED",
            "completion_semantics": (
                "Step 2 grocery procurement is complete for this run: every blocked "
                "row has a terminal artifact, and no partial input was promoted to "
                "formal category evidence."
            ),
            "explicit_non_claims": [
                "No row-ribbon-realization-package was produced.",
                "No low-rank ribbon classification established claim is supported.",
                "No scan plan, controls, target scan, aggregate, or no-signal claim is supported.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    catalog_v10 = load_json(CATALOG_V10)
    validate_low_rank_ribbon_catalog(catalog_v10)
    rows = {row["family_id"]: row for row in catalog_v10["families"]}
    if catalog_v10["blocked_family_ids"] != BLOCKED_ROW_ORDER:
        raise RuntimeError("blocked row order changed; update grocery procurement explicitly")

    partial_payloads = {
        family_id: build_su2_payload(family_id, started_at_utc=started_at_utc)
        for family_id in SU2_PAYLOAD_SPECS
    }
    blockers = {
        family_id: blocker_for_row(
            rows[family_id],
            started_at_utc=started_at_utc,
            partial_payload=partial_payloads.get(family_id),
        )
        for family_id in BLOCKED_ROW_ORDER
    }
    ledger = build_ledger(
        started_at_utc=started_at_utc,
        partial_payloads=partial_payloads,
        blockers=blockers,
    )
    catalog = build_catalog_v11(
        started_at_utc=started_at_utc,
        blockers=blockers,
        ledger_hash=ledger["content_hash"],
    )
    readiness = build_readiness_v11(started_at_utc=started_at_utc, catalog=catalog)

    artifacts: dict[str, dict[str, Any]] = {}
    for payload in partial_payloads.values():
        artifacts[f"grocery-procurement/{payload['payload_id']}.json"] = payload
    for blocker in blockers.values():
        artifacts[f"grocery-procurement/{blocker['blocker_id']}.json"] = blocker
    artifacts["low-rank-step2-grocery-procurement-v1.json"] = ledger
    artifacts["low-rank-ribbon-realization-catalog-v11.json"] = catalog
    artifacts["formal-low-rank-scan-readiness-v11.json"] = readiness
    return artifacts


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
