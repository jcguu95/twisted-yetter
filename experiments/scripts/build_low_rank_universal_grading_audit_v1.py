#!/usr/bin/env python3
"""Audit universal grading groups for the blocked low-rank rows.

This is a fusion-rule audit only.  It decides which blocked rows can even have
nontrivial character sectors before we spend effort procuring full F/R/pivotal
data.  It deliberately does not turn any row into ribbon realization evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import stable_content_hash  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
CATALOG_V11 = OUT_DIR / "low-rank-ribbon-realization-catalog-v11.json"
PROCUREMENT_LEDGER = OUT_DIR / "low-rank-step2-grocery-procurement-v1.json"

BLOCKED_ROW_ORDER = [
    "rank3-ising",
    "rank3-psu2-5",
    "rank4-psu2-7",
    "rank5-su2-4",
    "rank5-psu2-9",
    "rank5-psu3-4",
]

SU2_FUSION_MODELS = {
    "rank3-ising": {
        "level": 2,
        "labels": [0, 1, 2],
        "model": "full SU(2)_2 fusion rules",
        "expected_universal_group": "Z2",
    },
    "rank3-psu2-5": {
        "level": 5,
        "labels": [0, 2, 4],
        "model": "adjoint/even-label SU(2)_5 fusion rules",
        "expected_universal_group": "trivial",
    },
    "rank4-psu2-7": {
        "level": 7,
        "labels": [0, 2, 4, 6],
        "model": "adjoint/even-label SU(2)_7 fusion rules",
        "expected_universal_group": "trivial",
    },
    "rank5-su2-4": {
        "level": 4,
        "labels": [0, 1, 2, 3, 4],
        "model": "full SU(2)_4 fusion-rule model for the rank-5 family",
        "expected_universal_group": "Z2",
    },
    "rank5-psu2-9": {
        "level": 9,
        "labels": [0, 2, 4, 6, 8],
        "model": "adjoint/even-label SU(2)_9 fusion rules",
        "expected_universal_group": "trivial",
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
        "generator_script": "experiments/scripts/build_low_rank_universal_grading_audit_v1.py",
        "reproduce_command": (
            "python3 experiments/scripts/build_low_rank_universal_grading_audit_v1.py --write"
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


def su2_fusion_outputs(level: int, left: int, right: int) -> list[int]:
    lower = abs(left - right)
    upper = min(left + right, 2 * level - left - right)
    return [
        label
        for label in range(lower, upper + 1)
        if (left + right + label) % 2 == 0
    ]


def restricted_fusion_table(level: int, labels: list[int]) -> dict[int, dict[int, list[int]]]:
    label_set = set(labels)
    table: dict[int, dict[int, list[int]]] = {}
    for left in labels:
        table[left] = {}
        for right in labels:
            outputs = [
                output
                for output in su2_fusion_outputs(level, left, right)
                if output in label_set
            ]
            table[left][right] = outputs
    return table


def closure_under_fusion(
    generators: set[int],
    table: dict[int, dict[int, list[int]]],
) -> list[int]:
    closure = set(generators)
    changed = True
    while changed:
        changed = False
        for left in list(closure):
            for right in list(closure):
                for output in table[left][right]:
                    if output not in closure:
                        closure.add(output)
                        changed = True
    return sorted(closure)


class UnionFind:
    def __init__(self, labels: list[int]) -> None:
        self.parent = {label: label for label in labels}

    def find(self, label: int) -> int:
        parent = self.parent[label]
        if parent != label:
            self.parent[label] = self.find(parent)
        return self.parent[label]

    def union(self, left: int, right: int) -> None:
        lroot = self.find(left)
        rroot = self.find(right)
        if lroot != rroot:
            self.parent[rroot] = lroot


def universal_grading_from_fusion_rules(
    *,
    level: int,
    labels: list[int],
) -> dict[str, Any]:
    table = restricted_fusion_table(level, labels)
    adjoint_generators = {0}
    for label in labels:
        # SU(2)_k labels are self-dual.
        adjoint_generators.update(table[label][label])
    adjoint_component = closure_under_fusion(adjoint_generators, table)

    uf = UnionFind(labels)
    for label in labels:
        for adjoint_label in adjoint_component:
            for output in table[label][adjoint_label]:
                uf.union(label, output)

    buckets: dict[int, list[int]] = defaultdict(list)
    for label in labels:
        buckets[uf.find(label)].append(label)
    components = [sorted(bucket) for bucket in buckets.values()]
    components.sort(key=lambda item: (0 not in item, item[0]))
    component_index = {
        label: index
        for index, component in enumerate(components)
        for label in component
    }

    multiplication: dict[str, int] = {}
    for left_index, left_component in enumerate(components):
        for right_index, right_component in enumerate(components):
            output_components = {
                component_index[output]
                for left in left_component
                for right in right_component
                for output in table[left][right]
            }
            if len(output_components) != 1:
                raise RuntimeError(
                    "fusion components do not define a grading product: "
                    f"{left_component} x {right_component} -> {sorted(output_components)}"
                )
            multiplication[f"g{left_index}*g{right_index}"] = output_components.pop()

    group_name = "trivial" if len(components) == 1 else f"Z{len(components)}"
    if len(components) == 2 and multiplication != {
        "g0*g0": 0,
        "g0*g1": 1,
        "g1*g0": 1,
        "g1*g1": 0,
    }:
        raise RuntimeError("two-component SU(2) grading is not Z2")

    return {
        "fusion_table": {
            f"{left}x{right}": outputs
            for left, row in table.items()
            for right, outputs in row.items()
        },
        "adjoint_generators": sorted(adjoint_generators),
        "adjoint_component": adjoint_component,
        "universal_grading_components": components,
        "universal_group": "Z2" if len(components) == 2 else group_name,
        "component_multiplication": multiplication,
        "nontrivial_character_count": 0 if len(components) == 1 else len(components) - 1,
    }


def row_audit_for_su2_family(
    family_id: str,
    row: dict[str, Any],
    *,
    started_at_utc: str,
) -> dict[str, Any]:
    spec = SU2_FUSION_MODELS[family_id]
    computed = universal_grading_from_fusion_rules(
        level=spec["level"],
        labels=spec["labels"],
    )
    if computed["universal_group"] != spec["expected_universal_group"]:
        raise RuntimeError(f"unexpected universal group for {family_id}")

    nontrivial = computed["universal_group"] != "trivial"
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-row-universal-grading-audit.v1",
                (
                    "UNIVERSAL_GRADING_FORMALLY_DERIVED_NONTRIVIAL"
                    if nontrivial
                    else "UNIVERSAL_GRADING_FORMALLY_DERIVED_TRIVIAL"
                ),
                started_at_utc=started_at_utc,
            ),
            "family_id": family_id,
            "family": row["family"],
            "rank": row["rank"],
            "modular_braided_class_count": row["modular_braided_class_count"],
            "audit_scope": "fusion_rule_universal_grading_only",
            "fusion_rule_model": spec["model"],
            "level": spec["level"],
            "labels": spec["labels"],
            "duals": {str(label): label for label in spec["labels"]},
            "derivation_method": (
                "Compute the adjoint fusion subcategory generated by X tensor X* "
                "inside the restricted SU(2)_k fusion ring, then compute the "
                "universal grading components as cosets under tensoring with the "
                "adjoint component."
            ),
            "computed": computed,
            "scan_relevance": (
                "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST"
                if nontrivial
                else "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS"
            ),
            "formal_ribbon_realization_status": "NOT_PRODUCED_BY_THIS_AUDIT",
            "explicit_non_claims": [
                "This row audit does not provide F symbols.",
                "This row audit does not provide R symbols.",
                "This row audit does not provide pivotal/evaluation/coevaluation data.",
                "This row audit does not resolve the row as a ribbon realization.",
            ],
        }
    )


def psu3_blocked_audit(
    row: dict[str, Any],
    *,
    started_at_utc: str,
) -> dict[str, Any]:
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-row-universal-grading-audit.v1",
                "UNIVERSAL_GRADING_AUDIT_BLOCKED_NO_REPO_LOCAL_FUSION_TABLE",
                started_at_utc=started_at_utc,
            ),
            "family_id": "rank5-psu3-4",
            "family": row["family"],
            "rank": row["rank"],
            "modular_braided_class_count": row["modular_braided_class_count"],
            "audit_scope": "fusion_rule_universal_grading_only",
            "fusion_rule_model": None,
            "computed": None,
            "scan_relevance": "UNKNOWN_UNTIL_FUSION_TABLE_AUDIT",
            "blocked_reason": (
                "The row is named as an adjoint PSU(3)_4 family, but the repository "
                "does not currently contain a machine-readable fusion table for this "
                "multiplicity-two row.  The audit therefore does not promote the "
                "name '_ad' into a formal trivial-universal-grading certificate."
            ),
            "required_input_to_unblock": [
                "machine-readable PSU(3)_4 fusion table for the rank-5 row",
                "duality involution for simples",
                "source locator or derivation artifact for that fusion table",
            ],
            "candidate_inference_not_admitted": (
                "The '_ad' family name suggests the universal grading may be trivial, "
                "but this pass treats that as non-formal until the fusion table is pinned."
            ),
            "formal_ribbon_realization_status": "NOT_PRODUCED_BY_THIS_AUDIT",
            "explicit_non_claims": [
                "This row audit does not prove PSU(3)_4 has trivial universal grading.",
                "This row audit does not provide F/R data or basis/gauge conventions.",
                "This row audit does not resolve the row as a ribbon realization.",
            ],
        }
    )


def build_audit(*, started_at_utc: str) -> dict[str, Any]:
    catalog = load_json(CATALOG_V11)
    procurement = load_json(PROCUREMENT_LEDGER)
    rows = {row["family_id"]: row for row in catalog["families"]}
    if catalog["blocked_family_ids"] != BLOCKED_ROW_ORDER:
        raise RuntimeError("blocked row order changed; update universal grading audit")

    row_audits = []
    for family_id in BLOCKED_ROW_ORDER:
        if family_id in SU2_FUSION_MODELS:
            row_audits.append(
                row_audit_for_su2_family(
                    family_id,
                    rows[family_id],
                    started_at_utc=started_at_utc,
                )
            )
        else:
            row_audits.append(psu3_blocked_audit(rows[family_id], started_at_utc=started_at_utc))

    nontrivial = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS_EXIST"
    ]
    trivial = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "NO_NONTRIVIAL_UNIVERSAL_CHARACTER_SECTORS"
    ]
    blocked = [
        row["family_id"]
        for row in row_audits
        if row["scan_relevance"] == "UNKNOWN_UNTIL_FUSION_TABLE_AUDIT"
    ]
    return with_hash(
        {
            **base_meta(
                "twisted-yetter.low-rank-universal-grading-audit.v1",
                "UNIVERSAL_GRADING_AUDIT_COMPLETE_WITH_ONE_BLOCKER",
                started_at_utc=started_at_utc,
            ),
            "audit_id": "low-rank-universal-grading-audit-v1",
            "input_artifacts": {
                "catalog_v11": artifact_record(CATALOG_V11, catalog),
                "grocery_procurement": artifact_record(PROCUREMENT_LEDGER, procurement),
            },
            "blocked_family_ids": BLOCKED_ROW_ORDER,
            "row_audits": row_audits,
            "formal_nontrivial_universal_group_family_ids": nontrivial,
            "formal_trivial_universal_group_family_ids": trivial,
            "universal_grading_audit_blocked_family_ids": blocked,
            "twisted_scan_triage": {
                "need_full_ribbon_data_for_nontrivial_character_scan": nontrivial,
                "vacuous_for_nontrivial_universal_character_scan": trivial,
                "cannot_triage_without_fusion_table": blocked,
            },
            "scan_plan_status": "NOT_AUTHORIZED_BY_THIS_AUDIT",
            "classification_status": "NOT_ESTABLISHED_BY_THIS_AUDIT",
            "explicit_non_claims": [
                "This audit does not establish the low-rank ribbon classification.",
                "This audit does not produce any ribbon_realization_snapshot.",
                "This audit does not authorize scan-plan generation.",
                "Rows with trivial universal grading are only vacuous for nontrivial universal-character twists; they are not resolved as ribbon categories.",
                "The PSU(3)_4 universal grading is not formally decided by this pass.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    started_at_utc = utc_now()
    audit = build_audit(started_at_utc=started_at_utc)
    return {"low-rank-universal-grading-audit-v1.json": audit}


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
