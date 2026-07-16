#!/usr/bin/env sage
"""Export principal SU(2)_k category data for growth-target rows.

This exporter is a data-growth tool, not a row-completion tool.  It serializes
the principal SU(2)_k branch F/R/twist/dimension entries from the existing q6j
machinery so later audits can distinguish actual exported data from a mere
evaluator handle.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import stable_content_hash  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate" / "grown-category-data"
EVALUATOR_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"

TARGETS = {
    "rank3-ising": {
        "level": 2,
        "labels": [0, 1, 2],
        "export_id": "rank3-ising-principal-su2-level2-category-data-export-v1",
        "status": "PRINCIPAL_SU2_BRANCH_DATA_EXPORTED_NOT_ROW_COMPLETE",
    },
    "rank5-su2-4": {
        "level": 4,
        "labels": [0, 1, 2, 3, 4],
        "export_id": "rank5-su2-4-principal-su2-level4-category-data-export-v1",
        "status": "PRINCIPAL_SU2_BRANCH_DATA_EXPORTED_NOT_EXTENSION_COMPLETE",
    },
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def git_output(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def file_sha256_id(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def with_hash(payload):
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def write_json(path: Path, payload) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("su2k_export_source", EVALUATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules["su2k_export_source"] = module
    spec.loader.exec_module(module)
    return module


def str_value(value) -> str:
    return str(value)


def export_target(family_id: str, *, started_at_utc: str):
    target = TARGETS[family_id]
    su2k = load_evaluator_module()
    evaluator = su2k.SU2KBraidEvaluator(target["level"], exact=True)
    labels = list(target["labels"])
    label_set = set(labels)

    fusion = {}
    for left in labels:
        for right in labels:
            fusion[f"{left}x{right}"] = [
                output
                for output in evaluator.fusion_outputs(left, right)
                if output in label_set
            ]

    f_symbols = {}
    for a in labels:
        for b in labels:
            for c in labels:
                for d in labels:
                    left_channels = [
                        x
                        for x in evaluator.fusion_outputs(a, b)
                        if x in label_set and evaluator.admissible(x, c, d)
                    ]
                    right_channels = [
                        y
                        for y in evaluator.fusion_outputs(b, c)
                        if y in label_set and evaluator.admissible(a, y, d)
                    ]
                    for left_channel in left_channels:
                        for right_channel in right_channels:
                            value = evaluator.f_symbol(a, b, c, d, left_channel, right_channel)
                            f_symbols[
                                f"F({a},{b},{c}->{d};{left_channel},{right_channel})"
                            ] = str_value(value)

    r_symbols = {}
    for left in labels:
        for right in labels:
            for output in fusion[f"{left}x{right}"]:
                r_symbols[f"R+({left},{right}->{output})"] = str_value(
                    evaluator.r_symbol(left, right, output, positive=True)
                )
                r_symbols[f"R-({left},{right}->{output})"] = str_value(
                    evaluator.r_symbol(left, right, output, positive=False)
                )

    category_data = {
        "family_id": family_id,
        "branch_id": target["export_id"].removesuffix("-v1"),
        "level": target["level"],
        "root_order": evaluator.root_order,
        "labels": labels,
        "unit": 0,
        "duals": {str(label): label for label in labels},
        "fusion": fusion,
        "f_symbols": f_symbols,
        "r_symbols": r_symbols,
        "twists": {str(label): str_value(evaluator.twist(label)) for label in labels},
        "dimensions": {
            str(label): str_value(evaluator.dimension(label))
            for label in labels
        },
        "pivotal": {
            "status": "CANONICAL_SU2_PIVOTAL_FORMULA_EXPORTED_NOT_BRANCH_AUDITED",
            "evaluation_coevaluation": "standard SU(2)_k fusion-path convention from q6j evaluator",
        },
        "basis_gauge": "multiplicity-free SU(2)_k fusion-path basis from SU2KBraidEvaluator",
        "field_embedding": {
            "cyclotomic_root": f"A=zeta_{evaluator.root_order}",
            "branch": "principal evaluator branch",
        },
        "source_machinery": {
            "path": str(EVALUATOR_PATH.relative_to(REPO_ROOT)),
            "sha256": file_sha256_id(EVALUATOR_PATH),
        },
    }
    category_hash = stable_content_hash(category_data)
    return with_hash(
        {
            "schema": "twisted-yetter.su2k-principal-category-data-export.v1",
            "status": target["status"],
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/sage/export_su2k_principal_category_data.sage.py",
            "reproduce_command": (
                f'DOT_SAGE="$PWD/.sage" sage experiments/sage/export_su2k_principal_category_data.sage.py '
                f"--family-id {family_id} --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {
                "python": platform.python_version(),
                "sage": getattr(su2k, "SAGE_VERSION", "unknown"),
            },
            "export_id": target["export_id"],
            "family_id": family_id,
            "category_data_hash": category_hash,
            "category_data": category_data,
            "entry_counts": {
                "fusion_products": len(fusion),
                "f_symbols": len(f_symbols),
                "r_symbols": len(r_symbols),
                "twists": len(labels),
                "dimensions": len(labels),
            },
            "formal_row_resolution_allowed": False,
            "formal_ribbon_realization_snapshot_produced": False,
            "why_not_row_complete": [
                "This export is only the principal SU(2)_k branch.",
                "Galois/mirror/pivotal/ribbon branch enumeration is not complete.",
                "Producer/runtime/ribbon certificates for every row branch are not produced by this exporter.",
            ],
        }
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family-id", choices=sorted(TARGETS), required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    payload = export_target(args.family_id, started_at_utc=utc_now())
    if args.write:
        write_json(OUT_DIR / f"{payload['export_id']}.json", payload)
    else:
        print(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
