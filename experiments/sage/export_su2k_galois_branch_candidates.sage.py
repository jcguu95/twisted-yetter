#!/usr/bin/env sage
"""Export and revalidate SU(2)_k Galois branch candidate category data.

These artifacts continue the nontrivial row-growth pass beyond the principal
branch.  They are still candidate payloads, not row-complete ribbon
realization snapshots: pivotal/ribbon lift enumeration, row denominator
derivation, and SU(2)_4 extension/gamma branches remain outside this exporter.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from sage.all import QQbar


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.foundation_safety import stable_content_hash  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
BRANCH_DIR = OUT_DIR / "grown-category-branches"
EVALUATOR_PATH = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"

TARGETS = {
    "rank3-ising": {
        "level": 2,
        "labels": [0, 1, 2],
        "export_id": "rank3-ising-su2-level2-galois-branch-candidates-v1",
        "certificate_id": "rank3-ising-su2-level2-galois-branch-candidates-validation-v1",
        "remaining_growth": [
            "identify which candidate Galois branches correspond to the eight braided Ising classes",
            "materialize mirror/reverse equivalence conventions explicitly",
            "decide and materialize pivotal/ribbon lifts for each braided class",
            "produce row-complete producer/runtime/ribbon certificates for every lift",
            "derive the row ribbon denominator without copying the braided denominator",
        ],
    },
    "rank5-su2-4": {
        "level": 4,
        "labels": [0, 1, 2, 3, 4],
        "export_id": "rank5-su2-4-su2-level4-galois-branch-candidates-v1",
        "certificate_id": "rank5-su2-4-su2-level4-galois-branch-candidates-validation-v1",
        "remaining_growth": [
            "identify which SU(2)_4 Galois candidates correspond to the four braided family classes",
            "materialize Rep(S3)^omega / gamma extension branches",
            "separate spherical/ribbon refinements by snapshot hash",
            "produce row-complete producer/runtime/ribbon certificates for every branch",
            "derive the row ribbon denominator without copying the braided denominator",
        ],
    },
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload) -> None:
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


def with_hash(payload):
    result = dict(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def load_evaluator_module():
    spec = importlib.util.spec_from_file_location("su2k_galois_branch_source", EVALUATOR_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules["su2k_galois_branch_source"] = module
    spec.loader.exec_module(module)
    return module


def evaluator_for_branch(su2k, level: int, galois_power: int):
    class GaloisBranchCandidateEvaluator(su2k.SU2KBraidEvaluator):
        def sqrt(self, value):
            return self.coerce(QQbar(value).sqrt())

    evaluator = GaloisBranchCandidateEvaluator(level, exact=True)
    evaluator.A = evaluator.field.gen() ** int(galois_power)
    evaluator._fixed_label_cache = {}
    evaluator._numpy_crossing_cache = {}
    return evaluator


def unit_powers(root_order: int) -> list[int]:
    return [power for power in range(1, root_order) if math.gcd(power, root_order) == 1]


def str_value(value) -> str:
    try:
        return str(QQbar(value).radical_expression())
    except Exception:
        return str(value)


def branch_payload(su2k, family_id: str, galois_power: int):
    target = TARGETS[family_id]
    level = int(target["level"])
    evaluator = evaluator_for_branch(su2k, level, galois_power)
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

    branch = {
        "branch_id": f"{family_id}-su2-level{level}-galois-power-{galois_power}",
        "family_id": family_id,
        "level": level,
        "root_order": evaluator.root_order,
        "galois_power": int(galois_power),
        "field_embedding": {
            "cyclotomic_root": f"A=zeta_{evaluator.root_order}^{galois_power}",
            "branch_status": "candidate_galois_power_branch_not_row_certified",
            "sqrt_branch_convention": "QQbar(value).sqrt(); this is a candidate convention, not a row-complete pivotal/ribbon branch proof",
        },
        "labels": labels,
        "unit": 0,
        "duals": {str(label): label for label in labels},
        "fusion": fusion,
        "f_symbols": f_symbols,
        "r_symbols": r_symbols,
        "twists": {str(label): str_value(evaluator.twist(label)) for label in labels},
        "dimensions": {str(label): str_value(evaluator.dimension(label)) for label in labels},
        "pivotal": {
            "status": "CANONICAL_SU2_FORMULA_RECOMPUTED_NOT_ROW_BRANCH_AUDITED",
            "evaluation_coevaluation_materialized": False,
        },
        "basis_gauge": "multiplicity-free SU(2)_k fusion-path basis from SU2KBraidEvaluator",
        "pairing": {
            "status": "NOT_FORMALLY_CERTIFIED_FOR_ROW_COMPLETION",
            "fusion_pairing_invertibility_checked": False,
        },
    }
    branch["branch_data_hash"] = stable_content_hash(branch)
    return branch


def build_export(family_id: str, *, started_at_utc: str):
    target = TARGETS[family_id]
    su2k = load_evaluator_module()
    root_order = 4 * (int(target["level"]) + 2)
    powers = unit_powers(root_order)
    branches = [branch_payload(su2k, family_id, power) for power in powers]
    per_branch_counts = {
        "fusion_products": len(branches[0]["fusion"]),
        "f_symbols": len(branches[0]["f_symbols"]),
        "r_symbols": len(branches[0]["r_symbols"]),
        "twists": len(branches[0]["twists"]),
        "dimensions": len(branches[0]["dimensions"]),
    }
    return with_hash(
        {
            "schema": "twisted-yetter.su2k-galois-branch-candidates.v1",
            "status": "SU2K_GALOIS_BRANCH_CANDIDATES_EXPORTED_NOT_ROW_COMPLETE",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/sage/export_su2k_galois_branch_candidates.sage.py",
            "reproduce_command": (
                f'DOT_SAGE="$PWD/.sage" sage experiments/sage/export_su2k_galois_branch_candidates.sage.py '
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
            "level": int(target["level"]),
            "root_order": root_order,
            "galois_powers": powers,
            "candidate_branch_count": len(branches),
            "per_branch_entry_counts": per_branch_counts,
            "branches": branches,
            "source_machinery": {
                "path": str(EVALUATOR_PATH.relative_to(REPO_ROOT)),
                "sha256": file_sha256_id(EVALUATOR_PATH),
            },
            "formal_row_resolution_allowed": False,
            "formal_ribbon_realization_snapshot_produced": False,
            "remaining_growth": target["remaining_growth"],
            "explicit_non_claims": [
                "These are SU(2)_k Galois branch candidate payloads, not formal ribbon_realization_snapshot evidence.",
                "This artifact does not prove row denominator completeness.",
                "This artifact does not enumerate pivotal/ribbon lifts.",
                "Non-principal square roots use an explicit QQbar candidate convention and still require branch audit.",
                "This artifact does not authorize a formal scan plan.",
            ],
        }
    )


def assert_equal(actual, expected, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")


def validate_export_payload(export):
    body = dict(export)
    content_hash = body.pop("content_hash")
    assert_equal(content_hash, stable_content_hash(body), "export content_hash")
    assert_equal(export["source_machinery"]["sha256"], file_sha256_id(EVALUATOR_PATH), "source machinery hash")

    family_id = export["family_id"]
    su2k = load_evaluator_module()
    checked = {
        "branch_count": 0,
        "fusion_entries": 0,
        "f_symbol_entries": 0,
        "r_symbol_entries": 0,
        "r_inverse_entries": 0,
        "twist_entries": 0,
        "dimension_entries": 0,
    }
    for branch in export["branches"]:
        assert_equal(branch["branch_data_hash"], stable_content_hash({k: v for k, v in branch.items() if k != "branch_data_hash"}), f"{branch['branch_id']} branch hash")
        evaluator = evaluator_for_branch(su2k, export["level"], branch["galois_power"])
        labels = list(branch["labels"])
        label_set = set(labels)
        for left in labels:
            for right in labels:
                key = f"{left}x{right}"
                expected = [
                    output
                    for output in evaluator.fusion_outputs(left, right)
                    if output in label_set
                ]
                assert_equal(branch["fusion"][key], expected, f"{branch['branch_id']} fusion {key}")
                checked["fusion_entries"] += 1

        for key, value in branch["f_symbols"].items():
            inside = key.removeprefix("F(").removesuffix(")")
            abc, channels = inside.split(";")
            left_channel, right_channel = [int(item) for item in channels.split(",")]
            ab, d = abc.split("->")
            a, b, c = [int(item) for item in ab.split(",")]
            d = int(d)
            expected = str_value(evaluator.f_symbol(a, b, c, d, left_channel, right_channel))
            assert_equal(value, expected, f"{branch['branch_id']} F-symbol {key}")
            checked["f_symbol_entries"] += 1

        for key, value in branch["r_symbols"].items():
            positive = key.startswith("R+")
            inside = key.removeprefix("R+(").removeprefix("R-(").removesuffix(")")
            lr, output = inside.split("->")
            left, right = [int(item) for item in lr.split(",")]
            output = int(output)
            expected_value = evaluator.r_symbol(left, right, output, positive=positive)
            assert_equal(value, str_value(expected_value), f"{branch['branch_id']} R-symbol {key}")
            inverse_value = evaluator.r_symbol(left, right, output, positive=not positive)
            if str(expected_value * inverse_value) != "1":
                raise AssertionError(f"{branch['branch_id']} R inverse product failed for {key}")
            checked["r_symbol_entries"] += 1
            checked["r_inverse_entries"] += 1

        for label in labels:
            assert_equal(branch["twists"][str(label)], str_value(evaluator.twist(label)), f"{branch['branch_id']} twist {label}")
            assert_equal(branch["dimensions"][str(label)], str_value(evaluator.dimension(label)), f"{branch['branch_id']} dimension {label}")
            checked["twist_entries"] += 1
            checked["dimension_entries"] += 1
        checked["branch_count"] += 1

    assert_equal(checked["branch_count"], export["candidate_branch_count"], f"{family_id} branch count")
    return checked


def build_certificate(export, *, export_path: Path, started_at_utc: str):
    checked = validate_export_payload(export)
    target = TARGETS[export["family_id"]]
    return with_hash(
        {
            "schema": "twisted-yetter.su2k-galois-branch-candidates-validation.v1",
            "status": "PASS_STRICT_GALOIS_BRANCH_CANDIDATE_REVALIDATION",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/sage/export_su2k_galois_branch_candidates.sage.py",
            "reproduce_command": (
                f'DOT_SAGE="$PWD/.sage" sage experiments/sage/export_su2k_galois_branch_candidates.sage.py '
                f"--family-id {export['family_id']} --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {
                "python": platform.python_version(),
                "sage": getattr(load_evaluator_module(), "SAGE_VERSION", "unknown"),
            },
            "certificate_id": target["certificate_id"],
            "family_id": export["family_id"],
            "validated_export": {
                "path": str(export_path.relative_to(REPO_ROOT)),
                "sha256": file_sha256_id(export_path),
                "content_hash": export["content_hash"],
                "status": export["status"],
            },
            "checks": {
                "export_content_hash_fresh": "PASS",
                "source_machinery_hash_matches": "PASS",
                "branch_hashes_fresh": "PASS",
                "fusion_entries_recomputed": "PASS",
                "f_symbol_entries_recomputed": "PASS",
                "r_symbol_entries_recomputed": "PASS",
                "r_inverse_entries_recomputed": "PASS",
                "twist_entries_recomputed": "PASS",
                "dimension_entries_recomputed": "PASS",
                "candidate_branch_count_matches": "PASS",
            },
            "checked_entry_counts": checked,
            "formal_row_resolution_allowed": False,
            "formal_ribbon_realization_snapshot_produced": False,
            "explicit_non_claims": [
                "This certificate validates SU(2)_k Galois branch candidates only.",
                "This certificate is not a row-complete ribbon realization certificate.",
                "This certificate does not establish pivotal/ribbon lift completeness.",
                "This certificate does not authorize scan-plan generation.",
            ],
        }
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family-id", choices=sorted(TARGETS), required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    started_at = utc_now()
    export = build_export(args.family_id, started_at_utc=started_at)
    export_path = BRANCH_DIR / f"{export['export_id']}.json"
    if args.write:
        write_json(export_path, export)
        certificate = build_certificate(export, export_path=export_path, started_at_utc=started_at)
        write_json(BRANCH_DIR / f"{certificate['certificate_id']}.json", certificate)
    else:
        print(json.dumps(export, ensure_ascii=True, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
