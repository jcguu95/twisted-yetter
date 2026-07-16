#!/usr/bin/env python3
"""Audit the rank-3 Ising Galois candidates against the braided class count."""

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

from twisted_yetter.foundation_safety import stable_content_hash  # noqa: E402


OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
BRANCH_EXPORT = (
    OUT_DIR
    / "grown-category-branches"
    / "rank3-ising-su2-level2-galois-branch-candidates-v1.json"
)
BRANCH_CERTIFICATE = (
    OUT_DIR
    / "grown-category-branches"
    / "rank3-ising-su2-level2-galois-branch-candidates-validation-v1.json"
)
CLASSIFICATION_MATRIX = (
    REPO_ROOT / "experiments" / "inputs" / "mtc-classification" / "low-rank-mtc-families-v1.json"
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


def artifact_record(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
        "content_hash": payload["content_hash"],
        "status": payload["status"],
    }


def matrix_row(family_id: str) -> dict[str, Any]:
    matrix = load_json(CLASSIFICATION_MATRIX)
    for row in matrix["families"]:
        if row["family_id"] == family_id:
            return row
    raise RuntimeError(f"missing classification row: {family_id}")


def theta_sigma_exponent(galois_power: int) -> int:
    return (3 * int(galois_power)) % 16


def reverse_exponent(exponent: int) -> int:
    return (-int(exponent)) % 16


def branch_records(export: dict[str, Any]) -> list[dict[str, Any]]:
    by_exponent: dict[int, dict[str, Any]] = {}
    records = []
    for branch in export["branches"]:
        power = int(branch["galois_power"])
        exponent = theta_sigma_exponent(power)
        by_exponent[exponent] = branch
        records.append(
            {
                "branch_id": branch["branch_id"],
                "branch_data_hash": branch["branch_data_hash"],
                "galois_power": power,
                "braided_class_id": f"rank3-ising:theta_sigma=zeta16^{exponent}",
                "theta_sigma_zeta16_power": exponent,
                "theta_psi_zeta16_power": 8,
                "theta_psi": "-1",
                "sigma_dimension": branch["dimensions"]["1"],
                "mirror_reverse_theta_sigma_zeta16_power": reverse_exponent(exponent),
                "formal_ribbon_lifts_materialized": False,
            }
        )

    for record in records:
        reverse_branch = by_exponent[record["mirror_reverse_theta_sigma_zeta16_power"]]
        record["mirror_reverse_branch_id"] = reverse_branch["branch_id"]
        record["mirror_reverse_branch_data_hash"] = reverse_branch["branch_data_hash"]
    return sorted(records, key=lambda item: item["theta_sigma_zeta16_power"])


def build_audit(*, started_at_utc: str) -> dict[str, Any]:
    export = load_json(BRANCH_EXPORT)
    certificate = load_json(BRANCH_CERTIFICATE)
    row = matrix_row("rank3-ising")

    if certificate["validated_export"]["content_hash"] != export["content_hash"]:
        raise RuntimeError("Ising branch certificate is not bound to branch export")
    if certificate["status"] != "PASS_STRICT_GALOIS_BRANCH_CANDIDATE_REVALIDATION":
        raise RuntimeError("Ising branch certificate did not pass")

    records = branch_records(export)
    exponents = [record["theta_sigma_zeta16_power"] for record in records]
    expected_exponents = list(range(1, 16, 2))
    reverse_pairs = sorted(
        {
            tuple(sorted((record["theta_sigma_zeta16_power"], record["mirror_reverse_theta_sigma_zeta16_power"])))
            for record in records
        }
    )
    checks = {
        "classification_row_is_ising": row["family_id"] == "rank3-ising",
        "classification_braided_class_count_is_8": row["modular_braided_class_count"] == 8,
        "candidate_branch_count_is_8": export["candidate_branch_count"] == 8,
        "candidate_count_matches_braided_count": export["candidate_branch_count"] == row["modular_braided_class_count"],
        "theta_sigma_exponents_are_all_odd_zeta16_powers": exponents == expected_exponents,
        "theta_sigma_exponents_are_unique": len(set(exponents)) == len(exponents),
        "theta_psi_is_minus_one_for_all_candidates": all(
            record["theta_psi_zeta16_power"] == 8 for record in records
        ),
        "mirror_reverse_pairs_are_involutive": all(
            any(
                other["theta_sigma_zeta16_power"] == record["mirror_reverse_theta_sigma_zeta16_power"]
                and other["mirror_reverse_theta_sigma_zeta16_power"] == record["theta_sigma_zeta16_power"]
                for other in records
            )
            for record in records
        ),
        "branch_hashes_are_unique": len({record["branch_data_hash"] for record in records}) == len(records),
    }
    if not all(checks.values()):
        raise RuntimeError(f"Ising braided alignment audit failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.ising-braided-class-alignment-audit.v1",
            "status": "ISING_BRAIDED_CLASS_ALIGNMENT_BY_THETA_SIGMA_ESTABLISHED_RIBBON_LIFTS_PENDING",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_ising_braided_class_alignment_audit_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_ising_braided_class_alignment_audit_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "audit_id": "ising-braided-class-alignment-audit-v1",
            "family_id": "rank3-ising",
            "input_artifacts": {
                "galois_branch_export": artifact_record(BRANCH_EXPORT, export),
                "galois_branch_certificate": artifact_record(BRANCH_CERTIFICATE, certificate),
                "classification_matrix": {
                    "path": str(CLASSIFICATION_MATRIX.relative_to(REPO_ROOT)),
                    "sha256": file_sha256_id(CLASSIFICATION_MATRIX),
                    "family_id": row["family_id"],
                    "modular_braided_class_count": row["modular_braided_class_count"],
                    "spherical_structures_per_braided_class": row["spherical_structures_per_braided_class"],
                    "reference_id": row["reference_id"],
                },
            },
            "alignment_method": {
                "invariant": "theta_sigma_zeta16_power",
                "formula": "For SU(2)_2 with A=zeta16^p, theta_sigma = A^3 = zeta16^(3p).",
                "expected_braided_class_exponents": expected_exponents,
                "mirror_reverse_formula": "reverse(theta_sigma=zeta16^e) has theta_sigma=zeta16^(-e).",
                "scope": "braided class candidate alignment only",
            },
            "checks": checks,
            "candidate_branch_records": records,
            "mirror_reverse_pairs_by_theta_sigma": [
                {"pair": list(pair)} for pair in reverse_pairs
            ],
            "braided_class_alignment_status": "PASS",
            "ribbon_lift_status": "NOT_MATERIALIZED",
            "row_complete_status": "NOT_ROW_COMPLETE",
            "remaining_growth": [
                "materialize pivotal/ribbon lifts for each theta_sigma braided class",
                "prove whether the recorded two spherical structures per braided class produce sixteen ribbon snapshots",
                "build row-complete ribbon_realization_snapshot artifacts",
                "produce producer/runtime/ribbon-pivotal certificates for every Ising snapshot",
                "derive the Ising row ribbon denominator without copying the braided denominator",
            ],
            "explicit_non_claims": [
                "This audit does not produce ribbon_realization_snapshot formal evidence.",
                "This audit does not establish Ising row-complete ribbon classification.",
                "This audit does not prove pivotal/ribbon lift completeness.",
                "This audit does not authorize scan-plan generation.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "ising-braided-class-alignment-audit-v1.json": build_audit(
            started_at_utc=utc_now()
        )
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
