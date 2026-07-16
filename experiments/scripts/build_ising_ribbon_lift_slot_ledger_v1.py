#!/usr/bin/env python3
"""Enumerate pending Ising ribbon-lift slots after braided-class alignment."""

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
ALIGNMENT_AUDIT = OUT_DIR / "ising-braided-class-alignment-audit-v1.json"


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


def signed_expression(sign: str, expression: str) -> str:
    if sign == "plus":
        return expression
    if expression.startswith("-"):
        return expression[1:]
    return f"-({expression})"


def slot_records(alignment: dict[str, Any]) -> list[dict[str, Any]]:
    slots = []
    for record in alignment["candidate_branch_records"]:
        for lift_index, sign in enumerate(["plus", "minus"], start=1):
            theta = record["theta_sigma_zeta16_power"]
            slots.append(
                {
                    "slot_id": (
                        f"rank3-ising:theta_sigma=zeta16^{theta}:"
                        f"spherical-lift={sign}"
                    ),
                    "family_id": "rank3-ising",
                    "braided_class_id": record["braided_class_id"],
                    "source_branch_id": record["branch_id"],
                    "source_branch_data_hash": record["branch_data_hash"],
                    "theta_sigma_zeta16_power": theta,
                    "theta_psi_zeta16_power": record["theta_psi_zeta16_power"],
                    "spherical_lift_index": lift_index,
                    "spherical_lift_label": sign,
                    "candidate_pivotal_sigma_dimension": signed_expression(
                        sign, record["sigma_dimension"]
                    ),
                    "candidate_pivotal_psi_dimension": "1",
                    "formal_ribbon_realization_snapshot_produced": False,
                    "producer_exact_certificate_status": "MISSING",
                    "runtime_consumer_certificate_status": "MISSING",
                    "ribbon_pivotal_certificate_status": "MISSING",
                    "slot_status": "PENDING_RIBBON_LIFT_MATERIALIZATION",
                }
            )
    return slots


def build_ledger(*, started_at_utc: str) -> dict[str, Any]:
    alignment = load_json(ALIGNMENT_AUDIT)
    if alignment["status"] != (
        "ISING_BRAIDED_CLASS_ALIGNMENT_BY_THETA_SIGMA_ESTABLISHED_RIBBON_LIFTS_PENDING"
    ):
        raise RuntimeError("Ising braided-class alignment audit is not in the expected state")
    if alignment["braided_class_alignment_status"] != "PASS":
        raise RuntimeError("Ising braided-class alignment did not pass")

    slots = slot_records(alignment)
    slots_by_class: dict[str, list[str]] = {}
    for slot in slots:
        slots_by_class.setdefault(slot["braided_class_id"], []).append(slot["slot_id"])
    slots_by_class = {
        key: sorted(value)
        for key, value in sorted(slots_by_class.items(), key=lambda item: item[0])
    }
    checks = {
        "input_alignment_audit_passed": True,
        "braided_class_count_is_8": len(alignment["candidate_branch_records"]) == 8,
        "spherical_lifts_per_braided_class_is_2": all(
            len(value) == 2 for value in slots_by_class.values()
        ),
        "candidate_slot_count_is_16": len(slots) == 16,
        "slot_ids_are_unique": len({slot["slot_id"] for slot in slots}) == len(slots),
        "no_formal_snapshots_produced": all(
            slot["formal_ribbon_realization_snapshot_produced"] is False
            for slot in slots
        ),
        "all_certificates_missing": all(
            slot["producer_exact_certificate_status"] == "MISSING"
            and slot["runtime_consumer_certificate_status"] == "MISSING"
            and slot["ribbon_pivotal_certificate_status"] == "MISSING"
            for slot in slots
        ),
    }
    if not all(checks.values()):
        raise RuntimeError(f"Ising ribbon-lift slot ledger failed checks: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.ising-ribbon-lift-slot-ledger.v1",
            "status": "ISING_RIBBON_LIFT_SLOTS_ENUMERATED_NOT_MATERIALIZED",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_ising_ribbon_lift_slot_ledger_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_ising_ribbon_lift_slot_ledger_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "ledger_id": "ising-ribbon-lift-slot-ledger-v1",
            "family_id": "rank3-ising",
            "input_artifacts": {
                "ising_braided_class_alignment_audit": artifact_record(
                    ALIGNMENT_AUDIT, alignment
                )
            },
            "slot_derivation": {
                "braided_class_count": 8,
                "spherical_structures_per_braided_class": 2,
                "candidate_slot_count": 16,
                "source": "low-rank classification matrix records two spherical structures per Ising braided class; this ledger enumerates required lift slots only.",
                "warning": "Slot enumeration is not proof that every slot is a compatible ribbon realization.",
            },
            "checks": checks,
            "slots_by_braided_class": slots_by_class,
            "ribbon_lift_slots": slots,
            "row_complete_status": "NOT_ROW_COMPLETE",
            "formal_snapshot_count": 0,
            "pending_snapshot_count": len(slots),
            "remaining_growth": [
                "materialize category data for each slot",
                "check pivotal naturality, monoidality, and spherical trace per slot",
                "check twist/balancing/ribbon compatibility per slot",
                "produce producer/runtime/ribbon-pivotal certificates for every slot",
                "promote only passing slots to ribbon_realization_snapshot artifacts",
            ],
            "explicit_non_claims": [
                "This ledger does not produce ribbon_realization_snapshot formal evidence.",
                "This ledger does not prove that all sixteen slots survive ribbon compatibility.",
                "This ledger does not establish Ising row-complete ribbon classification.",
                "This ledger does not authorize scan-plan generation.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "ising-ribbon-lift-slot-ledger-v1.json": build_ledger(
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
