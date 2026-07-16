#!/usr/bin/env python3
"""Materialize hash-bound candidate payloads for the pending Ising ribbon lifts."""

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
SLOT_LEDGER = OUT_DIR / "ising-ribbon-lift-slot-ledger-v1.json"
BRANCH_EXPORT = (
    OUT_DIR
    / "grown-category-branches"
    / "rank3-ising-su2-level2-galois-branch-candidates-v1.json"
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


def branch_by_id(export: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {branch["branch_id"]: branch for branch in export["branches"]}


def build_candidate_payload(slot: dict[str, Any], branch: dict[str, Any]) -> dict[str, Any]:
    if slot["source_branch_data_hash"] != branch["branch_data_hash"]:
        raise RuntimeError(f"slot source hash mismatch: {slot['slot_id']}")

    payload_body = {
        "payload_schema": "twisted-yetter.ising-ribbon-lift-candidate-payload.v1",
        "payload_status": "CANDIDATE_PAYLOAD_MATERIALIZED_NOT_CERTIFIED",
        "family_id": "rank3-ising",
        "slot_id": slot["slot_id"],
        "braided_class_id": slot["braided_class_id"],
        "source_branch_id": branch["branch_id"],
        "source_branch_data_hash": branch["branch_data_hash"],
        "source_galois_power": branch["galois_power"],
        "theta_sigma_zeta16_power": slot["theta_sigma_zeta16_power"],
        "theta_psi_zeta16_power": slot["theta_psi_zeta16_power"],
        "spherical_lift_index": slot["spherical_lift_index"],
        "spherical_lift_label": slot["spherical_lift_label"],
        "category_payload": {
            "labels": branch["labels"],
            "unit": branch["unit"],
            "fusion": branch["fusion"],
            "duals": branch["duals"],
            "f_symbols": branch["f_symbols"],
            "r_symbols": branch["r_symbols"],
            "twists": branch["twists"],
            "basis_gauge": branch["basis_gauge"],
            "field_embedding": branch["field_embedding"],
            "level": branch["level"],
            "root_order": branch["root_order"],
        },
        "candidate_pivotal_data": {
            "simple_dimensions": {
                "0": "1",
                "1": slot["candidate_pivotal_sigma_dimension"],
                "2": slot["candidate_pivotal_psi_dimension"],
            },
            "evaluation_coevaluation_status": "CANDIDATE_DIMENSIONS_ONLY_NOT_MATERIALIZED",
            "pairing_status": "NOT_FORMALLY_CERTIFIED_FOR_ROW_COMPLETION",
            "source_warning": (
                "This slot binds the candidate spherical dimension sign to the F/R/twist payload, "
                "but it does not materialize evaluation/coevaluation maps."
            ),
        },
        "formal_ribbon_realization_snapshot_produced": False,
        "producer_exact_certificate_status": "MISSING",
        "runtime_consumer_certificate_status": "MISSING",
        "ribbon_pivotal_certificate_status": "MISSING",
        "row_complete_status": "NOT_ROW_COMPLETE",
        "explicit_non_claims": [
            "This payload is not formal ribbon_realization_snapshot evidence.",
            "This payload does not prove pivotal naturality, monoidality, or spherical trace.",
            "This payload does not prove twist/balancing/ribbon compatibility.",
            "This payload does not establish the Ising row ribbon denominator.",
            "This payload does not authorize scan-plan generation.",
        ],
    }
    payload = dict(payload_body)
    payload["candidate_payload_hash"] = stable_content_hash(payload_body)
    return payload


def build_candidate_payloads(*, started_at_utc: str) -> dict[str, Any]:
    slot_ledger = load_json(SLOT_LEDGER)
    branch_export = load_json(BRANCH_EXPORT)

    if slot_ledger["status"] != "ISING_RIBBON_LIFT_SLOTS_ENUMERATED_NOT_MATERIALIZED":
        raise RuntimeError("Ising ribbon-lift slot ledger is not in the expected state")
    if branch_export["status"] != "SU2K_GALOIS_BRANCH_CANDIDATES_EXPORTED_NOT_ROW_COMPLETE":
        raise RuntimeError("Ising branch export is not in the expected state")

    branches = branch_by_id(branch_export)
    payloads = []
    for slot in slot_ledger["ribbon_lift_slots"]:
        if slot["source_branch_id"] not in branches:
            raise RuntimeError(f"missing source branch for slot: {slot['slot_id']}")
        payloads.append(build_candidate_payload(slot, branches[slot["source_branch_id"]]))

    payloads_by_braided_class: dict[str, list[str]] = {}
    for payload in payloads:
        payloads_by_braided_class.setdefault(payload["braided_class_id"], []).append(
            payload["candidate_payload_hash"]
        )
    payloads_by_braided_class = {
        key: sorted(value)
        for key, value in sorted(payloads_by_braided_class.items(), key=lambda item: item[0])
    }

    checks = {
        "input_slot_ledger_has_16_pending_slots": slot_ledger["pending_snapshot_count"] == 16,
        "input_slot_ledger_has_no_formal_snapshots": slot_ledger["formal_snapshot_count"] == 0,
        "branch_export_has_8_candidates": branch_export["candidate_branch_count"] == 8,
        "candidate_payload_count_is_16": len(payloads) == 16,
        "slot_ids_are_unique": len({payload["slot_id"] for payload in payloads}) == len(payloads),
        "candidate_payload_hashes_are_unique": len(
            {payload["candidate_payload_hash"] for payload in payloads}
        )
        == len(payloads),
        "two_payloads_per_braided_class": all(
            len(value) == 2 for value in payloads_by_braided_class.values()
        ),
        "all_payloads_are_not_formal_snapshots": all(
            payload["formal_ribbon_realization_snapshot_produced"] is False
            for payload in payloads
        ),
        "all_certificates_still_missing": all(
            payload["producer_exact_certificate_status"] == "MISSING"
            and payload["runtime_consumer_certificate_status"] == "MISSING"
            and payload["ribbon_pivotal_certificate_status"] == "MISSING"
            for payload in payloads
        ),
        "all_payloads_bind_source_branch_hash": all(
            payload["source_branch_data_hash"]
            == branches[payload["source_branch_id"]]["branch_data_hash"]
            for payload in payloads
        ),
        "all_payloads_include_f_r_twist_fusion": all(
            payload["category_payload"]["f_symbols"]
            and payload["category_payload"]["r_symbols"]
            and payload["category_payload"]["twists"]
            and payload["category_payload"]["fusion"]
            for payload in payloads
        ),
    }
    if not all(checks.values()):
        raise RuntimeError(f"Ising ribbon-lift candidate payload checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.ising-ribbon-lift-candidate-payloads.v1",
            "status": "ISING_RIBBON_LIFT_CANDIDATE_PAYLOADS_MATERIALIZED_NOT_CERTIFIED",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_ising_ribbon_lift_candidate_payloads_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_ising_ribbon_lift_candidate_payloads_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "payload_set_id": "ising-ribbon-lift-candidate-payloads-v1",
            "family_id": "rank3-ising",
            "input_artifacts": {
                "ising_ribbon_lift_slot_ledger": artifact_record(SLOT_LEDGER, slot_ledger),
                "galois_branch_export": artifact_record(BRANCH_EXPORT, branch_export),
            },
            "checks": checks,
            "payloads_by_braided_class": payloads_by_braided_class,
            "candidate_payload_count": len(payloads),
            "formal_snapshot_count": 0,
            "pending_certificate_count": len(payloads) * 3,
            "row_complete_status": "NOT_ROW_COMPLETE",
            "candidate_payloads": payloads,
            "remaining_growth": [
                "materialize evaluation and coevaluation maps for each slot",
                "check pivotal naturality, monoidality, and spherical trace per slot",
                "check twist/balancing/ribbon compatibility per slot",
                "produce producer/runtime/ribbon-pivotal certificates for every surviving slot",
                "promote only passing payloads to ribbon_realization_snapshot artifacts",
            ],
            "explicit_non_claims": [
                "This artifact materializes candidate payloads only; it is not formal evidence.",
                "This artifact does not prove that all sixteen slots survive ribbon compatibility.",
                "This artifact does not establish Ising row-complete ribbon classification.",
                "This artifact does not authorize scan-plan generation.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "ising-ribbon-lift-candidate-payloads-v1.json": build_candidate_payloads(
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
