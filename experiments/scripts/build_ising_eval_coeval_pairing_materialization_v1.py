#!/usr/bin/env python3
"""Attempt Ising evaluation/coevaluation/pairing materialization, fail closed."""

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
CANDIDATE_PAYLOADS = OUT_DIR / "ising-ribbon-lift-candidate-payloads-v1.json"
CERTIFICATION_PREFLIGHT = OUT_DIR / "ising-ribbon-lift-certification-preflight-v1.json"
NUMERIC_PIVOTAL_PROFILE = (
    REPO_ROOT / "experiments" / "inputs" / "category-pivotal" / "su2-k-standard-pivotal-v1.json"
)
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"


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


def artifact_record(path: Path, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    record = {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": file_sha256_id(path),
    }
    if payload is not None:
        record["content_hash"] = payload["content_hash"]
        record["status"] = payload["status"]
    return record


def sqrt_expression(value: str) -> str:
    if value == "1":
        return "1"
    return f"sqrt({value})"


def fusion_channel_basis(fusion: dict[str, list[int]]) -> dict[str, dict[str, Any]]:
    channels = {}
    for product, outputs in sorted(fusion.items()):
        left, right = product.split("x")
        for output in outputs:
            channel_id = f"{left},{right}->{output}"
            channels[channel_id] = {
                "basis": [f"v({channel_id})"],
                "pairing_matrix": [["1"]],
                "inverse_pairing_matrix": [["1"]],
                "pairing_formula": "multiplicity-free orthonormal q-6j path basis candidate",
            }
    return channels


def materialization_attempt(payload: dict[str, Any]) -> dict[str, Any]:
    dimensions = payload["candidate_pivotal_data"]["simple_dimensions"]
    duals = payload["category_payload"]["duals"]
    labels = [str(label) for label in payload["category_payload"]["labels"]]
    attempts = {
        label: {
            "dual": str(duals[label]),
            "candidate_pivotal_dimension": dimensions[label],
            "left_evaluation_scalar_formula": sqrt_expression(dimensions[label]),
            "left_coevaluation_scalar_formula": sqrt_expression(dimensions[label]),
            "right_evaluation_scalar_formula": sqrt_expression(dimensions[label]),
            "right_coevaluation_scalar_formula": sqrt_expression(dimensions[label]),
            "normalization_source": "numeric SU(2)_k pivotal profile records sqrt(quantum_dimension), but this profile is not a formal row certificate",
        }
        for label in labels
    }
    blockers = [
        "numeric_su2k_pivotal_profile_not_formal_certificate",
        "su2k_evaluator_has_no_formal_eval_coeval_map_exporter",
        "square_root_branch_for_candidate_pivotal_dimensions_not_formally_pinned",
        "fusion_pairing_orthonormality_not_formally_certified_for_row_completion",
        "candidate_galois_branch_sqrt_convention_not_row_certified",
    ]
    attempt_body = {
        "slot_id": payload["slot_id"],
        "braided_class_id": payload["braided_class_id"],
        "candidate_payload_hash": payload["candidate_payload_hash"],
        "source_branch_id": payload["source_branch_id"],
        "source_branch_data_hash": payload["source_branch_data_hash"],
        "spherical_lift_label": payload["spherical_lift_label"],
        "attempt_status": "BLOCKED_FORMAL_MAP_SOURCE_OR_BRANCH_CONVENTION_MISSING",
        "proposed_map_formulas_not_formal_evidence": attempts,
        "proposed_pairing_not_formal_evidence": {
            "basis_gauge": payload["category_payload"]["basis_gauge"],
            "fusion_channels": fusion_channel_basis(payload["category_payload"]["fusion"]),
        },
        "materialized_evaluation_coevaluation_maps": False,
        "materialized_fusion_pairing": False,
        "formal_certificate_produced": False,
        "formal_snapshot_produced": False,
        "blockers": blockers,
    }
    return {**attempt_body, "attempt_hash": stable_content_hash(attempt_body)}


def build_materialization(*, started_at_utc: str) -> dict[str, Any]:
    payload_set = load_json(CANDIDATE_PAYLOADS)
    preflight = load_json(CERTIFICATION_PREFLIGHT)
    numeric_profile = load_json(NUMERIC_PIVOTAL_PROFILE)

    if payload_set["status"] != (
        "ISING_RIBBON_LIFT_CANDIDATE_PAYLOADS_MATERIALIZED_NOT_CERTIFIED"
    ):
        raise RuntimeError("Ising candidate payload set is not in the expected state")
    if preflight["status"] != "ISING_RIBBON_LIFT_CERTIFICATION_BLOCKED":
        raise RuntimeError("Ising certification preflight is not in the expected state")

    attempts = [materialization_attempt(payload) for payload in payload_set["candidate_payloads"]]
    checks = {
        "input_candidate_payload_count_is_16": payload_set["candidate_payload_count"] == 16,
        "input_preflight_blocked_all_16_payloads": preflight["blocked_payload_count"] == 16
        and preflight["ready_for_snapshot_promotion_count"] == 0,
        "attempt_count_is_16": len(attempts) == 16,
        "attempt_hashes_are_unique": len({attempt["attempt_hash"] for attempt in attempts})
        == len(attempts),
        "all_attempts_blocked": all(
            attempt["attempt_status"]
            == "BLOCKED_FORMAL_MAP_SOURCE_OR_BRANCH_CONVENTION_MISSING"
            for attempt in attempts
        ),
        "no_eval_coeval_maps_materialized": all(
            attempt["materialized_evaluation_coevaluation_maps"] is False
            for attempt in attempts
        ),
        "no_pairing_materialized": all(
            attempt["materialized_fusion_pairing"] is False for attempt in attempts
        ),
        "no_formal_certificates_or_snapshots": all(
            attempt["formal_certificate_produced"] is False
            and attempt["formal_snapshot_produced"] is False
            for attempt in attempts
        ),
        "numeric_pivotal_profile_is_not_formal_certificate": numeric_profile["status"]
        == "SUPPORTED_FOR_NUMERIC_MORSE_CONTROLS"
        and numeric_profile["pivotal_structure"]["mathematical_status"]
        == "NUMERIC_CONTROL_PROFILE_NOT_FORMAL_CERTIFICATE",
        "every_attempt_records_square_root_branch_blocker": all(
            "square_root_branch_for_candidate_pivotal_dimensions_not_formally_pinned"
            in attempt["blockers"]
            for attempt in attempts
        ),
    }
    if not all(checks.values()):
        raise RuntimeError(f"Ising eval/coeval materialization checks failed: {checks}")

    return with_hash(
        {
            "schema": "twisted-yetter.ising-eval-coeval-pairing-materialization.v1",
            "status": "ISING_EVAL_COEVAL_PAIRING_MATERIALIZATION_BLOCKED",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_ising_eval_coeval_pairing_materialization_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_ising_eval_coeval_pairing_materialization_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "materialization_id": "ising-eval-coeval-pairing-materialization-v1",
            "family_id": "rank3-ising",
            "input_artifacts": {
                "candidate_payload_set": artifact_record(CANDIDATE_PAYLOADS, payload_set),
                "certification_preflight": artifact_record(
                    CERTIFICATION_PREFLIGHT, preflight
                ),
                "numeric_pivotal_profile_reference": {
                    **artifact_record(NUMERIC_PIVOTAL_PROFILE),
                    "status": numeric_profile["status"],
                    "formal_certificate": False,
                },
                "su2k_evaluator": artifact_record(SU2K_EVALUATOR),
            },
            "attempt_scope": {
                "candidate_payload_count": len(attempts),
                "attempted_data": [
                    "evaluation scalar formulas",
                    "coevaluation scalar formulas",
                    "multiplicity-free pairing formulas",
                ],
                "strict_boundary": "Formula proposals are recorded as non-evidence until square-root branch, gauge, pairing, and producer/runtime/ribbon certificates are formalized.",
            },
            "checks": checks,
            "attempt_count": len(attempts),
            "blocked_attempt_count": len(attempts),
            "materialized_map_count": 0,
            "materialized_pairing_count": 0,
            "formal_certificate_count": 0,
            "formal_snapshot_count": 0,
            "row_complete_status": "NOT_ROW_COMPLETE",
            "formal_scan_plan_allowed": False,
            "attempt_records": attempts,
            "blocking_requirements_summary": [
                "Need a formal SU(2)_2 evaluation/coevaluation map exporter or derivation in the pinned Galois branch gauge.",
                "Need square-root branch choices for the candidate pivotal dimensions, including negative spherical lifts.",
                "Need a formal proof that the recorded multiplicity-free q-6j path basis pairing is the pairing consumed by the evaluator.",
                "Need producer/runtime/ribbon-pivotal certificates after maps and pairings are materialized.",
            ],
            "remaining_growth": [
                "implement or source formal evaluation/coevaluation maps in the pinned SU(2)_2 branch gauge",
                "pin square-root branches for every candidate pivotal dimension",
                "certify multiplicity-free pairing invertibility in the exact field embedding",
                "rerun this materialization artifact to produce ISING_EVAL_COEVAL_PAIRING_MATERIALIZED_NOT_CERTIFIED",
                "only then run producer/runtime/ribbon-pivotal certificates",
            ],
            "explicit_non_claims": [
                "This artifact does not materialize formal evaluation/coevaluation maps.",
                "This artifact does not certify fusion pairings.",
                "This artifact does not produce ribbon_realization_snapshot formal evidence.",
                "This artifact does not establish Ising row-complete ribbon classification.",
                "This artifact does not authorize scan-plan generation.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "ising-eval-coeval-pairing-materialization-v1.json": build_materialization(
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
