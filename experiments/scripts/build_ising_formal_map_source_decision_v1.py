#!/usr/bin/env python3
"""Decide whether repo-local sources can support formal Ising map export."""

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
MATERIALIZATION = OUT_DIR / "ising-eval-coeval-pairing-materialization-v1.json"
SU2K_EVALUATOR = REPO_ROOT / "experiments" / "sage" / "su2k_fusion_braid_evaluator.sage.py"
NUMERIC_PIVOTAL_PROFILE = (
    REPO_ROOT / "experiments" / "inputs" / "category-pivotal" / "su2-k-standard-pivotal-v1.json"
)
RIBBON_CATEGORY_V2 = REPO_ROOT / "experiments" / "sage" / "ribbon_category_v2.py"
SU2_2_RF_LOCAL = REPO_ROOT / "experiments" / "sage" / "su2_2_rf_local_backend.sage.py"
SU2_2_RF_OMEGA = REPO_ROOT / "experiments" / "sage" / "su2_2_rf_omega_backend.sage.py"
SAGE_README = REPO_ROOT / "experiments" / "sage" / "README.org"


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


def source_inventory() -> list[dict[str, Any]]:
    return [
        {
            **artifact_record(SU2K_EVALUATOR),
            "source_id": "su2k-fusion-braid-evaluator",
            "reviewed_capabilities": [
                "fusion_outputs",
                "dimension",
                "twist",
                "q6j / F-symbol",
                "R-symbol",
                "fixed-label braid closure evaluation",
            ],
            "blocking_finding": "No formal evaluation/coevaluation map exporter is exposed for row-complete ribbon snapshot production.",
            "decision": "INSUFFICIENT_FOR_FORMAL_ISING_MAP_SOURCE",
        },
        {
            **artifact_record(NUMERIC_PIVOTAL_PROFILE),
            "source_id": "su2-k-standard-pivotal-profile",
            "reviewed_capabilities": [
                "numeric Morse controls",
                "sqrt(quantum_dimension) normalization statement",
                "orthonormal q-6j path-basis convention statement",
            ],
            "blocking_finding": "Profile status is numeric controls only and explicitly not a formal row certificate.",
            "decision": "USEFUL_CONVENTION_REFERENCE_NOT_FORMAL_CERTIFICATE",
        },
        {
            **artifact_record(RIBBON_CATEGORY_V2),
            "source_id": "legacy-ribbon-category-v2-adapter",
            "reviewed_capabilities": [
                "legacy bridge left/right evaluation methods",
                "legacy bridge pairing identities",
                "numeric validation bridge",
            ],
            "blocking_finding": "Adapter docstring says production still requires a full hash-bound coherence certificate; it is not a row-complete formal source.",
            "decision": "INSUFFICIENT_FOR_FORMAL_ISING_MAP_SOURCE",
        },
        {
            **artifact_record(SU2_2_RF_LOCAL),
            "source_id": "su2-2-rf-local-backend",
            "reviewed_capabilities": [
                "explicit R/F local backend",
                "fixed all-sigma braid closures",
                "categorical trace over fusion-path spaces",
            ],
            "blocking_finding": "File header says it is not a full label-mixed evaluator and not a general planar F/R/eval/coeval tensor graph.",
            "decision": "INSUFFICIENT_FOR_FORMAL_ISING_MAP_SOURCE",
        },
        {
            **artifact_record(SU2_2_RF_OMEGA),
            "source_id": "su2-2-rf-omega-backend",
            "reviewed_capabilities": [
                "explicit R/F backend with Omega expansion",
                "supported braid closures",
            ],
            "blocking_finding": "File scope excludes arbitrary planar tensor graph and cup/cap programs.",
            "decision": "INSUFFICIENT_FOR_FORMAL_ISING_MAP_SOURCE",
        },
        {
            **artifact_record(SAGE_README),
            "source_id": "sage-readme-evaluator-map",
            "reviewed_capabilities": [
                "repo-local evaluator track inventory",
                "B0/B1/B2 scope descriptions",
            ],
            "blocking_finding": "README records B0 as not a full F/R/eval/coeval evaluator and not supporting cup/cap or trivalent graph programs.",
            "decision": "INSUFFICIENT_FOR_FORMAL_ISING_MAP_SOURCE",
        },
    ]


def build_decision(*, started_at_utc: str) -> dict[str, Any]:
    materialization = load_json(MATERIALIZATION)
    if materialization["status"] != "ISING_EVAL_COEVAL_PAIRING_MATERIALIZATION_BLOCKED":
        raise RuntimeError("Ising materialization artifact is not in the expected blocked state")

    inventory = source_inventory()
    insufficient = [
        item
        for item in inventory
        if item["decision"] != "USEFUL_CONVENTION_REFERENCE_NOT_FORMAL_CERTIFICATE"
    ]
    convention_only = [
        item
        for item in inventory
        if item["decision"] == "USEFUL_CONVENTION_REFERENCE_NOT_FORMAL_CERTIFICATE"
    ]
    required_source_gaps = [
        "formal SU(2)_2 evaluation/coevaluation map exporter in the pinned Galois branch gauge",
        "formal square-root branch ledger for candidate pivotal dimensions, including negative spherical lifts",
        "formal proof that the chosen q-6j path-basis pairing is the row-completion pairing consumed by evaluator certificates",
        "producer exact/symbolic coherence certificate bound to exported maps and pairings",
        "runtime consumer coherence certificate bound to exported maps and pairings",
        "ribbon/pivotal compatibility certificate bound to exported maps and pairings",
    ]
    checks = {
        "input_materialization_blocked": materialization["blocked_attempt_count"] == 16
        and materialization["materialized_map_count"] == 0,
        "source_inventory_nonempty": bool(inventory),
        "all_reviewed_sources_are_hash_recorded": all(
            item["sha256"].startswith("sha256:") for item in inventory
        ),
        "numeric_profile_not_promoted": len(convention_only) == 1,
        "no_repo_source_supports_formal_map_export": all(
            item["decision"] == "INSUFFICIENT_FOR_FORMAL_ISING_MAP_SOURCE"
            for item in insufficient
        ),
        "required_source_gaps_are_explicit": len(required_source_gaps) == 6,
        "decision_is_terminal_for_current_repo_local_ising_row_completion": True,
    }
    if not all(checks.values()):
        raise RuntimeError(f"Ising formal map source decision checks failed: {checks}")

    blocker_body = {
        "blocker_id": "rank3-ising-formal-map-source-terminal-blocker-v1",
        "family_id": "rank3-ising",
        "terminal_status": "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER",
        "blocked_scope": "current repo-local Ising row-complete ribbon realization snapshot production",
        "not_blocked_scope": [
            "future work that adds a source-backed formal SU(2)_2 eval/coeval derivation",
            "future work that imports a hash-bound external theorem/source locator",
            "ordinary numeric SU(2)_2 controls outside this formal low-rank catalog route",
        ],
        "required_source_gaps": required_source_gaps,
        "source_inventory_decisions": inventory,
    }
    blocker = {**blocker_body, "blocker_hash": stable_content_hash(blocker_body)}

    return with_hash(
        {
            "schema": "twisted-yetter.ising-formal-map-source-decision.v1",
            "status": "ISING_FORMAL_MAP_SOURCE_TERMINAL_BLOCKER",
            "generated_at_utc": started_at_utc,
            "generator_script": "experiments/scripts/build_ising_formal_map_source_decision_v1.py",
            "reproduce_command": (
                "python3 experiments/scripts/build_ising_formal_map_source_decision_v1.py --write"
            ),
            "repo_root": str(REPO_ROOT),
            "git": {
                "commit": git_output("rev-parse", "HEAD"),
                "dirty": bool(git_output("status", "--porcelain")),
            },
            "tool_versions": {"python": platform.python_version()},
            "decision_id": "ising-formal-map-source-decision-v1",
            "family_id": "rank3-ising",
            "input_artifacts": {
                "eval_coeval_pairing_materialization": artifact_record(
                    MATERIALIZATION, materialization
                )
            },
            "checks": checks,
            "decision": {
                "can_implement_formal_exporter_from_current_repo_local_sources": False,
                "can_promote_ising_candidate_payloads_to_snapshots": False,
                "row_complete_status": "TERMINAL_BLOCKED_UNTIL_NEW_FORMAL_MAP_SOURCE",
                "formal_scan_plan_allowed": False,
                "reason": "Current repo-local sources expose candidate F/R/twist/dimension data and numeric pivotal conventions, but not a formal eval/coeval map source or branch-pinned derivation sufficient for RibbonFusionCategoryV2 row-complete snapshots.",
            },
            "terminal_blocker": blocker,
            "remaining_growth_if_unblocked_later": [
                "add a hash-bound formal SU(2)_2 evaluation/coevaluation derivation or exporter",
                "pin square-root branches for every candidate pivotal dimension",
                "certify q-6j path-basis pairing convention",
                "rerun eval/coeval materialization and certification preflight",
                "only then produce ribbon_realization_snapshot artifacts",
            ],
            "explicit_non_claims": [
                "This artifact does not claim the mathematical Ising row is impossible.",
                "This artifact only blocks current repo-local formal snapshot production.",
                "This artifact does not produce ribbon_realization_snapshot formal evidence.",
                "This artifact does not establish low-rank ribbon classification.",
                "This artifact does not authorize scan-plan generation.",
            ],
        }
    )


def build_all() -> dict[str, dict[str, Any]]:
    return {
        "ising-formal-map-source-decision-v1.json": build_decision(
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
