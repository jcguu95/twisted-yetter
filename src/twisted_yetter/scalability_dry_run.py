"""Executable n75 scalability dry-run ledger.

This module records repo-local readiness and toy-scale inventory only.  It
does not run exotic computations, benchmark real exotic inputs, fetch data, or
promote any n80 route.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Final, Mapping

from twisted_yetter.artifacts import (
    default_tool_versions,
    dumps_certificate,
    git_metadata,
    hash_json,
    make_certificate,
)
from twisted_yetter.candidate_validation_suite import (
    CANDIDATE_VALIDATION_SUITE_SCHEMA,
    many_case_candidate_validation_suite_artifact,
    validate_candidate_validation_suite_metadata,
)
from twisted_yetter.decorated_kirby_gate import (
    DECORATED_KIRBY_GATE_SCHEMA,
    decorated_kirby_gate_artifact,
    validate_decorated_kirby_gate_artifact,
)
from twisted_yetter.exotic_input_certification import (
    EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
    EXOTIC_INPUT_CERTIFICATION_SCHEMA,
    exotic_input_certification_ledger_artifact,
    validate_exotic_input_certification_ledger_artifact,
)
from twisted_yetter.ordinary_surgery_gate import (
    ORDINARY_SURGERY_GATE_SCHEMA,
    ordinary_surgery_gate_certificate,
)
from twisted_yetter.presentation_pairs import (
    PRESENTATION_PAIR_REGISTRY_SCHEMA,
    presentation_pair_registry_artifact,
    validate_presentation_pair_registry_metadata,
)
from twisted_yetter.toy_closed_suite import (
    TOY_CLOSED_SUITE_SCHEMA,
    toy_closed_suite_ledger_artifact,
    validate_toy_closed_suite_ledger_artifact,
)

SCALABILITY_DRY_RUN_SCHEMA: Final = "twisted-yetter.scalability-dry-run.v1"
SCALABILITY_DRY_RUN_ARTIFACT: Final = (
    "experiments/results/scalability/n75-scalability-dry-run.json"
)
SCALABILITY_DRY_RUN_NOTE: Final = "wiki/understandings/scalability-dry-run.org"

NODE_ID: Final = "n75-scalability-dry-run"
CLAIM_LEVEL: Final = "dry-run/readiness ledger"

N70_DATA_BLOCKED_BLOCKER_ID: Final = "n70-exotic-input-certification-data-blocked"
N55_TOY_CLOSED_BLOCKED_BLOCKER_ID: Final = "n55-toy-closed-suite-blocked"
N50_DECORATED_GATE_BLOCKED_BLOCKER_ID: Final = "n50-decorated-kirby-move-gate-blocked"
N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID: Final = "n24-ordinary-surgery-gate-blocked"
NO_REAL_EXOTIC_INPUT_BLOCKER_ID: Final = "no-real-exotic-input-size-observed"

BLOCKED_CLAIMS: Final = (
    "n80 exotic computation route",
    "exotic smooth-structure detection claim",
    "marked or unmarked exotic distinction claim",
    "performance/scaling success claim for real exotic inputs",
    "closed 4-manifold invariant value claim",
)


def scalability_dry_run_artifact(
    *,
    n36: Mapping[str, object] | None = None,
    n45: Mapping[str, object] | None = None,
    n50: Mapping[str, object] | None = None,
    n55: Mapping[str, object] | None = None,
    n70: Mapping[str, object] | None = None,
    claim_n80_route: bool = False,
    claim_exotic_computation: bool = False,
    claim_real_scaling_success: bool = False,
    claim_exotic_detection: bool = False,
) -> dict[str, object]:
    """Return the deterministic n75 readiness/scaling ledger.

    Claim flags are explicit refusal checks.  n75 is allowed to count existing
    repo-local toy metadata, but it is not allowed to enter n80 or to describe
    real exotic-input performance.
    """

    if (
        claim_n80_route
        or claim_exotic_computation
        or claim_real_scaling_success
        or claim_exotic_detection
    ):
        raise ValueError(
            "n75-scalability-dry-run is dry-run-blocked by n70 and refuses "
            "n80 routing, exotic computation, real exotic scaling success, "
            "and exotic detection claims"
        )

    suite = many_case_candidate_validation_suite_artifact() if n36 is None else dict(n36)
    registry = presentation_pair_registry_artifact() if n45 is None else dict(n45)
    ordinary_gate = ordinary_surgery_gate_certificate()
    decorated_gate = decorated_kirby_gate_artifact(registry) if n50 is None else dict(n50)
    toy_suite = (
        toy_closed_suite_ledger_artifact(
            candidate_suite=suite,
            pair_registry=registry,
            ordinary_gate=ordinary_gate,
            decorated_gate=decorated_gate,
        )
        if n55 is None
        else dict(n55)
    )
    exotic_gate = (
        exotic_input_certification_ledger_artifact(
            ordinary_gate=ordinary_gate,
            decorated_gate=decorated_gate,
            toy_closed_suite=toy_suite,
        )
        if n70 is None
        else dict(n70)
    )

    artifact: dict[str, object] = {
        "schema": SCALABILITY_DRY_RUN_SCHEMA,
        "status": "dry-run-blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "n75 consumes repo-local n36/n45/n50/n55/n70 metadata and records "
            "toy-scale inventory plus blockers; no downloads, no real exotic "
            "input computation, and no performance benchmark are performed"
        ),
        "upstream_nodes": [
            "n24-ordinary-surgery-gate",
            "n36-many-case-candidate-validation-suite",
            "n45-kirby-presentation-pair-generator",
            "n50-decorated-kirby-move-gate",
            "n55-toy-closed-suite",
            "n70-exotic-input-certification",
        ],
        "input_artifacts": {
            "n70_exotic_input_certification": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
        },
        "input_schemas": {
            "ordinary_surgery_gate": ordinary_gate.get("schema"),
            "candidate_validation_suite": suite.get("schema"),
            "presentation_pair_registry": registry.get("schema"),
            "decorated_kirby_gate": decorated_gate.get("schema"),
            "toy_closed_suite": toy_suite.get("schema"),
            "exotic_input_certification": exotic_gate.get("schema"),
        },
        "input_statuses": {
            "ordinary_surgery_gate": ordinary_gate.get("status"),
            "candidate_validation_suite": suite.get("status"),
            "presentation_pair_registry": registry.get("status"),
            "decorated_kirby_gate": decorated_gate.get("status"),
            "toy_closed_suite": toy_suite.get("status"),
            "exotic_input_certification": exotic_gate.get("status"),
        },
        "input_validations": {
            "candidate_validation_suite": validate_candidate_validation_suite_metadata(
                suite
            ),
            "presentation_pair_registry": validate_presentation_pair_registry_metadata(
                registry
            ),
            "decorated_kirby_gate": validate_decorated_kirby_gate_artifact(
                decorated_gate
            ),
            "toy_closed_suite": validate_toy_closed_suite_ledger_artifact(toy_suite),
            "exotic_input_certification": (
                validate_exotic_input_certification_ledger_artifact(exotic_gate)
            ),
        },
        "toy_scale_inventory": _toy_scale_inventory(
            n36=suite,
            n45=registry,
            n50=decorated_gate,
            n55=toy_suite,
            n70=exotic_gate,
        ),
        "readiness_routes": _readiness_routes(
            ordinary_gate=ordinary_gate,
            decorated_gate=decorated_gate,
            toy_suite=toy_suite,
            exotic_gate=exotic_gate,
        ),
        "blocked_reason_ids": [
            N70_DATA_BLOCKED_BLOCKER_ID,
            N55_TOY_CLOSED_BLOCKED_BLOCKER_ID,
            N50_DECORATED_GATE_BLOCKED_BLOCKER_ID,
            N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID,
            NO_REAL_EXOTIC_INPUT_BLOCKER_ID,
        ],
        "blockers": _blockers(
            ordinary_gate=ordinary_gate,
            decorated_gate=decorated_gate,
            toy_suite=toy_suite,
            exotic_gate=exotic_gate,
        ),
        "n80_exotic_computation_route_allowed": False,
        "real_exotic_input_scaling_claim_allowed": False,
        "performance_benchmark_claim_allowed": False,
        "exotic_detection_claim_allowed": False,
        "closed_4_manifold_invariant_claim_allowed": False,
        "blocked_claims": list(BLOCKED_CLAIMS),
        "required_unblock_artifacts": [
            "n70 pass artifact selecting one certified exotic pair target",
            "machine-readable Kirby or handle data for both sides of the selected pair",
            "source reference records with exact page/figure/theorem ids and hashes",
            "H2/homeomorphism marking certificate with integer basis matrices",
            "n24 ordinary surgery gate pass certificate",
            "n50 decorated Kirby move gate pass certificate",
            "n55 closed toy suite pass certificate before promoting beyond toy metadata",
            "separate real-input benchmark artifact after real certified inputs exist",
        ],
        "claim_boundary": (
            "n75 is an executable dry-run/readiness ledger over existing "
            "repo-local metadata; it is not n80, not an exotic calculation, "
            "and not evidence of real exotic-input scalability"
        ),
        "ledger_note": SCALABILITY_DRY_RUN_NOTE,
        "artifact_path": SCALABILITY_DRY_RUN_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_scalability_dry_run_artifact(artifact)
    return artifact


def validate_scalability_dry_run_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n75 dry-run shape without certifying any scaling claim."""

    required = {
        "schema",
        "status",
        "node_id",
        "claim_level",
        "input_schemas",
        "input_statuses",
        "toy_scale_inventory",
        "readiness_routes",
        "blocked_reason_ids",
        "blockers",
        "blocked_claims",
        "required_unblock_artifacts",
    }
    missing = sorted(field for field in required if field not in artifact)
    input_schemas = artifact.get("input_schemas", {})
    input_schemas_ok = isinstance(input_schemas, Mapping) and input_schemas == {
        "ordinary_surgery_gate": ORDINARY_SURGERY_GATE_SCHEMA,
        "candidate_validation_suite": CANDIDATE_VALIDATION_SUITE_SCHEMA,
        "presentation_pair_registry": PRESENTATION_PAIR_REGISTRY_SCHEMA,
        "decorated_kirby_gate": DECORATED_KIRBY_GATE_SCHEMA,
        "toy_closed_suite": TOY_CLOSED_SUITE_SCHEMA,
        "exotic_input_certification": EXOTIC_INPUT_CERTIFICATION_SCHEMA,
    }
    blockers = artifact.get("blocked_reason_ids", [])
    blockers_ok = (
        isinstance(blockers, list)
        and set(blockers)
        >= {
            N70_DATA_BLOCKED_BLOCKER_ID,
            N55_TOY_CLOSED_BLOCKED_BLOCKER_ID,
            N50_DECORATED_GATE_BLOCKED_BLOCKER_ID,
            N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID,
            NO_REAL_EXOTIC_INPUT_BLOCKER_ID,
        }
    )
    inventory = artifact.get("toy_scale_inventory", {})
    inventory_ok = (
        isinstance(inventory, Mapping)
        and inventory.get("n36_case_count") == 8
        and inventory.get("n45_pair_count") == 4
        and inventory.get("n50_pair_classification_count") == 4
        and inventory.get("n55_toy_case_count") == 8
        and inventory.get("n70_candidate_count") == 4
        and inventory.get("real_exotic_input_count") == 0
    )
    routes = artifact.get("readiness_routes", {})
    routes_ok = (
        isinstance(routes, Mapping)
        and routes.get("n80-exotic-computation") == "blocked"
        and routes.get("real_exotic_scaling_benchmark") == "blocked"
    )
    blocked_claims_ok = all(
        artifact.get(field) is False
        for field in (
            "n80_exotic_computation_route_allowed",
            "real_exotic_input_scaling_claim_allowed",
            "performance_benchmark_claim_allowed",
            "exotic_detection_claim_allowed",
            "closed_4_manifold_invariant_claim_allowed",
        )
    )
    return {
        "valid": (
            not missing
            and artifact.get("schema") == SCALABILITY_DRY_RUN_SCHEMA
            and artifact.get("status") == "dry-run-blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("claim_level") == CLAIM_LEVEL
            and input_schemas_ok
            and blockers_ok
            and inventory_ok
            and routes_ok
            and blocked_claims_ok
        ),
        "missing_required_fields": missing,
        "input_schemas_ok": input_schemas_ok,
        "blockers_ok": blockers_ok,
        "toy_scale_inventory_ok": inventory_ok,
        "routes_ok": routes_ok,
        "blocked_claims_ok": blocked_claims_ok,
        "scope": "n75 dry-run/readiness ledger only; no n80 computation or benchmark",
    }


def stable_scalability_dry_run_json(artifact: Mapping[str, object]) -> str:
    """Serialize an n75 dry-run artifact deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def scalability_dry_run_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a certificate envelope for the current n75 dry-run ledger."""

    root = Path(repo_root)
    exact_output = scalability_dry_run_artifact()
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.scalability_dry_run --write "
            f"{SCALABILITY_DRY_RUN_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.scalability_dry_run",
            "--write",
            SCALABILITY_DRY_RUN_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "upstream_statuses": exact_output["input_statuses"],
                "toy_scale_inventory": exact_output["toy_scale_inventory"],
                "blocked_reason_ids": exact_output["blocked_reason_ids"],
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/scalability_dry_run.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.scalability_dry_run --write "
            "experiments/results/scalability/n75-scalability-dry-run.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n75 is dry-run-blocked because n70 is data-blocked.",
            "No real exotic input computation, download, or benchmark is performed.",
        ],
    )


def _toy_scale_inventory(
    *,
    n36: Mapping[str, object],
    n45: Mapping[str, object],
    n50: Mapping[str, object],
    n55: Mapping[str, object],
    n70: Mapping[str, object],
) -> dict[str, object]:
    cases = _list_or_empty(n36.get("cases"))
    pairs = _list_or_empty(n45.get("pairs"))
    pair_classifications = _list_or_empty(n50.get("pair_classifications"))
    toy_cases = _list_or_empty(n55.get("toy_cases"))
    candidates = _list_or_empty(n70.get("candidate_results"))
    fixture_paths = sorted(
        {
            str(case.get("fixture_path"))
            for case in cases
            if isinstance(case, Mapping) and case.get("fixture_path")
        }
    )
    diagram_ids = sorted(
        {
            str(case.get("diagram_id"))
            for case in cases
            if isinstance(case, Mapping) and case.get("diagram_id")
        }
    )
    component_slots = sum(
        len(_list_or_empty(case.get("diagram_component_ids")))
        for case in cases
        if isinstance(case, Mapping)
    )
    sector_slots = sum(
        len(_list_or_empty(case.get("component_sector_ids")))
        for case in cases
        if isinstance(case, Mapping)
    )
    return {
        "n36_case_count": _int_field(n36, "case_count", len(cases)),
        "n36_unique_fixture_count": len(fixture_paths),
        "n36_unique_diagram_count": len(diagram_ids),
        "n36_total_component_slots": component_slots,
        "n36_total_sector_slots": sector_slots,
        "n45_pair_count": _int_field(n45, "pair_count", len(pairs)),
        "n50_pair_classification_count": _int_field(
            n50, "pair_count", len(pair_classifications)
        ),
        "n55_toy_case_count": _int_field(n55, "case_count", len(toy_cases)),
        "n70_candidate_count": _int_field(n70, "candidate_count", len(candidates)),
        "real_exotic_input_count": 0,
        "certified_n80_target_count": 0,
        "counting_scope": (
            "deterministic counts over existing repo-local toy/candidate "
            "metadata only"
        ),
        "real_input_scope": (
            "no certified real exotic Kirby diagrams or H2 markings are "
            "available to size"
        ),
    }


def _readiness_routes(
    *,
    ordinary_gate: Mapping[str, object],
    decorated_gate: Mapping[str, object],
    toy_suite: Mapping[str, object],
    exotic_gate: Mapping[str, object],
) -> dict[str, object]:
    return {
        "n80-exotic-computation": "blocked",
        "real_exotic_scaling_benchmark": "blocked",
        "toy_metadata_counting": "available",
        "reason_id": "n75-dry-run-blocked-by-n70",
        "consumed_statuses": {
            "n24": ordinary_gate.get("status"),
            "n50": decorated_gate.get("status"),
            "n55": toy_suite.get("status"),
            "n70": exotic_gate.get("status"),
        },
        "claim_boundary": (
            "only metadata-size/readiness counting is available; real exotic "
            "calculation and benchmark routes remain closed"
        ),
    }


def _blockers(
    *,
    ordinary_gate: Mapping[str, object],
    decorated_gate: Mapping[str, object],
    toy_suite: Mapping[str, object],
    exotic_gate: Mapping[str, object],
) -> list[dict[str, object]]:
    return [
        {
            "reason_id": N70_DATA_BLOCKED_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n70-exotic-input-certification",
            "observed": exotic_gate.get("status", "missing"),
            "required": "pass with one certified n80 target",
            "upstream_artifact": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
            "upstream_blocker_reason_ids": exotic_gate.get("blocker_reason_ids", []),
            "claim_boundary": "n75 cannot route into n80 while n70 is data-blocked",
        },
        {
            "reason_id": N55_TOY_CLOSED_BLOCKED_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n55-toy-closed-suite",
            "observed": toy_suite.get("status", "missing"),
            "required": "pass",
            "upstream_blocker_reason_ids": toy_suite.get(
                "global_blocker_reason_ids", []
            ),
            "claim_boundary": (
                "toy closed metadata cannot be treated as closed invariant "
                "performance evidence"
            ),
        },
        {
            "reason_id": N50_DECORATED_GATE_BLOCKED_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n50-decorated-kirby-move-gate",
            "observed": decorated_gate.get("status", "missing"),
            "required": "pass",
            "claim_boundary": (
                "presentation/dry-run pairs do not certify decorated Kirby "
                "move scalability"
            ),
        },
        {
            "reason_id": N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n24-ordinary-surgery-gate",
            "observed": ordinary_gate.get("status", "missing"),
            "required": "pass",
            "upstream_blocker_reason_ids": [
                str(reason["reason_id"])
                for reason in ordinary_gate.get("blocked_reasons", [])
                if isinstance(reason, Mapping) and "reason_id" in reason
            ],
            "claim_boundary": (
                "ordinary closed surgery support is still blocked upstream"
            ),
        },
        {
            "reason_id": NO_REAL_EXOTIC_INPUT_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n75-scalability-dry-run",
            "observed": "zero certified real exotic input targets",
            "required": "at least one certified real exotic input target",
            "claim_boundary": (
                "toy metadata counts are not a performance/scaling success "
                "claim for real exotic inputs"
            ),
        },
    ]


def _int_field(mapping: Mapping[str, object], field: str, default: int) -> int:
    value = mapping.get(field, default)
    return value if isinstance(value, int) and not isinstance(value, bool) else default


def _list_or_empty(value: object) -> list[object]:
    return value if isinstance(value, list) else []


def _main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the n75 certificate JSON")
    args = parser.parse_args()

    certificate = scalability_dry_run_certificate(repo_root=Path.cwd())
    output = dumps_certificate(certificate)
    if args.write is None:
        print(output, end="")
        return
    args.write.parent.mkdir(parents=True, exist_ok=True)
    args.write.write_text(output, encoding="utf-8")


if __name__ == "__main__":
    _main()


__all__ = [
    "BLOCKED_CLAIMS",
    "CLAIM_LEVEL",
    "N24_ORDINARY_SURGERY_BLOCKED_BLOCKER_ID",
    "N50_DECORATED_GATE_BLOCKED_BLOCKER_ID",
    "N55_TOY_CLOSED_BLOCKED_BLOCKER_ID",
    "N70_DATA_BLOCKED_BLOCKER_ID",
    "NO_REAL_EXOTIC_INPUT_BLOCKER_ID",
    "NODE_ID",
    "SCALABILITY_DRY_RUN_ARTIFACT",
    "SCALABILITY_DRY_RUN_NOTE",
    "SCALABILITY_DRY_RUN_SCHEMA",
    "scalability_dry_run_artifact",
    "scalability_dry_run_certificate",
    "stable_scalability_dry_run_json",
    "validate_scalability_dry_run_artifact",
]
