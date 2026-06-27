"""Executable n80 exotic-computation gate verdict.

This module is a terminal blocked verdict for the current graph endpoint.  It
does not run invariants, benchmark diagrams, fetch sources, or synthesize
exotic values.  It only consumes the n70 input-certification status and the
n75 scalability dry-run status and records why n80 cannot compute yet.
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
from twisted_yetter.exotic_input_certification import (
    EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
    EXOTIC_INPUT_CERTIFICATION_SCHEMA,
    exotic_input_certification_ledger_artifact,
    validate_exotic_input_certification_ledger_artifact,
)
from twisted_yetter.scalability_dry_run import (
    SCALABILITY_DRY_RUN_ARTIFACT,
    SCALABILITY_DRY_RUN_SCHEMA,
    scalability_dry_run_artifact,
    validate_scalability_dry_run_artifact,
)

EXOTIC_COMPUTATION_SCHEMA: Final = "twisted-yetter.exotic-computation.v1"
EXOTIC_COMPUTATION_ARTIFACT: Final = (
    "experiments/results/exotic-computation/n80-exotic-computation.json"
)
EXOTIC_COMPUTATION_NOTE: Final = "wiki/understandings/exotic-computation.org"

NODE_ID: Final = "n80-exotic-computation"
CLAIM_LEVEL: Final = "terminal blocked computation gate verdict"

N70_NO_CERTIFIED_INPUT_BLOCKER_ID: Final = "n70-no-certified-exotic-input"
N70_NO_SELECTED_TARGET_BLOCKER_ID: Final = "n70-no-selected-computation-target"
N75_DRY_RUN_BLOCKED_BLOCKER_ID: Final = "n75-dry-run-blocked"
NO_INVARIANT_INPUT_BLOCKER_ID: Final = "no-invariant-input-available"
NO_BENCHMARK_INPUT_BLOCKER_ID: Final = "no-benchmark-input-available"

BLOCKED_CLAIMS: Final = (
    "exotic invariant value claim",
    "exotic pair exact comparison claim",
    "marked exotic distinction claim",
    "cork-canonical exotic distinction claim",
    "unmarked or orbit exotic distinction claim",
    "real exotic input benchmark claim",
    "n82 result-classification route",
)


def exotic_computation_artifact(
    *,
    n70: Mapping[str, object] | None = None,
    n75: Mapping[str, object] | None = None,
    claim_invariant_run: bool = False,
    claim_exotic_values: bool = False,
    claim_benchmark: bool = False,
    claim_result_route: bool = False,
) -> dict[str, object]:
    """Return the deterministic n80 terminal blocked verdict.

    The claim flags are guardrails against accidentally using this endpoint as
    a calculator or benchmark launcher while n70/n75 are blocked.
    """

    if claim_invariant_run or claim_exotic_values or claim_benchmark or claim_result_route:
        raise ValueError(
            "n80-exotic-computation is blocked by n70/n75 and refuses "
            "invariant runs, exotic values, benchmarks, and n82 result routes"
        )

    exotic_input = exotic_input_certification_ledger_artifact() if n70 is None else dict(n70)
    dry_run = scalability_dry_run_artifact(n70=exotic_input) if n75 is None else dict(n75)

    artifact: dict[str, object] = {
        "schema": EXOTIC_COMPUTATION_SCHEMA,
        "status": "blocked",
        "node_id": NODE_ID,
        "claim_level": CLAIM_LEVEL,
        "source_status": (
            "n80 consumes n70/n75 status only and emits a terminal blocked "
            "verdict; no invariant, exotic-value, benchmark, source-fetch, "
            "or Dolgachev calculation is run"
        ),
        "upstream_nodes": [
            "n70-exotic-input-certification",
            "n75-scalability-dry-run",
        ],
        "input_artifacts": {
            "n70_exotic_input_certification": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
            "n75_scalability_dry_run": SCALABILITY_DRY_RUN_ARTIFACT,
        },
        "input_schemas": {
            "exotic_input_certification": exotic_input.get("schema"),
            "scalability_dry_run": dry_run.get("schema"),
        },
        "dependency_statuses": _dependency_statuses(
            n70=exotic_input,
            n75=dry_run,
        ),
        "dependency_validations": {
            "exotic_input_certification": (
                validate_exotic_input_certification_ledger_artifact(exotic_input)
            ),
            "scalability_dry_run": validate_scalability_dry_run_artifact(dry_run),
        },
        "blocked_reason_ids": [
            N70_NO_CERTIFIED_INPUT_BLOCKER_ID,
            N70_NO_SELECTED_TARGET_BLOCKER_ID,
            N75_DRY_RUN_BLOCKED_BLOCKER_ID,
            NO_INVARIANT_INPUT_BLOCKER_ID,
            NO_BENCHMARK_INPUT_BLOCKER_ID,
        ],
        "blockers": _blockers(n70=exotic_input, n75=dry_run),
        "computation_policy": {
            "invariant_run_allowed": False,
            "exotic_values_allowed": False,
            "comparison_certificate_allowed": False,
            "benchmark_allowed": False,
            "n82_result_classification_route_allowed": False,
            "source_guess_allowed": False,
            "network_allowed": False,
            "core_evaluator_change_allowed": False,
        },
        "computation_run_summary": {
            "did_run_computation": False,
            "invariant_runs": [],
            "exotic_values": [],
            "benchmarks": [],
            "source_fetches": [],
            "engine_invocations": [],
            "reason": (
                "n70 certified_input_count=0 and selected_computation_target=null; "
                "n75 status=dry-run-blocked"
            ),
        },
        "next_steps": [
            "offline/source acquisition for n72",
            "rerun n72-dolgachev-source-capture after source records exist",
            "rerun n73-exotic-diagram-digitization after exact page/figure data exist",
            "rerun n74-exotic-h2-marking-certification after machine-readable diagrams exist",
            "rerun n70-exotic-input-certification until one certified target is selected",
            "rerun n75-scalability-dry-run only after n70 has a pass artifact",
        ],
        "blocked_claims": list(BLOCKED_CLAIMS),
        "claim_boundary": (
            "This is a machine-readable terminal blocked verdict for n80.  "
            "It proves only that current repo-local dependency statuses do "
            "not authorize exotic computation; it is not exotic evidence, "
            "not a benchmark, and not a no-go theorem."
        ),
        "ledger_note": EXOTIC_COMPUTATION_NOTE,
        "artifact_path": EXOTIC_COMPUTATION_ARTIFACT,
    }
    artifact["metadata_validation"] = validate_exotic_computation_artifact(artifact)
    return artifact


def validate_exotic_computation_artifact(
    artifact: Mapping[str, object],
) -> dict[str, object]:
    """Validate n80 terminal blocked verdict shape."""

    required = {
        "schema",
        "status",
        "node_id",
        "claim_level",
        "input_schemas",
        "dependency_statuses",
        "blocked_reason_ids",
        "blockers",
        "computation_policy",
        "computation_run_summary",
        "next_steps",
        "blocked_claims",
    }
    missing = sorted(field for field in required if field not in artifact)
    input_schemas = artifact.get("input_schemas", {})
    input_schemas_ok = isinstance(input_schemas, Mapping) and input_schemas == {
        "exotic_input_certification": EXOTIC_INPUT_CERTIFICATION_SCHEMA,
        "scalability_dry_run": SCALABILITY_DRY_RUN_SCHEMA,
    }
    statuses = artifact.get("dependency_statuses", {})
    statuses_ok = (
        isinstance(statuses, Mapping)
        and statuses.get("n70_status") == "blocked"
        and statuses.get("n70_source_status") == "source-needed"
        and statuses.get("n70_certified_input_count") == 0
        and statuses.get("n70_selected_computation_target") is None
        and statuses.get("n75_status") == "dry-run-blocked"
        and statuses.get("n75_n80_route_allowed") is False
    )
    blockers = artifact.get("blocked_reason_ids", [])
    blockers_ok = isinstance(blockers, list) and set(blockers) >= {
        N70_NO_CERTIFIED_INPUT_BLOCKER_ID,
        N70_NO_SELECTED_TARGET_BLOCKER_ID,
        N75_DRY_RUN_BLOCKED_BLOCKER_ID,
        NO_INVARIANT_INPUT_BLOCKER_ID,
        NO_BENCHMARK_INPUT_BLOCKER_ID,
    }
    policy = artifact.get("computation_policy", {})
    policy_ok = isinstance(policy, Mapping) and all(
        policy.get(field) is False
        for field in (
            "invariant_run_allowed",
            "exotic_values_allowed",
            "comparison_certificate_allowed",
            "benchmark_allowed",
            "n82_result_classification_route_allowed",
            "source_guess_allowed",
            "network_allowed",
            "core_evaluator_change_allowed",
        )
    )
    run_summary = artifact.get("computation_run_summary", {})
    run_summary_ok = (
        isinstance(run_summary, Mapping)
        and run_summary.get("did_run_computation") is False
        and run_summary.get("invariant_runs") == []
        and run_summary.get("exotic_values") == []
        and run_summary.get("benchmarks") == []
        and run_summary.get("engine_invocations") == []
    )
    return {
        "valid": (
            not missing
            and artifact.get("schema") == EXOTIC_COMPUTATION_SCHEMA
            and artifact.get("status") == "blocked"
            and artifact.get("node_id") == NODE_ID
            and artifact.get("claim_level") == CLAIM_LEVEL
            and input_schemas_ok
            and statuses_ok
            and blockers_ok
            and policy_ok
            and run_summary_ok
        ),
        "missing_required_fields": missing,
        "input_schemas_ok": input_schemas_ok,
        "dependency_statuses_ok": statuses_ok,
        "blockers_ok": blockers_ok,
        "computation_policy_ok": policy_ok,
        "computation_run_summary_ok": run_summary_ok,
        "scope": "n80 terminal blocked verdict only; no invariant computation or benchmark",
    }


def stable_exotic_computation_json(artifact: Mapping[str, object]) -> str:
    """Serialize an n80 verdict deterministically."""

    return json.dumps(artifact, indent=2, sort_keys=True)


def exotic_computation_certificate(
    *,
    repo_root: str | Path = ".",
) -> dict[str, object]:
    """Return a certificate envelope for the current n80 blocked verdict."""

    root = Path(repo_root)
    exact_output = exotic_computation_artifact()
    return make_certificate(
        status="inconclusive",
        command=(
            "PYTHONPATH=src uv run python -m twisted_yetter.exotic_computation --write "
            f"{EXOTIC_COMPUTATION_ARTIFACT}"
        ),
        argv=[
            "python",
            "-m",
            "twisted_yetter.exotic_computation",
            "--write",
            EXOTIC_COMPUTATION_ARTIFACT,
        ],
        git=git_metadata(root),
        tool_versions=default_tool_versions(),
        input_hash=hash_json(
            {
                "node_id": NODE_ID,
                "dependency_statuses": exact_output["dependency_statuses"],
                "blocked_reason_ids": exact_output["blocked_reason_ids"],
                "computation_run_summary": exact_output["computation_run_summary"],
            }
        ),
        exact_output=exact_output,
        generator_script="src/twisted_yetter/exotic_computation.py",
        reproduce_command=(
            "UV_CACHE_DIR=/Users/jin/data/local/projects/twisted-yetter/.uv-cache "
            "PYTHONPATH=src uv run python -m twisted_yetter.exotic_computation --write "
            "experiments/results/exotic-computation/n80-exotic-computation.json"
        ),
        repo_root=str(root.resolve()),
        notes=[
            "n80 is blocked because n70 has no certified exotic input target.",
            "n75 is dry-run-blocked, so no invariant computation or benchmark is run.",
        ],
    )


def _dependency_statuses(
    *,
    n70: Mapping[str, object],
    n75: Mapping[str, object],
) -> dict[str, object]:
    return {
        "n70_status": n70.get("status"),
        "n70_source_status": n70.get("source_status"),
        "n70_certified_input_count": _int_field(n70, "certified_input_count", 0),
        "n70_candidate_count": _int_field(n70, "candidate_count", 0),
        "n70_any_candidate_certified": n70.get("any_candidate_certified"),
        "n70_selected_computation_target": n70.get("selected_computation_target"),
        "n70_n80_route_allowed": n70.get("n80_exotic_computation_route_allowed"),
        "n75_status": n75.get("status"),
        "n75_readiness_status": _mapping(n75.get("readiness_summary")).get("status"),
        "n75_n80_route_allowed": n75.get("n80_exotic_computation_route_allowed"),
        "n75_real_benchmark_available": _mapping(n75.get("readiness_summary")).get(
            "real_benchmark_available"
        ),
    }


def _blockers(
    *,
    n70: Mapping[str, object],
    n75: Mapping[str, object],
) -> list[dict[str, object]]:
    return [
        {
            "reason_id": N70_NO_CERTIFIED_INPUT_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n70-exotic-input-certification",
            "observed": _int_field(n70, "certified_input_count", 0),
            "required": "at least one certified exotic pair input",
            "upstream_artifact": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
            "upstream_blocker_reason_ids": n70.get("blocker_reason_ids", []),
            "claim_boundary": "n80 cannot run an invariant without a certified input",
        },
        {
            "reason_id": N70_NO_SELECTED_TARGET_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n70-exotic-input-certification",
            "observed": n70.get("selected_computation_target"),
            "required": "selected_computation_target must name a certified pair",
            "upstream_artifact": EXOTIC_INPUT_CERTIFICATION_ARTIFACT,
            "claim_boundary": "n80 cannot compare values when no pair is selected",
        },
        {
            "reason_id": N75_DRY_RUN_BLOCKED_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n75-scalability-dry-run",
            "observed": n75.get("status"),
            "required": "pass for the certified real input",
            "upstream_artifact": SCALABILITY_DRY_RUN_ARTIFACT,
            "upstream_blocked_reason_ids": n75.get("blocked_reason_ids", []),
            "claim_boundary": "n75 dry-run-blocked status cannot route to n80 pass work",
        },
        {
            "reason_id": NO_INVARIANT_INPUT_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n80-exotic-computation",
            "observed": "no machine-readable certified exotic diagrams or H2 marking",
            "required": "certified diagrams, markings, normalization, and formula confidence",
            "claim_boundary": "no exotic invariant value or comparison certificate is produced",
        },
        {
            "reason_id": NO_BENCHMARK_INPUT_BLOCKER_ID,
            "status": "blocked",
            "source_node": "n80-exotic-computation",
            "observed": "no certified real exotic size data",
            "required": "n75 pass artifact for a real certified target",
            "claim_boundary": "no performance benchmark or scalability result is produced",
        },
    ]


def _int_field(mapping: Mapping[str, object], field: str, default: int) -> int:
    value = mapping.get(field, default)
    return value if isinstance(value, int) and not isinstance(value, bool) else default


def _mapping(value: object) -> Mapping[str, object]:
    return value if isinstance(value, Mapping) else {}


def _main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", type=Path, help="write the n80 certificate JSON")
    args = parser.parse_args()

    certificate = exotic_computation_certificate(repo_root=Path.cwd())
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
    "EXOTIC_COMPUTATION_ARTIFACT",
    "EXOTIC_COMPUTATION_NOTE",
    "EXOTIC_COMPUTATION_SCHEMA",
    "N70_NO_CERTIFIED_INPUT_BLOCKER_ID",
    "N70_NO_SELECTED_TARGET_BLOCKER_ID",
    "N75_DRY_RUN_BLOCKED_BLOCKER_ID",
    "NO_BENCHMARK_INPUT_BLOCKER_ID",
    "NO_INVARIANT_INPUT_BLOCKER_ID",
    "NODE_ID",
    "exotic_computation_artifact",
    "exotic_computation_certificate",
    "stable_exotic_computation_json",
    "validate_exotic_computation_artifact",
]
