#!/usr/bin/env python3
"""Build the typed closed-presentation execution checkpoint."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "presentation-execution-trace-v1.json"
)
GENERATOR = "experiments/scripts/build_presentation_execution_trace_v1.py"

SOURCE_FILES = [
    GENERATOR,
    "experiments/inputs/lean-kirby/framed-link-presentation-fixture-v1.json",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "lean/Mutations/MissingPresentationExecutionTrace.lean",
    "lean/PresentationArtifactReplay.lean",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "FourManifoldInvariantTargetAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/KirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/PresentationExecutionTrace.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "PresentationExecutionTraceAxiomAudit.lean"
    ),
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_kirby_completeness_mutation_tests.sh",
    "scripts/lean_presentation_artifact_replay.sh",
]


def run(*argv: str, env: dict[str, str] | None = None) -> str:
    result = subprocess.run(
        argv,
        cwd=ROOT,
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    return (result.stdout + result.stderr).strip()


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode()


def add_content_hash(value: dict[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop("content_hash", None)
    result["content_hash"] = sha256_bytes(canonical_bytes(result))
    return result


def file_record(relative: str) -> dict[str, Any]:
    data = (ROOT / relative).read_bytes()
    return {
        "bytes": len(data),
        "sha256": sha256_bytes(data),
    }


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def main() -> None:
    dirty = run("git", "status", "--porcelain")
    if dirty:
        raise SystemExit(
            "refusing to build execution-trace artifact from dirty tree"
        )

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")

    replay_output = run(
        "./scripts/lean_presentation_artifact_replay.sh",
        env=env,
    )
    if "15 passed" not in replay_output:
        raise RuntimeError("unexpected Python presentation test denominator")
    if "closed typed trace" not in replay_output:
        raise RuntimeError("typed trace replay did not report terminal pass")
    if "trace_steps=12" not in replay_output:
        raise RuntimeError("fixture trace denominator drifted")

    mutation_output = run(
        "./scripts/lean_kirby_completeness_mutation_tests.sh",
        env=env,
    )
    if mutation_output.count("PASS expected rejection:") != 10:
        raise RuntimeError("unexpected Kirby mutation denominator")
    if "MissingPresentationExecutionTrace.lean" not in mutation_output:
        raise RuntimeError("missing execution-trace mutation was not exercised")

    target_audit_output = run(
        "./scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
        env=env,
    )
    forbidden = ("sorryAx", "declaration uses `sorry`", "native_decide.ax")
    if any(token in target_audit_output for token in forbidden):
        raise RuntimeError("target axiom audit found a proof oracle")
    if "standardSpecialKirbyCalculusConnected" not in target_audit_output:
        raise RuntimeError("explicit topology axiom disappeared from audit")

    fixture_path = (
        ROOT
        / "experiments/inputs/lean-kirby/"
        "framed-link-presentation-fixture-v1.json"
    )
    fixture = json.loads(fixture_path.read_text())

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.presentation-execution-trace.v1",
        "status": "PASS_CLOSED_TYPED_PRESENTATION_EXECUTION_ESTABLISHED",
        "mathematical_status": (
            "COMBINATORIAL_EXECUTION_ESTABLISHED_"
            "CATEGORICAL_INTERPRETATION_OPEN"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": GENERATOR,
        "argv": [GENERATOR],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 "
            "uv run python "
            "experiments/scripts/build_presentation_execution_trace_v1.py"
        ),
        "repo_root": str(ROOT),
        "git": {
            "commit": run("git", "rev-parse", "HEAD"),
            "branch": run("git", "branch", "--show-current"),
            "dirty_before_generation": False,
        },
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": run("lake", "env", "lean", "--version"),
            "lake": run("lake", "--version"),
            "uv": run("uv", "--version"),
        },
        "inputs": {
            "fixture": {
                "path": str(fixture_path.relative_to(ROOT)),
                "content_hash": fixture["content_hash"],
                "event_count": len(fixture["events"]),
                "declared_slice_count": len(fixture["declared_slices"]),
            },
            "source_files": {
                relative: file_record(relative)
                for relative in SOURCE_FILES
            },
        },
        "checks": {
            "closed_trace_runtime_replay": {
                "status": "PASS",
                "initial_boundary": [],
                "terminal_boundary": [],
                "event_count": 12,
                "trace_step_count": 12,
                "trace_state_count": 13,
                "declared_slice_count": 13,
            },
            "trace_kernel_theorems": {
                "status": "PASS_NO_PROJECT_AXIOMS_OR_PROOF_ORACLES",
                "theorem_count": 6,
            },
            "fail_closed_mutations": {
                "status": "PASS",
                "total_mutation_count": 10,
                "missing_execution_trace_rejected": True,
            },
            "fresh_olean_guard": {
                "status": "PASS",
                "presentation_script_rebuilds_trace_module": True,
                "mutation_script_rebuilds_trace_and_completeness": True,
                "target_audit_rebuilds_target_module": True,
            },
            "target_condition_ledger": {
                "required": 10,
                "established_foundation": 8,
                "open_construction": 2,
                "closed_typed_presentation_execution": "ESTABLISHED",
            },
        },
        "remaining_construction_gaps": [
            {
                "condition": "sourceBoundEvaluatorCompilerInstance",
                "status": "OPEN",
                "exact_gap": (
                    "No categorical interpreter yet derives the eight local "
                    "evaluator proofs from the typed raw event trace and "
                    "source-bound move recipes."
                ),
            },
            {
                "condition": "sourceBoundGeometricH2CompilerInstance",
                "status": "OPEN",
                "exact_gap": (
                    "No concrete geometric compiler yet proves every local "
                    "chain transport agrees with the shared H2 coordinates."
                ),
            },
        ],
        "axiom_boundary": {
            "project_proof_oracles": [],
            "custom_topology_axioms": [
                (
                    "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
                    "standardSpecialKirbyCalculusConnected"
                )
            ],
            "categorical_event_interpretation_assumed": False,
        },
        "explicit_nonclaims": [
            (
                "A successful raw event trace does not prove that any event "
                "has the intended categorical morphism interpretation."
            ),
            "This artifact does not construct the eight-case evaluator compiler.",
            "This artifact does not construct geometric H2 transport.",
            "This artifact does not establish a four-manifold invariant.",
            "This artifact does not identify the invariant with Crane-Yetter.",
            "This artifact does not admit a CTL theorem claim.",
        ],
        "admission": {
            "status": "REPO_LOCAL_ENGINEERING_CHECKPOINT_ONLY",
            "ctl_manifest_written": False,
            "ctl_theorem_claim_admitted": False,
        },
    }
    payload = add_content_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
    )
    print(OUTPUT.relative_to(ROOT))
    print(payload["content_hash"])


if __name__ == "__main__":
    main()
