#!/usr/bin/env python3
"""Build the source-bound v5 four-manifold invariant target checkpoint."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v5.json"
)
GENERATOR = "experiments/scripts/build_four_manifold_invariant_target_v5.py"
PREDECESSOR = (
    "experiments/results/lean-kirby/four-manifold-invariant-target-v4.json"
)
TRACE_CHECKPOINT = (
    "experiments/results/lean-kirby/presentation-execution-trace-v1.json"
)

REQUIRED_CONDITIONS = [
    "categoryAndGraphicalAlgebra",
    "explicitThreeHandleNormalization",
    "closedTypedPresentationExecution",
    "primitiveCategoricalEventCompilerMechanism",
    "chainDerivedMarkedH2Transport",
    "sourceBoundGeometricH2CompilerMechanism",
    "specialKirbyCalculusCompleteness",
    "exhaustiveEvaluatorCompilerMechanism",
    "markedPairAssemblyMechanism",
    "sourceBoundLocalMoveRecipes",
    "sourceBoundEvaluatorCompilerInstance",
    "sourceBoundGeometricH2CompilerInstance",
]
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:10]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[10:]

SOURCE_FILES = [
    GENERATOR,
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Kirby/CategoricalPresentationCompiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CategoricalPresentationCompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "FourManifoldInvariantTargetAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/PresentationExecutionTrace.lean",
    "lean/TwistedYetter/Kirby/SourceBoundGeometricH2Compiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundGeometricH2CompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBoundTableTwoEvaluatorCompiler.lean",
    "lean/Mutations/ArbitraryCouponInsideStructuralEventContext.lean",
    "lean/Mutations/ArbitraryEvaluatorCompilerAsTargetInput.lean",
    "lean/Mutations/DirectGeometricH2CompilerAsTargetInput.lean",
    "lean/Mutations/FinalH2IdentityInsideSourceBoundCompiler.lean",
    "lean/Mutations/MissingCategoricalCouponEventCompiler.lean",
    "lean/Mutations/MissingGeometricH2CoordinateNaturality.lean",
    "lean/Mutations/WrongPositiveCrossingEventPrimitive.lean",
    "scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
    "scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
    "scripts/lean_presentation_artifact_replay.sh",
    "scripts/lean_source_bound_geometric_h2_compiler_axiom_audit.sh",
    "scripts/lean_source_bound_geometric_h2_compiler_mutation_tests.sh",
    "tests/test_four_manifold_invariant_target_artifact_v5.py",
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
    return {"bytes": len(data), "sha256": sha256_bytes(data)}


def load_content_addressed(relative: str) -> dict[str, Any]:
    payload = json.loads((ROOT / relative).read_text())
    expected = add_content_hash(payload)["content_hash"]
    if payload.get("content_hash") != expected:
        raise RuntimeError(f"stale content hash: {relative}")
    return payload


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def mutation_count(output: str) -> int:
    return output.count("PASS expected rejection:")


def custom_axioms(output: str) -> list[str]:
    return sorted(
        set(
            re.findall(
                r"TwistedYetter\.[A-Za-z0-9_.]+"
                r"standardSpecialKirbyCalculusConnected",
                output,
            )
        )
    )


def main() -> None:
    if run("git", "status", "--porcelain"):
        raise SystemExit("refusing to build v5 target artifact from dirty tree")

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")

    replay = run("./scripts/lean_presentation_artifact_replay.sh", env=env)
    categorical_mutations = run(
        "./scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
        env=env,
    )
    categorical_axioms = run(
        "./scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
        env=env,
    )
    h2_mutations = run(
        "./scripts/lean_source_bound_geometric_h2_compiler_mutation_tests.sh",
        env=env,
    )
    h2_axioms = run(
        "./scripts/lean_source_bound_geometric_h2_compiler_axiom_audit.sh",
        env=env,
    )
    target_mutations = run(
        "./scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
        env=env,
    )
    target_axioms = run(
        "./scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
        env=env,
    )
    run("./scripts/lean_local_build.sh", "lean/TwistedYetter.lean", env=env)

    if "closed typed trace" not in replay or "trace_steps=12" not in replay:
        raise RuntimeError("closed typed trace replay did not pass")
    if mutation_count(categorical_mutations) != 3:
        raise RuntimeError("categorical mutation denominator changed")
    if mutation_count(h2_mutations) != 2:
        raise RuntimeError("H2 mutation denominator changed")
    if mutation_count(target_mutations) != 5:
        raise RuntimeError("target mutation denominator changed")
    forbidden = ("sorryAx", "declaration uses `sorry`", "native_decide.ax")
    for label, output in (
        ("categorical", categorical_axioms),
        ("H2", h2_axioms),
        ("target", target_axioms),
    ):
        if any(token in output for token in forbidden):
            raise RuntimeError(f"{label} axiom audit found a proof oracle")

    observed_custom = custom_axioms(target_axioms)
    expected_custom = [
        (
            "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
            "standardSpecialKirbyCalculusConnected"
        )
    ]
    if observed_custom != expected_custom:
        raise RuntimeError(f"custom axiom denominator: {observed_custom!r}")
    if custom_axioms(categorical_axioms) or custom_axioms(h2_axioms):
        raise RuntimeError("compiler mechanisms unexpectedly depend on axiom")

    predecessor = load_content_addressed(PREDECESSOR)
    trace_checkpoint = load_content_addressed(TRACE_CHECKPOINT)
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v5",
        "status": (
            "PASS_TEN_FOUNDATION_CONDITIONS_ESTABLISHED_"
            "TWO_SOURCE_BOUND_INSTANCES_OPEN"
        ),
        "mathematical_status": (
            "CONDITIONAL_TARGET_THEOREM_ESTABLISHED_"
            "CONCRETE_FOUR_MANIFOLD_INVARIANT_NOT_YET_ESTABLISHED"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": GENERATOR,
        "argv": [GENERATOR],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 "
            "uv run python "
            "experiments/scripts/build_four_manifold_invariant_target_v5.py"
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
            "predecessor": {
                "path": PREDECESSOR,
                "content_hash": predecessor["content_hash"],
                "source_commit": predecessor["git"]["commit"],
            },
            "typed_trace_checkpoint": {
                "path": TRACE_CHECKPOINT,
                "content_hash": trace_checkpoint["content_hash"],
                "source_commit": trace_checkpoint["git"]["commit"],
            },
            "source_files": {
                relative: file_record(relative)
                for relative in SOURCE_FILES
            },
        },
        "target_condition_ledger": {
            "required_conditions": REQUIRED_CONDITIONS,
            "established_conditions": ESTABLISHED_CONDITIONS,
            "open_conditions": OPEN_CONDITIONS,
            "counts": {"required": 12, "established": 10, "open": 2},
        },
        "compiler_boundaries": {
            "categorical_event_compiler": {
                "event_case_count": 6,
                "whole_diagram_is_direct_input": False,
                "raw_numerator_is_direct_input": False,
                "primitive_sign_is_type_indexed": True,
                "event_context_is_coherence_only": True,
                "concrete_instance_constructed": False,
            },
            "geometric_h2_compiler": {
                "final_identity_is_direct_input": False,
                "actual_chain_equivalence_required": True,
                "shared_recipe_identity_required": True,
                "coordinate_naturality_square_required": True,
                "identity_is_derived": True,
                "concrete_instance_constructed": False,
            },
        },
        "checks": {
            "presentation_replay": {
                "status": "PASS",
                "event_count": 12,
                "slice_count": 13,
            },
            "categorical_compiler": {
                "status": "PASS",
                "mutation_count": 3,
                "proof_oracle_count": 0,
            },
            "geometric_h2_compiler": {
                "status": "PASS",
                "mutation_count": 2,
                "proof_oracle_count": 0,
            },
            "target": {
                "status": "PASS",
                "mutation_count": 5,
                "custom_axioms": observed_custom,
                "custom_axiom_count": len(observed_custom),
            },
            "full_umbrella_build": {"status": "PASS"},
        },
        "remaining_instance_obligations": [
            {
                "condition": "sourceBoundEvaluatorCompilerInstance",
                "status": "OPEN",
                "required_output": (
                    "Concrete six-event primitive/context interpreter plus "
                    "all eight source-bound R7/R8/R9 proof objects."
                ),
            },
            {
                "condition": "sourceBoundGeometricH2CompilerInstance",
                "status": "OPEN",
                "required_output": (
                    "For every source-backed topology move, an actual "
                    "handle-chain equivalence and geometric-coordinate "
                    "naturality square bound to the same recipe ID."
                ),
            },
        ],
        "explicit_nonclaims": [
            "No concrete source-bound evaluator compiler instance exists yet.",
            "No concrete source-bound geometric H2 compiler instance exists yet.",
            "The current code does not yet define a concrete invariant value.",
            "The target theorem remains conditional on the two open instances.",
            "The construction is not identified with Crane-Yetter.",
            "No CTL theorem claim is admitted by this artifact.",
        ],
        "admission": {
            "status": "REPO_LOCAL_GOAL_EVIDENCE_ONLY",
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
