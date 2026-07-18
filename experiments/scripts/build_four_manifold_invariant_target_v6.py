#!/usr/bin/env python3
"""Build the 11/1 four-manifold invariant target checkpoint."""

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
    "four-manifold-invariant-target-v6.json"
)
GENERATOR = "experiments/scripts/build_four_manifold_invariant_target_v6.py"
PREDECESSOR = (
    "experiments/results/lean-kirby/four-manifold-invariant-target-v5.json"
)

TOPOLOGY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
    "standardSpecialKirbyCalculusConnected"
)
HOMOLOGY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
    "standardHandleChainNaturalityInput"
)
DOMAIN_AXIOMS = sorted([TOPOLOGY_AXIOM, HOMOLOGY_AXIOM])

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
    "sourceBoundGeometricH2CompilerInstance",
    "sourceBoundEvaluatorCompilerInstance",
]
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:-1]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[-1:]

SOURCE_FILES = [
    GENERATOR,
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "FourManifoldInvariantTargetAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturality.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturalityAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBoundGeometricH2Compiler.lean",
    "lean/Mutations/EvaluatorEqualityInsideStandardNaturalityInput.lean",
    "lean/Mutations/FinalH2IdentityInsideStandardNaturalityInput.lean",
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
    (
        "scripts/"
        "lean_source_backed_handle_chain_naturality_axiom_audit.sh"
    ),
    (
        "scripts/"
        "lean_source_backed_handle_chain_naturality_mutation_tests.sh"
    ),
    "tests/test_four_manifold_invariant_target_artifact_v6.py",
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


def observed_domain_axioms(output: str) -> list[str]:
    return sorted(
        set(
            re.findall(
                r"TwistedYetter\.[A-Za-z0-9_.]*"
                r"(?:standardSpecialKirbyCalculusConnected|"
                r"standardHandleChainNaturalityInput)",
                output,
            )
        )
    )


def reject_proof_oracles(label: str, output: str) -> None:
    forbidden = ("sorryAx", "declaration uses `sorry`", "native_decide.ax")
    if any(token in output for token in forbidden):
        raise RuntimeError(f"{label} audit found a proof oracle")


def main() -> None:
    if run("git", "status", "--porcelain"):
        raise SystemExit("refusing to build v6 target artifact from dirty tree")

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")

    presentation_replay = run(
        "./scripts/lean_presentation_artifact_replay.sh", env=env
    )
    categorical_mutations = run(
        "./scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
        env=env,
    )
    categorical_axioms = run(
        "./scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
        env=env,
    )
    h2_mechanism_mutations = run(
        "./scripts/lean_source_bound_geometric_h2_compiler_mutation_tests.sh",
        env=env,
    )
    h2_mechanism_axioms = run(
        "./scripts/lean_source_bound_geometric_h2_compiler_axiom_audit.sh",
        env=env,
    )
    h2_domain_mutations = run(
        (
            "./scripts/"
            "lean_source_backed_handle_chain_naturality_mutation_tests.sh"
        ),
        env=env,
    )
    h2_domain_axioms = run(
        (
            "./scripts/"
            "lean_source_backed_handle_chain_naturality_axiom_audit.sh"
        ),
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

    if (
        "closed typed trace" not in presentation_replay
        or "trace_steps=12" not in presentation_replay
    ):
        raise RuntimeError("closed typed trace replay did not pass")
    expected_mutations = {
        "categorical": (categorical_mutations, 3),
        "H2 mechanism": (h2_mechanism_mutations, 2),
        "H2 domain": (h2_domain_mutations, 2),
        "target": (target_mutations, 5),
    }
    for label, (output, expected) in expected_mutations.items():
        observed = mutation_count(output)
        if observed != expected:
            raise RuntimeError(
                f"{label} mutation denominator: {observed} != {expected}"
            )
    for label, output in (
        ("categorical", categorical_axioms),
        ("H2 mechanism", h2_mechanism_axioms),
        ("H2 domain", h2_domain_axioms),
        ("target", target_axioms),
    ):
        reject_proof_oracles(label, output)

    if observed_domain_axioms(categorical_axioms):
        raise RuntimeError("categorical mechanism depends on a domain axiom")
    if observed_domain_axioms(h2_mechanism_axioms):
        raise RuntimeError("generic H2 mechanism depends on a domain axiom")
    if observed_domain_axioms(h2_domain_axioms) != [HOMOLOGY_AXIOM]:
        raise RuntimeError("H2 domain-axiom denominator changed")
    if observed_domain_axioms(target_axioms) != DOMAIN_AXIOMS:
        raise RuntimeError("target domain-axiom denominator changed")

    predecessor = load_content_addressed(PREDECESSOR)
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v6",
        "status": (
            "PASS_ELEVEN_FOUNDATION_CONDITIONS_ESTABLISHED_"
            "ONE_SOURCE_BOUND_EVALUATOR_INSTANCE_OPEN"
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
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_four_manifold_invariant_target_v6.py"
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
            "source_files": {
                relative: file_record(relative) for relative in SOURCE_FILES
            },
        },
        "target_condition_ledger": {
            "required_conditions": REQUIRED_CONDITIONS,
            "established_conditions": ESTABLISHED_CONDITIONS,
            "open_conditions": OPEN_CONDITIONS,
            "counts": {"required": 12, "established": 11, "open": 1},
        },
        "domain_axiom_boundary": {
            "axioms": DOMAIN_AXIOMS,
            "count": 2,
            "topology_axiom_output": "TopologicalTableTwoMovie",
            "homology_axiom_output": "StandardHandleChainNaturalityInput",
            "homology_axiom_contains_chain_equivalences": True,
            "homology_axiom_contains_coordinate_naturality": True,
            "homology_axiom_contains_final_h2_identity": False,
            "homology_axiom_contains_evaluator_equality": False,
            "geometric_h2_semantics_external": True,
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
                "custom_domain_axiom_count": 0,
            },
            "geometric_h2_mechanism": {
                "status": "PASS",
                "mutation_count": 2,
                "custom_domain_axiom_count": 0,
            },
            "handle_chain_domain": {
                "status": "PASS_EXACTLY_ONE_VISIBLE_HOMOLOGY_AXIOM",
                "mutation_count": 2,
                "custom_domain_axioms": [HOMOLOGY_AXIOM],
            },
            "target": {
                "status": "PASS_EXACTLY_TWO_VISIBLE_DOMAIN_AXIOMS",
                "mutation_count": 5,
                "custom_domain_axioms": DOMAIN_AXIOMS,
            },
            "full_umbrella_build": {"status": "PASS"},
        },
        "remaining_instance_obligations": [
            {
                "condition": "sourceBoundEvaluatorCompilerInstance",
                "status": "OPEN",
                "required_output": (
                    "A concrete six-event primitive/context interpreter and "
                    "all eight source-bound R7/R8/R9 proof objects."
                ),
            }
        ],
        "explicit_nonclaims": [
            "No concrete source-bound evaluator compiler instance exists yet.",
            "The current code does not yet define a concrete invariant value.",
            "The target theorem remains conditional on the one open instance.",
            "Handle-chain naturality is imported as one visible domain axiom.",
            (
                "The geometric semantics of presentation H2 certificates "
                "remain external to Lean."
            ),
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
