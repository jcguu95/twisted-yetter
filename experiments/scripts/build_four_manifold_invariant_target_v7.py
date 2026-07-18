#!/usr/bin/env python3
"""Build the honest 12/3 four-manifold invariant target checkpoint."""

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
    "four-manifold-invariant-target-v7.json"
)
GENERATOR = "experiments/scripts/build_four_manifold_invariant_target_v7.py"
PREDECESSOR = (
    "experiments/results/lean-kirby/four-manifold-invariant-target-v6.json"
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
    "globalFiniteKirbyColorExpansionMechanism",
    "sourceBoundGeometricH2CompilerInstance",
    "globalFiniteKirbyColorExpansionInstance",
    "sourceBoundGraphicalMoveCompilerInstance",
    "sourceBoundEvaluatorCompilerInstance",
]
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:12]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[12:]

SOURCE_FILES = [
    GENERATOR,
    "experiments/inputs/lean-kirby/framed-link-presentation-fixture-v1.json",
    "lake-manifest.json",
    "lakefile.toml",
    "lean/PresentationArtifactReplay.lean",
    "lean-toolchain",
    "lean/TwistedYetter.lean",
    "lean/Mutations/ArbitraryCouponInsideStructuralEventContext.lean",
    "lean/Mutations/ArbitraryEvaluatorCompilerAsTargetInput.lean",
    "lean/Mutations/ArbitraryPropAsLocalMoveRecipe.lean",
    "lean/Mutations/ArbitraryWholeDiagramInFiniteCompiler.lean",
    "lean/Mutations/DirectGeometricH2CompilerAsTargetInput.lean",
    "lean/Mutations/DropFourManifoldInvariantTargetCondition.lean",
    "lean/Mutations/EvaluatorEqualityInsideStandardNaturalityInput.lean",
    "lean/Mutations/EventwiseLabelingInFiniteCompiler.lean",
    "lean/Mutations/FinalEvaluatorInsideRibbonKirbyAlgebra.lean",
    "lean/Mutations/FinalH2IdentityInsideSourceBoundCompiler.lean",
    "lean/Mutations/FinalH2IdentityInsideStandardNaturalityInput.lean",
    "lean/Mutations/FinalMoveEqualityInsideRibbonKirbyAlgebra.lean",
    "lean/Mutations/FinalEqualityInsideLocalMoveRecipe.lean",
    "lean/Mutations/HandwrittenWholeLinkWeight.lean",
    "lean/Mutations/MissingCategoricalCouponEventCompiler.lean",
    "lean/Mutations/MissingGeometricH2CoordinateNaturality.lean",
    "lean/Mutations/MissingSourceBoundRecipeCase.lean",
    "lean/Mutations/PromoteFourManifoldInvariantTarget.lean",
    "lean/Mutations/RequireCraneYetterIdentificationForTarget.lean",
    "lean/Mutations/SplitGraphicalChainRecipeIdentity.lean",
    "lean/Mutations/SwappedPresentationLocalMoveRecipe.lean",
    "lean/Mutations/WrongKindLocalMoveRecipe.lean",
    "lean/Mutations/WrongPositiveCrossingEventPrimitive.lean",
    "lean/TwistedYetter/Kirby/CategoricalPresentationCompiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CategoricalPresentationCompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/LinearDiagram.lean",
    "lean/TwistedYetter/Kirby/PresentationExecutionTrace.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "PresentationExecutionTraceAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/PresentationSchemaRegression.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "PresentationSchemaRegressionAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "FourManifoldInvariantTargetAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/RibbonKirbyGraphicalAlgebra.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "RibbonKirbyGraphicalAlgebraAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipe.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundLocalMoveRecipeAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundTableTwoEvaluatorCompiler.lean"
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
    "scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
    "scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
    "scripts/lean_presentation_artifact_replay.sh",
    "scripts/lean_ribbon_kirby_graphical_algebra_axiom_audit.sh",
    "scripts/lean_ribbon_kirby_graphical_algebra_mutation_tests.sh",
    (
        "scripts/"
        "lean_source_backed_handle_chain_naturality_axiom_audit.sh"
    ),
    (
        "scripts/"
        "lean_source_backed_handle_chain_naturality_mutation_tests.sh"
    ),
    "scripts/lean_source_bound_geometric_h2_compiler_axiom_audit.sh",
    "scripts/lean_source_bound_geometric_h2_compiler_mutation_tests.sh",
    "scripts/lean_source_bound_local_move_recipe_axiom_audit.sh",
    "scripts/lean_source_bound_local_move_recipe_mutation_tests.sh",
    "tests/test_framed_link_presentation_syntax_v1.py",
    "tests/test_four_manifold_invariant_target_artifact_v7.py",
    "tests/test_kirby_presentation_v1.py",
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
        raise SystemExit("refusing to build v7 target artifact from dirty tree")

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")

    presentation_replay = run(
        "./scripts/lean_presentation_artifact_replay.sh", env=env
    )
    local_recipe_mutations = run(
        "./scripts/lean_source_bound_local_move_recipe_mutation_tests.sh",
        env=env,
    )
    local_recipe_axioms = run(
        "./scripts/lean_source_bound_local_move_recipe_axiom_audit.sh",
        env=env,
    )
    categorical_mutations = run(
        "./scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
        env=env,
    )
    categorical_axioms = run(
        "./scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
        env=env,
    )
    ribbon_mutations = run(
        "./scripts/lean_ribbon_kirby_graphical_algebra_mutation_tests.sh",
        env=env,
    )
    ribbon_axioms = run(
        "./scripts/lean_ribbon_kirby_graphical_algebra_axiom_audit.sh",
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

    mutation_outputs = {
        "local move recipe": (local_recipe_mutations, 6),
        "categorical": (categorical_mutations, 6),
        "ribbon algebra": (ribbon_mutations, 2),
        "H2 mechanism": (h2_mechanism_mutations, 2),
        "H2 domain": (h2_domain_mutations, 2),
        "target": (target_mutations, 5),
    }
    for label, (output, expected) in mutation_outputs.items():
        observed = mutation_count(output)
        if observed != expected:
            raise RuntimeError(
                f"{label} mutation denominator: {observed} != {expected}"
            )

    axiom_outputs = {
        "local move recipe": local_recipe_axioms,
        "categorical": categorical_axioms,
        "ribbon algebra": ribbon_axioms,
        "H2 mechanism": h2_mechanism_axioms,
        "H2 domain": h2_domain_axioms,
        "target": target_axioms,
    }
    for label, output in axiom_outputs.items():
        reject_proof_oracles(label, output)

    for label in (
        "local move recipe",
        "categorical",
        "ribbon algebra",
        "H2 mechanism",
    ):
        if observed_domain_axioms(axiom_outputs[label]):
            raise RuntimeError(f"{label} depends on a domain axiom")
    if observed_domain_axioms(h2_domain_axioms) != [HOMOLOGY_AXIOM]:
        raise RuntimeError("H2 domain-axiom denominator changed")
    if observed_domain_axioms(target_axioms) != DOMAIN_AXIOMS:
        raise RuntimeError("target domain-axiom denominator changed")

    predecessor = load_content_addressed(PREDECESSOR)
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v7",
        "status": (
            "PASS_TWELVE_FOUNDATION_CONDITIONS_ESTABLISHED_"
            "THREE_CONCRETE_INSTANCES_OPEN"
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
            "experiments/scripts/build_four_manifold_invariant_target_v7.py"
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
            "counts": {"required": 15, "established": 12, "open": 3},
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
            "local_move_recipe": {
                "status": "PASS",
                "mutation_count": 6,
                "custom_domain_axiom_count": 0,
            },
            "categorical_compiler": {
                "status": "PASS_GLOBAL_FINITE_COMPONENTWISE_EXPANSION",
                "mutation_count": 6,
                "custom_domain_axiom_count": 0,
            },
            "ribbon_graphical_algebra": {
                "status": "PASS_TRANSPARENT_NO_FINAL_EVALUATOR",
                "mutation_count": 2,
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
                "condition": "globalFiniteKirbyColorExpansionInstance",
                "status": "OPEN",
                "required_output": (
                    "The exact finite label fiber and Kirby-colour weight for "
                    "every link component, together with a category-bound "
                    "event interpreter for every global labeling."
                ),
            },
            {
                "condition": "sourceBoundGraphicalMoveCompilerInstance",
                "status": "OPEN",
                "required_output": (
                    "A closed graphical rewrite program that derives all "
                    "eight directed R7/R8/R9 proof objects from the shared "
                    "source-bound recipes and ribbon-Kirby algebra."
                ),
            },
            {
                "condition": "sourceBoundEvaluatorCompilerInstance",
                "status": "OPEN",
                "required_output": (
                    "The final SourceBoundTableTwoEvaluatorCompiler assembled "
                    "only from the two preceding concrete instances."
                ),
            },
        ],
        "explicit_nonclaims": [
            "No concrete global Kirby-colour expansion instance exists yet.",
            "No source-bound graphical eight-case compiler exists yet.",
            "No concrete source-bound evaluator compiler instance exists yet.",
            "The current code does not yet define a concrete invariant value.",
            "The target theorem remains conditional on three open instances.",
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
