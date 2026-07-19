#!/usr/bin/env python3
"""Build the untwisted-control four-manifold invariant target checkpoint."""

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
    "four-manifold-invariant-target-v11.json"
)
GENERATOR = "experiments/scripts/build_four_manifold_invariant_target_v11.py"
PREDECESSOR = (
    "experiments/results/lean-kirby/four-manifold-invariant-target-v10.json"
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
    "sourceBoundGraphicalMoveCompilerMechanism",
    "categoryBoundKirbyColorCompilerMechanism",
    "integralCharacterKirbyColorCompilerMechanism",
    "integralCycleRepresentativeSystemInstance",
    "tensorAutomorphismGeneratorInstance",
    "globalFiniteKirbyColorExpansionInstance",
    "sourceBoundGraphicalMoveCompilerInstance",
    "sourceBoundEvaluatorCompilerInstance",
]
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:15]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[15:]

SOURCE_FILES = [
    GENERATOR,
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralCharacterKirbyColorCompiler.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralCharacterKirbyColorCompilerAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundTableTwoEvaluatorCompiler.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipe.lean",
    "lean/TwistedYetter/Kirby/SourceBoundGraphicalMoveCompiler.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "FourManifoldInvariantTargetAxiomAudit.lean"
    ),
    (
        "lean/Mutations/"
        "GenericCategoryBoundAsIntegralCharacterCompiler.lean"
    ),
    "lean/Mutations/MissingIntegralCycleClassSoundness.lean",
    "lean/Mutations/MissingTensorAutomorphismLaw.lean",
    "lean/Mutations/OverrideTrivialGeneratorScalar.lean",
    (
        "scripts/"
        "lean_integral_character_kirby_color_compiler_axiom_audit.sh"
    ),
    (
        "scripts/"
        "lean_integral_character_kirby_color_compiler_mutation_tests.sh"
    ),
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
    "tests/test_four_manifold_invariant_target_artifact_v11.py",
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
        raise SystemExit("refusing to build v11 target artifact from dirty tree")

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")

    integral_mutations = run(
        (
            "./scripts/"
            "lean_integral_character_kirby_color_compiler_mutation_tests.sh"
        ),
        env=env,
    )
    integral_axioms = run(
        (
            "./scripts/"
            "lean_integral_character_kirby_color_compiler_axiom_audit.sh"
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

    if mutation_count(integral_mutations) != 4:
        raise RuntimeError("integral-character mutation denominator changed")
    if mutation_count(target_mutations) != 5:
        raise RuntimeError("target mutation denominator changed")

    reject_proof_oracles("integral-character", integral_axioms)
    reject_proof_oracles("target", target_axioms)
    if observed_domain_axioms(integral_axioms):
        raise RuntimeError("integral-character mechanism uses a domain axiom")
    if observed_domain_axioms(target_axioms) != DOMAIN_AXIOMS:
        raise RuntimeError("target domain-axiom denominator changed")

    predecessor = load_content_addressed(PREDECESSOR)
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v11",
        "status": (
            "PASS_UNTWISTED_CONTROL_ESTABLISHED_"
            "NONTRIVIAL_CONCRETE_TARGET_REMAINS_OPEN"
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
            "experiments/scripts/build_four_manifold_invariant_target_v11.py"
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
            "counts": {"required": 20, "established": 15, "open": 5},
        },
        "target_theorem": {
            "lean_name": (
                "TwistedYetter.Kirby.FourManifoldInvariantTarget."
                "FourManifoldInvariantInputs.four_manifold_invariant_target"
            ),
            "conclusion": (
                "Any two certified special Kirby presentations representing "
                "the same marked pair have equal normalized evaluations."
            ),
            "conditional_on_concrete_inputs": True,
            "concrete_inputs_constructed": False,
        },
        "integral_character_scope": {
            "marked_group": (
                "integral H2 model carried by SpecialKirbyPresentation"
            ),
            "representative": (
                "additive section into actual degree-two cycles, with "
                "homology-class equality"
            ),
            "component_binding": (
                "all ordinary components indexed by the degree-two handle "
                "basis"
            ),
            "coefficient_formula": (
                "ordinaryWeight(simple) * "
                "simpleScalar(simple)^cycleCoefficient(component)"
            ),
            "tensor_character_source": (
                "monoidal natural automorphism of the identity, with exact "
                "scalar action on admitted simples"
            ),
            "specially_dotted_status": (
                "excluded until a source-backed translation to direct "
                "two-cycle coordinates exists"
            ),
        },
        "untwisted_control": {
            "status": "PASS_KERNEL_CHECKED_ALPHA_INSENSITIVE_CONTROL",
            "constructor": (
                "TensorAutomorphismGenerator.trivial"
            ),
            "coefficient_theorem": (
                "trivial_generator_coefficient_is_ordinary"
            ),
            "simple_scalar": "1",
            "all_integral_powers": "1",
            "all_marked_classes_reduce_to_ordinary_weight": True,
            "caller_scalar_override_rejected": True,
            "non_claim": (
                "The identity control is not a nontrivial universal-grading "
                "character or nontrivial tensor automorphism."
            ),
        },
        "concrete_move_fixture_boundary": {
            "status": "BLOCKED_MISSING_CATEGORY_VALUED_FIXTURE",
            "recipe_layer_contains": [
                "literal component and event replacement windows",
                "one of eight directed handle-edit constructors",
                "ordered tags from the 22 framed-isotopy generators",
                "shared graphical and chain recipe identity",
            ],
            "recipe_layer_deliberately_omits": [
                "category objects assigned to local strands",
                "category morphisms assigned to coupons",
                "typed local before and after diagrams",
                "typed surrounding contexts",
                "presentation-specific cancellation factorizations",
            ],
            "first_concrete_move_requirement": (
                "Provide one admitted category-valued presentation fixture "
                "and one source recipe whose local strands, coupons, diagrams, "
                "and contexts are fully typed. No final evaluator equality may "
                "be substituted for that fixture."
            ),
            "synthetic_final_equality_forbidden": True,
        },
        "domain_axiom_boundary": {
            "axioms": DOMAIN_AXIOMS,
            "count": 2,
            "integral_character_mechanism_custom_axioms": [],
        },
        "checks": {
            "integral_character_compiler": {
                "status": "PASS_KERNEL_CHECKED_MECHANISM",
                "mutation_count": 4,
                "custom_domain_axiom_count": 0,
                "arbitrary_weight_compiler_rejected": True,
                "missing_cycle_class_soundness_rejected": True,
                "missing_tensor_law_rejected": True,
                "trivial_generator_scalar_override_rejected": True,
                "untwisted_control_established": True,
            },
            "target_theorem": {
                "status": "PASS_CONDITIONAL_TARGET_ONLY",
                "mutation_count": 5,
                "custom_domain_axioms": DOMAIN_AXIOMS,
            },
            "umbrella_build": {
                "status": "PASS",
                "lean_num_threads": 1,
            },
        },
        "open_instance_details": [
            {
                "condition": "integralCycleRepresentativeSystemInstance",
                "missing": (
                    "Concrete component-to-two-handle indexing and additive "
                    "cycle representatives for every admitted presentation."
                ),
            },
            {
                "condition": "tensorAutomorphismGeneratorInstance",
                "missing": (
                    "A selected nontrivial monoidal natural automorphism and "
                    "verified simple scalar action. The identity control is "
                    "now constructed but does not close this nontrivial input."
                ),
            },
            {
                "condition": "globalFiniteKirbyColorExpansionInstance",
                "missing": (
                    "Concrete event interpreter for every globally labelled "
                    "presentation trace."
                ),
            },
            {
                "condition": "sourceBoundGraphicalMoveCompilerInstance",
                "missing": (
                    "Concrete R7/R8/R9 graphical programs for every source "
                    "recipe."
                ),
            },
            {
                "condition": "sourceBoundEvaluatorCompilerInstance",
                "missing": (
                    "Final assembly after the four preceding concrete inputs."
                ),
            },
        ],
        "non_claims": [
            "No concrete four-manifold invariant instance is established.",
            (
                "The identity tensor-automorphism control is not evidence "
                "for a nontrivial homological twist."
            ),
            "No arbitrary H2(X; A) coefficient system is formalized.",
            (
                "No specially-dotted presentation is admitted by the direct "
                "integral-cycle compiler."
            ),
            "No identification with the original Crane-Yetter state sum.",
            "No theorem says the invariant detects or cannot detect exoticness.",
        ],
    }
    payload = add_content_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(OUTPUT.relative_to(ROOT))
    print(payload["content_hash"])


if __name__ == "__main__":
    main()
