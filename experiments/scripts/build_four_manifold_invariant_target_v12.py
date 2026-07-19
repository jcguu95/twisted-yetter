#!/usr/bin/env python3
"""Build the terminal last-five invariant-construction checkpoint."""

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
    "four-manifold-invariant-target-v12.json"
)
GENERATOR = "experiments/scripts/build_four_manifold_invariant_target_v12.py"
PREDECESSOR = (
    "experiments/results/lean-kirby/four-manifold-invariant-target-v11.json"
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
ESTABLISHED_CONDITIONS = REQUIRED_CONDITIONS[:16]
OPEN_CONDITIONS = REQUIRED_CONDITIONS[16:]

SOURCE_FILES = [
    GENERATOR,
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Kirby/CategoricalTangle.lean",
    "lean/TwistedYetter/Kirby/CategoricalPresentationCompiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CategoricalPresentationCompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CategoryBoundKirbyColorCompiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CategoryBoundKirbyColorCompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean",
    "lean/TwistedYetter/Kirby/IntegralCharacterKirbyColorCompiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralCharacterKirbyColorCompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBoundGraphicalMoveCompiler.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundGraphicalMoveCompilerAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBoundTableTwoEvaluatorCompiler.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "FourManifoldInvariantTargetAxiomAudit.lean"
    ),
    "lean/Mutations/ArbitraryWholeCompilerInIntegralRoute.lean",
    "lean/Mutations/HandwrittenRawFactorInsideOneTwoFactorization.lean",
    "lean/Mutations/RenamedCouponInBoundWindow.lean",
    "lean/Mutations/UnboundFramingStrandInWindow.lean",
    "lean/Mutations/WrongRecordedDualInBirthPrimitive.lean",
    "scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
    "scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
    (
        "scripts/"
        "lean_integral_character_kirby_color_compiler_axiom_audit.sh"
    ),
    (
        "scripts/"
        "lean_integral_character_kirby_color_compiler_mutation_tests.sh"
    ),
    "scripts/lean_source_bound_graphical_move_compiler_axiom_audit.sh",
    "scripts/lean_source_bound_graphical_move_compiler_mutation_tests.sh",
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
    "tests/test_four_manifold_invariant_target_artifact_v12.py",
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
        raise SystemExit("refusing to build v12 target artifact from dirty tree")
    run("git", "diff", "--check")

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")

    categorical_mutations = run(
        "./scripts/lean_categorical_presentation_compiler_mutation_tests.sh",
        env=env,
    )
    categorical_axioms = run(
        "./scripts/lean_categorical_presentation_compiler_axiom_audit.sh",
        env=env,
    )
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
    graphical_mutations = run(
        "./scripts/lean_source_bound_graphical_move_compiler_mutation_tests.sh",
        env=env,
    )
    graphical_axioms = run(
        "./scripts/lean_source_bound_graphical_move_compiler_axiom_audit.sh",
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

    expected_mutations = {
        "categorical_event_compiler": 9,
        "integral_character_compiler": 7,
        "source_bound_graphical_compiler": 5,
        "four_manifold_target": 5,
    }
    observed_mutations = {
        "categorical_event_compiler": mutation_count(categorical_mutations),
        "integral_character_compiler": mutation_count(integral_mutations),
        "source_bound_graphical_compiler": mutation_count(
            graphical_mutations
        ),
        "four_manifold_target": mutation_count(target_mutations),
    }
    if observed_mutations != expected_mutations:
        raise RuntimeError(
            "mutation denominator changed: "
            f"expected={expected_mutations}, observed={observed_mutations}"
        )

    for label, output in [
        ("categorical", categorical_axioms),
        ("integral-character", integral_axioms),
        ("graphical", graphical_axioms),
        ("target", target_axioms),
    ]:
        reject_proof_oracles(label, output)

    for label, output in [
        ("categorical", categorical_axioms),
        ("integral-character", integral_axioms),
        ("graphical", graphical_axioms),
    ]:
        if observed_domain_axioms(output):
            raise RuntimeError(f"{label} mechanism uses a domain axiom")
    if observed_domain_axioms(target_axioms) != DOMAIN_AXIOMS:
        raise RuntimeError("target domain-axiom denominator changed")

    predecessor = load_content_addressed(PREDECESSOR)
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v12",
        "status": (
            "PASS_LAST_FIVE_TERMINALIZED_"
            "WITH_EXPLICIT_CONCRETE_INPUT_BLOCKERS"
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
            "experiments/scripts/build_four_manifold_invariant_target_v12.py"
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
            "counts": {"required": 20, "established": 16, "open": 4},
        },
        "last_five_terminal_outcomes": [
            {
                "ordinal": 1,
                "condition": "integralCycleRepresentativeSystemInstance",
                "status": "ESTABLISHED_KERNEL_CHECKED",
                "result": (
                    "Normalized representatives are selected from the actual "
                    "Mathlib H2 quotient and use each presentation's mandatory "
                    "two-handle component index."
                ),
                "non_claim": (
                    "The representative choice is not asserted additive."
                ),
            },
            {
                "ordinal": 2,
                "condition": "tensorAutomorphismGeneratorInstance",
                "status": (
                    "TERMINAL_BLOCKED_MISSING_CONCRETE_CATEGORY_VALUE"
                ),
                "mechanism_status": (
                    "PASS_EXPLICIT_WITNESSED_NONTRIVIAL_INTERFACE"
                ),
                "missing": (
                    "One admitted category-specific monoidal natural "
                    "automorphism, its exact scalar action on every retained "
                    "simple, and one scalar-not-one witness."
                ),
            },
            {
                "ordinal": 3,
                "condition": "globalFiniteKirbyColorExpansionInstance",
                "status": (
                    "TERMINAL_BLOCKED_MISSING_CATEGORY_VALUED_EVENT_SEMANTICS"
                ),
                "mechanism_status": (
                    "PASS_GLOBAL_FINITE_SUM_AND_SOURCE_BOUND_WINDOWS"
                ),
                "missing": (
                    "Category-valued component resolution, exact dual "
                    "pairings, and coupon morphisms for every admitted raw "
                    "presentation event."
                ),
            },
            {
                "ordinal": 4,
                "condition": "sourceBoundGraphicalMoveCompilerInstance",
                "status": (
                    "TERMINAL_BLOCKED_MISSING_TYPED_RECIPE_REALIZATIONS"
                ),
                "mechanism_status": (
                    "PASS_EIGHT_CASE_COMPILER_WITH_TYPED_FACTOR_ONLY"
                ),
                "missing": (
                    "Typed categorical contexts for each source recipe's "
                    "R7/R8/R9 script, slide exterior, and cancellation "
                    "factorization."
                ),
            },
            {
                "ordinal": 5,
                "condition": "sourceBoundEvaluatorCompilerInstance",
                "status": "TERMINAL_BLOCKED_TRANSITIVE_INPUTS",
                "mechanism_status": "PASS_FINAL_ASSEMBLER_KERNEL_CHECKED",
                "missing": (
                    "The category-bound presentation compiler and graphical "
                    "move compiler values from outcomes 3 and 4."
                ),
            },
        ],
        "safety_hardening": {
            "whole_event_compiler_is_derived": True,
            "event_exterior_is_coherence_only": True,
            "event_windows_bind": [
                "component IDs",
                "ordered strand IDs",
                "strand orientations at birth",
                "coupon ID and label",
                "framing-twist strand ID",
                "complete planar active order",
            ],
            "birth_and_death_use_explicit_exact_pairings": True,
            "category_dual_cannot_be_silently_replaced": True,
            "cancellation_raw_factor_is_derived_from_diagram_factorization": (
                True
            ),
            "handwritten_raw_or_normalized_move_equality_rejected": True,
            "final_assembler_accepts_no_evaluator_function": True,
            "final_assembler_accepts_no_move_equality": True,
        },
        "checks": {
            "mutation_denominators": observed_mutations,
            "proof_oracles": [],
            "mechanism_custom_domain_axioms": [],
            "target_domain_axioms": DOMAIN_AXIOMS,
            "umbrella_build": {
                "status": "PASS",
                "lean_num_threads": 1,
            },
        },
        "target_theorem": {
            "lean_name": (
                "TwistedYetter.Kirby.FourManifoldInvariantTarget."
                "FourManifoldInvariantInputs.four_manifold_invariant_target"
            ),
            "conditional_on_concrete_inputs": True,
            "concrete_inputs_constructed": False,
            "conclusion": (
                "Any two certified special Kirby presentations representing "
                "the same marked pair have equal normalized evaluations."
            ),
        },
        "terminal_blocker_boundary": {
            "repo_has_concrete_lean_mtc_fixture": False,
            "repo_has_category_neutral_source_recipes": True,
            "category_neutral_recipes_include_typed_category_morphisms": False,
            "blockers_can_be_closed_by_hash_only": False,
            "blockers_can_be_closed_by_numerical_artifacts_only": False,
            "required_next_evidence": [
                (
                    "A Lean category model or separately admitted categorical "
                    "domain package with tensor automorphism and pairings."
                ),
                (
                    "Category-valued interpretation of each retained coupon "
                    "and event window."
                ),
                (
                    "Typed realization of each source-bound graphical recipe."
                ),
            ],
        },
        "non_claims": [
            "No concrete four-manifold invariant instance is established.",
            "No open condition was renamed or counted as established.",
            "No numerical category artifact was promoted to a Lean category.",
            "No category-neutral move tag was promoted to a graphical proof.",
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
