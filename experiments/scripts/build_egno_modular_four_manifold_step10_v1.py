#!/usr/bin/env python3
"""Build the terminal certificate for EGNO modular four-manifold Step 10."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "egno-modular-four-manifold-step10-v1.json"
)
ROADMAP = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)
STEP9_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "egno-modular-kirby-moves-step9-v1.json"
)
REFERENCE_LEDGERS = [
    (
        REPO_ROOT
        / "experiments/inputs/references/"
        "source-backed-special-kirby-completeness-v1.json"
    ),
    (
        REPO_ROOT
        / "experiments/inputs/references/"
        "kirby-completeness-primary-sources-v1.json"
    ),
    (
        REPO_ROOT
        / "experiments/inputs/references/"
        "four-manifold-invariant-target-primary-sources-v1.json"
    ),
    (
        REPO_ROOT
        / "experiments/inputs/references/"
        "generalized-sliding-framed-context-primary-sources-v1.json"
    ),
]
NEW_MUTATIONS = [
    "lean/Mutations/GenericTaggedMoveInEGNOAssembly.lean",
    "lean/Mutations/ReboundPackageInEGNOAssembly.lean",
    "lean/Mutations/GeneralizedSlideAsOrdinary.lean",
    "lean/Mutations/OrdinarySlideAsGeneralized.lean",
    "lean/Mutations/FreeComponentWeightInEGNOAssembly.lean",
    "lean/Mutations/EventwiseLabelWithoutGlobalResolver.lean",
    "lean/Mutations/NormalizedEqualityAsLocalMoveCompiler.lean",
    "lean/Mutations/MissingMoveFamiliesInLocalCompiler.lean",
    "lean/Mutations/MalformedInvariantAssemblyHash.lean",
    "lean/Mutations/ReboundPresentationCompilerPackage.lean",
]
SOURCE_FILES = [
    "experiments/scripts/build_egno_modular_four_manifold_step10_v1.py",
    "tests/test_egno_modular_four_manifold_step10_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Kirby/EGNOModularFourManifoldInvariant.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "EGNOModularFourManifoldInvariantAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean",
    "lean/TwistedYetter/Kirby/IntegralCharacterKirbyColorCompiler.lean",
    "lean/TwistedYetter/Kirby/CategoricalPresentationCompiler.lean",
    "lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean",
    "lean/TwistedYetter/Kirby/ConcreteMarkedPairAssembly.lean",
    "lean/TwistedYetter/Kirby/SourceBackedKirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/SourceBoundGeometricH2Compiler.lean",
    "lean/TwistedYetter/Kirby/SourceBackedHandleChainNaturality.lean",
    "scripts/lean_egno_modular_four_manifold_axiom_audit.sh",
    "scripts/lean_egno_modular_four_manifold_mutation_tests.sh",
    "scripts/lean_egno_modular_kirby_moves_axiom_audit.sh",
    "scripts/lean_egno_modular_kirby_moves_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    *NEW_MUTATIONS,
    str(ROADMAP.relative_to(REPO_ROOT)),
    str(STEP9_ARTIFACT.relative_to(REPO_ROOT)),
    *[str(path.relative_to(REPO_ROOT)) for path in REFERENCE_LEDGERS],
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
]
PROOF_HOLE_FILES = [
    "lean/TwistedYetter/Kirby/EGNOModularFourManifoldInvariant.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "EGNOModularFourManifoldInvariantAxiomAudit.lean"
    ),
    *NEW_MUTATIONS,
]
EXPECTED_CUSTOM_AXIOMS = {
    (
        "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
        "standardSpecialKirbyCalculusConnected"
    ),
    (
        "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
        "standardHandleChainNaturalityInput"
    ),
}


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def run(argv: list[str]) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    result = subprocess.run(
        argv,
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"{argv!r} returned {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def version(argv: list[str]) -> str:
    result = run(argv)
    return (result.stdout or result.stderr).strip().splitlines()[0]


def output_tail(result: subprocess.CompletedProcess[str]) -> str:
    lines = (result.stdout + result.stderr).strip().splitlines()
    return lines[-1] if lines else "(no output)"


def proof_hole_scan() -> dict[str, Any]:
    forbidden = re.compile(
        r"\b(sorry|admit|native_decide)\b|^\s*axiom\b",
        re.MULTILINE,
    )
    for relative in PROOF_HOLE_FILES:
        text = (REPO_ROOT / relative).read_text()
        match = forbidden.search(text)
        if match:
            raise AssertionError(
                f"forbidden proof-oracle token in {relative}: "
                f"{match.group(0)!r}"
            )
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": PROOF_HOLE_FILES,
    }


def check_roadmap(roadmap: dict[str, Any]) -> None:
    expected = (
        "TEN_STEP_CATEGORY_TO_MARKED_FOUR_MANIFOLD_INVARIANT_ROUTE_"
        "ESTABLISHED_RELATIVE_TO_EXPLICIT_DOMAIN_INPUTS"
    )
    if roadmap["status"] != expected:
        raise AssertionError("unexpected terminal roadmap status")
    statuses = [step["status"] for step in roadmap["steps"]]
    if statuses[:6] != ["ESTABLISHED_IN_LEAN"] * 6:
        raise AssertionError("Steps 1 through 6 must remain established")
    if statuses[6] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    ):
        raise AssertionError("Step 7 lost its theorem-input boundary")
    if statuses[7] != "ESTABLISHED_IN_LEAN":
        raise AssertionError("Step 8 is not established")
    if statuses[8] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_EXPLICIT_GLOBAL_"
        "STANDARD_GRAPHICAL_LAWS"
    ):
        raise AssertionError("Step 9 lost its theorem-input boundary")
    if statuses[9] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_EXPLICIT_SOURCE_BOUND_"
        "COMPILERS_AND_STANDARD_TOPOLOGY_DOMAIN_INPUTS"
    ):
        raise AssertionError("Step 10 is not terminal with its exact boundary")
    if len(roadmap["steps"][9]["visible_domain_input_classes"]) != 6:
        raise AssertionError("the terminal domain-input denominator changed")


def check_step9_artifact() -> dict[str, Any]:
    artifact = json.loads(STEP9_ARTIFACT.read_text())
    if artifact["content_hash"] != canonical_hash(artifact):
        raise AssertionError("Step 9 artifact content hash is stale")
    if artifact["status"] != (
        "PASS_STEP_9_CATEGORY_BOUND_MODULAR_KIRBY_MOVES_RELATIVE_"
        "TO_EXPLICIT_GLOBAL_STANDARD_GRAPHICAL_LAWS"
    ):
        raise AssertionError("Step 9 category package is not admitted")
    return {
        "path": str(STEP9_ARTIFACT.relative_to(REPO_ROOT)),
        "content_hash": artifact["content_hash"],
        "sha256": sha256_path(STEP9_ARTIFACT),
    }


def check_contracts() -> None:
    source = (
        REPO_ROOT
        / "lean/TwistedYetter/Kirby/"
        "EGNOModularFourManifoldInvariant.lean"
    ).read_text()
    required = [
        "abbrev GlobalLabeling",
        "noncomputable def componentExponent",
        "noncomputable def componentWeight",
        "data.quantumDimension simple *",
        "automorphismScalarPower",
        "structure LabelledComponentResolver",
        "component_sound :",
        "structure PresentationCompiler",
        "WindowedCategoricalEventSemantics",
        "noncomputable def linearDiagram",
        "weightedSum",
        "theorem linearDiagram_eval",
        "inductive PackageTaggedMove",
        "inductive PackageIsotopy",
        "inductive BoundOrdinarySlide",
        "inductive BoundGeneralizedSlide",
        "structure OneTwoFactorization",
        "structure TwoThreeFactorization",
        "structure LocalMoveCompiler",
        "framedIsotopy :",
        "oneOverOne :",
        "twoOverOne :",
        "twoOverTwo :",
        "oneTwoBirth :",
        "oneTwoDeath :",
        "twoThreeBirth :",
        "twoThreeDeath :",
        "theorem move_invariant",
        "theorem movie_invariant",
        "structure InvariantInputs",
        "theorem presentation_independent",
        "theorem four_manifold_invariant",
        "requiredDomainInputClasses.length = 6",
        "requiredDomainInputClasses.Nodup",
    ]
    missing = [item for item in required if item not in source]
    if missing:
        raise AssertionError(f"missing Step 10 contracts: {missing}")
    package_moves = source.split(
        "inductive PackageTaggedMove", maxsplit=1
    )[1].split("namespace PackageTaggedMove", maxsplit=1)[0]
    if "| generic" in package_moves or "| arbitrary" in package_moves:
        raise AssertionError("package isotopy has an unrestricted constructor")
    presentation = source.split(
        "structure PresentationCompiler", maxsplit=1
    )[1].split("namespace PresentationCompiler", maxsplit=1)[0]
    if "wholeDiagram :" in presentation or "normalizedValue :" in presentation:
        raise AssertionError("presentation compiler accepts a final-value bypass")
    local = source.split("structure LocalMoveCompiler", maxsplit=1)[1].split(
        "namespace LocalMoveCompiler", maxsplit=1
    )[0]
    if "finalEquality :" in local or "normalizedEquality :" in local:
        raise AssertionError("local compiler accepts a final-equality bypass")


def verify_baerenz_barrett_capture(
    topology_refs: dict[str, Any],
) -> dict[str, Any]:
    capture = topology_refs["references"][0]["captured_pdf"]
    path = Path(capture["capture_path_at_capture_time"])
    if not path.exists():
        raise AssertionError("the pinned Bärenz--Barrett PDF is absent")
    if path.stat().st_size != capture["bytes"]:
        raise AssertionError("the pinned Bärenz--Barrett PDF size changed")
    if sha256_path(path) != capture["sha256"]:
        raise AssertionError("the pinned Bärenz--Barrett PDF hash changed")
    return {
        "path_at_capture_time": str(path),
        "bytes": capture["bytes"],
        "sha256": capture["sha256"],
    }


def custom_axioms(output: str) -> set[str]:
    return set(
        re.findall(
            r"TwistedYetter\.[A-Za-z0-9_.]+standard"
            r"(?:SpecialKirbyCalculusConnected|HandleChainNaturalityInput)",
            output,
        )
    )


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("Step 10 artifact requires a clean source commit")

    roadmap = json.loads(ROADMAP.read_text())
    check_roadmap(roadmap)
    check_contracts()
    step9 = check_step9_artifact()

    reference_hashes = {
        str(path.relative_to(REPO_ROOT)): {"sha256": sha256_path(path)}
        for path in REFERENCE_LEDGERS
    }
    topology_refs = json.loads(REFERENCE_LEDGERS[0].read_text())
    topology_pdf = verify_baerenz_barrett_capture(topology_refs)

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(
        ["./scripts/lean_egno_modular_four_manifold_axiom_audit.sh"]
    )
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 10 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 145:
        raise AssertionError(
            f"expected 145 audited declarations, got {audited_declarations}"
        )
    observed_custom_axioms = custom_axioms(axiom_output)
    if observed_custom_axioms != EXPECTED_CUSTOM_AXIOMS:
        raise AssertionError(
            "terminal custom-axiom set changed: "
            f"{sorted(observed_custom_axioms)}"
        )

    mutations = run(
        ["./scripts/lean_egno_modular_four_manifold_mutation_tests.sh"]
    )
    rejections = [
        line
        for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 46:
        raise AssertionError("expected forty-six rejected Step 1-10 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    payload: dict[str, Any] = {
        "schema": (
            "twisted-yetter.egno-modular-four-manifold-step10.v1"
        ),
        "status": (
            "PASS_STEP_10_MARKED_FOUR_MANIFOLD_INVARIANT_RELATIVE_TO_"
            "EXPLICIT_SOURCE_BOUND_COMPILERS_AND_STANDARD_TOPOLOGY_INPUTS"
        ),
        "mathematical_status": (
            "CONDITIONAL_PRESENTATION_INDEPENDENCE_KERNEL_CHECKED_WITH_"
            "VISIBLE_DOMAIN_INPUTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/"
            "build_egno_modular_four_manifold_step10_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_egno_modular_four_manifold_step10_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 UV_CACHE_DIR=.uv-cache uv run python "
            "experiments/scripts/"
            "build_egno_modular_four_manifold_step10_v1.py"
        ),
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": version(["lake", "env", "lean", "--version"]),
            "lake": version(["lake", "--version"]),
            "mathlib_tag": "v4.29.1",
            "mathlib_commit": git(
                "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"
            ),
        },
        "inputs": {
            "step9_category_package": step9,
            "roadmap": {
                "path": str(ROADMAP.relative_to(REPO_ROOT)),
                "sha256": sha256_path(ROADMAP),
            },
            "reference_ledgers": reference_hashes,
            "source_pdfs": {
                "baerenz_barrett": topology_pdf,
                "gompf_stipsicz": {
                    "status": "LOCATORS_VERIFIED_NO_REPO_LOCAL_BOOK_BYTES"
                },
                "de_sa": {
                    "status": "METADATA_ONLY_NO_CHAPTER_BYTES"
                },
            },
            "source_files": source_files,
        },
        "checks": {
            "full_lean_build": {
                "status": "PASS",
                "command": "LEAN_NUM_THREADS=1 lake build TwistedYetter",
                "output_tail": output_tail(build_result),
            },
            "axiom_audit": {
                "status": (
                    "PASS_NO_PROOF_ORACLE_AND_EXACTLY_TWO_NAMED_"
                    "TOPOLOGY_AXIOMS"
                ),
                "audited_declaration_count": audited_declarations,
                "custom_axioms": sorted(observed_custom_axioms),
            },
            "mutations": {
                "status": "PASS_FAIL_CLOSED",
                "rejected_count": len(rejections),
                "rejections": rejections,
            },
            "proof_hole_scan": proof_hole_scan(),
            "global_labeling": (
                "PASS_ONE_COMPLETE_LABEL_ASSIGNMENT_PER_FINITE_SUM_TERM"
            ),
            "coefficient_origin": (
                "PASS_DIMENSION_TIMES_DERIVED_AUTOMORPHISM_POWER_AT_"
                "CANONICAL_INTEGRAL_EXPONENT"
            ),
            "eventwise_compilation": (
                "PASS_VALIDATED_EXECUTION_TRACE_COMPILED_BEFORE_SUMMATION"
            ),
            "proof_grammar_separation": (
                "PASS_ISOTOPY_ORDINARY_SLIDE_GENERALIZED_SLIDE_AND_"
                "CANCELLATION_REMAIN_DISTINCT"
            ),
            "move_coverage": "PASS_ALL_EIGHT_DIRECTED_TABLE2_CONSTRUCTORS",
            "movie_induction": "PASS_STRUCTURAL_INDUCTION",
            "marked_descent": (
                "PASS_SOURCE_BACKED_MOVIE_AND_CHAIN_DERIVED_H2_TRANSPORT"
            ),
            "domain_input_denominator": "PASS_EXACTLY_SIX_VISIBLE_CLASSES",
        },
        "lean_derived": [
            "closed-diagram scalar multiplicativity under disjoint union",
            "canonical integral-character coefficient for every component",
            "finite sum over complete global simple labelings",
            "package-bound framed isotopy evaluation invariance",
            "ordinary-slide finite-sum evaluation invariance",
            "label-indexed generalized 2-over-2 evaluation invariance",
            "1--2 and 2--3 normalized cancellation invariance",
            "normalized invariance for every directed Table 2 move",
            "normalized invariance under every finite Table 2 movie",
            "presentation independence for every certified marked pair",
        ],
        "visible_domain_input_classes": roadmap["steps"][9][
            "visible_domain_input_classes"
        ],
        "explicit_custom_topology_axioms": sorted(EXPECTED_CUSTOM_AXIOMS),
        "remaining_steps_in_ten_step_generic_route": [],
        "concrete_instantiation_obligations": [
            "construct a concrete ribbon fusion category and tensor automorphism",
            "construct the source-bound whole-presentation compiler",
            "construct all eight source-bound local-move compiler fields",
        ],
        "explicit_non_claims": roadmap["explicit_non_claims"],
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


if __name__ == "__main__":
    result = build()
    print(
        json.dumps(
            {
                "output": str(OUTPUT),
                "status": result["status"],
                "content_hash": result["content_hash"],
            },
            indent=2,
        )
    )
