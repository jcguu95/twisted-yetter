#!/usr/bin/env python3
"""Build the audited v2 status artifact for the canonical modular invariant."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "canonical-modular-four-manifold-invariant-v2.json"
)

SOURCE_FILES = [
    "experiments/scripts/"
    "build_canonical_modular_four_manifold_invariant_v2.py",
    "tests/test_canonical_modular_four_manifold_invariant_v2.py",
    "lean-toolchain",
    "lakefile.toml",
    "pyproject.toml",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOPremodularModular.lean",
    "lean/TwistedYetter/Fusion/EGNOTensorAutomorphism.lean",
    "lean/TwistedYetter/Kirby/CanonicalKirbyTrace.lean",
    "lean/TwistedYetter/Kirby/CanonicalModularKirbyEvaluator.lean",
    "lean/TwistedYetter/Kirby/TensorAutomorphismCouponCalculus.lean",
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean",
    "lean/TwistedYetter/Kirby/CanonicalMoveGeometry.lean",
    "lean/TwistedYetter/Kirby/CanonicalCycleMoveGeometry.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleMoveGeometryAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CanonicalCycleSlideGeometry.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleSlideGeometryAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CanonicalCycleLocalInvariance.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleLocalInvarianceAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBackedHandleChainNaturality.lean",
    "lean/TwistedYetter/Kirby/CanonicalSourceBackedMove.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedCanonicalGraphicalInput.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedCanonicalGraphicalInputAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalRawLocalMoveTarget.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalRawLocalMoveTargetAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedFourManifoldTopology.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedFourManifoldTopologyAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedFourManifoldInputs.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedFourManifoldInputsAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CanonicalModularKirbyInvariance.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyInvarianceAxiomAudit.lean"
    ),
]

REFERENCE_FILES = [
    (
        "experiments/inputs/references/"
        "egno-category-foundations-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "four-manifold-invariant-target-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "kirby-completeness-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "generalized-sliding-core-primary-sources-v2.json"
    ),
    (
        "experiments/inputs/references/"
        "kirby-cancellation-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "framed-link-presentation-independence-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "homologically-twisted-kirby-invariant-sources-v1.json"
    ),
]

SMOOTH_TOPOLOGY_INPUTS = [
    "markedRealization",
    "elementaryMoveSoundness",
    "markedPresentationExistence",
    "markedKirbyCerfCompleteness",
]

DIAGRAMMATIC_INPUTS = [
    (
        "TwistedYetter.Kirby."
        "LiteratureBackedCanonicalGraphicalInput."
        "standardCycleBoundaryGraphicalRealization"
    ),
    (
        "TwistedYetter.Kirby."
        "LiteratureBackedCanonicalGraphicalInput."
        "standardLocalCycleCalculation"
    ),
]

HANDLE_CHAIN_INPUT = (
    "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
    "standardHandleChainNaturalityInput"
)

CATEGORY_LITERATURE_INPUTS = [
    (
        "TwistedYetter.Fusion.EGNO."
        "sMatrixNondegenerate_iff_trivialMuegerCenter"
    ),
    (
        "TwistedYetter.Fusion.EGNO.ModularCategory."
        "globalDimension_ne_zero"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "baerenzBarrett_oneTwoHopfPairSum"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "baerenzBarrett_ordinaryKirbySliding"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "egno_quantumDimension_unit"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "shum_ribbonFramedKink"
    ),
]

EXPECTED_PROJECT_AXIOMS = sorted(
    [HANDLE_CHAIN_INPUT, *DIAGRAMMATIC_INPUTS, *CATEGORY_LITERATURE_INPUTS]
)
EXPECTED_FOUNDATIONAL_AXIOMS = [
    "Classical.choice",
    "Quot.sound",
    "propext",
]

LOCAL_MOVE_CLASSES = [
    "framedIsotopy",
    "oneOverOne",
    "twoOverOne",
    "twoOverTwo",
    "oneTwoBirth",
    "oneTwoDeath",
    "twoThreeBirth",
    "twoThreeDeath",
]


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_metadata(relative: str) -> dict[str, Any]:
    data = (ROOT / relative).read_bytes()
    return {"bytes": len(data), "sha256": sha256_bytes(data)}


def canonical_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{sha256_bytes(encoded)}"


def run(argv: list[str]) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    result = subprocess.run(
        argv,
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(argv)}\n"
            f"{result.stdout}"
        )
    return result


def command_summary(
    argv: list[str],
    result: subprocess.CompletedProcess[str],
) -> dict[str, Any]:
    output = result.stdout
    return {
        "argv": argv,
        "returncode": result.returncode,
        "completed_successfully": (
            "build completed successfully" in output.lower()
        ),
        "stdout_bytes": len(output.encode()),
        "stdout_sha256": sha256_bytes(output.encode()),
        "warning_count": output.count("warning:"),
    }


def git_text(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    ).stdout.strip()


def extract_axiom_names(output: str) -> tuple[list[str], list[str]]:
    blocks = re.findall(
        r"depends on axioms:\s*\[(.*?)\]",
        output,
        flags=re.DOTALL,
    )
    names: set[str] = set()
    for block in blocks:
        names.update(
            re.findall(
                r"(?:TwistedYetter\.[A-Za-z0-9_.]+"
                r"|Classical\.choice|Quot\.sound|propext)",
                block,
            )
        )
    project = sorted(
        name for name in names if name.startswith("TwistedYetter.")
    )
    foundational = sorted(
        name for name in names if not name.startswith("TwistedYetter.")
    )
    return project, foundational


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def source_guards() -> dict[str, Any]:
    paths = [ROOT / relative for relative in SOURCE_FILES]
    lean_paths = [
        path
        for path in paths
        if path.suffix == ".lean"
        and not path.name.endswith("AxiomAudit.lean")
    ]
    hole_pattern = re.compile(
        r"(?m)^\s*(?:sorry|admit)\b|\bnative_decide\b"
    )
    proof_holes = [
        str(path.relative_to(ROOT))
        for path in lean_paths
        if hole_pattern.search(path.read_text())
    ]
    require(not proof_holes, f"proof holes found: {proof_holes}")

    final_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyInvariance.lean"
    )
    final_text = final_path.read_text()
    final_start = final_text.index(
        "noncomputable def EvalCOnClosedFourManifolds"
    )
    final_signature = final_text[final_start:final_start + 1800]
    require(
        "LocalMoveRealization" not in final_text,
        "the retired caller-supplied LocalMoveRealization returned",
    )
    require(
        "compiler" not in final_signature.lower()
        and "scalarEquality" not in final_signature,
        "the final definition accepts an engineering compiler or equality",
    )
    require(
        "standardLocalCycleCalculation" in final_text
        and "representativeIndependenceSystem" in final_text,
        "the two fixed diagrammatic inputs are no longer visibly used",
    )
    require(
        "h2ModelEquiv_transport" not in final_text
        and "topology.h2ModelEquiv alpha" not in final_text,
        "the final theorem still exposes the retired ambient H2 coordinate",
    )

    evaluator_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyEvaluator.lean"
    ).read_text()
    eval_start = evaluator_text.index("noncomputable def EvalC")
    eval_signature = evaluator_text[eval_start:eval_start + 1000]
    require(
        "presentation.topology.handleChain.SecondHomology"
        in eval_signature,
        "canonical EvalC does not take an actual second-homology class",
    )

    local_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalCycleLocalInvariance.lean"
    ).read_text()
    require(
        "inductive LocalCycleCalculation" in local_text
        and "theorem sound" in local_text,
        "the closed eight-case proof grammar or its soundness is absent",
    )
    for move_class in LOCAL_MOVE_CLASSES:
        require(
            f"  | {move_class}" in local_text,
            f"missing local calculation class: {move_class}",
        )

    move_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalCycleMoveGeometry.lean"
    ).read_text()
    require(
        "HomologicalComplex.cyclesMap" in move_text
        and "HomologicalComplex.homologyπ_naturality" in move_text,
        "explicit target cycles are not derived from the forward chain map",
    )

    slide_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalCycleSlideGeometry.lean"
    ).read_text()
    require(
        "closedWindow.linearBefore coefficient" in slide_text
        and "closedWindow.linearAfter coefficient" in slide_text,
        "generalized sliding is not proved at whole-finite-sum level",
    )

    graphical_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "LiteratureBackedCanonicalGraphicalInput.lean"
    ).read_text()
    require(
        graphical_text.count("\naxiom standard") == 2,
        "diagrammatic literature axiom denominator is not exactly two",
    )
    require(
        "Lean does not compile raw planar coordinates" in graphical_text,
        "the raw-planar limitation is no longer conspicuous",
    )

    raw_target_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalRawLocalMoveTarget.lean"
    ).read_text()
    instruction_start = raw_target_text.index(
        "structure Instruction (source : FormalPresentation)"
    )
    instruction_end = raw_target_text.index(
        "namespace Instruction", instruction_start
    )
    instruction_signature = raw_target_text[
        instruction_start:instruction_end
    ]
    require(
        "targetPresentationHash" not in instruction_signature
        and "\n  target :" not in instruction_signature,
        "the source-local instruction accepts an independently chosen target",
    )
    require(
        "structure Engine where" in raw_target_text
        and "structure Completion" in raw_target_text
        and "TARGET_PINNED_NOT_IMPLEMENTED" in raw_target_text,
        "the raw local move completion target is not visibly pinned",
    )
    require(
        "generates_exact_target" in raw_target_text
        and "generated_move_calculation" in raw_target_text
        and "LocalCycleCalculation" in raw_target_text,
        "the raw target omits endpoint generation or graphical soundness",
    )
    require(
        re.search(
            r"(?m)^\s*(?:axiom|sorry|admit)\b",
            raw_target_text,
        )
        is None,
        "the raw completion target falsely asserts an implementation",
    )

    retired_slide = (
        ROOT
        / "lean/TwistedYetter/Kirby/CanonicalSlideGeometry.lean"
    )
    require(
        not retired_slide.exists(),
        "the retired chosen-representative slide route still exists",
    )

    return {
        "status": "PASS_FAIL_CLOSED_SOURCE_GUARDS",
        "proof_holes": proof_holes,
        "final_accepts_caller_compiler": False,
        "final_accepts_caller_scalar_equality": False,
        "retired_local_move_realization_absent": True,
        "explicit_cycle_uses_forward_chain_map": True,
        "whole_sum_slide_endpoints_required": True,
        "local_move_class_count": 8,
        "diagrammatic_axiom_count": 2,
        "raw_planar_compiler_present": False,
        "raw_planar_compiler_target_pinned": True,
        "raw_planar_compiler_target_status": (
            "TARGET_PINNED_NOT_IMPLEMENTED"
        ),
        "raw_instruction_accepts_whole_target": False,
        "raw_instruction_accepts_target_hash": False,
        "public_eval_alpha_is_actual_second_homology": True,
        "final_ambient_h2_coordinate_bridge_absent": True,
        "retired_chosen_representative_slide_route_absent": True,
    }


def tool_version(argv: list[str]) -> str:
    output = run(argv).stdout.strip().splitlines()
    return output[0] if output else ""


def main() -> None:
    started_at = utc_now()
    start = time.monotonic()
    guards = source_guards()

    umbrella_argv = ["lake", "-Kjobs=2", "build", "TwistedYetter"]
    umbrella = run(umbrella_argv)

    final_audit_argv = [
        "lake",
        "-Kjobs=2",
        "build",
        (
            "TwistedYetter.Kirby."
            "CanonicalModularKirbyInvarianceAxiomAudit"
        ),
    ]
    final_audit = run(final_audit_argv)
    project_axioms, foundational_axioms = extract_axiom_names(
        final_audit.stdout
    )
    require(
        project_axioms == EXPECTED_PROJECT_AXIOMS,
        f"unexpected final project axiom set: {project_axioms}",
    )
    require(
        foundational_axioms == EXPECTED_FOUNDATIONAL_AXIOMS,
        f"unexpected foundational axiom set: {foundational_axioms}",
    )

    layer_audit_argv = [
        "lake",
        "-Kjobs=2",
        "build",
        (
            "TwistedYetter.Kirby."
            "LiteratureBackedCanonicalGraphicalInputAxiomAudit"
        ),
        (
            "TwistedYetter.Kirby."
            "CanonicalRawLocalMoveTargetAxiomAudit"
        ),
        (
            "TwistedYetter.Kirby."
            "CanonicalCycleMoveGeometryAxiomAudit"
        ),
        (
            "TwistedYetter.Kirby."
            "CanonicalCycleSlideGeometryAxiomAudit"
        ),
        (
            "TwistedYetter.Kirby."
            "CanonicalCycleLocalInvarianceAxiomAudit"
        ),
        (
            "TwistedYetter.Kirby."
            "LiteratureBackedFourManifoldTopologyAxiomAudit"
        ),
        (
            "TwistedYetter.Kirby."
            "LiteratureBackedFourManifoldInputsAxiomAudit"
        ),
    ]
    layer_audit = run(layer_audit_argv)

    status_porcelain = git_text("status", "--porcelain")
    payload: dict[str, Any] = {
        "schema": "canonical-modular-four-manifold-invariant-v2",
        "status": (
            "KERNEL_CHECKED_CLOSED_FOUR_MANIFOLD_INVARIANT_"
            "RELATIVE_TO_EXPLICIT_LITERATURE_BOUNDARY"
        ),
        "mathematical_status": "ESTABLISHED_RELATIVE_TO_NAMED_INPUTS",
        "generator_script": (
            "experiments/scripts/"
            "build_canonical_modular_four_manifold_invariant_v2.py"
        ),
        "argv": sys.argv,
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 "
            "experiments/scripts/"
            "build_canonical_modular_four_manifold_invariant_v2.py"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - start, 6),
        "repo": {
            "root": str(ROOT),
            "git_commit": git_text("rev-parse", "HEAD"),
            "git_branch": git_text(
                "rev-parse", "--abbrev-ref", "HEAD"
            ),
            "dirty": bool(status_porcelain),
            "status_porcelain_sha256": sha256_bytes(
                status_porcelain.encode()
            ),
        },
        "tool_versions": {
            "python": platform.python_version(),
            "lean": tool_version(["lake", "env", "lean", "--version"]),
            "lake": tool_version(["lake", "--version"]),
        },
        "supersedes": {
            "artifact": (
                "experiments/results/lean-kirby/"
                "canonical-modular-four-manifold-invariant-v1.json"
            ),
            "reason": (
                "v1 correctly recorded that canonical cycle descent and "
                "the eight source-bound local realizations were open. v2 "
                "adds explicit-cycle transport, restricted proof grammars, "
                "the eight-case soundness proof, and two conspicuous "
                "diagrammatic literature inputs."
            ),
        },
        "inputs": {
            "source_files": {
                relative: file_metadata(relative)
                for relative in SOURCE_FILES
            },
            "reference_records": {
                relative: file_metadata(relative)
                for relative in REFERENCE_FILES
            },
        },
        "external_statement_denominator": {
            "total_count": 16,
            "smooth_topology_arguments": {
                "count": 4,
                "items": SMOOTH_TOPOLOGY_INPUTS,
                "representation": (
                    "explicit fields of "
                    "LiteratureBackedFourManifoldTopology.Assumptions"
                ),
            },
            "handle_chain_axioms": {
                "count": 1,
                "items": [HANDLE_CHAIN_INPUT],
            },
            "diagrammatic_realization_axioms": {
                "count": 2,
                "items": DIAGRAMMATIC_INPUTS,
            },
            "category_literature_axioms": {
                "count": 9,
                "items": CATEGORY_LITERATURE_INPUTS,
            },
            "foundational_lean_axioms": EXPECTED_FOUNDATIONAL_AXIOMS,
        },
        "first_block": {
            "status": "COMPLETE_AS_EXPLICIT_LITERATURE_BOUNDARY",
            "public_alpha_type": (
                "presentation.topology.handleChain.SecondHomology"
            ),
            "proved_in_lean": [
                "the four imported topology classes form a fixed denominator",
                "Kirby-class quotient descent",
                "oriented-diffeomorphism invariance after local invariance",
                "presentation formula recovery",
                "chain-induced H2 transport from an actual chain map",
            ],
            "not_formalized": [
                "smooth manifolds from foundations",
                "Morse and Cerf theory",
                "attaching maps and handle-chain matrices from geometry",
                "raw planar coordinates and attaching-band neighborhoods",
            ],
        },
        "second_block": {
            "status": (
                "CATEGORY_CALCULATION_COMPLETE_AFTER_TWO_EXPLICIT_"
                "DIAGRAMMATIC_REALIZATION_INPUTS"
            ),
            "proved_in_lean": [
                "target cycle is the image under the actual forward chain map",
                "coupon naturality, tensor, unit, duality, and cancellation",
                "representative independence from a generated coupon movie",
                "ordinary slides at whole-linear-sum level",
                "generalized slides at whole-linear-sum level",
                "one-two cancellation finite sum and normalization",
                "two-three cancellation finite sum and normalization",
                "birth and death directions without strict representative naturality",
                "all eight local move classes preserve canonical EvalC",
                "finite-movie descent to oriented diffeomorphism classes",
            ],
            "local_move_classes": LOCAL_MOVE_CLASSES,
            "caller_supplies_local_realization": False,
            "caller_supplies_final_equality": False,
            "raw_planar_endpoint_compiler": {
                "status": "TARGET_PINNED_NOT_IMPLEMENTED",
                "meaning": (
                    "Lean does not reconstruct the exact planar placement "
                    "of every slide/coupon from serialized embeddings. A "
                    "source-only deterministic Engine and its exact "
                    "Completion obligations are now pinned, but no Engine "
                    "or Completion value is constructed. The two existing "
                    "axioms still return restricted proof terms, not scalar "
                    "or EvalC equalities."
                ),
                "completion_type": (
                    "TwistedYetter.Kirby."
                    "CanonicalRawLocalMoveTarget.Completion"
                ),
                "instruction_contains_whole_target": False,
                "instruction_contains_target_hash": False,
                "required_obligations": [
                    "generated components equal the local splice",
                    "generated events equal the local splice",
                    "the generated formal presentation is the exact topology target",
                    "the generated move compiles to LocalCycleCalculation",
                ],
            },
        },
        "final_theorem": {
            "lean_function": (
                "TwistedYetter.Kirby."
                "CanonicalModularKirbyInvariance."
                "EvalCOnClosedFourManifolds"
            ),
            "lean_diffeomorphism_theorem": (
                "TwistedYetter.Kirby."
                "CanonicalModularKirbyInvariance."
                "EvalCOnClosedFourManifolds_"
                "diffeomorphism_invariant"
            ),
            "lean_presentation_formula": (
                "TwistedYetter.Kirby."
                "CanonicalModularKirbyInvariance."
                "EvalCOnClosedFourManifolds_on_presentation"
            ),
            "scope": (
                "marked closed connected oriented smooth four-manifolds "
                "represented by the cited special Kirby calculus, over an "
                "algebraically closed characteristic-zero field, for a "
                "ModularCategory and a tensor automorphism of the identity"
            ),
            "alpha_interface": (
                "Each presentation is evaluated directly on its actual "
                "handle-chain SecondHomology; a move transports alpha by "
                "the chain equivalence's secondHomologyAddEquiv."
            ),
            "is_axiom_free": False,
            "is_kernel_checked_relative_to_inputs": True,
        },
        "resource_safety": {
            (
                "experiments/results/lean-kirby/"
                "canonical-modular-four-manifold-invariant-v1.json"
            ): "HISTORICAL_SUPERSEDED_NOT_CURRENT_COMPLETION_STATUS",
            (
                "lean/TwistedYetter/Kirby/"
                "CanonicalMoveGeometry.lean"
            ): (
                "REUSE_ONLY_INDEX_AND_COMPONENT_CHANGE_TYPES; "
                "ITS CHOSEN-TARGET-REPRESENTATIVE GEOMETRIES DO NOT "
                "SUPPORT THE V2 FINAL THEOREM"
            ),
            (
                "lean/TwistedYetter/Kirby/"
                "CanonicalSlideGeometry.lean"
            ): "RETIRED_FILE_ABSENT",
        },
        "checks": {
            "source_guards": guards,
            "umbrella_build": command_summary(
                umbrella_argv, umbrella
            ),
            "final_axiom_audit_build": command_summary(
                final_audit_argv, final_audit
            ),
            "layer_axiom_audit_build": command_summary(
                layer_audit_argv, layer_audit
            ),
            "final_axiom_audit": {
                "project_axioms": project_axioms,
                "foundational_axioms": foundational_axioms,
            },
        },
        "explicit_non_claims": [
            (
                "This is not an axiom-free formalization of smooth "
                "four-manifolds, Morse theory, or Cerf theory."
            ),
            (
                "The two diagrammatic realization statements are still "
                "axioms. The raw serialized-planar compiler completion "
                "type is pinned, but no Engine or Completion value "
                "constructs them."
            ),
            (
                "A restricted proof grammar is safer than a scalar-equality "
                "axiom, but inhabiting that grammar remains substantive "
                "geometric content and is not reported as proved in Lean."
            ),
            (
                "The result is for modular categories, not arbitrary "
                "premodular categories."
            ),
            (
                "The result is not identified here with Yetter's original "
                "state-sum invariant."
            ),
            (
                "No concrete category or concrete four-manifold is "
                "instantiated by this theorem artifact."
            ),
        ],
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )
    print(OUTPUT)


if __name__ == "__main__":
    main()
