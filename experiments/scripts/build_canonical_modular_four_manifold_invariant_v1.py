#!/usr/bin/env python3
"""Build the audited status artifact for the canonical modular invariant."""

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
    "canonical-modular-four-manifold-invariant-v1.json"
)

SOURCE_FILES = [
    "experiments/scripts/"
    "build_canonical_modular_four_manifold_invariant_v1.py",
    "tests/test_canonical_modular_four_manifold_invariant_v1.py",
    "lean-toolchain",
    "lakefile.toml",
    "pyproject.toml",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOPremodularModular.lean",
    "lean/TwistedYetter/Fusion/EGNOTensorAutomorphism.lean",
    (
        "lean/TwistedYetter/Fusion/"
        "EGNOTensorAutomorphismAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CanonicalKirbyTrace.lean",
    "lean/TwistedYetter/Kirby/CanonicalKirbyTraceAxiomAudit.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "TensorAutomorphismCouponCalculus.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "TensorAutomorphismCouponCalculusAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CanonicalModularKirbyEvaluator.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyEvaluatorAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralCharacterKirbyColorCompiler.lean"
    ),
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean",
    "lean/TwistedYetter/Kirby/EGNOModularFourManifoldInvariant.lean",
    "lean/TwistedYetter/Kirby/KirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/SourceBoundLocalMoveRecipe.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundGraphicalMoveCompiler.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "ModularFourManifoldInvariantFinalTarget.lean"
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
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBoundGeometricH2Compiler.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturality.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyInvariance.lean"
    ),
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
        "boundary-standardization-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "kirby-completeness-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "framed-link-presentation-independence-primary-sources-v1.json"
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
        "homologically-twisted-kirby-invariant-sources-v1.json"
    ),
]

TOPOLOGY_ASSUMPTIONS = [
    "markedRealization",
    "elementaryMoveSoundness",
    "markedPresentationExistence",
    "markedKirbyCerfCompleteness",
]

HANDLE_HOMOLOGY_ASSUMPTIONS = [
    "handleChainNaturality",
]

IMPORTED_STATEMENT_CLASSES = [
    *TOPOLOGY_ASSUMPTIONS,
    *HANDLE_HOMOLOGY_ASSUMPTIONS,
]

LOCAL_CALCULATION_CLASSES = [
    "framedIsotopy",
    "oneOverOne",
    "twoOverOne",
    "twoOverTwo",
    "oneTwoBirth",
    "oneTwoDeath",
    "twoThreeBirth",
    "twoThreeDeath",
]

EXPECTED_PROJECT_AXIOMS = [
    "TwistedYetter.Fusion.EGNO."
    "sMatrixNondegenerate_iff_trivialMuegerCenter",
    "TwistedYetter.Fusion.EGNO.ModularCategory."
    "globalDimension_ne_zero",
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
    (
        "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
        "standardHandleChainNaturalityInput"
    ),
]

FOUNDATIONAL_AXIOMS = ["Classical.choice", "Quot.sound", "propext"]


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_metadata(relative: str) -> dict[str, Any]:
    path = ROOT / relative
    data = path.read_bytes()
    return {
        "bytes": len(data),
        "sha256": sha256_bytes(data),
    }


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
        "stdout_bytes": len(output.encode()),
        "stdout_sha256": sha256_bytes(output.encode()),
        "warning_count": output.count("warning:"),
        "completed_successfully": "completed successfully" in output.lower(),
    }


def git_text(*args: str) -> str:
    return run(["git", *args]).stdout.strip()


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
    invariance_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyInvariance.lean"
    )
    evaluator_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyEvaluator.lean"
    )
    recipe_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "SourceBoundLocalMoveRecipe.lean"
    )
    weight_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "EGNOModularFourManifoldInvariant.lean"
    )
    cycle_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "IntegralCharacterKirbyColorCompiler.lean"
    )
    invariance = invariance_path.read_text()
    evaluator = evaluator_path.read_text()
    recipe = recipe_path.read_text()
    weight = weight_path.read_text()
    cycle = cycle_path.read_text()

    theory_start = invariance.index(
        "noncomputable def handlePresentationTheory"
    )
    theory_end = invariance.index(
        "noncomputable def presentationEvaluation", theory_start
    )
    theory_signature = invariance[theory_start:theory_end]

    realization_start = invariance.index(
        "structure LocalMoveRealization"
    )
    realization_end = invariance.index(
        "namespace LocalMoveRealization", realization_start
    )
    realization_structure = invariance[
        realization_start:realization_end
    ]

    eval_start = evaluator.index("noncomputable def EvalC")
    eval_end = evaluator.index(
        "theorem linearDiagram_eval", eval_start
    )
    eval_signature = evaluator[eval_start:eval_end]

    require(
        "ElementaryMove := fun source target =>\n"
        "    TopologicalTableTwoMove source.topology target.topology"
        in theory_signature,
        "topology theory is not visibly TopologicalTableTwoMove-based",
    )
    require(
        "ModularCategory" not in theory_signature
        and "TensorIdentityAutomorphism" not in theory_signature,
        "category data leaked into the topology move theory",
    )
    require(
        all(
            re.search(rf"(?m)^  {name}\s*:", realization_structure)
            for name in LOCAL_CALCULATION_CLASSES
        ),
        "the eight local realization fields are not all visible",
    )
    forbidden_equality_fields = [
        "valueEquality",
        "evalEquality",
        "scalarEquality",
        "invariantEquality",
    ]
    require(
        all(
            field not in realization_structure
            for field in forbidden_equality_fields
        ),
        "a forbidden final-equality field entered LocalMoveRealization",
    )
    require(
        "PresentationCompiler" not in eval_signature
        and "LocalMoveCompiler" not in eval_signature
        and "EvidenceBinding" not in eval_signature,
        "canonical EvalC still accepts an engineering compiler",
    )
    require(
        "GraphicallyRealizedMove" not in invariance,
        "the category-dependent topology move relation returned",
    )
    require(
        "noncomputable def enrichedMove" in invariance
        and "sourceBackedGeometricH2Compiler" in invariance,
        "the source-backed handle-chain enrichment is not visible",
    )
    require(
        "MarkedH2Transport" not in realization_structure,
        "LocalMoveRealization accepts a freely supplied H2 transport",
    )
    require(
        "normalizedCycleRepresentative" in cycle
        and "IntegralTwoHandleCycleModel.canonical" in weight,
        "the representative-choice route changed without updating its audit",
    )

    cycle_realization_start = evaluator.index(
        "structure CycleBoundaryGraphicalRealization"
    )
    cycle_realization_end = evaluator.index(
        "theorem CycleBoundaryGraphicalRealization."
        "respects_homology_class",
        cycle_realization_start,
    )
    cycle_realization_structure = evaluator[
        cycle_realization_start:cycle_realization_end
    ]
    require(
        "LinearGeneratedCalculation" in cycle_realization_structure,
        "cycle descent is not expressed by the coupon proof grammar",
    )
    require(
        all(
            field not in cycle_realization_structure
            for field in forbidden_equality_fields
        )
        and "cycleEvalC" not in cycle_realization_structure
        and "LinearDiagram.eval" not in cycle_realization_structure,
        "cycle descent accepts a final evaluator equality",
    )
    tensor_automorphism = (
        ROOT
        / "lean/TwistedYetter/Fusion/"
        "EGNOTensorAutomorphism.lean"
    ).read_text()
    require(
        "automorphismCouponPower_eq_smul_identity"
        in tensor_automorphism,
        "the scalar-weight/coupon-power comparison theorem is absent",
    )

    proof_holes: list[str] = []
    hole_pattern = re.compile(
        r"(?m)^\s*(?:sorry|admit)\b|\bnative_decide\b"
    )
    for relative in SOURCE_FILES:
        if not relative.endswith(".lean") or relative.endswith(
            "AxiomAudit.lean"
        ):
            continue
        text = (ROOT / relative).read_text()
        if hole_pattern.search(text):
            proof_holes.append(relative)
    require(not proof_holes, f"proof holes found: {proof_holes}")

    return {
        "status": "PASS_GUARDS",
        "topology_theory_is_category_neutral": True,
        "canonical_eval_has_no_compiler_argument": True,
        "topology_move_uses_source_backed_h2_enrichment": True,
        "local_realization_has_no_free_h2_transport": True,
        "local_realization_has_eight_named_fields": True,
        "local_realization_has_no_final_scalar_equality_field": True,
        "cycle_descent_uses_coupon_proof_grammar": True,
        "cycle_descent_has_no_final_evaluator_equality_field": True,
        "scalar_weight_equals_actual_coupon_power": True,
        "proof_holes": proof_holes,
        "recipe_data_audit": {
            "status": "INSUFFICIENT_FOR_TOTAL_CANONICAL_REALIZATION",
            "basis": [
                (
                    "Cycle-level evaluation and the generated coupon proof "
                    "grammar are now explicit, but no constructor yet "
                    "compiles a degree-three handle boundary into that "
                    "grammar."
                ),
                (
                    "The source-backed chain compiler now binds the "
                    "equivalence to the exact topology move; the graphical "
                    "recipe still lacks the typed trace data needed to "
                    "construct the corresponding evaluator calculation."
                ),
                (
                    "GraphicalEditProgram stores generator tags and "
                    "component IDs but no typed categorical contexts."
                ),
                (
                    "PresentationWindowEdit does not supply a proved "
                    "source-target component correspondence or the global "
                    "simple-label bijection required by the finite sums."
                ),
                (
                    "The recipe does not prove preservation of global "
                    "homological weights under the label and chain "
                    "transport."
                ),
                (
                    "Cancellation constructors do not supply the exact "
                    "diagram factorization needed by normalization."
                ),
            ],
            "source_uses_per_presentation_choice_of_cycle_representative": (
                "normalizedCycleRepresentative" in cycle
                and "IntegralTwoHandleCycleModel.canonical" in weight
            ),
            "source_contains_representative_independence_theorem": (
                "CycleBoundaryGraphicalRealization."
                "respects_homology_class" in evaluator
            ),
            "source_binds_chain_equivalence_to_handle_edit": (
                "SourceBoundChainMoveCertificate move" in (
                    ROOT
                    / "lean/TwistedYetter/Kirby/"
                    "SourceBackedHandleChainNaturality.lean"
                ).read_text()
            ),
            "source_contains_typed_context": (
                "TypedCategoricalContext" in recipe
            ),
            "source_contains_label_bijection": (
                "GlobalLabelBijection" in recipe
            ),
            "source_contains_global_weight_transport": (
                "GlobalWeightTransport" in recipe
            ),
            "source_contains_cancellation_factorization": (
                "CancellationFactorization" in recipe
            ),
        },
    }


def tool_version(argv: list[str]) -> str:
    return run(argv).stdout.strip().splitlines()[0]


def main() -> None:
    started_at = utc_now()
    start = time.monotonic()

    guards = source_guards()

    umbrella_argv = ["lake", "-Kjobs=2", "build", "TwistedYetter"]
    umbrella_result = run(umbrella_argv)

    audit_argv = [
        "lake",
        "-Kjobs=2",
        "build",
        (
            "TwistedYetter.Kirby."
            "CanonicalModularKirbyInvarianceAxiomAudit"
        ),
    ]
    audit_result = run(audit_argv)
    project_axioms, foundational_axioms = extract_axiom_names(
        audit_result.stdout
    )
    require(
        project_axioms == sorted(EXPECTED_PROJECT_AXIOMS),
        "unexpected canonical-invariance project axiom set: "
        f"{project_axioms}",
    )
    require(
        foundational_axioms == sorted(FOUNDATIONAL_AXIOMS),
        "unexpected foundational axiom set: "
        f"{foundational_axioms}",
    )

    topology_audit_argv = [
        "lake",
        "-Kjobs=2",
        "build",
        (
            "TwistedYetter.Kirby."
            "LiteratureBackedFourManifoldTopologyAxiomAudit"
        ),
    ]
    topology_audit_result = run(topology_audit_argv)
    topology_project_axioms, topology_foundational_axioms = (
        extract_axiom_names(topology_audit_result.stdout)
    )
    require(
        topology_project_axioms == [],
        "derived topology layer introduced a hidden project axiom",
    )

    imported_boundary_audit_argv = [
        "lake",
        "-Kjobs=2",
        "build",
        (
            "TwistedYetter.Kirby."
            "LiteratureBackedFourManifoldInputsAxiomAudit"
        ),
    ]
    imported_boundary_audit_result = run(imported_boundary_audit_argv)
    (
        imported_boundary_project_axioms,
        imported_boundary_foundational_axioms,
    ) = extract_axiom_names(imported_boundary_audit_result.stdout)
    expected_handle_axiom = [
        (
            "TwistedYetter.Kirby."
            "SourceBackedHandleChainNaturality."
            "standardHandleChainNaturalityInput"
        )
    ]
    require(
        imported_boundary_project_axioms == expected_handle_axiom,
        "unexpected complete imported-boundary project axiom set: "
        f"{imported_boundary_project_axioms}",
    )

    coupon_audit_argv = [
        "lake",
        "-Kjobs=2",
        "build",
        (
            "TwistedYetter.Kirby."
            "TensorAutomorphismCouponCalculusAxiomAudit"
        ),
        (
            "TwistedYetter.Fusion."
            "EGNOTensorAutomorphismAxiomAudit"
        ),
    ]
    coupon_audit_result = run(coupon_audit_argv)
    coupon_project_axioms, coupon_foundational_axioms = (
        extract_axiom_names(coupon_audit_result.stdout)
    )
    require(
        coupon_project_axioms == [],
        "coupon calculus or scalar bridge introduced a project axiom: "
        f"{coupon_project_axioms}",
    )

    status_porcelain = git_text("status", "--porcelain")
    source_inputs = {
        relative: file_metadata(relative)
        for relative in SOURCE_FILES
    }
    reference_inputs = {
        relative: file_metadata(relative)
        for relative in REFERENCE_FILES
    }

    payload: dict[str, Any] = {
        "schema": "canonical-modular-four-manifold-invariant-v1",
        "status": (
            "TOPOLOGY_BOUNDARY_SEPARATED_CANONICAL_EVAL_KERNEL_CHECKED_"
            "LOCAL_REALIZATION_OPEN"
        ),
        "generator_script": (
            "experiments/scripts/"
            "build_canonical_modular_four_manifold_invariant_v1.py"
        ),
        "argv": sys.argv,
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 "
            "experiments/scripts/"
            "build_canonical_modular_four_manifold_invariant_v1.py"
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
        "inputs": {
            "source_files": source_inputs,
            "reference_records": reference_inputs,
        },
        "first_block": {
            "status": (
                "COMPLETE_AS_FOUR_TOPOLOGY_PLUS_ONE_HANDLE_CHAIN_"
                "LITERATURE_BOUNDARY"
            ),
            "imported_statement_count": 5,
            "imported_statement_classes": IMPORTED_STATEMENT_CLASSES,
            "smooth_topology": {
                "assumption_count": 4,
                "assumptions": TOPOLOGY_ASSUMPTIONS,
                "lean_type": (
                    "TwistedYetter.Kirby."
                    "LiteratureBackedFourManifoldTopology.Assumptions"
                ),
            },
            "handle_homology": {
                "assumption_count": 1,
                "assumptions": HANDLE_HOMOLOGY_ASSUMPTIONS,
                "lean_name": (
                    "TwistedYetter.Kirby."
                    "SourceBackedHandleChainNaturality."
                    "standardHandleChainNaturalityInput"
                ),
            },
            "topology_move_relation": (
                "category-neutral TopologicalTableTwoMove"
            ),
            "derived_in_lean": [
                "Kirby quotient equivalence",
                "descent of any locally invariant evaluation",
                "oriented-diffeomorphism invariance",
                "recovery of the presentation formula",
            ],
            "imported_not_formalized": [
                "marked realization by special handle presentations",
                "geometric soundness of elementary moves",
                "existence of a marked presentation",
                "marked Kirby-Cerf completeness",
                "handle-chain equivalence and geometric-H2 naturality",
            ],
            "source_refs": [
                "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
                "ref:baerenz-barrett-dichromatic-2018",
                "ref:de-sa-link-calculus-1979",
                "ref:laudenbach-poenaru-4d-handlebodies-1972",
            ],
            "assumption_source_mapping": {
                "markedRealization": [
                    (
                        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                        "#Definition-4.2.1"
                    ),
                    (
                        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                        "#Proposition-4.2.13"
                    ),
                ],
                "elementaryMoveSoundness": [
                    (
                        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                        "#Section-5.1"
                    ),
                    (
                        "ref:baerenz-barrett-dichromatic-2018"
                        "#Table-2"
                    ),
                ],
                "markedPresentationExistence": [
                    (
                        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                        "#Proposition-4.2.13"
                    ),
                    (
                        "ref:laudenbach-poenaru-4d-handlebodies-1972"
                    ),
                ],
                "markedKirbyCerfCompleteness": [
                    (
                        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                        "#Theorem-4.2.12"
                    ),
                    (
                        "ref:baerenz-barrett-dichromatic-2018"
                        "#Theorem-3.9"
                    ),
                    "ref:de-sa-link-calculus-1979",
                ],
                "handleChainNaturality": [
                    (
                        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
                        "#Theorem-4.2.12"
                    ),
                    (
                        "ref:baerenz-barrett-dichromatic-2018"
                        "#Table-2"
                    ),
                ],
            },
        },
        "second_block": {
            "status": (
                "PARTIAL_COUPON_LAWS_AND_SCALAR_BRIDGE_PROVED_"
                "BOUNDARY_MOVIE_AND_EIGHT_REALIZATIONS_OPEN"
            ),
            "canonical_evaluator": {
                "status": "KERNEL_CHECKED",
                "lean_name": (
                    "TwistedYetter.Kirby."
                    "CanonicalModularKirbyEvaluator."
                    "CanonicalPresentation.EvalC"
                ),
                "caller_supplies_evaluator": False,
                "caller_supplies_compiler": False,
                "caller_supplies_evidence_hash": False,
            },
            "coupon_calculus": {
                "status": "KERNEL_CHECKED",
                "proved": [
                    "tensor and unit laws",
                    "naturality and inverse naturality",
                    "positive and negative crossing passage",
                    "left and right cup/cap passage",
                    "coupon/inverse cancellation",
                    (
                        "context, transitivity, symmetry, and "
                        "linear closure"
                    ),
                    (
                        "integral simple coupon power equals evaluator "
                        "scalar power"
                    ),
                ],
                "project_axioms": [],
            },
            "representative_descent": {
                "status": "OPEN_GEOMETRIC_COMPILATION_OBLIGATION",
                "scalar_equality_is_not_an_input": True,
                "proved_if_graphical_calculation_is_supplied": True,
                "missing": (
                    "A source-bound compiler from each degree-three handle "
                    "boundary to the closed generated coupon calculation."
                ),
            },
            "local_calculation_soundness": {
                "status": "KERNEL_CHECKED_FOR_ALL_EIGHT_CONSTRUCTORS",
                "count": 8,
                "classes": LOCAL_CALCULATION_CLASSES,
                "lean_name": (
                    "TwistedYetter.Kirby."
                    "CanonicalModularKirbyInvariance."
                    "LocalCalculation.sound"
                ),
            },
            "missing_realization": {
                "status": "OPEN_ESSENTIAL_OBLIGATION",
                "count": 8,
                "classes": LOCAL_CALCULATION_CLASSES,
                "lean_type": (
                    "TwistedYetter.Kirby."
                    "CanonicalModularKirbyInvariance."
                    "LocalMoveRealization"
                ),
                "meaning": (
                    "For every concrete TopologicalTableTwoMove and every "
                    "marking, "
                    "construct the corresponding typed local graphical "
                    "calculation from the source-bound recipe."
                ),
                "not_equivalent_to": (
                    "a final equality of EvalC values"
                ),
            },
            "current_recipe_gap": guards["recipe_data_audit"],
            "required_completion_order": [
                (
                    "Done: define the evaluator first on explicit "
                    "degree-two cycles."
                ),
                (
                    "Done: prove all local tensor-automorphism coupon laws "
                    "and identify scalar powers with actual coupon powers."
                ),
                (
                    "Compile each degree-three handle boundary into those "
                    "local coupon laws, then descend cycle evaluation to H2."
                ),
                (
                    "Done: bind each topology move to its source-backed "
                    "chain equivalence and geometric-H2 naturality square."
                ),
                (
                    "Derive source-target component and global-label "
                    "transport together with global-weight preservation."
                ),
                (
                    "Compile the exact local trace contexts, slide windows, "
                    "and cancellation factorizations."
                ),
                (
                    "Construct all eight LocalMoveRealization fields and "
                    "remove that parameter from the final theorem."
                ),
            ],
        },
        "conditional_final_theorem": {
            "status": (
                "KERNEL_CHECKED_CONDITIONAL_ON_EXPLICIT_TOPOLOGY_"
                "AND_LOCAL_MOVE_REALIZATION"
            ),
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
            "is_unconditional_closed_four_manifold_invariant": False,
            "caller_supplies_final_scalar_equality": False,
            "caller_supplies_local_move_realization": True,
            "caller_supplies_topology_assumptions": True,
            "uses_separate_handle_chain_naturality_axiom": True,
        },
        "checks": {
            "source_guards": guards,
            "umbrella_build": command_summary(
                umbrella_argv, umbrella_result
            ),
            "canonical_axiom_audit_build": command_summary(
                audit_argv, audit_result
            ),
            "topology_axiom_audit_build": command_summary(
                topology_audit_argv, topology_audit_result
            ),
            "imported_boundary_axiom_audit_build": command_summary(
                imported_boundary_audit_argv,
                imported_boundary_audit_result,
            ),
            "coupon_axiom_audit_build": command_summary(
                coupon_audit_argv, coupon_audit_result
            ),
            "canonical_axiom_audit": {
                "project_axioms": project_axioms,
                "foundational_axioms": foundational_axioms,
            },
            "topology_derived_layer_axiom_audit": {
                "project_axioms": topology_project_axioms,
                "foundational_axioms": topology_foundational_axioms,
            },
            "complete_imported_boundary_axiom_audit": {
                "project_axioms": imported_boundary_project_axioms,
                "foundational_axioms": (
                    imported_boundary_foundational_axioms
                ),
            },
            "coupon_and_scalar_bridge_axiom_audit": {
                "project_axioms": coupon_project_axioms,
                "foundational_axioms": coupon_foundational_axioms,
            },
        },
        "explicit_non_claims": [
            (
                "This artifact does not claim that the canonical modular "
                "evaluation is already an unconditional four-manifold "
                "invariant."
            ),
            (
                "Lean does not formalize smooth manifolds, Morse theory, "
                "Cerf theory, or the cited special Kirby completeness "
                "theorems here."
            ),
            (
                "No value of LocalMoveRealization has yet been constructed "
                "from the current SourceBoundRecipe interface."
            ),
            (
                "The current recipe tags do not by themselves certify typed "
                "categorical contexts, global label and weight transport, "
                "chain-edit compatibility, or cancellation factorizations."
            ),
            (
                "The scalar/coupon bridge and coupon laws are proved, but "
                "degree-three boundaries have not yet been compiled into "
                "the generated coupon grammar; representative independence "
                "therefore remains open."
            ),
            (
                "This artifact does not identify EvalC with the original "
                "Crane-Yetter state sum."
            ),
            (
                "This artifact proves no premodular-category theorem and "
                "instantiates no concrete modular category."
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
