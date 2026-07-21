#!/usr/bin/env python3
"""Build the certificate for the clean Kirby-quotient descent boundary."""

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


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-modular-final-theorem-refactor-v1.json"
)
SUPERSEDING_ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "canonical-modular-four-manifold-invariant-v1.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_modular_final_theorem_refactor_v1.py",
    "tests/test_egno_modular_final_theorem_refactor_v1.py",
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOPremodularModular.lean",
    "lean/TwistedYetter/Fusion/EGNOPremodularModularAxiomAudit.lean",
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "EGNOModularKirbyMovesAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/EGNOModularFourManifoldInvariant.lean",
    "lean/TwistedYetter/Kirby/BoundaryStandardization.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryStandardizationAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/StandardCapClosure.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "StandardCapClosureAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/BoundaryDerivedHandleChain.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryDerivedHandleChainAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/BoundaryDerivedHandleChainModel.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryDerivedHandleChainModelAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/BoundaryCertifiedKirbyPresentation.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryCertifiedKirbyPresentationAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/SourceBackedKirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/SourceBoundGeometricH2Compiler.lean",
    "lean/TwistedYetter/Kirby/SourceBackedHandleChainNaturality.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturalityAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/BoundaryCertifiedModularEvaluator.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryCertifiedModularEvaluatorAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/ModularFourManifoldInvariantFinalTarget.lean",
    "lean/TwistedYetter/Kirby/EGNOModularFinalTheoremRefactor.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "EGNOModularFinalTheoremRefactorAxiomAudit.lean"
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
]
DESIGN_FILES = [
    (
        "experiments/inputs/lean-kirby/"
        "boundary-standardization-obligation-matrix-v1.json"
    ),
]
BOUNDARY_AUDIT_FILES = {
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryStandardizationAxiomAudit.lean"
    ): 5,
    (
        "lean/TwistedYetter/Kirby/"
        "StandardCapClosureAxiomAudit.lean"
    ): 3,
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryDerivedHandleChainAxiomAudit.lean"
    ): 6,
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryDerivedHandleChainModelAxiomAudit.lean"
    ): 5,
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryCertifiedKirbyPresentationAxiomAudit.lean"
    ): 4,
}
BOUNDARY_EVALUATOR_AUDIT_FILE = (
    "lean/TwistedYetter/Kirby/"
    "BoundaryCertifiedModularEvaluatorAxiomAudit.lean"
)
BOUNDARY_EVALUATOR_AUDIT_COUNT = 6
EXPECTED_CUSTOM_AXIOMS = [
    (
        "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
        "standardHandleChainNaturalityInput"
    ),
    (
        "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
        "standardSpecialKirbyCalculusConnected"
    ),
]
EXPECTED_TEXTBOOK_AXIOMS = [
    "TwistedYetter.Fusion.EGNO.sphericalRibbonReconstruction",
    (
        "TwistedYetter.Fusion.EGNO."
        "sMatrixNondegenerate_iff_trivialMuegerCenter"
    ),
    (
        "TwistedYetter.Fusion.EGNO.ModularCategory."
        "globalDimension_ne_zero"
    ),
]
EXPECTED_GRAPHICAL_LITERATURE_AXIOMS = [
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "egno_quantumDimension_unit"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "baerenzBarrett_ordinaryKirbySliding"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "baerenzBarrett_oneTwoHopfPairSum"
    ),
    (
        "TwistedYetter.Kirby.EGNOModularKirbyMoves."
        "LiteratureBackedModularGraphicalEnvironment."
        "shum_ribbonFramedKink"
    ),
]
EXPECTED_GRAPHICAL_ENVIRONMENT_AXIOMS = [
    EXPECTED_TEXTBOOK_AXIOMS[1],
    EXPECTED_TEXTBOOK_AXIOMS[2],
    EXPECTED_GRAPHICAL_LITERATURE_AXIOMS[0],
    EXPECTED_GRAPHICAL_LITERATURE_AXIOMS[1],
    EXPECTED_GRAPHICAL_LITERATURE_AXIOMS[3],
]
EXPECTED_GRAPHICAL_AUDIT_AXIOMS = [
    EXPECTED_TEXTBOOK_AXIOMS[1],
    EXPECTED_TEXTBOOK_AXIOMS[2],
    *EXPECTED_GRAPHICAL_LITERATURE_AXIOMS,
]
EXPECTED_FINAL_AXIOMS = [
    *EXPECTED_GRAPHICAL_ENVIRONMENT_AXIOMS,
]
EXPECTED_BOUNDARY_EVALUATOR_AXIOMS = [
    EXPECTED_CUSTOM_AXIOMS[0],
    *EXPECTED_FINAL_AXIOMS,
]


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
        cwd=ROOT,
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
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def version(argv: list[str]) -> str:
    result = run(argv)
    return (result.stdout or result.stderr).strip().splitlines()[0]


def proof_hole_scan() -> dict[str, Any]:
    forbidden = re.compile(
        r"^\s*(?:sorry|admit)\b|\bnative_decide\b",
        re.MULTILINE,
    )
    checked: list[str] = []
    for relative in SOURCE_FILES:
        if not relative.endswith(".lean") or relative.endswith(
            "AxiomAudit.lean"
        ):
            continue
        text = (ROOT / relative).read_text()
        match = forbidden.search(text)
        if match:
            raise AssertionError(
                f"forbidden proof-oracle token in {relative}: "
                f"{match.group(0)!r}"
            )
        checked.append(relative)
    return {
        "status": "PASS_NO_SORRY_ADMIT_OR_NATIVE_DECIDE",
        "checked_files": checked,
    }


def project_axioms_from_audit(output: str) -> list[str]:
    axiom_lists = re.findall(
        r"depends on axioms:\s*\[(.*?)\]",
        output,
        flags=re.DOTALL,
    )
    return sorted(
        {
            name
            for axiom_list in axiom_lists
            for name in re.findall(
                r"TwistedYetter\.[A-Za-z0-9_.]+",
                axiom_list,
            )
        }
    )


def run_boundary_axiom_audits() -> dict[str, Any]:
    reports: dict[str, Any] = {}
    for relative, expected_count in BOUNDARY_AUDIT_FILES.items():
        result = run(["lake", "env", "lean", relative])
        output = result.stdout + result.stderr
        if "sorryAx" in output or "native_decide.ax" in output:
            raise AssertionError(
                f"boundary axiom audit exposed a proof oracle: {relative}"
            )
        audited_count = len(
            re.findall(r"^'TwistedYetter\.", output, flags=re.MULTILINE)
        )
        if audited_count != expected_count:
            raise AssertionError(
                f"{relative} audited {audited_count} declarations; "
                f"expected {expected_count}"
            )
        project_axioms = project_axioms_from_audit(output)
        if project_axioms:
            raise AssertionError(
                f"{relative} unexpectedly used project axioms: "
                f"{project_axioms}"
            )
        foundational_axioms = sorted(
            {
                name
                for axiom_list in re.findall(
                    r"depends on axioms:\s*\[(.*?)\]",
                    output,
                    flags=re.DOTALL,
                )
                for name in re.findall(
                    r"(?<!TwistedYetter\.)\b"
                    r"(?:propext|Classical\.choice|Quot\.sound)\b",
                    axiom_list,
                )
            }
        )
        reports[relative] = {
            "status": "PASS_NO_PROJECT_AXIOMS_OR_PROOF_ORACLES",
            "audited_declaration_count": audited_count,
            "project_axioms": project_axioms,
            "lean_foundational_axioms": foundational_axioms,
        }
    return {
        "status": "PASS_ALL_BOUNDARY_LAYERS_AUDITED",
        "files": reports,
    }


def run_boundary_evaluator_axiom_audit() -> dict[str, Any]:
    result = run(["lake", "env", "lean", BOUNDARY_EVALUATOR_AUDIT_FILE])
    output = result.stdout + result.stderr
    if "sorryAx" in output or "native_decide.ax" in output:
        raise AssertionError(
            "boundary evaluator axiom audit exposed a proof oracle"
        )
    audited_count = len(
        re.findall(r"^'TwistedYetter\.", output, flags=re.MULTILINE)
    )
    if audited_count != BOUNDARY_EVALUATOR_AUDIT_COUNT:
        raise AssertionError(
            "boundary evaluator audit checked "
            f"{audited_count} declarations; expected "
            f"{BOUNDARY_EVALUATOR_AUDIT_COUNT}"
        )
    project_axioms = project_axioms_from_audit(output)
    if project_axioms != sorted(EXPECTED_BOUNDARY_EVALUATOR_AXIOMS):
        raise AssertionError(
            "boundary evaluator introduced an unexpected project axiom set: "
            f"{project_axioms}"
        )
    return {
        "status": (
            "PASS_EXACT_GRAPHICAL_AXIOMS_PLUS_VISIBLE_"
            "HANDLE_CHAIN_NATURALITY_AXIOM"
        ),
        "file": BOUNDARY_EVALUATOR_AUDIT_FILE,
        "audited_declaration_count": audited_count,
        "project_axioms": project_axioms,
    }


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }

    final_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "EGNOModularFinalTheoremRefactor.lean"
    ).read_text()
    target_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "ModularFourManifoldInvariantFinalTarget.lean"
    ).read_text()
    kirby_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "EGNOModularKirbyMoves.lean"
    ).read_text()
    assembly_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "EGNOModularFourManifoldInvariant.lean"
    ).read_text()
    boundary_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "BoundaryStandardization.lean"
    ).read_text()
    cap_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "StandardCapClosure.lean"
    ).read_text()
    derived_chain_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "BoundaryDerivedHandleChain.lean"
    ).read_text()
    derived_model_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "BoundaryDerivedHandleChainModel.lean"
    ).read_text()
    certified_presentation_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "BoundaryCertifiedKirbyPresentation.lean"
    ).read_text()
    certified_evaluator_source = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "BoundaryCertifiedModularEvaluator.lean"
    ).read_text()
    required_contracts = [
        "structure CompiledEvaluatorEvidence",
        "theorem h2ModelEquiv_transport",
        "theorem evalC_local_move_invariant",
        "noncomputable def compiledEvaluation",
        "noncomputable def compiledEvaluationOnKirbyClass",
        "theorem compiledEvaluationOnKirbyClass_mk",
    ]
    missing = [
        name for name in required_contracts if name not in final_source
    ]
    target_contracts = [
        "structure HandlePresentationTheory",
        "inductive KirbyMovie",
        "def KirbyEquivalent",
        "def KirbyClass",
        "structure PresentationEvaluation",
        "def IsInvariantUnderElementaryMoves",
        "theorem respectsKirbyEquivalent",
        "def descendToKirbyClass",
        "structure MarkedFourManifoldRealization",
        "structure ElementaryMoveGeometricSoundness",
        "structure MarkedPresentationExistence",
        "structure MarkedKirbyCerfCompleteness",
        "def kirbyClassEquivDiffeomorphismClass",
        "theorem fourManifoldInvariant_diffeomorphism_invariant",
        "theorem fourManifoldInvariant_on_presentation",
    ]
    missing.extend(
        name for name in target_contracts if name not in target_source
    )
    boundary_contracts = [
        "inductive ElementaryMove",
        "inductive KirbyMovie",
        "structure SurgerySemantics",
        "structure BoundaryStandardizationCertificate",
        "def threeHandleCount",
        "def boundaryDiffeomorphism",
        "structure CertifiedClosedPresentation",
        "def handleCounts",
        "theorem h3_eq_boundary_genus",
    ]
    missing.extend(
        name for name in boundary_contracts if name not in boundary_source
    )
    cap_contracts = [
        "structure StandardBoundaryGenusDetection",
        "structure StandardCapTheory",
        "structure LaudenbachPoenaruExtensionTheorem",
        "structure StandardCapGluingTheory",
        "theorem genus_unique",
        "def closedManifold",
        "def closedCompletionChoiceDiffeomorphism",
    ]
    missing.extend(
        name for name in cap_contracts if name not in cap_source
    )
    derived_chain_contracts = [
        "structure SphereSystemTransport",
        "def attachingSphereSystem",
        "structure AttachingSphereIntersectionTheory",
        "def d3",
        "theorem d2_d3_zero",
        "abbrev SecondHomology",
        "def derivedHandleBoundaryData",
        "abbrev derivedSecondHomology",
    ]
    missing.extend(
        name
        for name in derived_chain_contracts
        if name not in derived_chain_source
    )
    derived_model_contracts = [
        "def chainDifferential",
        "theorem chainDifferential_squared",
        "def derivedComplex",
        "theorem derivedComplex_d2",
        "theorem derivedComplex_d3",
        "def derivedHandleChainModel",
        "def CertifiedClosedPresentation.derivedHandleChainModel",
    ]
    missing.extend(
        name
        for name in derived_model_contracts
        if name not in derived_model_source
    )
    certified_presentation_contracts = [
        "structure LowerKirbyDiagramSemantics",
        "structure BoundaryCertifiedPresentation",
        "def handleChain",
        "def toSpecialKirbyPresentation",
        "theorem toSpecialKirbyPresentation_handleChain",
        "theorem formal_boundary_diagram_sound",
    ]
    missing.extend(
        name
        for name in certified_presentation_contracts
        if name not in certified_presentation_source
    )
    certified_evaluator_contracts = [
        "structure BoundaryCertifiedMove",
        "noncomputable def enriched",
        "noncomputable def boundaryCertifiedCalculus",
        "noncomputable def boundaryCertifiedEvaluation",
        "theorem boundaryCertifiedEvaluation_localInvariant",
        "noncomputable def boundaryCertifiedEvaluationOnKirbyClass",
        "theorem boundaryCertifiedEvaluationOnKirbyClass_mk",
    ]
    missing.extend(
        name
        for name in certified_evaluator_contracts
        if name not in certified_evaluator_source
    )
    graphical_fields = [
        "ordinaryKirbySlidingLaw",
        "cancellationLaw",
        "framedKinkLaw",
    ]
    missing.extend(
        name for name in graphical_fields if name not in kirby_source
    )
    if "theorem required_graphical_rule_class_count" not in kirby_source:
        missing.append("theorem required_graphical_rule_class_count")
    literature_axiom_names = [
        name.rsplit(".", maxsplit=1)[-1]
        for name in EXPECTED_GRAPHICAL_LITERATURE_AXIOMS
    ]
    missing.extend(
        f"axiom {name}"
        for name in literature_axiom_names
        if f"axiom {name}" not in kirby_source
    )
    if missing:
        raise AssertionError(f"missing final theorem contracts: {missing}")
    stale_overclaims = [
        "theorem refactoredFourManifoldInvariant",
        "theorem four_manifold_invariant",
        "theorem conditional_descent",
        "theorem conditionalPresentationSpecificDescent",
        "structure ConditionalDescentInputs",
        "theorem conditional_shared_coordinate_descent",
        "def CandidateEvalCGraphicalInvarianceTarget",
        "noncomputable def candidateEvalC",
        "UnprovedGraphicalInvarianceInputs",
        "def EvalCFourManifoldInvariantTarget",
        "def evalCFromPresentationCompiler",
        "structure FourManifoldTopologyBridge",
        "structure ModularKirbyEvaluator",
        "structure ClosedFourManifoldKirbyCorrespondence",
        "kirbyCerfAndThreeHandleCompletion",
    ]
    present_overclaims = [
        name
        for name in stale_overclaims
        if name in final_source
        or name in target_source
        or name in kirby_source
        or name in assembly_source
    ]
    if present_overclaims:
        raise AssertionError(
            f"stale overclaiming theorem names remain: {present_overclaims}"
        )
    if "Terminal theorem" in final_source or "Terminal theorem" in target_source:
        raise AssertionError("stale Terminal theorem comment remains")
    if "inductive KirbyEquivalent" in target_source:
        raise AssertionError(
            "KirbyEquivalent must erase a proof-relevant KirbyMovie; "
            "it cannot itself be a Prop-valued inductive movie"
        )
    certified_presentation_match = re.search(
        r"structure BoundaryCertifiedPresentation\b(?P<body>.*?)"
        r"\nnamespace BoundaryCertifiedPresentation",
        certified_presentation_source,
        flags=re.DOTALL,
    )
    if certified_presentation_match is None:
        raise AssertionError(
            "could not isolate BoundaryCertifiedPresentation structure body"
        )
    if re.search(
        r"^\s*handleChain\s*:",
        certified_presentation_match.group("body"),
        flags=re.MULTILINE,
    ):
        raise AssertionError(
            "BoundaryCertifiedPresentation must not accept a handleChain field"
        )
    boundary_move_match = re.search(
        r"structure BoundaryCertifiedMove\b(?P<body>.*?)"
        r"\nnamespace BoundaryCertifiedMove",
        certified_evaluator_source,
        flags=re.DOTALL,
    )
    if boundary_move_match is None:
        raise AssertionError(
            "could not isolate BoundaryCertifiedMove structure body"
        )
    boundary_move_body = boundary_move_match.group("body")
    if "TopologicalTableTwoMove" not in boundary_move_body:
        raise AssertionError(
            "BoundaryCertifiedMove must contain a topology-only move"
        )
    if (
        "MarkedH2Transport" in boundary_move_body
        or "HandleChainEquivalence" in boundary_move_body
    ):
        raise AssertionError(
            "BoundaryCertifiedMove must not accept caller-supplied transport"
        )
    if (
        "sourceBackedGeometricH2Compiler"
        not in certified_evaluator_source
    ):
        raise AssertionError(
            "boundary move transport is not derived from the visible "
            "handle-chain naturality axiom"
        )
    if "move.underlying.homologyTransport" in certified_evaluator_source:
        raise AssertionError(
            "boundary evaluator still consumes caller-supplied move transport"
        )
    if (
        "Marking := fun presentation =>\n"
        "    presentation.handleChain.SecondHomology"
        not in certified_evaluator_source
    ):
        raise AssertionError(
            "boundary evaluator marking is not the derived handle-chain H2"
        )
    if (
        "inputs.evalC_local_move_invariant"
        not in certified_evaluator_source
    ):
        raise AssertionError(
            "boundary evaluator no longer derives local invariance from "
            "the existing event compiler"
        )

    build_result = run(["lake", "-Kjobs=2", "build", "TwistedYetter"])
    boundary_audit = run_boundary_axiom_audits()
    boundary_evaluator_audit = run_boundary_evaluator_axiom_audit()
    audit_result = run(
        [
            "lake",
            "env",
            "lean",
            (
                "lean/TwistedYetter/Kirby/"
                "EGNOModularFinalTheoremRefactorAxiomAudit.lean"
            ),
        ]
    )
    audit_output = audit_result.stdout + audit_result.stderr
    if "sorryAx" in audit_output or "native_decide.ax" in audit_output:
        raise AssertionError("final axiom audit exposed a proof oracle")
    audited = len(
        re.findall(r"^'TwistedYetter\.", audit_output, flags=re.MULTILINE)
    )
    if audited != 12:
        raise AssertionError(f"expected 12 audited declarations, got {audited}")
    project_axioms = project_axioms_from_audit(audit_output)
    if project_axioms != sorted(EXPECTED_FINAL_AXIOMS):
        raise AssertionError(
            f"unexpected project axiom set: {project_axioms}"
        )
    graphical_audit_result = run(
        [
            "lake",
            "env",
            "lean",
            (
                "lean/TwistedYetter/Kirby/"
                "EGNOModularKirbyMovesAxiomAudit.lean"
            ),
        ]
    )
    graphical_audit_output = (
        graphical_audit_result.stdout + graphical_audit_result.stderr
    )
    if (
        "sorryAx" in graphical_audit_output
        or "native_decide.ax" in graphical_audit_output
    ):
        raise AssertionError("graphical axiom audit exposed a proof oracle")
    graphical_axiom_lists = re.findall(
        r"depends on axioms:\s*\[(.*?)\]",
        graphical_audit_output,
        flags=re.DOTALL,
    )
    graphical_axioms = sorted(
        {
            name
            for axiom_list in graphical_axiom_lists
            for name in re.findall(
                r"TwistedYetter\.[A-Za-z0-9_.]+",
                axiom_list,
            )
        }
    )
    if graphical_axioms != sorted(EXPECTED_GRAPHICAL_AUDIT_AXIOMS):
        raise AssertionError(
            f"unexpected graphical environment axiom set: "
            f"{graphical_axioms}"
        )
    category_audit_result = run(
        [
            "lake",
            "env",
            "lean",
            (
                "lean/TwistedYetter/Fusion/"
                "EGNOPremodularModularAxiomAudit.lean"
            ),
        ]
    )
    category_audit_output = (
        category_audit_result.stdout + category_audit_result.stderr
    )
    if (
        "sorryAx" in category_audit_output
        or "native_decide.ax" in category_audit_output
    ):
        raise AssertionError("category axiom audit exposed a proof oracle")
    category_axiom_lists = re.findall(
        r"depends on axioms:\s*\[(.*?)\]",
        category_audit_output,
        flags=re.DOTALL,
    )
    textbook_axioms = sorted(
        {
            name
            for axiom_list in category_axiom_lists
            for name in re.findall(
                r"TwistedYetter\.[A-Za-z0-9_.]+",
                axiom_list,
            )
        }
    )
    if textbook_axioms != sorted(EXPECTED_TEXTBOOK_AXIOMS):
        raise AssertionError(
            f"unexpected textbook axiom set: {textbook_axioms}"
        )

    source_files = {
        relative: {
            "bytes": (ROOT / relative).stat().st_size,
            "sha256": sha256_path(ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    references = {
        relative: {
            "bytes": (ROOT / relative).stat().st_size,
            "sha256": sha256_path(ROOT / relative),
        }
        for relative in REFERENCE_FILES
    }
    design_records = {
        relative: {
            "bytes": (ROOT / relative).stat().st_size,
            "sha256": sha256_path(ROOT / relative),
        }
        for relative in DESIGN_FILES
    }
    build_lines = (build_result.stdout + build_result.stderr).splitlines()
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-modular-final-theorem-refactor.v1",
        "status": (
            "SUPERSEDED_BY_CANONICAL_MODULAR_"
            "FOUR_MANIFOLD_INVARIANT_V1"
        ),
        "mathematical_status": (
            "HISTORICAL_BOUNDARY_CERTIFIED_KIRBY_QUOTIENT_"
            "RESULT_SUPERSEDED"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.perf_counter() - started_clock, 6),
        "repo_root": str(ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/"
            "build_egno_modular_final_theorem_refactor_v1.py"
        ),
        "argv": [
            (
                "experiments/scripts/"
                "build_egno_modular_final_theorem_refactor_v1.py"
            )
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 experiments/scripts/"
            "build_egno_modular_final_theorem_refactor_v1.py"
        ),
        "supersession": {
            "artifact": str(SUPERSEDING_ARTIFACT.relative_to(ROOT)),
            "content_hash": json.loads(
                SUPERSEDING_ARTIFACT.read_text(encoding="utf-8")
            )["content_hash"],
            "reason": (
                "The superseding artifact constructs canonical EvalC, "
                "separates the category-neutral topology calculus, and "
                "exposes the still-open local-move realization obligations."
            ),
        },
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": version(["lake", "env", "lean", "--version"]),
            "lake": version(["lake", "--version"]),
            "mathlib_commit": git(
                "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"
            ),
        },
        "inputs": {
            "source_files": source_files,
            "reference_records": references,
            "design_records": design_records,
        },
        "checks": {
            "umbrella_build": {
                "status": "PASS",
                "lean_num_threads": 1,
                "lake_jobs": 2,
                "output_tail": build_lines[-1] if build_lines else "",
            },
            "proof_hole_scan": proof_hole_scan(),
            "boundary_axiom_audit": boundary_audit,
            "boundary_evaluator_axiom_audit": boundary_evaluator_audit,
            "axiom_audit": {
                "status": (
                    "PASS_NO_PROOF_ORACLE_AND_EXACT_EXPECTED_AXIOM_SET"
                ),
                "audited_declaration_count": audited,
                "all_project_axioms": project_axioms,
                "topology_axioms_used_by_quotient_descent": [],
                "graphical_environment_axioms": (
                    EXPECTED_GRAPHICAL_ENVIRONMENT_AXIOMS
                ),
            },
            "graphical_axiom_audit": {
                "status": (
                    "PASS_EXACTLY_FOUR_NAMED_LITERATURE_AXIOMS_PLUS_"
                    "TWO_EXISTING_MODULAR_CATEGORY_AXIOMS"
                ),
                "graphical_literature_axioms": (
                    EXPECTED_GRAPHICAL_LITERATURE_AXIOMS
                ),
                "all_graphical_environment_axioms": graphical_axioms,
            },
            "textbook_axiom_audit": {
                "status": "PASS_EXACTLY_THREE_NAMED_EGNO_AXIOMS",
                "textbook_axioms": textbook_axioms,
            },
            "presentation_marking": (
                "PASS_MARKING_IS_EACH_PRESENTATION_HANDLE_CHAIN_H2"
            ),
            "elementary_transport": (
                "PASS_DERIVED_FROM_CHAIN_HOMOTOPY_EQUIVALENCE"
            ),
            "local_move_soundness": (
                "PASS_FROM_CONCRETE_EIGHT_CASE_COMPILER_AND_FIXED_"
                "LITERATURE_BACKED_GRAPHICAL_ENVIRONMENT"
            ),
            "generated_equivalence_soundness": (
                "PASS_REFL_SYMM_TRANS_INDUCTION"
            ),
            "kirby_quotient_descent": "PASS_QUOTIENT_LIFT",
            "proof_relevant_kirby_movie": (
                "PASS_MOVIE_LIVES_IN_TYPE_AND_ONLY_EXISTENCE_IS_ERASED"
            ),
            "boundary_standardization_movie": (
                "PASS_EXACT_WHITELIST_ISOTOPY_SLIDE_AND_"
                "SIGNED_STABILIZATION"
            ),
            "standard_cap_closure": (
                "PASS_CHOICE_INDEPENDENCE_DERIVED_FROM_GENUS_DETECTION_"
                "LAUDENBACH_POENARU_AND_GLUING"
            ),
            "derived_d3_and_h2": (
                "PASS_D3_DERIVED_FROM_TRANSPORTED_SPHERES_AND_"
                "INTERSECTION_NUMBERS"
            ),
            "derived_mathlib_handle_chain_model": (
                "PASS_CHAIN_COMPLEX_D2_D3_AND_H2_ARE_BOUNDARY_DERIVED"
            ),
            "certified_legacy_adapter": (
                "PASS_NO_CALLER_SUPPLIED_HANDLE_CHAIN"
            ),
            "topology_descent": (
                "PASS_GENERIC_DERIVATION_FROM_SPLIT_MOVE_SOUNDNESS_"
                "EXISTENCE_AND_KIRBY_CERF_COMPLETENESS_INPUTS"
            ),
            "three_handle_geometry": (
                "PASS_ARCHITECTURE_BOUNDARY_CERTIFICATE_DERIVES_H3_"
                "AND_STANDARD_CAP_CLOSED_COMPLETION"
            ),
            "legacy_evaluator_bridge": (
                "PASS_EVALUATOR_CONSUMES_BOUNDARY_DERIVED_HANDLE_CHAIN_H2_"
                "AND_MOVE_TRANSPORT_IS_DERIVED_FROM_VISIBLE_AXIOM"
            ),
        },
        "lean_derived": [
            "chain-induced transport on each presentation's handle H2",
            "compatibility with the legacy pinned H2 coordinate equivalences",
            (
                "local graphical proof from the eight-case compiler and the "
                "fixed literature-backed graphical environment"
            ),
            "invariance under the equivalence relation generated by marked moves",
            "a well-defined scalar function on the marked Kirby quotient",
            (
                "3-handle count from the certified standard boundary genus"
            ),
            (
                "closed completion and independence of the selected boundary "
                "standardization certificate from split topology inputs"
            ),
            (
                "d3 and handle-chain H2 from transported attaching spheres "
                "and intersection numbers"
            ),
            (
                "the legacy evaluator input from a boundary-certified "
                "presentation has a definitionally derived handle chain"
            ),
            (
                "the modular evaluator descends on the boundary-certified "
                "marked Kirby quotient"
            ),
            (
                "generic equivalence between the Kirby quotient and "
                "diffeomorphism classes from separately stated soundness, "
                "existence, and completeness inputs"
            ),
        ],
        "graphical_rule_boundary": {
            "status": (
                "DISCHARGED_RELATIVE_TO_EXPLICIT_LITERATURE_AXIOMS"
            ),
            "rule_count": 3,
            "rules": [
                "ordinary Kirby-colour sliding",
                "1--2 and 2--3 cancellation identities",
                "positive and negative ribbon framed-kink identities",
            ],
            "caller_supplies_graphical_laws": False,
            "literature_axioms": EXPECTED_GRAPHICAL_LITERATURE_AXIOMS,
            "cancellation_status": (
                "LEAN_DERIVED_FROM_CATEGORY_DIMENSIONS_AND_NORMALIZATION"
            ),
            "honesty_caveat": (
                "Ordinary sliding, the isolated one-two Hopf-pair sum, "
                "framed-kink coherence, and the unit-dimension fact are "
                "explicit literature axioms. "
                "Fixed-label 2-over-2 sliding is derived term by term."
            ),
        },
        "remaining_concrete_instantiation_boundary": {
            "status": (
                "CONCRETE_TOPOLOGY_GLOBAL_FAMILY_AND_COMPILER_"
                "INSTANCES_REMAIN_OPEN"
            ),
            "required_fields": [
                "concrete FramedSurgeryDiagramTheory",
                "concrete SurgerySemantics for the three primitive moves",
                "boundary standardization certificates for presentations",
                "standard boundary genus detection",
                "Laudenbach-Poenaru cap-extension theorem",
                "standard-cap gluing semantics",
                "sphere-system transport through each primitive move",
                "attaching-sphere intersection-number theory",
                (
                    "concrete lower-Kirby-diagram semantics binding serialized "
                    "evaluator inputs to boundary surgery diagrams"
                ),
                "canonical presentation and local-move compilers",
                (
                    "a global family over manifold inputs, or an equivalent "
                    "construction assembling the fixed-manifold calculi"
                ),
                "concrete marked realization and move soundness",
                "marked presentation existence",
                "marked Kirby-Cerf completeness",
            ],
            "meaning": (
                "The evaluator bridge is closed: its chain complex and H2 "
                "come from the boundary certificate, and each move transport "
                "comes from the one visible standard handle-chain naturality "
                "axiom rather than a move field. Lean checks every subsequent "
                "algebraic descent. The listed geometric theories, global "
                "assembly, certificate constructors, compilers, and "
                "Kirby-Cerf inputs still require concrete mathematical "
                "instances before this becomes an instantiated "
                "closed-four-manifold invariant."
            ),
            "not_a_global_graphical_law": True,
            "terminal_blocker": None,
        },
        "used_topology_axioms": [EXPECTED_CUSTOM_AXIOMS[0]],
        "available_but_not_used_topology_axioms": [
            EXPECTED_CUSTOM_AXIOMS[1]
        ],
        "explicit_standard_textbook_axioms": EXPECTED_TEXTBOOK_AXIOMS,
        "explicit_graphical_literature_axioms": (
            EXPECTED_GRAPHICAL_LITERATURE_AXIOMS
        ),
        "explicit_non_claims": [
            (
                "No axiom-free derivation of the four named graphical "
                "literature interfaces has been formalized."
            ),
            (
                "This historical refactor did not provide the canonical "
                "Eval_C constructor. The superseding artifact now provides "
                "that constructor and records the remaining local-move gap."
            ),
            (
                "No concrete framed-surgery semantics, boundary "
                "standardization certificate generator, or Kirby-Cerf "
                "instance has been constructed."
            ),
            (
                "The standard handle-chain naturality statement is a visible "
                "domain axiom; Lean has not reconstructed its chain maps from "
                "the attaching data of each local Kirby move."
            ),
            "No concrete modular category instance is constructed here.",
            "No numerical artifact is promoted to an exact Lean theorem.",
            (
                "The adapter accepts no independent legacy handle chain and "
                "no equivalence between two independently supplied chain "
                "complexes. It does retain an explicit marked-coordinate "
                "equivalence from the derived handle-chain H2 to the fixed "
                "H2 type expected by the event compiler."
            ),
            (
                "The generic quotient-to-diffeomorphism equivalence is not "
                "a concrete closed-four-manifold invariant until its split "
                "topology inputs are instantiated."
            ),
            (
                "The boundary-certified calculus is currently parameterized "
                "by one fixed manifold input; no global family over all "
                "closed oriented smooth four-manifolds is assembled here."
            ),
            (
                "No identification with the original Crane--Yetter or Yetter "
                "state sum is claimed."
            ),
            "No premodular-category four-manifold theorem is claimed.",
        ],
        "target_theorem": {
            "lean_name": (
                "TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator."
                "boundaryCertifiedEvaluationOnKirbyClass_mk"
            ),
            "status": (
                "KERNEL_CHECKED_BOUNDARY_CERTIFIED_KIRBY_QUOTIENT_"
                "DESCENT_RELATIVE_TO_EXPLICIT_GRAPHICAL_AND_"
                "HANDLE_CHAIN_NATURALITY_AXIOMS"
            ),
            "conclusion": (
                "For one fixed manifold input, the compiled modular "
                "evaluation defines a well-defined scalar on the generated "
                "boundary-certified marked Kirby quotient."
            ),
            "caller_supplies_graphical_laws": False,
            "explicit_axiom_boundary": EXPECTED_BOUNDARY_EVALUATOR_AXIOMS,
        },
        "graphical_target_predicate": {
            "lean_predicate": (
                "TwistedYetter.Kirby."
                "ModularFourManifoldInvariantFinalTarget."
                "IsInvariantUnderElementaryMoves"
            ),
            "rule_independent_public_eval_constructor_status": (
                "AVAILABLE_IN_SUPERSEDING_ARTIFACT"
            ),
            "proof_status": "KERNEL_CHECKED",
        },
        "four_manifold_boundary": {
            "status": (
                "GENERIC_DERIVATION_KERNEL_CHECKED_CONCRETE_INSTANCES_OPEN"
            ),
            "lean_types": [
                (
                    "TwistedYetter.Kirby."
                    "ModularFourManifoldInvariantFinalTarget."
                    "MarkedFourManifoldRealization"
                ),
                (
                    "TwistedYetter.Kirby."
                    "ModularFourManifoldInvariantFinalTarget."
                    "ElementaryMoveGeometricSoundness"
                ),
                (
                    "TwistedYetter.Kirby."
                    "ModularFourManifoldInvariantFinalTarget."
                    "MarkedPresentationExistence"
                ),
                (
                    "TwistedYetter.Kirby."
                    "ModularFourManifoldInvariantFinalTarget."
                    "MarkedKirbyCerfCompleteness"
                ),
            ],
            "generic_equivalence_theorem": (
                "TwistedYetter.Kirby."
                "ModularFourManifoldInvariantFinalTarget."
                "kirbyClassEquivDiffeomorphismClass"
            ),
            "generic_descent_theorem": (
                "TwistedYetter.Kirby."
                "ModularFourManifoldInvariantFinalTarget."
                "fourManifoldInvariant_on_presentation"
            ),
            "three_handle_caveat": (
                "h3 is derived from a movie to the standard boundary. "
                "Uniqueness of the closed completion additionally uses "
                "boundary genus detection, cap extension, and gluing."
            ),
            "boundary_route": [
                (
                    "TwistedYetter.Kirby.BoundaryStandardization."
                    "BoundaryStandardizationCertificate"
                ),
                (
                    "TwistedYetter.Kirby.StandardCapClosure."
                    "closedCompletionChoiceDiffeomorphism"
                ),
                (
                    "TwistedYetter.Kirby.BoundaryDerivedHandleChain."
                    "CertifiedClosedPresentation.derivedSecondHomology"
                ),
                (
                    "TwistedYetter.Kirby."
                    "BoundaryDerivedHandleChainModel."
                    "CertifiedClosedPresentation.derivedHandleChainModel"
                ),
                (
                    "TwistedYetter.Kirby."
                    "BoundaryCertifiedKirbyPresentation."
                    "BoundaryCertifiedPresentation."
                    "toSpecialKirbyPresentation"
                ),
                (
                    "TwistedYetter.Kirby."
                    "BoundaryCertifiedModularEvaluator."
                    "boundaryCertifiedEvaluationOnKirbyClass"
                ),
            ],
            "concrete_instance_status": (
                "BLOCKED_NO_CONCRETE_BOUNDARY_CERTIFICATES_OR_"
                "GLOBAL_TOPOLOGY_INSTANCES"
            ),
        },
        "anti_hack_guards": {
            "status": "PASS_FORBIDDEN_SHORTCUTS_ABSENT",
            "forbidden_legacy_interfaces": [
                "ClosedFourManifoldKirbyCorrespondence",
                "kirbyCerfAndThreeHandleCompletion",
                "inductive KirbyEquivalent",
            ],
            "required_design_properties": [
                "KirbyMovie is proof-relevant Type data",
                "KirbyEquivalent erases only movie existence",
                "h3 is the certified standard-boundary genus",
                "d3 is derived from transported sphere intersections",
                "closed-completion independence is a proved theorem",
                "BoundaryCertifiedPresentation has no handleChain field",
                "the legacy adapter handleChain is definitionally derived",
                "the evaluator marking is the boundary-derived handle-chain H2",
                "BoundaryCertifiedMove has no homology transport field",
                (
                    "move transport is derived from the visible standard "
                    "handle-chain naturality axiom"
                ),
            ],
        },
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    result = build()
    print(
        json.dumps(
            {
                "artifact": str(OUTPUT.relative_to(ROOT)),
                "status": result["status"],
                "content_hash": result["content_hash"],
            },
            indent=2,
        )
    )
