#!/usr/bin/env python3
"""Build the fail-closed dotted-boundary H2 descent status artifact."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dotted-boundary-h2-descent-v1.json"
)

LEAN_FILES = [
    "lean/TwistedYetter/Kirby/CanonicalModularKirbyEvaluator.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyEvaluatorAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/ComponentBoundaryCharacter.lean",
    "lean/TwistedYetter/Kirby/ComponentBoundarySignedProduct.lean",
    "lean/TwistedYetter/Kirby/DottedBoundaryGeometry.lean",
    "lean/TwistedYetter/Kirby/DottedBoundaryGeometryAxiomAudit.lean",
    "lean/TwistedYetter/Kirby/DottedBoundaryFiniteSum.lean",
    "lean/TwistedYetter/Kirby/DottedBoundaryFiniteSumAxiomAudit.lean",
    "lean/TwistedYetter/Kirby/DottedBoundaryGeneratorInvariance.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "DottedBoundaryGeneratorInvarianceAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/CanonicalCycleLocalInvariance.lean",
    "lean/TwistedYetter/Kirby/LiteratureBackedCanonicalGraphicalInput.lean",
    "lean/TwistedYetter/Kirby/CanonicalModularKirbyInvariance.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyInvarianceAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedDottedBoundaryGeometry.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedDottedBoundaryGeometryAxiomAudit.lean"
    ),
    "lean/TwistedYetter.lean",
]

REFERENCE_FILES = [
    (
        "experiments/inputs/references/"
        "general-h2-kirby-route-source-audit-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "generalized-sliding-core-primary-sources-v2.json"
    ),
    (
        "experiments/inputs/references/"
        "four-manifold-invariant-target-primary-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "egno-category-foundations-primary-sources-v1.json"
    ),
]

SCRIPT_FILE = (
    "experiments/scripts/build_dotted_boundary_h2_descent_v1.py"
)

AUDIT_TARGETS = [
    "TwistedYetter.Kirby.CanonicalModularKirbyEvaluatorAxiomAudit",
    "TwistedYetter.Kirby.DottedBoundaryGeometryAxiomAudit",
    "TwistedYetter.Kirby.DottedBoundaryFiniteSumAxiomAudit",
    "TwistedYetter.Kirby.DottedBoundaryGeneratorInvarianceAxiomAudit",
    "TwistedYetter.Kirby.CanonicalCycleLocalInvarianceAxiomAudit",
    (
        "TwistedYetter.Kirby."
        "LiteratureBackedDottedBoundaryGeometryAxiomAudit"
    ),
    "TwistedYetter.Kirby.CanonicalModularKirbyInvarianceAxiomAudit",
]

EXPECTED_FINAL_PROJECT_AXIOMS = [
    (
        "TwistedYetter.Fusion.EGNO."
        "sMatrixNondegenerate_iff_trivialMuegerCenter"
    ),
    (
        "TwistedYetter.Fusion.EGNO.ModularCategory."
        "globalDimension_ne_zero"
    ),
    (
        "TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput."
        "standardLocalCycleCalculation"
    ),
    (
        "TwistedYetter.Kirby.ModularDottedEncircling."
        "baerenzBarrett_tham_openKirbyKilling"
    ),
    (
        "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
        "standardHandleChainNaturalityInput"
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

FORBIDDEN_RETIRED_INPUTS = [
    "tham_dualBoundaryGraphicalRealization",
    "baerenzBarrett_labelIndexedSlidingMovies",
    "standardDottedDiskGeometry",
]


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{sha256_bytes(encoded)}"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


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


def command_version(argv: list[str]) -> str:
    return run(argv).stdout.strip().splitlines()[0]


def git_text(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    ).stdout.strip()


def file_metadata(relative: str) -> dict[str, Any]:
    data = (ROOT / relative).read_bytes()
    return {"bytes": len(data), "sha256": sha256_bytes(data)}


def source_guards() -> dict[str, Any]:
    proof_hole = re.compile(
        r"(?m)^\s*(?:sorry|admit)\b|\bnative_decide\b"
    )
    proof_holes = []
    for relative in LEAN_FILES:
        match = proof_hole.search((ROOT / relative).read_text())
        if match is not None:
            proof_holes.append(relative)
    require(not proof_holes, f"proof holes found: {proof_holes}")

    evaluator = (ROOT / LEAN_FILES[0]).read_text()
    require(
        "abbrev CycleRepresentativeIndependence" in evaluator,
        "clean cycle representative independence proposition is missing",
    )
    require(
        "theorem EvalC_eq_cycleEvalC" in evaluator
        and "CycleRepresentativeIndependence\n" in evaluator,
        "EvalC bridge does not consume the clean proposition",
    )

    finite_sum = (ROOT / LEAN_FILES[6]).read_text()
    require(
        "theorem fixedRemaining_dottedSum_invariant" in finite_sum,
        "fixed-exterior finite dotted sum theorem is missing",
    )

    generator = (ROOT / LEAN_FILES[8]).read_text()
    for theorem in (
        "fixedRemaining_completeSummand_invariant",
        "cycleLinearDiagram_eval_add_integralGenerator",
        "cycleEvalC_add_integralGenerator",
        "GeometrySystem.respects_homology_class",
    ):
        require(theorem in generator, f"missing theorem: {theorem}")

    local = (ROOT / LEAN_FILES[10]).read_text()
    require(
        "CycleRepresentativeIndependenceSystem" in local,
        "local move proof does not use the clean descent interface",
    )
    require(
        "CycleBoundaryGraphicalRealizationSystem" not in local,
        "local move proof still uses the retired global graphical input",
    )

    final = (ROOT / LEAN_FILES[12]).read_text()
    require(
        "StandardDottedCanonicalPresentation" in final,
        "final theorem is not restricted to certified dotted presentations",
    )
    require(
        "representativeIndependenceOfStandardDottedPresentation" in final,
        "final theorem does not derive representative independence",
    )
    require(
        "LocalCycleCalculation.soundOfEndpoints" in final,
        "final theorem does not use endpoint-certified descent",
    )
    terminal_surface = final[final.index(
        "noncomputable def EvalCOnClosedFourManifolds"
    ):]
    require(
        "dottedBoundaryGeometry" not in terminal_surface,
        "final public theorem still accepts caller-supplied geometry",
    )
    require(
        "CycleBoundaryGraphicalRealizationSystem" not in final,
        "final theorem still accepts the retired graphical descent system",
    )

    return {
        "status": "PASS_FAIL_CLOSED_SOURCE_GUARDS",
        "proof_holes": proof_holes,
        "clean_descent_interface": True,
        "finite_dotted_sum_theorem": True,
        "integral_generator_invariance": True,
        "actual_h2_quotient_descent": True,
        "final_theorem_derives_representative_independence": True,
        "final_theorem_uses_certified_standard_dotted_domain": True,
        "caller_supplied_geometry_absent_from_terminal_surface": True,
        "overbroad_global_geometry_axiom_absent": True,
        "retired_global_graphical_descent_absent": True,
    }


def main() -> None:
    started_at = utc_now()
    started = time.monotonic()

    guards = source_guards()
    diff_check = run(["git", "diff", "--check"])
    audit = run(["lake", "-Kjobs=2", "build", *AUDIT_TARGETS])
    umbrella = run(["lake", "-Kjobs=2", "build", "TwistedYetter"])

    for axiom in EXPECTED_FINAL_PROJECT_AXIOMS:
        require(axiom in audit.stdout, f"expected axiom absent: {axiom}")
    for retired in FORBIDDEN_RETIRED_INPUTS:
        require(
            retired not in audit.stdout,
            f"retired input reappeared in audit: {retired}",
        )

    status_porcelain = git_text("status", "--porcelain")
    source_inputs = {
        relative: file_metadata(relative)
        for relative in [*LEAN_FILES, SCRIPT_FILE]
    }
    reference_inputs = {
        relative: file_metadata(relative)
        for relative in REFERENCE_FILES
    }

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.dotted-boundary-h2-descent.v1",
        "status": (
            "KERNEL_CHECKED_MODULAR_CLOSED_FOUR_MANIFOLD_INVARIANT_"
            "RELATIVE_TO_CERTIFIED_DOMAIN_AND_NAMED_LITERATURE_BOUNDARY"
        ),
        "mathematical_status": (
            "ESTABLISHED_MODULAR_CASE_RELATIVE_TO_EXPLICIT_NAMED_"
            "LITERATURE_FACTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": SCRIPT_FILE,
        "argv": [SCRIPT_FILE],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 " + SCRIPT_FILE
        ),
        "repo": {
            "root": str(ROOT),
            "git_commit": git_text("rev-parse", "HEAD"),
            "git_branch": git_text("branch", "--show-current"),
            "dirty": bool(status_porcelain),
            "status_porcelain_sha256": sha256_bytes(
                status_porcelain.encode()
            ),
        },
        "tool_versions": {
            "python": command_version(["python3", "--version"]),
            "lean": command_version(["lean", "--version"]),
            "lake": command_version(["lake", "--version"]),
        },
        "resource_limits": {
            "lean_threads": 1,
            "max_parallel_jobs": 2,
        },
        "inputs": {
            "source_files": source_inputs,
            "reference_records": reference_inputs,
        },
        "proved_chain": [
            {
                "stage": "one_dotted_generator_fixed_exterior",
                "theorem": (
                    "TwistedYetter.Kirby.DottedBoundaryGeometry."
                    "GeneratorGeometry.fixedRemaining_dottedSum_invariant"
                ),
                "status": "PROVED",
            },
            {
                "stage": "one_dotted_generator_complete_label_sum",
                "theorem": (
                    "TwistedYetter.Kirby.DottedBoundaryGeometry."
                    "GeneratorGeometry."
                    "cycleLinearDiagram_eval_add_integralGenerator"
                ),
                "status": "PROVED",
            },
            {
                "stage": "one_integral_generator_normalized_evaluation",
                "theorem": (
                    "TwistedYetter.Kirby.DottedBoundaryGeometry."
                    "GeneratorGeometry.cycleEvalC_add_integralGenerator"
                ),
                "status": "PROVED",
            },
            {
                "stage": "all_boundaries_actual_h2_descent",
                "theorem": (
                    "TwistedYetter.Kirby.DottedBoundaryGeometry."
                    "GeometrySystem.respects_homology_class"
                ),
                "status": "PROVED",
            },
            {
                "stage": "eight_local_kirby_moves",
                "theorem": (
                    "TwistedYetter.Kirby.CanonicalModularKirbyInvariance."
                    "evalC_local_move_invariant"
                ),
                "status": "PROVED_RELATIVE_TO_VISIBLE_INPUTS",
            },
            {
                "stage": "closed_four_manifold_oriented_diffeomorphism",
                "theorem": (
                    "TwistedYetter.Kirby.CanonicalModularKirbyInvariance."
                    "EvalCOnClosedFourManifolds_diffeomorphism_invariant"
                ),
                "status": "PROVED_RELATIVE_TO_VISIBLE_INPUTS",
            },
        ],
        "visible_input_boundary": {
            "dotted_geometry": (
                "The final handle-presentation theory ranges only over "
                "StandardDottedCanonicalPresentation. Each term carries one "
                "category-neutral GeometrySystem; no global axiom asserts "
                "geometry for malformed raw syntax."
            ),
            "smooth_topology": (
                "LiteratureBackedFourManifoldTopology.Assumptions supplies "
                "Kirby-Cerf realization and completeness."
            ),
            "local_move_geometry": (
                "standardLocalCycleCalculation supplies a restricted local "
                "Table 2 geometry term, never a scalar equality."
            ),
        },
        "axiom_audit": {
            "foundational_axioms": [
                "Classical.choice",
                "Quot.sound",
                "propext",
            ],
            "expected_final_project_axioms": (
                EXPECTED_FINAL_PROJECT_AXIOMS
            ),
            "retired_inputs_absent": FORBIDDEN_RETIRED_INPUTS,
            "audit_stdout": {
                "bytes": len(audit.stdout.encode()),
                "sha256": sha256_bytes(audit.stdout.encode()),
            },
        },
        "checks": {
            "source_guards": guards,
            "git_diff_check": {"returncode": diff_check.returncode},
            "targeted_axiom_audit": {
                "argv": ["lake", "-Kjobs=2", "build", *AUDIT_TARGETS],
                "returncode": audit.returncode,
            },
            "umbrella_build": {
                "argv": ["lake", "-Kjobs=2", "build", "TwistedYetter"],
                "returncode": umbrella.returncode,
                "stdout_bytes": len(umbrella.stdout.encode()),
                "stdout_sha256": sha256_bytes(umbrella.stdout.encode()),
            },
        },
        "remaining_topology_side_obligation": {
            "status": (
                "CLOSED_BY_CERTIFIED_STANDARD_DOTTED_PRESENTATION_DOMAIN"
            ),
            "description": (
                "No executable raw-diagram geometry parser is required for "
                "the theorem. Standard spanning-disk, dual-incidence, and "
                "trace-factorization certificates are part of the admitted "
                "presentation domain; their existence and Kirby-Cerf "
                "completeness remain visible in the topology assumptions."
            ),
        },
        "explicit_nonclaims": [
            (
                "This does not provide an executable parser that constructs "
                "dotted spanning-disk geometry from arbitrary raw pixels or "
                "planar coordinates."
            ),
            "This is not an axiom-free reconstruction of Kirby-Cerf theory.",
            (
                "The restricted local Table 2 endpoint realization remains "
                "a named literature axiom."
            ),
            "This does not establish the premodular case.",
            (
                "This does not identify the evaluator with Yetter's original "
                "state-sum definition."
            ),
        ],
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
