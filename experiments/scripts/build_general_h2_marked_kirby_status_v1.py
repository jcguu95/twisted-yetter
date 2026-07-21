#!/usr/bin/env python3
"""Build the fail-closed status of the arbitrary-H2 marked Kirby route."""

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
    "general-h2-marked-kirby-status-v1.json"
)
TEMP_AUDIT_MODULE = (
    "TwistedYetter.Kirby.GeneralH2MarkedKirbyStatusAuditTemp"
)
TEMP_AUDIT_PATH = (
    ROOT
    / "lean/TwistedYetter/Kirby/"
    "GeneralH2MarkedKirbyStatusAuditTemp.lean"
)
AUDIT_TARGETS = [
    (
        "TwistedYetter.Kirby."
        "GeneralH2MarkedKirbyInvarianceAxiomAudit"
    ),
    (
        "TwistedYetter.Kirby."
        "CanonicalRawLocalMoveTargetAxiomAudit"
    ),
    (
        "TwistedYetter.Kirby."
        "CancellationSafeH2TransportAxiomAudit"
    ),
    (
        "TwistedYetter.Kirby."
        "GeneralH2FourManifoldInvariantAxiomAudit"
    ),
]
LOCAL_THEOREM = (
    "TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance."
    "markedEvaluation_localInvariant"
)
QUOTIENT_THEOREM = (
    "TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance."
    "evaluationOnKirbyClass_mk"
)
RAW_CORE_THEOREM = (
    "TwistedYetter.Kirby.CanonicalRawLocalMoveTarget."
    "canonicalEngine.generates_exact_target"
)
CANCELLATION_LIFT_THEOREM = (
    "TwistedYetter.Kirby.CancellationSafeH2Transport."
    "StrictCycleRetraction.eval_lift_eq"
)
ONE_TWO_DEATH_RETRACTION = (
    "TwistedYetter.Kirby.CancellationSafeH2Transport."
    "StrictCycleRetraction.ofOneTwoDeath"
)
TWO_THREE_DEATH_RETRACTION = (
    "TwistedYetter.Kirby.CancellationSafeH2Transport."
    "StrictCycleRetraction.ofTwoThreeDeath"
)
CANONICAL_LOCAL_THEOREM = (
    "TwistedYetter.Kirby.GeneralH2FourManifoldInvariant."
    "canonicalMarkedEvaluation_localInvariant"
)
FINAL_INVARIANCE_THEOREM = (
    "TwistedYetter.Kirby.GeneralH2FourManifoldInvariant."
    "EvalC_diffeomorphism_invariant"
)
FINAL_PRESENTATION_THEOREM = (
    "TwistedYetter.Kirby.GeneralH2FourManifoldInvariant."
    "EvalC_on_presentation"
)
SOURCE_FILES = [
    "experiments/scripts/build_general_h2_marked_kirby_status_v1.py",
    "tests/test_general_h2_marked_kirby_status_v1.py",
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "GeneralH2MarkedKirbyInvariance.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "GeneralH2MarkedKirbyInvarianceAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Representative.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Transport.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2TransportAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleMoveGeometry.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleMoveGeometryAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleLocalInvariance.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "ModularFourManifoldInvariantFinalTarget.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "HomologicalFourManifoldInvariantFinalTarget.lean"
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
        "GeneralH2FourManifoldInvariant.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "GeneralH2FourManifoldInvariantAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturality.lean"
    ),
]

EXPECTED_LOCAL_PROJECT_AXIOMS = {
    (
        "TwistedYetter.Fusion.EGNO."
        "sMatrixNondegenerate_iff_trivialMuegerCenter"
    ),
    (
        "TwistedYetter.Fusion.EGNO."
        "ModularCategory.globalDimension_ne_zero"
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
}

HANDLE_CHAIN_NATURALITY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
    "standardHandleChainNaturalityInput"
)
EXPECTED_CANONICAL_PROJECT_AXIOMS = (
    EXPECTED_LOCAL_PROJECT_AXIOMS | {HANDLE_CHAIN_NATURALITY_AXIOM}
)


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


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def git_text(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    ).stdout.strip()


def tool_version(argv: list[str]) -> str:
    output = run(argv).stdout.strip().splitlines()
    return output[0] if output else ""


def extract_axiom_audit(output: str) -> dict[str, dict[str, Any]]:
    pattern = re.compile(
        r"'([^']+)' depends on axioms:\s*\[(.*?)\]",
        flags=re.DOTALL,
    )
    audit: dict[str, dict[str, Any]] = {}
    for declaration, block in pattern.findall(output):
        axioms = sorted(
            set(
                re.findall(
                    r"(?:TwistedYetter\.[A-Za-z0-9_.]+"
                    r"|Classical\.choice|Quot\.sound|propext)",
                    block,
                )
            )
        )
        audit[declaration] = {
            "project_axioms": [
                axiom
                for axiom in axioms
                if axiom.startswith("TwistedYetter.")
            ],
            "foundational_axioms": [
                axiom
                for axiom in axioms
                if not axiom.startswith("TwistedYetter.")
            ],
        }
    return audit


def run_axiom_audit() -> tuple[list[str], str]:
    declarations = [
        LOCAL_THEOREM,
        QUOTIENT_THEOREM,
        RAW_CORE_THEOREM,
        CANCELLATION_LIFT_THEOREM,
        ONE_TWO_DEATH_RETRACTION,
        TWO_THREE_DEATH_RETRACTION,
        CANONICAL_LOCAL_THEOREM,
        FINAL_INVARIANCE_THEOREM,
        FINAL_PRESENTATION_THEOREM,
    ]
    source = [
        "import TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance",
        "import TwistedYetter.Kirby.CanonicalRawLocalMoveTarget",
        "import TwistedYetter.Kirby.CancellationSafeH2Transport",
        "import TwistedYetter.Kirby.GeneralH2FourManifoldInvariant",
        f"-- Regeneration nonce: {utc_now()}",
    ]
    source.extend(
        f"#print axioms {declaration}"
        for declaration in declarations
    )
    require(
        not TEMP_AUDIT_PATH.exists(),
        f"stale temporary audit source exists: {TEMP_AUDIT_PATH}",
    )
    TEMP_AUDIT_PATH.write_text("\n".join(source) + "\n")
    try:
        argv = [
            "lake",
            "-Kjobs=2",
            "build",
            TEMP_AUDIT_MODULE,
        ]
        output = run(argv).stdout
    finally:
        TEMP_AUDIT_PATH.unlink(missing_ok=True)
    return argv, output


def source_guards() -> dict[str, Any]:
    proof_hole = re.compile(
        r"(?m)^\s*(?:sorry|admit)\b|\bnative_decide\b"
    )
    checked: list[str] = []
    for relative in SOURCE_FILES:
        if not relative.endswith(".lean"):
            continue
        text = (ROOT / relative).read_text()
        require(
            proof_hole.search(text) is None,
            f"proof hole found in {relative}",
        )
        checked.append(relative)

    route_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "GeneralH2MarkedKirbyInvariance.lean"
    )
    route = route_path.read_text()
    require(
        "import TwistedYetter.Kirby.IntegralH2CycleBasis" not in route,
        "general H2 route depends on the finite-free basis route",
    )
    require(
        "[AddCommGroup H2]" in route,
        "general H2 route lost its additive-group boundary",
    )
    theorem_surface = route.split(
        "theorem markedEvaluation_localInvariant", 1
    )[1].split("/-- Evaluation on the quotient", 1)[0]
    for forbidden in (
        "CycleBasis",
        "Finite",
        "Free",
        "TorsionFree",
        "SimplyConnected",
        "rank : Nat",
    ):
        require(
            forbidden not in theorem_surface,
            f"general local theorem acquired restriction: {forbidden}",
        )

    move_surface = route.split("structure MarkedMove", 1)[1].split(
        "/--\nThe marked-presentation calculus", 1
    )[0]
    for forbidden in (
        "evaluation_eq",
        "value_eq",
        "scalar_eq",
        "cycleEvalC 𝒞 automorphism =",
    ):
        require(
            forbidden not in move_surface,
            f"marked move hides evaluator equality: {forbidden}",
        )

    root = (ROOT / "lean/TwistedYetter.lean").read_text()
    require(
        "GeneralH2MarkedKirbyInvariance" in root,
        "general H2 route is not imported by the library root",
    )
    raw_target = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalRawLocalMoveTarget.lean"
    ).read_text()
    require(
        "CORE_REWRITE_ENGINE_KERNEL_CHECKED" in raw_target,
        "raw core rewrite engine is not marked kernel checked",
    )
    require(
        "LOCAL_GRAPHICAL_COMPILER_NOT_IMPLEMENTED" in raw_target,
        "remaining graphical compiler blocker is hidden",
    )
    transport_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Transport.lean"
    )
    transport = transport_path.read_text()
    retraction_surface = transport.split(
        "structure StrictCycleRetraction", 1
    )[1].split("namespace StrictCycleRetraction", 1)[0]
    for forbidden in (
        "eval",
        "value",
        "scalar",
        "cycleEvalC",
        " = K",
    ):
        require(
            forbidden not in retraction_surface,
            "strict cycle retraction hides evaluator data: "
            f"{forbidden}",
        )
    move_geometry = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalCycleMoveGeometry.lean"
    ).read_text()
    local_calculation = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalCycleLocalInvariance.lean"
    ).read_text()
    for death_structure in (
        "structure OneTwoDeathCycleGeometry",
        "structure TwoThreeDeathCycleGeometry",
    ):
        require(
            death_structure in move_geometry,
            f"death geometry is missing: {death_structure}",
        )
    require(
        move_geometry.count("forward_reverse_cycle :") >= 2,
        "death geometries do not both require strict cycle retraction",
    )
    for required_type in (
        "OneTwoDeathCycleGeometry source target transport",
        "TwoThreeDeathCycleGeometry source target transport",
    ):
        require(
            required_type in local_calculation,
            f"local calculation does not require {required_type}",
        )
    for constructor in (
        "noncomputable def ofOneTwoDeath",
        "noncomputable def ofTwoThreeDeath",
    ):
        require(
            constructor in transport,
            f"canonical death retraction constructor missing: {constructor}",
        )

    final_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "GeneralH2FourManifoldInvariant.lean"
    )
    final_route = final_path.read_text()
    require(
        "GeneralH2FourManifoldInvariant" in root,
        "general H2 four-manifold assembly is not imported by the root",
    )
    final_theorem_surface = final_route.split(
        "theorem EvalC_diffeomorphism_invariant", 1
    )[1].split("/-- Pulling `EvalC`", 1)[0]
    for forbidden in (
        "SimplyConnected",
        "TorsionFree",
        "CycleBasis",
        "FiniteFree",
        "rank : Nat",
    ):
        require(
            forbidden not in final_theorem_surface,
            f"final theorem acquired restriction: {forbidden}",
        )
    canonical_move_surface = final_route.split(
        "structure CanonicalMarkedMove", 1
    )[1].split("/--\nThe canonical arbitrary-H2", 1)[0]
    for forbidden in (
        "evaluation_eq",
        "value_eq",
        "scalar_eq",
        "EvalC =",
    ):
        require(
            forbidden not in canonical_move_surface,
            f"canonical marked move hides evaluator equality: {forbidden}",
        )

    chain_boundary = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturality.lean"
    ).read_text()
    require(
        "axiom standardHandleChainNaturalityInput" in chain_boundary,
        "handle-chain literature boundary is not explicit",
    )
    require(
        "theorem local_transport_is_identity" in chain_boundary,
        "chain-derived H2 identity theorem is missing",
    )
    return {
        "status": "PASS_FAIL_CLOSED_SOURCE_GUARDS",
        "checked_lean_files": checked,
        "proof_holes": [],
        "requires_only_add_comm_group_on_h2": True,
        "depends_on_finite_free_basis_route": False,
        "marked_move_has_no_evaluator_equality": True,
        "library_root_imports_general_h2_route": True,
        "library_root_imports_four_manifold_assembly": True,
        "raw_core_rewrite_engine_kernel_checked": True,
        "local_graphical_compiler_still_blocked": True,
        "strict_cycle_retraction_has_no_evaluator_data": True,
        "death_geometry_requires_strict_cycle_retraction": True,
        "death_calculations_generate_strict_retractions": True,
        "four_manifold_assembly_theorem_present": True,
        "source_bound_chain_naturality_boundary_wired": True,
    }


def main() -> None:
    started = time.monotonic()
    started_at = utc_now()
    guards = source_guards()

    build_argv, audit_stdout = run_axiom_audit()
    audit = extract_axiom_audit(audit_stdout)
    for declaration in (
        LOCAL_THEOREM,
        QUOTIENT_THEOREM,
        CANCELLATION_LIFT_THEOREM,
        ONE_TWO_DEATH_RETRACTION,
        TWO_THREE_DEATH_RETRACTION,
        CANONICAL_LOCAL_THEOREM,
        FINAL_INVARIANCE_THEOREM,
        FINAL_PRESENTATION_THEOREM,
    ):
        require(
            declaration in audit,
            f"declaration absent from axiom audit: {declaration}",
        )
    require(
        RAW_CORE_THEOREM in audit,
        f"declaration absent from axiom audit: {RAW_CORE_THEOREM}",
    )

    observed = set(audit[LOCAL_THEOREM]["project_axioms"])
    require(
        observed == EXPECTED_LOCAL_PROJECT_AXIOMS,
        "general-H2 local theorem axiom boundary changed",
    )
    require(
        set(audit[QUOTIENT_THEOREM]["project_axioms"])
        == EXPECTED_LOCAL_PROJECT_AXIOMS,
        "quotient theorem axiom boundary changed",
    )
    require(
        audit[RAW_CORE_THEOREM]["project_axioms"] == [],
        "raw core engine acquired a project axiom",
    )
    require(
        set(audit[CANCELLATION_LIFT_THEOREM]["project_axioms"])
        == EXPECTED_LOCAL_PROJECT_AXIOMS,
        "strict cancellation lift theorem axiom boundary changed",
    )
    for declaration in (
        CANONICAL_LOCAL_THEOREM,
        FINAL_INVARIANCE_THEOREM,
        FINAL_PRESENTATION_THEOREM,
    ):
        require(
            set(audit[declaration]["project_axioms"])
            == EXPECTED_CANONICAL_PROJECT_AXIOMS,
            f"canonical final theorem axiom boundary changed: {declaration}",
        )

    diff_check = subprocess.run(
        ["git", "diff", "--check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    require(
        diff_check.returncode == 0,
        f"git diff --check failed:\n{diff_check.stdout}",
    )
    status_porcelain = git_text("status", "--porcelain=v1")

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.general-h2-marked-kirby-status.v1",
        "status": (
            "KERNEL_CHECKED_ARBITRARY_INTEGRAL_H2_MARKED_KIRBY_QUOTIENT_"
            "AND_FOUR_MANIFOLD_ASSEMBLY;"
            "GRAPHICAL_AND_MARKED_TOPOLOGY_INPUTS_BLOCKED"
        ),
        "mathematical_status": (
            "FOUR_MANIFOLD_INVARIANCE_DERIVED_FROM_EXPLICIT_GRAPHICAL_"
            "AND_MARKED_TOPOLOGY_INPUTS_FOR_ARBITRARY_ADDITIVE_"
            "COMMUTATIVE_H2;INPUTS_NOT_YET_CONSTRUCTED"
        ),
        "lifecycle": {
            "status": "SUPERSEDED",
            "superseded_by": (
                "experiments/results/lean-kirby/"
                "general-h2-kirby-route-resolution-v1.json"
            ),
            "reason": (
                "The raw arbitrary-H2 descent premise was refuted by a "
                "kernel-checked cancelling 2-3 pair counterexample."
            ),
        },
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": (
            "experiments/scripts/"
            "build_general_h2_marked_kirby_status_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_general_h2_marked_kirby_status_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 experiments/scripts/"
            "build_general_h2_marked_kirby_status_v1.py"
        ),
        "scope": {
            "coefficient_ring": "Z",
            "handle_chain_h2": (
                "arbitrary additive commutative group presented as the "
                "second homology of the handle chain complex"
            ),
            "torsion_policy": "SUPPORTED_BY_THEOREM_SURFACE",
            "simply_connected_required": False,
            "finite_free_required": False,
            "category": (
                "modular category over an algebraically closed "
                "characteristic-zero field, with a tensor "
                "automorphism of the identity"
            ),
            "marking": "alpha is an actual integral H2 class",
        },
        "established": {
            "representative_level": {
                "statement": (
                    "Every internal state carries an explicit degree-two "
                    "cycle and a kernel-checked proof that it represents "
                    "the requested H2 class."
                ),
                "lean_structure": (
                    "TwistedYetter.Kirby."
                    "CancellationSafeH2Representative."
                    "GeometricRepresentative"
                ),
            },
            "local_move_invariance": {
                "statement": (
                    "Every certified move with literal cycle transport "
                    "and cancellation safety preserves the modular value."
                ),
                "lean_theorem": LOCAL_THEOREM,
            },
            "generated_quotient": {
                "statement": (
                    "The value descends to the quotient generated by "
                    "certified cancellation-safe moves for the fixed "
                    "public class alpha."
                ),
                "lean_theorem": QUOTIENT_THEOREM,
            },
            "torsion_scope": {
                "statement": (
                    "The theorem has no basis, rank, freeness, "
                    "torsion-free, or simply-connected hypothesis."
                ),
                "source_guard": (
                    "requires_only_add_comm_group_on_h2"
                ),
            },
            "raw_move_core_generation": {
                "statement": (
                    "For all eight source-bound move constructors, literal "
                    "window replacement reconstructs exactly the target "
                    "components and slice events."
                ),
                "lean_theorem": RAW_CORE_THEOREM,
                "project_axioms": [],
            },
            "cancellation_retraction_descent": {
                "statement": (
                    "Each death calculation must structurally carry a "
                    "topology-only strict cycle retraction. Lean extracts "
                    "that retraction, constructs a representative of the "
                    "inverse-transported arbitrary H2 class, proves "
                    "cancellation safety, and derives equal evaluation."
                ),
                "lean_theorem": CANCELLATION_LIFT_THEOREM,
                "one_two_constructor": ONE_TWO_DEATH_RETRACTION,
                "two_three_constructor": TWO_THREE_DEATH_RETRACTION,
                "required_by_local_calculation_type": True,
                "retraction_contains_evaluator_data": False,
            },
            "source_bound_chain_naturality": {
                "status": "CITED_DOMAIN_AXIOM_AND_KERNEL_WIRED",
                "axiom": HANDLE_CHAIN_NATURALITY_AXIOM,
                "derived_theorem": (
                    "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
                    "local_transport_is_identity"
                ),
                "statement": (
                    "The standard handle-chain equivalence and H2 naturality "
                    "square are imported at one explicit literature boundary; "
                    "Lean derives identity in common geometric coordinates."
                ),
            },
            "four_manifold_assembly": {
                "status": "KERNEL_CHECKED_THEOREM_WITH_EXPLICIT_INPUTS",
                "invariance_theorem": FINAL_INVARIANCE_THEOREM,
                "presentation_formula_theorem": FINAL_PRESENTATION_THEOREM,
                "statement": (
                    "Given an actual eight-move graphical compiler and a "
                    "category-free marked Kirby-Cerf topology input, EvalC "
                    "is an oriented-diffeomorphism invariant and agrees with "
                    "every displayed presentation formula."
                ),
            },
        },
        "remaining_blockers": [
            {
                "id": "LOCAL_GRAPHICAL_MOVE_COMPILER_NOT_IMPLEMENTED",
                "kind": "FINITE_FORMALIZATION_WORK_WITH_STANDARD_CATEGORY_INPUT",
                "reason": (
                    "The mathematical core rewrite and exact target theorem "
                    "are complete, but the generated core is not yet "
                    "compiled to an actual LocalCycleCalculation for all "
                    "eight constructors."
                ),
            },
            {
                "id": "GLOBAL_MARKED_KIRBY_CERF_LIFT_NOT_PROVED",
                "kind": "NEW_TOPOLOGY_THEOREM_REQUIRED",
                "reason": (
                    "Death calculations now structurally include strict "
                    "cycle retractions. What remains is the global topology "
                    "theorem that ordinary Kirby-Cerf movies admit a "
                    "coherent marked lift for the fixed arbitrary H2 class, "
                    "together with an inhabitant of the explicit topology "
                    "input. The final assembly theorem is already proved "
                    "once this category-free input exists."
                ),
            },
        ],
        "finite_free_route": {
            "status": "OPTIONAL_SPECIALIZED_COMPUTATION_ROUTE",
            "artifact": (
                "experiments/results/lean-kirby/"
                "integral-h2-cycle-basis-status-v1.json"
            ),
            "not_a_final_theorem_requirement": True,
        },
        "explicit_nonclaims": [
            (
                "No inhabitant of the final graphical Completion or marked "
                "Kirby-Cerf TopologyInput has yet been constructed."
            ),
            (
                "This does not say that arbitrary homologous raw cycles "
                "have equal evaluations."
            ),
            (
                "The kernel-checked four-manifold theorem is an assembly "
                "theorem with explicit inputs, not yet an instantiated "
                "invariant for every pair (X, alpha)."
            ),
            (
                "Support for torsion in the theorem surface is not a proof "
                "that the remaining global topology theorem holds."
            ),
        ],
        "axiom_audit": {
            "targets": AUDIT_TARGETS,
            "declarations": audit,
            "expected_local_project_axioms": sorted(
                EXPECTED_LOCAL_PROJECT_AXIOMS
            ),
            "expected_canonical_project_axioms": sorted(
                EXPECTED_CANONICAL_PROJECT_AXIOMS
            ),
            "hidden_representative_descent_axiom": False,
            "finite_free_axiom": False,
            "topology_input_is_explicit_parameter": True,
        },
        "checks": {
            "lean_build": "PASS",
            "lean_threads": 1,
            "max_parallel_jobs": 2,
            "source_guards": guards,
            "git_diff_check": {"returncode": diff_check.returncode},
            "audit_stdout": {
                "bytes": len(audit_stdout.encode()),
                "sha256": sha256_bytes(audit_stdout.encode()),
            },
        },
        "repo": {
            "root": str(ROOT),
            "git_branch": git_text("branch", "--show-current"),
            "git_commit": git_text("rev-parse", "HEAD"),
            "dirty": bool(status_porcelain),
            "status_porcelain_sha256": sha256_bytes(
                status_porcelain.encode()
            ),
        },
        "tool_versions": {
            "python": platform.python_version(),
            "lean": tool_version(["lean", "--version"]),
            "lake": tool_version(["lake", "--version"]),
        },
        "inputs": {
            relative: file_metadata(relative)
            for relative in SOURCE_FILES
        },
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n"
    )
    print(OUTPUT)
    print(payload["content_hash"])
    print(payload["status"])


if __name__ == "__main__":
    main()
