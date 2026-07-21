#!/usr/bin/env python3
"""Build the fail-closed status of the integral H2 cycle-basis route."""

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
    "integral-h2-cycle-basis-status-v1.json"
)
AUDIT_TARGETS = [
    "TwistedYetter.Kirby.IntegralH2CycleBasisAxiomAudit",
    (
        "TwistedYetter.Kirby."
        "IntegralH2CycleBasisKirbyInvarianceAxiomAudit"
    ),
    (
        "TwistedYetter.Kirby."
        "NaturalCycleSelectorCounterexampleAxiomAudit"
    ),
]
SOURCE_FILES = [
    (
        "experiments/scripts/"
        "build_integral_h2_cycle_basis_status_v1.py"
    ),
    "tests/test_integral_h2_cycle_basis_status_v1.py",
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralH2CycleBasis.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralH2CycleBasisAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralH2CycleBasisKirbyInvariance.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "IntegralH2CycleBasisKirbyInvarianceAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Representative.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CycleRepresentativeCounterexample.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "NaturalCycleSelectorCounterexample.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "NaturalCycleSelectorCounterexampleAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "HandleHomologyBoundaryReduction.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturality.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalRawLocalMoveTarget.lean"
    ),
    (
        "experiments/results/lean-kirby/"
        "cycle-representative-descent-counterexample-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "homologically-twisted-kirby-invariant-sources-v1.json"
    ),
]

BASIS_DECLARATIONS = [
    (
        "TwistedYetter.Kirby.IntegralH2.CycleBasis."
        "liftedBasisCycle_class"
    ),
    (
        "TwistedYetter.Kirby.IntegralH2.CycleBasis."
        "ofFreeCoordinates"
    ),
    (
        "TwistedYetter.Kirby.IntegralH2.CycleBasis."
        "cycleLinearMap_homology_coordinates_eq"
    ),
    (
        "TwistedYetter.Kirby.IntegralH2.CycleBasis."
        "markedCycle_class"
    ),
    (
        "TwistedYetter.Kirby.IntegralH2.CycleBasis."
        "rebase_markedCycle"
    ),
    (
        "TwistedYetter.Kirby.IntegralH2.CycleBasis."
        "rebaseStrictComparison"
    ),
]

LOCAL_MOVE_THEOREM = (
    "TwistedYetter.Kirby."
    "IntegralH2CycleBasisKirbyInvariance."
    "IntegralCycleBasisMoveCompatibility.presentationValue_eq"
)
LOCAL_INVARIANCE_THEOREM = (
    "TwistedYetter.Kirby."
    "IntegralH2CycleBasisKirbyInvariance."
    "integralCycleBasisEvaluation_localInvariant"
)
QUOTIENT_EVALUATOR = (
    "TwistedYetter.Kirby."
    "IntegralH2CycleBasisKirbyInvariance."
    "integralCycleBasisEvaluationOnKirbyClass"
)
REBASE_VALUE_THEOREM = (
    "TwistedYetter.Kirby."
    "IntegralH2CycleBasisKirbyInvariance."
    "integralCycleBasisPresentationValue_rebase"
)
NO_STRICT_SELECTOR_THEOREM = (
    "TwistedYetter.Kirby."
    "NaturalCycleSelectorCounterexample."
    "no_strictNaturalSelector"
)

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

    basis_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/IntegralH2CycleBasis.lean"
    )
    basis_text = basis_path.read_text()
    basis_structure = basis_text.split(
        "structure CycleBasis", 1
    )[1].split("namespace CycleBasis", 1)[0]
    for field in (
        "rank",
        "coordinates",
        "basisCycle",
        "basis_homology_coordinates",
    ):
        require(
            field in basis_structure,
            f"integral cycle basis lost required field: {field}",
        )
    require(
        "basisHandle" not in basis_structure,
        "general cycle basis silently reverted to selected handles",
    )
    for theorem in (
        "theorem markedCycle_class",
        "theorem rebase_markedCycle",
        "def rebaseStrictComparison",
    ):
        require(
            theorem in basis_text,
            f"missing integral basis theorem: {theorem}",
        )

    invariance_path = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "IntegralH2CycleBasisKirbyInvariance.lean"
    )
    invariance_text = invariance_path.read_text()
    compatibility = invariance_text.split(
        "structure IntegralCycleBasisMoveCompatibility", 1
    )[1].split(
        "namespace IntegralCycleBasisMoveCompatibility", 1
    )[0]
    for field in ("marked_cycle_transport", "cancellation_safe"):
        require(
            field in compatibility,
            f"move compatibility lost required field: {field}",
        )
    for forbidden in (
        "evaluation_eq",
        "value_eq",
        "scalar_eq",
        "rawCycleColourEval =",
    ):
        require(
            forbidden not in compatibility,
            f"move compatibility hides evaluator equality: {forbidden}",
        )
    for theorem in (
        "theorem integralCycleBasisPresentationValue_rebase",
        "theorem integralCycleBasisEvaluation_localInvariant",
        "def integralCycleBasisEvaluationOnKirbyClass",
    ):
        require(
            theorem in invariance_text,
            f"missing integral invariance declaration: {theorem}",
        )

    all_lean = "\n".join(
        path.read_text()
        for path in (ROOT / "lean/TwistedYetter").rglob("*.lean")
    )
    refuted_axiom_declaration = re.search(
        r"(?m)^\s*axiom\s+standardCycleBoundaryGraphicalRealization\b",
        all_lean,
    )
    require(
        refuted_axiom_declaration is None,
        "refuted arbitrary representative axiom returned",
    )
    require(
        "IntegralH2CycleBasisKirbyInvariance" in (
            ROOT / "lean/TwistedYetter.lean"
        ).read_text(),
        "integral route is not imported by the library root",
    )
    require(
        "NaturalCycleSelectorCounterexample" in (
            ROOT / "lean/TwistedYetter.lean"
        ).read_text(),
        "strict-selector obstruction is not imported by the library root",
    )
    chain_compiler_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "SourceBackedHandleChainNaturality.lean"
    ).read_text()
    require(
        re.search(
            r"(?m)^\s*axiom\s+standardHandleChainNaturalityInput\b",
            chain_compiler_text,
        )
        is not None,
        "chain compiler blocker changed; update the status artifact",
    )
    raw_compiler_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CanonicalRawLocalMoveTarget.lean"
    ).read_text()
    require(
        '"CORE_REWRITE_ENGINE_KERNEL_CHECKED;' in raw_compiler_text
        and 'LOCAL_GRAPHICAL_COMPILER_NOT_IMPLEMENTED"'
        in raw_compiler_text,
        "raw graphical compiler blocker changed; update the status artifact",
    )

    return {
        "status": "PASS_FAIL_CLOSED_SOURCE_GUARDS",
        "checked_lean_files": checked,
        "proof_holes": [],
        "cycle_basis_is_not_handle_supported_by_definition": True,
        "move_compatibility_has_no_evaluator_equality": True,
        "refuted_arbitrary_representative_axiom_absent": True,
        "library_root_imports_integral_route": True,
        "library_root_imports_strict_selector_obstruction": True,
        "chain_move_compiler_still_axiomatic": True,
        "raw_core_rewrite_engine_kernel_checked": True,
        "local_graphical_move_compiler_still_unimplemented": True,
    }


def main() -> None:
    started = time.monotonic()
    started_at = utc_now()

    guards = source_guards()
    build_argv = ["lake", "-Kjobs=2", "build", *AUDIT_TARGETS]
    build = run(build_argv)
    audit = extract_axiom_audit(build.stdout)

    for declaration in BASIS_DECLARATIONS:
        require(
            declaration in audit,
            f"basis declaration absent from axiom audit: {declaration}",
        )
        require(
            audit[declaration]["project_axioms"] == [],
            f"basis theorem acquired project axiom: {declaration}",
        )

    for declaration in (
        REBASE_VALUE_THEOREM,
        LOCAL_MOVE_THEOREM,
        LOCAL_INVARIANCE_THEOREM,
        QUOTIENT_EVALUATOR,
        NO_STRICT_SELECTOR_THEOREM,
    ):
        require(
            declaration in audit,
            f"invariance declaration absent from audit: {declaration}",
        )

    observed_local = set(
        audit[LOCAL_MOVE_THEOREM]["project_axioms"]
    )
    require(
        observed_local == EXPECTED_LOCAL_PROJECT_AXIOMS,
        "local move axiom boundary changed",
    )
    require(
        not any(
            "CycleBoundaryGraphicalRealization" in axiom
            for axiom in observed_local
        ),
        "hidden representative-descent axiom entered local theorem",
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
        "schema": "twisted-yetter.integral-h2-cycle-basis-status.v1",
        "status": (
            "KERNEL_CHECKED_FINITE_FREE_INTEGRAL_H2_CYCLE_BASIS_"
            "AND_CERTIFIED_KIRBY_QUOTIENT;"
            "GLOBAL_ENRICHED_KIRBY_CERF_BLOCKED"
        ),
        "mathematical_status": (
            "ESTABLISHED_FOR_FINITE_FREE_HANDLE_CHAIN_H2_ON_THE_"
            "CERTIFIED_INTEGRAL_CYCLE_BASIS_KIRBY_QUOTIENT;"
            "NOT_YET_A_GLOBAL_FOUR_MANIFOLD_INVARIANT"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": (
            "experiments/scripts/"
            "build_integral_h2_cycle_basis_status_v1.py"
        ),
        "argv": [
            (
                "experiments/scripts/"
                "build_integral_h2_cycle_basis_status_v1.py"
            )
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 experiments/scripts/"
            "build_integral_h2_cycle_basis_status_v1.py"
        ),
        "scope": {
            "coefficient_ring": "Z",
            "handle_chain_h2": (
                "finite free, exhibited by an additive equivalence "
                "H2 ~= (Fin rank -> Z)"
            ),
            "category": (
                "modular category over an algebraically closed "
                "characteristic-zero field, with a tensor "
                "automorphism of the identity"
            ),
            "marking": (
                "alpha is an element of the actual Mathlib "
                "handle-chain second homology"
            ),
            "not_in_scope": [
                "torsion in integral H2",
                "premodular categories",
                "arbitrary homologous raw cycle representatives",
                "an unconditional all-presentations four-manifold theorem",
            ],
            "final_theorem_route": (
                "The general-H2 marked route supports arbitrary additive "
                "commutative H2 at the theorem surface; this finite-free "
                "basis route is an optional specialized computation route."
            ),
        },
        "established": {
            "cycle_basis_construction": {
                "statement": (
                    "Every displayed finite-free integral H2 basis "
                    "has actual degree-two cycle lifts."
                ),
                "lean_declarations": BASIS_DECLARATIONS[:2],
            },
            "class_correctness": {
                "statement": (
                    "The integral linear combination selected by "
                    "alpha maps back to exactly alpha in H2."
                ),
                "lean_declarations": [
                    BASIS_DECLARATIONS[2],
                    BASIS_DECLARATIONS[3],
                ],
            },
            "unimodular_rebasing": {
                "statement": (
                    "Every GL_r(Z) coordinate change transforms the "
                    "basis cycles contragrediently, so the actual "
                    "marked cycle and its evaluator value are "
                    "literally unchanged."
                ),
                "lean_declarations": [
                    BASIS_DECLARATIONS[4],
                    BASIS_DECLARATIONS[5],
                    REBASE_VALUE_THEOREM,
                ],
            },
            "local_kirby_invariance": {
                "statement": (
                    "A local calculation preserves the value when "
                    "topology proves literal marked-cycle transport "
                    "and cancellation safety."
                ),
                "lean_declarations": [
                    LOCAL_MOVE_THEOREM,
                    LOCAL_INVARIANCE_THEOREM,
                ],
            },
            "generated_quotient": {
                "statement": (
                    "The value descends to the quotient generated by "
                    "those certified integral-cycle-basis moves."
                ),
                "lean_declaration": QUOTIENT_EVALUATOR,
            },
        },
        "critical_distinctions": {
            "safe_rebasing": (
                "Coordinates and basis cycles change together; the "
                "actual degree-two marked cycle does not change."
            ),
            "unsafe_lift_change": (
                "Replacing a cycle lift by another lift differing by "
                "a degree-three boundary can change the raw twisted "
                "link evaluation."
            ),
            "counterexample_artifact": (
                "experiments/results/lean-kirby/"
                "cycle-representative-descent-counterexample-v1.json"
            ),
            "fail_closed_rule": (
                "No theorem may replace literal cycle transport or "
                "cancellation safety by equality of H2 classes alone."
            ),
            "strict_natural_selector_obstruction": {
                "statement": (
                    "Even for H2 = Z, no cycle selector can both "
                    "represent every class and be strictly fixed by "
                    "every boundary shear of the displayed test."
                ),
                "lean_theorem": NO_STRICT_SELECTOR_THEOREM,
                "scope_caveat": (
                    "This is an algebraic strategy obstruction. It "
                    "does not assert that the test shear is already "
                    "realized by a concrete Kirby-movie loop."
                ),
                "consequence": (
                    "The global proof must use a stable normal form "
                    "or distinguished admissible orbit, not a "
                    "strictly natural section of cycles over H2."
                ),
            },
        },
        "remaining_blockers": [
            {
                "id": "TORSION_H2_NOT_SUPPORTED",
                "reason": (
                    "A coordinate equivalence to Z^r excludes torsion. "
                    "Choosing integer lifts of torsion coordinates "
                    "would reintroduce the refuted representative-"
                    "descent problem."
                ),
                "terminal_condition": (
                    "Either restrict the paper theorem to finite-free "
                    "H2, or provide a new torsion-safe formula and "
                    "prove its representative independence."
                ),
            },
            {
                "id": "SOURCE_BOUND_CHAIN_MOVE_COMPILER_NOT_IMPLEMENTED",
                "reason": (
                    "The boundary-derived d2/d3 model exists, but no "
                    "implementation currently compiles every exact "
                    "source-bound Kirby recipe to its chain "
                    "equivalence and coordinate-naturality square. "
                    "The older route still uses the explicit "
                    "standardHandleChainNaturalityInput axiom."
                ),
                "terminal_condition": (
                    "Implement the recipe-to-chain-map compiler from "
                    "the boundary-derived handle complexes, prove the "
                    "chain-homotopy inverse and coordinate square for "
                    "all eight move constructors, and remove the "
                    "custom compiler axiom from the final route."
                ),
            },
            {
                "id": "RAW_LOCAL_GRAPHICAL_MOVE_COMPILER_NOT_IMPLEMENTED",
                "reason": (
                    "The core window-rewrite engine and exact target-core "
                    "theorem are kernel checked. The remaining gap is to "
                    "compile each generated core to an actual "
                    "LocalCycleCalculation; provenance metadata is "
                    "correctly kept outside the mathematical engine."
                ),
                "terminal_condition": (
                    "Compile every generated move to the restricted "
                    "LocalCycleCalculation grammar without importing "
                    "standardLocalCycleCalculation."
                ),
            },
            {
                "id": "GLOBAL_SAFE_LIFT_NORMAL_FORM_NOT_CONSTRUCTED",
                "reason": (
                    "The algebra constructs cycle lifts, but an "
                    "arbitrary lift can carry a boundary component on "
                    "a two-handle that is later cancelled."
                ),
                "terminal_condition": (
                    "Construct a stable geometric normal form or a "
                    "distinguished admissible orbit whose selected "
                    "cycles avoid every dying two-handle. A strictly "
                    "natural cycle selector is ruled out by the "
                    "kernel-checked boundary-shear counterexample."
                ),
            },
            {
                "id": "ENRICHED_KIRBY_CERF_COVERAGE_NOT_PROVED",
                "reason": (
                    "Ordinary Kirby-Cerf connectivity does not by "
                    "itself prove connectivity after cycle bases and "
                    "cancellation-safety witnesses are added."
                ),
                "terminal_condition": (
                    "Prove every marked diffeomorphism is represented "
                    "by a finite certified movie satisfying literal "
                    "cycle transport and cancellation safety at every "
                    "step."
                ),
            },
            {
                "id": "PUBLIC_FOUR_MANIFOLD_INSTANCE_NOT_ASSEMBLED",
                "reason": (
                    "The established object is a value on a generated "
                    "presentation quotient, not yet a function "
                    "Eval_C(X, alpha) on all intended manifolds."
                ),
                "terminal_condition": (
                    "Instantiate the public topology boundary with "
                    "the enriched presentation theorem and then apply "
                    "the already proved generic descent constructor."
                ),
            },
        ],
        "reference_boundary": {
            "may_be_cited_as_standard_foundation": [
                (
                    "Mathlib homology quotient: homologyPi is "
                    "surjective onto homology."
                ),
                (
                    "Ordinary handle/Kirby-Cerf and boundary "
                    "standardization theorems, at their exact stated "
                    "topological scope."
                ),
                (
                    "The six disclosed modular graphical/category "
                    "identities listed by the axiom audit."
                ),
            ],
            "proved_in_repo_instead_of_cited": [
                "lifting a finite-free H2 basis to actual cycles",
                "the marked-cycle class equation",
                "arbitrary GL_r(Z) rebasing invariance",
                "induction from one certified move to the generated quotient",
                (
                    "the negative theorem that arbitrary raw "
                    "representative descent is false"
                ),
                (
                    "the negative theorem that a strictly "
                    "boundary-shear-natural cycle selector need not "
                    "exist"
                ),
            ],
            "no_reference_currently_supports": [
                (
                    "a concrete source-recipe-to-chain-equivalence "
                    "compiler for this repository's serialized moves"
                ),
                (
                    "a concrete raw rewrite-to-LocalCycleCalculation "
                    "compiler for all eight move constructors"
                ),
                (
                    "the enriched integral cycle-basis Kirby-Cerf "
                    "coverage theorem needed for the global result"
                ),
                (
                    "a torsion-H2 extension of the present surgery "
                    "formula"
                ),
                (
                    "Yetter's full surgery theorem generalized from "
                    "his simply-connected Z2 Uq(sl2) scope to arbitrary "
                    "integral markings and arbitrary modular categories"
                ),
            ],
            "primary_scope_warning": (
                "ref:yetter-homologically-twisted-1993, Definition "
                "10 and Theorem 11, proves only the simply-connected "
                "H2(-; Z2) Uq(sl2) surgical case. It cannot be cited "
                "as the missing general theorem."
            ),
        },
        "explicit_nonclaims": [
            "This is not yet an invariant of every pair (X, alpha).",
            (
                "This does not prove equality for arbitrary cycle "
                "representatives of one H2 class."
            ),
            (
                "This does not cover torsion in integral second "
                "homology."
            ),
            (
                "This does not promote ordinary Kirby-Cerf "
                "connectivity to enriched cancellation-safe "
                "connectivity."
            ),
            (
                "This does not claim that the source-bound chain or "
                "raw graphical move compilers have been implemented."
            ),
            (
                "This does not claim that Yetter's 1993 surgery proof "
                "already contains the arbitrary modular integral "
                "generalization."
            ),
        ],
        "axiom_audit": {
            "targets": AUDIT_TARGETS,
            "declarations": audit,
            "basis_project_axioms_empty": True,
            "expected_local_project_axioms": sorted(
                EXPECTED_LOCAL_PROJECT_AXIOMS
            ),
            "hidden_representative_descent_axiom": False,
        },
        "checks": {
            "lean_build": "PASS",
            "lean_threads": 1,
            "max_parallel_jobs": 2,
            "source_guards": guards,
            "git_diff_check": {
                "returncode": diff_check.returncode,
            },
            "audit_stdout": {
                "bytes": len(build.stdout.encode()),
                "sha256": sha256_bytes(build.stdout.encode()),
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
