#!/usr/bin/env python3
"""Build the audited status of the corrected H2-basis-marked target."""

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
    "homological-four-manifold-final-target-status-v1.json"
)
AUDIT_TARGETS = [
    (
        "TwistedYetter.Kirby."
        "HomologicalFourManifoldInvariantFinalTargetAxiomAudit"
    ),
    (
        "TwistedYetter.Kirby."
        "H2BasisMarkedEvaluatorAxiomAudit"
    ),
    (
        "TwistedYetter.Kirby."
        "H2BasisMarkedKirbyInvarianceAxiomAudit"
    ),
]
SOURCE_FILES = [
    (
        "experiments/scripts/"
        "build_homological_four_manifold_final_target_status_v1.py"
    ),
    (
        "tests/"
        "test_homological_four_manifold_final_target_status_v1.py"
    ),
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOPremodularModular.lean",
    "lean/TwistedYetter/Fusion/EGNOTensorAutomorphism.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "TensorAutomorphismCouponCalculus.lean"
    ),
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalModularKirbyEvaluator.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleMoveGeometry.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleSlideGeometry.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleLocalInvariance.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Representative.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "H2BasisMarkedEvaluator.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "H2BasisMarkedEvaluatorAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "H2BasisMarkedKirbyInvariance.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "H2BasisMarkedKirbyInvarianceAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "ModularFourManifoldInvariantFinalTarget.lean"
    ),
    "lean/TwistedYetter/Kirby/BoundaryStandardization.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "HomologicalFourManifoldInvariantFinalTarget.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "HomologicalFourManifoldInvariantFinalTargetAxiomAudit.lean"
    ),
    (
        "experiments/inputs/references/"
        "homologically-twisted-kirby-invariant-sources-v1.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "cycle-representative-descent-counterexample-v1.json"
    ),
]
GENERIC_PRESENTATION_THEOREM = (
    "TwistedYetter.Kirby."
    "HomologicalFourManifoldInvariantFinalTarget."
    "AdmissibleKirbyCerfTheorem.EvalC_eq_presentation"
)
GENERIC_DIFFEO_THEOREM = (
    "TwistedYetter.Kirby."
    "HomologicalFourManifoldInvariantFinalTarget."
    "AdmissibleKirbyCerfTheorem.EvalC_diffeomorphism_invariant"
)
PUBLIC_INVARIANT_CONSTRUCTION = (
    "TwistedYetter.Kirby."
    "HomologicalFourManifoldInvariantFinalTarget."
    "AdmissibleKirbyCerfTheorem.constructInvariant"
)
BASIS_MARKED_CLASS_THEOREM = (
    "TwistedYetter.Kirby."
    "H2BasisMarkedEvaluator.CanonicalPresentation."
    "H2BasisRealization.markedCycle_class"
)
BASIS_MARKED_RAW_BRIDGE = (
    "TwistedYetter.Kirby."
    "H2BasisMarkedEvaluator.CanonicalPresentation."
    "basisMarkedPresentationValue_eq_rawCycleColourEval"
)
BASIS_REINDEXING_THEOREM = (
    "TwistedYetter.Kirby."
    "H2BasisMarkedEvaluator.CanonicalPresentation."
    "BasisReindexing.presentationValue_eq"
)
BASIS_LOCAL_MOVE_THEOREM = (
    "TwistedYetter.Kirby."
    "H2BasisMarkedKirbyInvariance."
    "BasisMarkedMoveCompatibility.presentationValue_eq"
)
BASIS_LOCAL_INVARIANCE_THEOREM = (
    "TwistedYetter.Kirby."
    "H2BasisMarkedKirbyInvariance."
    "basisMarkedEvaluation_localInvariant"
)
BASIS_QUOTIENT_EVALUATOR = (
    "TwistedYetter.Kirby."
    "H2BasisMarkedKirbyInvariance."
    "basisMarkedEvaluationOnKirbyClass"
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

    target_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "HomologicalFourManifoldInvariantFinalTarget.lean"
    ).read_text()
    require(
        "theorem EvalC_diffeomorphism_invariant" in target_text,
        "pinned diffeomorphism theorem is missing",
    )
    theorem_tail = target_text.split(
        "theorem EvalC_diffeomorphism_invariant", 1
    )[1]
    require(
        "DegreeTwoCycle" not in theorem_tail,
        "public final theorem leaked a cycle input",
    )
    require(
        "CycleBoundaryGraphicalRealizationSystem" not in target_text,
        "refuted arbitrary representative interface leaked into target",
    )
    topology_block = target_text.split(
        "structure AdmissibleKirbyCerfTheorem", 1
    )[1].split("/-- The scalar formula", 1)[0]
    require(
        "formula" not in topology_block
        and "value" not in topology_block
        and " = " not in topology_block,
        "topology boundary contains evaluator or scalar equality",
    )

    basis_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/H2BasisMarkedEvaluator.lean"
    ).read_text()
    basis_block = basis_text.split(
        "structure H2BasisRealization", 1
    )[1].split("namespace H2BasisRealization", 1)[0]
    for required_field in (
        "basisCycle",
        "basis_cycle_handle_coordinates",
        "basis_homology_coordinates",
    ):
        require(
            required_field in basis_block,
            f"basis realization lost required field: {required_field}",
        )

    move_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "H2BasisMarkedKirbyInvariance.lean"
    ).read_text()
    compatibility_block = move_text.split(
        "structure BasisMarkedMoveCompatibility", 1
    )[1].split("namespace BasisMarkedMoveCompatibility", 1)[0]
    for required_field in (
        "marked_cycle_transport",
        "cancellation_safe",
    ):
        require(
            required_field in compatibility_block,
            f"move compatibility lost required field: {required_field}",
        )
    require(
        "basisMarkedPresentationValue" not in compatibility_block
        and "rawCycleColourEval" not in compatibility_block,
        "move compatibility stores the desired evaluator equality",
    )

    reference_ledger = json.loads(
        (
            ROOT
            / "experiments/inputs/references/"
            "homologically-twisted-kirby-invariant-sources-v1.json"
        ).read_text()
    )
    counterexample = json.loads(
        (
            ROOT
            / "experiments/results/lean-kirby/"
            "cycle-representative-descent-counterexample-v1.json"
        ).read_text()
    )
    yetter_reference = next(
        reference
        for reference in reference_ledger["references"]
        if reference["ref_id"]
        == "ref:yetter-homologically-twisted-1993"
    )
    require(
        counterexample["primary_source_check"]["local_pdf_sha256"]
        == yetter_reference["captured_pdf"]["sha256"],
        "Yetter PDF hash disagrees across the reference ledger and "
        "counterexample artifact",
    )
    return {
        "status": "PASS_FAIL_CLOSED_SOURCE_GUARDS",
        "lean_sources_without_proof_holes": checked,
        "public_theorem_has_no_cycle_input": True,
        "refuted_representative_interface_absent": True,
        "topology_boundary_has_no_evaluator_or_scalar_equality": True,
        "basis_cycles_are_bound_to_handles_and_homology": True,
        "move_compatibility_has_no_evaluator_equality": True,
        "yetter_pdf_hashes_align_across_artifacts": True,
    }


def main() -> None:
    started = utc_now()
    start_time = time.monotonic()
    guards = source_guards()
    build = run(
        [
            "lake",
            "-Kjobs=2",
            "build",
            *AUDIT_TARGETS,
        ]
    )
    audit = extract_axiom_audit(build.stdout)
    for declaration in (
        GENERIC_PRESENTATION_THEOREM,
        GENERIC_DIFFEO_THEOREM,
        PUBLIC_INVARIANT_CONSTRUCTION,
        BASIS_MARKED_CLASS_THEOREM,
        BASIS_MARKED_RAW_BRIDGE,
        BASIS_REINDEXING_THEOREM,
        BASIS_LOCAL_MOVE_THEOREM,
        BASIS_LOCAL_INVARIANCE_THEOREM,
        BASIS_QUOTIENT_EVALUATOR,
    ):
        require(
            declaration in audit,
            f"missing axiom audit declaration: {declaration}",
        )
    require(
        audit[GENERIC_PRESENTATION_THEOREM]["project_axioms"] == [],
        "presentation independence has a hidden project axiom",
    )
    require(
        audit[GENERIC_DIFFEO_THEOREM]["project_axioms"] == [],
        "diffeomorphism descent has a hidden project axiom",
    )
    require(
        audit[PUBLIC_INVARIANT_CONSTRUCTION]["project_axioms"] == [],
        "public invariant construction has a hidden project axiom",
    )
    require(
        audit[BASIS_MARKED_CLASS_THEOREM]["project_axioms"] == [],
        "marked cycle class theorem has a hidden project axiom",
    )
    for declaration in (
        BASIS_MARKED_RAW_BRIDGE,
        BASIS_REINDEXING_THEOREM,
        BASIS_LOCAL_MOVE_THEOREM,
        BASIS_LOCAL_INVARIANCE_THEOREM,
        BASIS_QUOTIENT_EVALUATOR,
    ):
        unexpected = (
            set(audit[declaration]["project_axioms"])
            - EXPECTED_LOCAL_PROJECT_AXIOMS
        )
        require(
            not unexpected,
            f"unexpected project axioms for {declaration}: "
            f"{sorted(unexpected)}",
        )
    require(
        set(audit[BASIS_LOCAL_MOVE_THEOREM]["project_axioms"])
        == EXPECTED_LOCAL_PROJECT_AXIOMS,
        "local move theorem did not expose the expected category axioms",
    )
    require(
        all(
            "CycleBoundaryGraphicalRealization" not in axiom
            and "representative" not in axiom.lower()
            for declaration in audit.values()
            for axiom in declaration["project_axioms"]
        ),
        "refuted representative-descent axiom leaked into the audit",
    )

    elapsed = time.monotonic() - start_time
    payload: dict[str, Any] = {
        "schema": (
            "twisted-yetter."
            "homological-four-manifold-final-target-status.v1"
        ),
        "status": (
            "CORRECTED_H2_BASIS_MARKED_KIRBY_QUOTIENT_ESTABLISHED_"
            "GLOBAL_FOUR_MANIFOLD_DESCENT_BLOCKED"
        ),
        "mathematical_status": (
            "ESTABLISHED_ON_BASIS_COMPATIBLE_KIRBY_QUOTIENT;"
            "GLOBAL_FOUR_MANIFOLD_THEOREM_NOT_YET_ESTABLISHED"
        ),
        "generator_script": (
            "experiments/scripts/"
            "build_homological_four_manifold_final_target_status_v1.py"
        ),
        "argv": [
            "python3",
            (
                "experiments/scripts/"
                "build_homological_four_manifold_final_target_status_v1.py"
            ),
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 experiments/scripts/"
            "build_homological_four_manifold_final_target_status_v1.py"
        ),
        "utc_started": started,
        "utc_finished": utc_now(),
        "elapsed_seconds": round(elapsed, 6),
        "repo_root": str(ROOT),
        "git_commit": git_text("rev-parse", "HEAD"),
        "git_dirty": bool(git_text("status", "--porcelain")),
        "tool_versions": {
            "python": platform.python_version(),
            "lean": tool_version(["lake", "env", "lean", "--version"]),
            "lake": tool_version(["lake", "--version"]),
        },
        "public_statement": {
            "inputs": [
                "a closed oriented smooth four-manifold X",
                "alpha in integral H_2(X)",
            ],
            "value": "EvalC(X, alpha)",
            "diffeomorphism_law": (
                "EvalC(X, alpha) = EvalC(Y, f_*(alpha)) for every "
                "orientation-preserving diffeomorphism f : X -> Y"
            ),
            "excluded_public_inputs": [
                "degree-two cycle representative",
                "handle presentation",
                "presentation compiler",
                "graphical realization selector",
            ],
        },
        "refuted_statement": {
            "text": (
                "The raw cycle-colour expression is constant on every "
                "fiber of degree-two cycles -> H_2."
            ),
            "status": "FALSE",
            "counterexample_artifact": (
                "experiments/results/lean-kirby/"
                "cycle-representative-descent-counterexample-v1.json"
            ),
        },
        "corrected_statement": {
            "input": (
                "alpha in the actual handle-chain second homology of a "
                "basis-certified presentation"
            ),
            "definition": (
                "Expand alpha in a certified sphere basis, put those "
                "coordinates only on the selected two-handles, and put "
                "zero on every other handle."
            ),
            "local_theorem": (
                "A basis-compatible, cancellation-safe Kirby calculation "
                "preserves the normalized value."
            ),
            "quotient_theorem": (
                "The value descends to the quotient generated by those "
                "certified moves."
            ),
        },
        "proved_now": {
            "canonical_marked_cycle_represents_alpha": (
                "H2BasisRealization.markedCycle_class"
            ),
            "nonbasis_handles_have_zero_exponent": (
                "H2BasisRealization.nonbasis_componentExponent"
            ),
            "formula_matches_raw_evaluator_at_canonical_cycle": (
                "basisMarkedPresentationValue_eq_rawCycleColourEval"
            ),
            "basis_reindexing_is_irrelevant": (
                "BasisReindexing.presentationValue_eq"
            ),
            "certified_local_move_preserves_value": (
                "BasisMarkedMoveCompatibility.presentationValue_eq"
            ),
            "finite_movies_preserve_value": (
                "PresentationEvaluation.respectsKirbyMovie"
            ),
            "basis_compatible_quotient_evaluator": (
                "basisMarkedEvaluationOnKirbyClass"
            ),
            "generic_choice_of_admissible_presentation_is_irrelevant": (
                "AdmissibleKirbyCerfTheorem.EvalC_eq_presentation"
            ),
            "generic_diffeomorphism_descent": (
                "AdmissibleKirbyCerfTheorem."
                "EvalC_diffeomorphism_invariant"
            ),
            "generic_public_invariant_constructor": (
                "AdmissibleKirbyCerfTheorem.constructInvariant"
            ),
        },
        "remaining_blocker": {
            "name": (
                "GLOBAL_BASIS_COMPATIBLE_KIRBY_CERF_COMPLETENESS"
            ),
            "exact_obligations": [
                (
                    "Construct a certified two-handle sphere-basis "
                    "realization for every intended simply-connected "
                    "presentation."
                ),
                (
                    "For every actual Kirby-Cerf move, prove that the "
                    "selected source and target bases obey literal "
                    "chain-level marked-cycle transport."
                ),
                (
                    "For every cancellation death, prove that the selected "
                    "basis excludes the deleted two-handle and hence the "
                    "canonical marked cycle is cancellation-safe."
                ),
                (
                    "Derive non-reindexing sphere-basis changes from "
                    "explicit handle slides and coupon calculations."
                ),
                (
                    "Instantiate the generic public four-manifold topology "
                    "boundary with the resulting basis-compatible "
                    "presentation calculus."
                ),
                (
                    "Either restrict the theorem to Yetter's sourced "
                    "simply-connected mod-two U_q(sl2) scope, or prove the "
                    "integral arbitrary-modular-category generalization."
                ),
            ],
            "not_allowed_as_substitute": [
                "arbitrary cycle representative independence",
                "a scalar equality stored in the topology input",
                "a scalar equality stored in move compatibility",
                "the old shared-H2 marked-manifold shell",
            ],
        },
        "source_scope": {
            "primary_reference": (
                "ref:yetter-homologically-twisted-1993"
            ),
            "locator": "Definition 10 and Theorem 11, printed page 5",
            "exact_scope": (
                "simply connected, H_2(-; Z_2), and the stated "
                "U_q(sl2) Kauffman-bracket surgery formula"
            ),
            "generalization_warning": (
                "The integral arbitrary-modular-category theorem is not "
                "contained in this source."
            ),
        },
        "explicit_nonclaims": [
            (
                "The raw cycle-colour expression is not claimed to be a "
                "function on H_2."
            ),
            (
                "A complete closed-four-manifold invariant has not yet "
                "been constructed from the corrected basis calculus."
            ),
            (
                "General integral sphere-basis independence has not yet "
                "been proved."
            ),
            "No premodular theorem is claimed.",
            (
                "No identification with Yetter's triangulation state sum "
                "is claimed."
            ),
        ],
        "axiom_audit": {
            "targets": AUDIT_TARGETS,
            "declarations": audit,
            "generic_descent_project_axioms": [],
            "expected_local_category_axioms": sorted(
                EXPECTED_LOCAL_PROJECT_AXIOMS
            ),
            "hidden_representative_descent_axiom": False,
        },
        "checks": {
            "lean_build": "PASS",
            "source_guards": guards,
            "max_parallel_jobs": 2,
            "lean_threads": 1,
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


if __name__ == "__main__":
    main()
