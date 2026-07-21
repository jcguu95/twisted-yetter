#!/usr/bin/env python3
"""Build the fail-closed correction for the primal/dual handle mismatch."""

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
    "dual-handle-convention-correction-v1.json"
)
SUPERSEDED_OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "general-h2-kirby-route-resolution-v1.json"
)

SOURCE_FILES = [
    "lean/TwistedYetter/Kirby/KirbyCancellation.lean",
    "lean/TwistedYetter/Kirby/KirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/DualHandleConvention.lean",
    "lean/TwistedYetter/Kirby/DualHandleConventionAxiomAudit.lean",
    "lean/TwistedYetter/Kirby/BoundaryCertifiedKirbyPresentation.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "BoundaryCertifiedKirbyPresentationAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/ThamThreeHandleVacuum.lean",
    "lean/TwistedYetter/Kirby/ModularDottedVacuumBridge.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "ModularDottedVacuumBridgeAxiomAudit.lean"
    ),
    "lean/TwistedYetter/Kirby/GeneralH2RawKirbyNoGo.lean",
    (
        "experiments/inputs/references/"
        "general-h2-kirby-route-source-audit-v1.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "cycle-representative-descent-counterexample-v1.json"
    ),
    (
        "experiments/scripts/"
        "build_dual_handle_convention_correction_v1.py"
    ),
]

BUILD_TARGETS = [
    "TwistedYetter.Kirby.DualHandleConventionAxiomAudit",
    "TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentationAxiomAudit",
    "TwistedYetter.Kirby.ModularDottedVacuumBridgeAxiomAudit",
]

UNSAFE_PRIOR_ARTIFACTS = [
    (
        "experiments/results/lean-kirby/"
        "canonical-modular-four-manifold-invariant-v1.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "canonical-modular-four-manifold-invariant-v2.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "general-h2-marked-kirby-status-v1.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "h2-and-label-indexed-sliding-proof-status-v1.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "homological-four-manifold-final-target-status-v1.json"
    ),
    (
        "experiments/results/lean-kirby/"
        "integral-h2-cycle-basis-status-v1.json"
    ),
]

UNSAFE_PRIOR_GENERATORS = [
    (
        "experiments/scripts/"
        "build_canonical_modular_four_manifold_invariant_v1.py"
    ),
    (
        "experiments/scripts/"
        "build_canonical_modular_four_manifold_invariant_v2.py"
    ),
    (
        "experiments/scripts/"
        "build_general_h2_marked_kirby_status_v1.py"
    ),
    (
        "experiments/scripts/"
        "build_h2_and_label_indexed_sliding_proof_status_v1.py"
    ),
    (
        "experiments/scripts/"
        "build_homological_four_manifold_final_target_status_v1.py"
    ),
    (
        "experiments/scripts/"
        "build_integral_h2_cycle_basis_status_v1.py"
    ),
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
    for relative in SOURCE_FILES[:10]:
        text = (ROOT / relative).read_text()
        require(
            proof_hole.search(text) is None,
            f"proof hole found in {relative}",
        )

    counts = (ROOT / SOURCE_FILES[0]).read_text()
    require(
        "def turnedOver" in counts
        and "theorem turnedOver_addOneTwo" in counts
        and "theorem turnedOver_addTwoThree" in counts,
        "handle reversal or cancellation swap theorem is missing",
    )

    presentation = (ROOT / SOURCE_FILES[1]).read_text()
    require(
        "handleChain : HandleChainModel counts.turnedOver" in presentation,
        "SpecialKirbyPresentation does not force a dual handle chain",
    )

    adapter = (ROOT / SOURCE_FILES[4]).read_text()
    require(
        "dualBoundaryCertificate" in adapter,
        "boundary adapter lacks a transpose certificate",
    )
    require(
        "counts := presentation.closure.handleCounts" in adapter,
        "primal normalization counts were silently reversed",
    )
    require(
        "presentation.dualBoundaryCertificate.dualBoundaryData" in adapter,
        "adapter does not build the evaluator chain from dual data",
    )

    dual = (ROOT / SOURCE_FILES[2]).read_text()
    for theorem in (
        "primalTwoThree_dualCycle_forced_zero",
        "primalTwoThree_coefficientOne_not_dualCycle",
        "primalOneTwo_unitCycle_is_dualBoundary",
        "primalOneTwo_zero_eq_one_in_dualH2",
    ):
        require(theorem in dual, f"missing dual regression: {theorem}")

    bridge = (ROOT / SOURCE_FILES[7]).read_text()
    require(
        "theorem twistedHopfPairSum_eq_globalDimension" in bridge,
        "all-exponent dotted-vacuum theorem is missing",
    )
    require(
        "PASS_ALL_EXPONENT_MODULAR_DOTTED_THAM_K3_VACUUM_BRIDGE"
        in bridge,
        "dotted-vacuum status is not passing",
    )

    retraction = (ROOT / SOURCE_FILES[9]).read_text()
    require(
        "RETRACTED_WRONG_PRIMAL_DUAL_IDENTIFICATION_NOT_AN_INVARIANT_NOGO"
        in retraction,
        "old no-go interpretation was not retracted",
    )

    references = json.loads((ROOT / SOURCE_FILES[10]).read_text())
    require(
        references["status"]
        == "PRIMARY_SOURCE_SCOPE_AUDITED_DUAL_HANDLE_CONVENTION_CORRECTED",
        "source audit still records the wrong handle convention",
    )

    regression = json.loads((ROOT / SOURCE_FILES[11]).read_text())
    require(
        regression["status"]
        == "REGRESSION_ONLY_WRONG_PRIMAL_CHAIN_NOT_FORMAL_EVIDENCE"
        and regression["formal_evidence_admissible"] is False,
        "wrong-primal-chain regression was promoted to formal evidence",
    )
    return {
        "status": "PASS_FAIL_CLOSED_DUAL_CONVENTION_GUARDS",
        "proof_holes": [],
        "primal_counts_preserved": True,
        "dual_handle_chain_forced": True,
        "transpose_certificate_required": True,
        "cancellation_indices_swapped": True,
        "old_no_go_retracted": True,
        "wrong_primal_regression_quarantined": True,
    }


def build_tombstone(correction_hash: str) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.general-h2-kirby-route-resolution.v1",
        "status": "SUPERSEDED_WRONG_PRIMAL_DUAL_IDENTIFICATION",
        "formal_evidence_admissible": False,
        "superseded_by": {
            "path": str(OUTPUT.relative_to(ROOT)),
            "content_hash": correction_hash,
        },
        "reason": (
            "The former terminal no-go treated primal d3 as the evaluator's "
            "degree-three boundary. The evaluator uses the upside-down "
            "complex: primal 2-3 becomes dual 1-2, while primal dotted 1-2 "
            "becomes the dual 2-3 case controlled by Tham k=3."
        ),
        "unsafe_interpretation": (
            "Do not use the old numerical toy calculation as evidence that "
            "the intended H2-marked modular evaluator fails to descend."
        ),
    }
    payload["content_hash"] = canonical_hash(payload)
    return payload


def main() -> None:
    started = time.monotonic()
    started_at = utc_now()
    guards = source_guards()
    build_argv = ["lake", "-Kjobs=2", "build", *BUILD_TARGETS]
    build = run(build_argv)

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
        "schema": "twisted-yetter.dual-handle-convention-correction.v1",
        "status": "PASS_DUAL_HANDLE_CONVENTION_CORRECTED_LOCAL_REGRESSIONS",
        "mathematical_status": "ESTABLISHED_LOCAL_CORRECTION_GLOBAL_INTEGRATION_OPEN",
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": str(Path(__file__).relative_to(ROOT)),
        "argv": [str(Path(__file__).relative_to(ROOT))],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 experiments/scripts/"
            "build_dual_handle_convention_correction_v1.py"
        ),
        "correct_convention": {
            "primal_1_handle": "Tham k=3 vacuum projector",
            "primal_2_handle": "Tham k=2 link component",
            "primal_3_handle": "Tham k=1 inverse-dimension map",
            "homology_chain": (
                "C_primal_1 --transpose(d2)--> C_primal_2 "
                "--transpose(d3)--> C_primal_3"
            ),
            "normalization_counts": "primal counts, not reversed",
        },
        "established": {
            "presentation_type_separation": (
                "SpecialKirbyPresentation keeps primal counts and forces "
                "handleChain : HandleChainModel counts.turnedOver."
            ),
            "boundary_adapter": (
                "A DualBoundaryCertificate proves both transpose/adjoint "
                "identities and derives the dual d_squared=0 theorem."
            ),
            "primal_two_three": (
                "It is dual 1-2; the new coefficient one is not a cycle."
            ),
            "primal_one_two": (
                "It is dual 2-3; zero and one differ by a dual boundary."
            ),
            "dotted_vacuum": (
                "For every integral exponent, the exact positive Hopf-pair "
                "sum equals the global dimension."
            ),
            "retracted_interpretation": (
                "The old primal-chain toy counterexample is not an "
                "invariant no-go theorem."
            ),
        },
        "explicit_axiom_boundary": [
            {
                "axiom": (
                    "TwistedYetter.Kirby.EGNOModularKirbyMoves."
                    "LiteratureBackedModularGraphicalEnvironment."
                    "baerenzBarrett_hopfKirbyKillingFiber"
                ),
                "role": (
                    "Label-resolved modular killing lemma; Lean derives "
                    "the all-exponent finite-sum identity from it."
                ),
            },
            {
                "axiom": (
                    "TwistedYetter.Kirby.EGNOModularKirbyMoves."
                    "LiteratureBackedModularGraphicalEnvironment."
                    "egno_quantumDimension_unit"
                ),
                "role": "The tensor unit has quantum dimension one.",
            },
        ],
        "remaining_global_obligation": {
            "status": "BLOCKED_GLOBAL_DUAL_BOUNDARY_MOVIE_INTEGRATION",
            "description": (
                "Connect every generated dual d3 boundary movie in a full "
                "serialized presentation to the proved local dotted Hopf "
                "vacuum theorem. The local theorem is complete; the global "
                "factorization/compiler connection is not yet derived."
            ),
            "not_missing": [
                "an actual category instance",
                "the primal 2-3 cycle check",
                "the all-exponent modular dotted-vacuum identity",
            ],
        },
        "resource_safety": {
            "unsafe_prior_artifacts": UNSAFE_PRIOR_ARTIFACTS,
            "unsafe_prior_generators": UNSAFE_PRIOR_GENERATORS,
            "unsafe_scope": (
                "Any claim in these artifacts that arbitrary representative "
                "descent was refuted by a primal cancelling 2-3 pair."
            ),
            "safe_scope": (
                "Their syntactic local-move work may be reused only after "
                "revalidation against the dual handle chain."
            ),
        },
        "explicit_nonclaims": [
            "This artifact does not yet establish the final closed four-manifold invariant.",
            "It does not prove the global dual-boundary movie integration.",
            "It does not identify the construction with the original Crane-Yetter state sum.",
            "The old primal-chain numerical calculation remains only a regression test for the wrong adapter.",
        ],
        "checks": {
            "lean_build": "PASS",
            "build_command": build_argv,
            "lean_threads": 1,
            "max_parallel_jobs": 2,
            "source_guards": guards,
            "git_diff_check": {"returncode": diff_check.returncode},
            "build_stdout": {
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
            "lean": run(["lean", "--version"]).stdout.splitlines()[0],
            "lake": run(["lake", "--version"]).stdout.splitlines()[0],
        },
        "inputs": {
            relative: file_metadata(relative)
            for relative in SOURCE_FILES
        },
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    tombstone = build_tombstone(payload["content_hash"])
    SUPERSEDED_OUTPUT.write_text(
        json.dumps(tombstone, indent=2, sort_keys=True) + "\n"
    )
    print(OUTPUT)
    print(payload["content_hash"])
    print(payload["status"])


if __name__ == "__main__":
    main()
