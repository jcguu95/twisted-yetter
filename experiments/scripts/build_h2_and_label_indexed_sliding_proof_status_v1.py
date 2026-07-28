#!/usr/bin/env python3
"""Build the audited status of the H2 and fixed-label slide corrections."""

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
    "h2-and-label-indexed-sliding-proof-status-v1.json"
)
AUDIT_TARGET = (
    "TwistedYetter.Kirby."
    "H2AndLabelIndexedSlidingProofAxiomAudit"
)
SOURCE_FILES = [
    (
        "experiments/scripts/"
        "build_h2_and_label_indexed_sliding_proof_status_v1.py"
    ),
    (
        "tests/"
        "test_h2_and_label_indexed_sliding_proof_status_v1.py"
    ),
    "lean-toolchain",
    "lakefile.toml",
    "lean/TwistedYetter.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "CycleRepresentativeCounterexample.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Representative.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "H2AndLabelIndexedSlidingProofAxiomAudit.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "EGNOKirbyColorEncircling.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "CanonicalCycleSlideGeometry.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "EGNOModularKirbyMoves.lean"
    ),
    (
        "lean/TwistedYetter/Kirby/"
        "LiteratureBackedCanonicalGraphicalInput.lean"
    ),
]
REFERENCE_FILES = [
    (
        "experiments/inputs/references/"
        "homologically-twisted-kirby-invariant-sources-v1.json"
    ),
    (
        "experiments/inputs/references/"
        "generalized-sliding-core-primary-sources-v2.json"
    ),
]
OLD_LABEL_AXIOM = (
    "baerenzBarrett_labelIndexedSlidingMovies"
)
OLD_REPRESENTATIVE_AXIOM = (
    "standardCycleBoundaryGraphicalRealization"
)
ORDINARY_SLIDING_AXIOM = (
    "TwistedYetter.Kirby.EGNOModularKirbyMoves."
    "LiteratureBackedModularGraphicalEnvironment."
    "baerenzBarrett_ordinaryKirbySliding"
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

    lean_sources = "\n".join(
        path.read_text()
        for path in (ROOT / "lean/TwistedYetter").rglob("*.lean")
    )
    require(
        OLD_LABEL_AXIOM not in lean_sources,
        "retired label-indexed sliding axiom returned",
    )
    literature_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "LiteratureBackedCanonicalGraphicalInput.lean"
    ).read_text()
    require(
        OLD_REPRESENTATIVE_AXIOM not in literature_text,
        "refuted arbitrary representative axiom returned",
    )

    h2_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "CancellationSafeH2Representative.lean"
    ).read_text()
    require(
        "alpha : presentation.topology.handleChain.SecondHomology"
        in h2_text,
        "public H2 input is not actual handle-chain second homology",
    )
    for declaration in (
        "theorem targetCycle_class",
        "theorem alpha_transport",
        "theorem eval_sound",
        "theorem value_sound",
    ):
        require(
            declaration in h2_text,
            f"missing H2 proof declaration: {declaration}",
        )

    slide_text = (
        ROOT
        / "lean/TwistedYetter/Kirby/"
        "EGNOKirbyColorEncircling.lean"
    ).read_text()
    require(
        "structure OrdinaryLabelIndexedSlidingWindow" in slide_text,
        "fixed-label ordinary sliding window is missing",
    )
    for declaration in (
        "theorem open_term_sound",
        "theorem term_sound",
        "theorem linear_eval_sound",
    ):
        require(
            declaration in slide_text,
            f"missing label-indexed proof declaration: {declaration}",
        )

    return {
        "status": "PASS_FAIL_CLOSED_SOURCE_GUARDS",
        "proof_holes": [],
        "checked_lean_files": checked,
        "retired_label_indexed_axiom_absent": True,
        "refuted_arbitrary_representative_axiom_absent": True,
        "public_alpha_is_actual_handle_chain_h2": True,
    }


def main() -> None:
    started_at = utc_now()
    start = time.monotonic()
    guards = source_guards()

    build_argv = ["lake", "-Kjobs=2", "build", AUDIT_TARGET]
    build = run(build_argv)
    audit = extract_axiom_audit(build.stdout)

    h2_movie = (
        "TwistedYetter.Kirby."
        "CancellationSafeH2Representative."
        "CancellationSafeMovie.value_sound"
    )
    fixed_label = (
        "TwistedYetter.Kirby."
        "EGNOKirbyColorEncircling."
        "OrdinaryLabelIndexedSlidingWindow.open_term_sound"
    )
    fixed_sum = (
        "TwistedYetter.Kirby."
        "EGNOKirbyColorEncircling."
        "OrdinaryLabelIndexedSlidingWindow.linear_eval_sound"
    )
    canonical_sum = (
        "TwistedYetter.Kirby."
        "CanonicalCycleSlideGeometry."
        "BoundGeneralizedLinearSlide.eval_eq"
    )
    for declaration in (h2_movie, fixed_label, fixed_sum, canonical_sum):
        require(
            declaration in audit,
            f"missing declaration from axiom audit: {declaration}",
        )

    require(
        audit[fixed_label]["project_axioms"] == [],
        "fixed-label theorem unexpectedly uses a project axiom",
    )
    require(
        audit[fixed_sum]["project_axioms"] == [],
        "fixed-sum theorem unexpectedly uses a project axiom",
    )
    require(
        audit[canonical_sum]["project_axioms"]
        == [ORDINARY_SLIDING_AXIOM],
        "canonical generalized slide has an unexpected axiom denominator",
    )
    all_project_axioms = sorted(
        {
            axiom
            for report in audit.values()
            for axiom in report["project_axioms"]
        }
    )
    require(
        not any(
            OLD_LABEL_AXIOM in axiom
            or OLD_REPRESENTATIVE_AXIOM in axiom
            for axiom in all_project_axioms
        ),
        "a retired axiom remains in the focused proof audit",
    )

    diff_check = run(["git", "diff", "--check"])
    status_porcelain = git_text("status", "--porcelain")
    payload: dict[str, Any] = {
        "schema": (
            "twisted-yetter."
            "h2-and-label-indexed-sliding-proof-status.v1"
        ),
        "status": (
            "KERNEL_CHECKED_TWO_PART_CORRECTION_"
            "WITH_EXPLICIT_GLOBAL_H2_BLOCKER"
        ),
        "mathematical_status": "ESTABLISHED_IN_EXACT_STATED_SCOPE",
        "generator_script": (
            "experiments/scripts/"
            "build_h2_and_label_indexed_sliding_proof_status_v1.py"
        ),
        "argv": sys.argv,
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 python3 "
            "experiments/scripts/"
            "build_h2_and_label_indexed_sliding_proof_status_v1.py"
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
            "source_files": {
                relative: file_metadata(relative)
                for relative in SOURCE_FILES
            },
            "reference_records": {
                relative: file_metadata(relative)
                for relative in REFERENCE_FILES
            },
        },
        "part_one_h2_correction": {
            "status": "PROVED_FOR_CANCELLATION_SAFE_H2_MOVIES",
            "public_input": (
                "alpha : presentation.topology.handleChain.SecondHomology"
            ),
            "proved": [
                "every stored cycle is certified to represent alpha",
                (
                    "the forward chain map sends the source cycle to a "
                    "cycle representing the transported H2 class"
                ),
                (
                    "a cancellation-safe local move preserves the "
                    "normalized evaluation"
                ),
                (
                    "a finite cancellation-safe movie preserves the "
                    "evaluation by induction"
                ),
            ],
            "lean_theorems": [
                (
                    "TwistedYetter.Kirby."
                    "CancellationSafeH2Representative.targetCycle_class"
                ),
                (
                    "TwistedYetter.Kirby."
                    "CancellationSafeH2Representative."
                    "CancellationSafeStep.alpha_transport"
                ),
                (
                    "TwistedYetter.Kirby."
                    "CancellationSafeH2Representative.eval_sound"
                ),
                h2_movie,
            ],
            "refuted_stronger_statement": (
                "arbitrary degree-two cycle representatives of one H2 "
                "class always have equal naive cycle-colour evaluations"
            ),
            "remaining_global_blocker": (
                "No theorem yet constructs a coherent cancellation-safe "
                "representative prescription for every marked Kirby "
                "presentation and every Kirby-Cerf movie. Therefore this "
                "artifact does not promote the naive EvalC to an "
                "unconditional invariant of (X, alpha)."
            ),
        },
        "part_two_label_indexed_sliding": {
            "status": (
                "PROVED_FOR_MODULAR_IDENTITY_FUNCTOR_FROM_"
                "ORDINARY_KIRBY_SLIDING"
            ),
            "proof_steps": [
                (
                    "specialize the ordinary Kirby-colour sliding natural "
                    "transformation to each actual simple label"
                ),
                "move the visible exterior diagram by naturality",
                "close the open equality inside an arbitrary typed context",
                "sum termwise with arbitrary twisted coefficients",
            ],
            "lean_theorems": [
                fixed_label,
                (
                    "TwistedYetter.Kirby."
                    "EGNOKirbyColorEncircling."
                    "OrdinaryLabelIndexedSlidingWindow.term_sound"
                ),
                fixed_sum,
                canonical_sum,
            ],
            "retired_axiom": OLD_LABEL_AXIOM,
            "remaining_literature_input": ORDINARY_SLIDING_AXIOM,
            "scope_caveat": (
                "This proves the identity-ribbon-functor specialization "
                "needed by the modular evaluator. It does not formalize "
                "the fully general pivotal-functor version of "
                "Bärenz-Barrett Lemma 3.3."
            ),
        },
        "axiom_audit": {
            "declarations": audit,
            "project_axioms_union": all_project_axioms,
            "retired_axioms_absent": True,
        },
        "resource_safety": {
            (
                "experiments/results/lean-kirby/"
                "canonical-modular-four-manifold-invariant-v2.json"
            ): (
                "HISTORICAL_OVERSTRONG_COMPLETION_STATUS; "
                "DO_NOT_USE AS CURRENT EVIDENCE FOR H2 DESCENT"
            ),
            (
                "TwistedYetter.Kirby."
                "CanonicalModularKirbyEvaluator."
                "CycleBoundaryGraphicalRealizationSystem"
            ): (
                "CONDITIONAL_INTERFACE_ONLY; GLOBALLY UNINHABITED FOR "
                "THE NAIVE EVALUATOR BY THE CANCELLING-PAIR COUNTEREXAMPLE"
            ),
        },
        "checks": {
            "source_guards": guards,
            "targeted_axiom_audit": {
                "argv": build_argv,
                "returncode": build.returncode,
                "stdout_bytes": len(build.stdout.encode()),
                "stdout_sha256": sha256_bytes(
                    build.stdout.encode()
                ),
            },
            "git_diff_check": {
                "returncode": diff_check.returncode,
            },
        },
        "explicit_nonclaims": [
            (
                "This is not an unconditional invariant of a pair "
                "(closed four-manifold, H2 class)."
            ),
            (
                "This does not prove arbitrary cycle-representative "
                "independence; that statement is false for the naive "
                "cycle-colour evaluator."
            ),
            (
                "This does not construct a globally coherent safe "
                "representative or basis prescription."
            ),
            (
                "This does not prove the fully general pivotal-functor "
                "label-indexed sliding theorem."
            ),
            (
                "This does prove the modular identity-functor sliding "
                "case used by the current evaluator."
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
