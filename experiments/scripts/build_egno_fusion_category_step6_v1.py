#!/usr/bin/env python3
"""Build the source-bound certificate for EGNO fusion-category Step 6."""

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
    "egno-fusion-category-step6-v1.json"
)
ROADMAP = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "egno-category-foundations-primary-sources-v1.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_fusion_category_step6_v1.py",
    "tests/test_egno_fusion_category_step6_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNORibbon.lean",
    "lean/TwistedYetter/Fusion/EGNOCanonicalPivotal.lean",
    "lean/TwistedYetter/Fusion/EGNOCanonicalSpherical.lean",
    "lean/TwistedYetter/Fusion/EGNOTraceCyclicity.lean",
    "lean/TwistedYetter/Fusion/EGNOFusionCategory.lean",
    "lean/TwistedYetter/Fusion/EGNOFusionCategoryAxiomAudit.lean",
    "lean/TwistedYetter/Fusion/Insertion.lean",
    "lean/Mutations/FusionListWithoutCompleteness.lean",
    "lean/Mutations/NumericalMultiplicityIsNotDecomposition.lean",
    "lean/Mutations/DuplicateSimpleListWithoutGuard.lean",
    "lean/Mutations/FusionUnitNeedsSimpleRepresentative.lean",
    "lean/Mutations/FusionDualNeedsRepresentative.lean",
    "lean/Mutations/ArbitraryClosedScalarIsNotFusionData.lean",
    "lean/Mutations/FusionDataWithoutRibbonIsNotRibbonData.lean",
    "scripts/lean_egno_fusion_category_axiom_audit.sh",
    "scripts/lean_egno_fusion_category_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    str(ROADMAP.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
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
    checked: list[str] = []
    for relative in SOURCE_FILES:
        if not relative.endswith(".lean"):
            continue
        text = (REPO_ROOT / relative).read_text()
        match = forbidden.search(text)
        if match:
            raise AssertionError(
                f"forbidden proof-oracle token in {relative}: "
                f"{match.group(0)!r}"
            )
        checked.append(relative)
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": checked,
    }


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("Step 6 artifact requires a clean source commit")

    roadmap = json.loads(ROADMAP.read_text())
    references = json.loads(REFERENCES.read_text())
    if roadmap["status"] != "STEP_6_ESTABLISHED_STEPS_7_TO_10_EXPLICIT":
        raise AssertionError("unexpected roadmap status")
    statuses = [step["status"] for step in roadmap["steps"]]
    if statuses[:6] != ["ESTABLISHED_IN_LEAN"] * 6:
        raise AssertionError("Steps 1 through 6 must be established")
    if any(status != "NOT_YET_ESTABLISHED" for status in statuses[6:]):
        raise AssertionError("a post-Step-6 obligation was silently promoted")

    capture = references["references"][0]["captured_pdf"]
    capture_path = Path(capture["capture_path_at_capture_time"])
    if not capture_path.exists():
        raise AssertionError("the pinned local EGNO PDF is absent")
    if capture_path.stat().st_size != capture["bytes"]:
        raise AssertionError("the pinned EGNO PDF size changed")
    if sha256_path(capture_path) != capture["sha256"]:
        raise AssertionError("the pinned EGNO PDF hash changed")

    module_text = (
        REPO_ROOT
        / "lean/TwistedYetter/Fusion/EGNOFusionCategory.lean"
    ).read_text()
    required_contracts = [
        "structure FusionCategoryData",
        "theorem everySimple_is_represented",
        "theorem simple_iso_iff_eq",
        "theorem simpleHom_finrank",
        "noncomputable def unitEndLinearEquiv",
        "noncomputable def closedScalar",
        "theorem closedScalar_comp",
        "theorem sum_projection_inclusion",
        "noncomputable def identityResolution",
        "noncomputable def tensorIdentityResolution",
        "structure RibbonFusionCategoryData",
        "noncomputable def quantumDimension",
    ]
    missing = [
        contract for contract in required_contracts
        if contract not in module_text
    ]
    if missing:
        raise AssertionError(f"missing Step 6 contracts: {missing}")
    if "closedScalar :" in module_text.split(
        "structure FusionCategoryData where", maxsplit=1
    )[1].split("namespace FusionCategoryData", maxsplit=1)[0]:
        raise AssertionError("closedScalar became a caller-provided structure field")

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(["./scripts/lean_egno_fusion_category_axiom_audit.sh"])
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 6 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 57:
        raise AssertionError(
            f"expected 57 audited declarations, got {audited_declarations}"
        )

    mutations = run(["./scripts/lean_egno_fusion_category_mutation_tests.sh"])
    rejections = [
        line for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 22:
        raise AssertionError("expected twenty-two rejected Step 1-6 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-fusion-category-step6.v1",
        "status": "PASS_STEP_6_FINITE_SEMISIMPLE_FUSION_INTERFACE_ESTABLISHED",
        "mathematical_status": (
            "GENERIC_PROOF_RELEVANT_FUSION_AND_RIBBON_INTERFACE_ESTABLISHED"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_egno_fusion_category_step6_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_egno_fusion_category_step6_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_egno_fusion_category_step6_v1.py"
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
            "roadmap": {
                "path": str(ROADMAP.relative_to(REPO_ROOT)),
                "sha256": sha256_path(ROADMAP),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "sha256": sha256_path(REFERENCES),
            },
            "egno_pdf": {
                "path_at_capture_time": str(capture_path),
                "bytes": capture["bytes"],
                "sha256": capture["sha256"],
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
                "status": "PASS_NO_SORRYAX_OR_NATIVE_ORACLE",
                "audited_declaration_count": audited_declarations,
            },
            "mutations": {
                "status": "PASS_FAIL_CLOSED",
                "rejected_count": len(rejections),
                "rejections": rejections,
            },
            "proof_hole_scan": proof_hole_scan(),
            "source_capture": "PASS_LOCAL_EGNO_PDF_HASH_MATCH",
            "closed_scalar_origin": "PASS_SCHUR_DERIVED_NOT_CALLER_FIELD",
            "identity_resolution_origin": (
                "PASS_ACTUAL_BIPRODUCT_ISOMORPHISM_NOT_NUMERICAL_TABLE"
            ),
        },
        "established": [
            (
                "FusionCategoryData records a finite duplicate-free complete "
                "simple skeleton and an actual finite simple decomposition of "
                "every object."
            ),
            (
                "Finite Hom spaces plus the explicit decomposition encode the "
                "finite semisimple content of EGNO Definition 4.1.1."
            ),
            (
                "Schur's lemma derives the canonical K-linear equivalence "
                "K ≃ End(1) from the listed simple tensor unit."
            ),
            (
                "Closed-diagram scalarization preserves identity, addition, "
                "scalar multiplication, and composition."
            ),
            (
                "Every object and every tensor product of simples has a "
                "kernel-checked finite identity resolution."
            ),
            (
                "RibbonFusionCategoryData binds the Step 1-5 pivotal, "
                "spherical, trace, and quantum-dimension constructions to one "
                "finite semisimple category package."
            ),
        ],
        "definition_boundary": {
            "source": (
                "EGNO Definitions 1.8.1, 1.8.6, and 4.1.1; "
                "Proposition 1.8.4"
            ),
            "unit_condition_encoding": (
                "The interface stores the unit as a simple representative. "
                "In the finite semisimple algebraically closed setting this is "
                "the strengthened proof-relevant form used to derive, rather "
                "than assume, End(1) ≃ K."
            ),
            "semisimplicity_encoding": (
                "Every object carries an explicit finite biproduct "
                "isomorphism to listed simple representatives."
            ),
        },
        "proof_scope": {
            "ambient_typeclasses": [
                "Field K",
                "IsAlgClosed K",
                "Abelian C",
                "Linear K C",
                "MonoidalCategory C",
                "RigidCategory C",
                "MonoidalPreadditive C",
                "MonoidalLinear K C",
            ],
            "stored_fusion_data": [
                "finite simple index type",
                "simple representatives and simplicity proofs",
                "pairwise non-isomorphic guard",
                "completeness among all simple objects",
                "finite-dimensional Hom spaces",
                "actual biproduct decompositions",
                "simple unit representative",
                "right-dual representatives",
            ],
            "derived_not_assumed": [
                "simple Hom dimensions",
                "K-linear scalar equivalence K ≃ End(1)",
                "closed-diagram scalarization laws",
                "finite identity resolutions",
                "canonical pivotal and spherical structures after ribbon input",
            ],
        },
        "remaining_blockers": [
            "Derive the nondegenerate trace pairing and its mate compatibility.",
            "Derive Kirby-colour expansion from the fusion data.",
            "Bind category laws to Kirby moves and assemble the invariant.",
        ],
        "explicit_non_claims": roadmap["explicit_non_claims"],
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


if __name__ == "__main__":
    result = build()
    print(json.dumps({
        "output": str(OUTPUT),
        "status": result["status"],
        "content_hash": result["content_hash"],
    }, indent=2))
