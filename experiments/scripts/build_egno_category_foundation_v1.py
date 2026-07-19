#!/usr/bin/env python3
"""Build the source-bound EGNO category-foundation certificate."""

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
    / "experiments/results/lean-kirby/egno-category-foundation-v1.json"
)
MATRIX = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-category-foundation-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "egno-category-foundations-primary-sources-v1.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_category_foundation_v1.py",
    "tests/test_egno_category_foundation_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNORibbon.lean",
    "lean/TwistedYetter/Fusion/EGNORibbonAxiomAudit.lean",
    "lean/TwistedYetter/Fusion/AxiomAudit.lean",
    "lean/TwistedYetter/Kirby/FramingNaturality.lean",
    "lean/TwistedYetter/Kirby/PresentationIsotopy.lean",
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean",
    "lean/TwistedYetter/Kirby/TableTwoEvaluatorCompiler.lean",
    "lean/TwistedYetter/Kirby/FinalFormalizationPackage.lean",
    "lean/Mutations/MissingPivotalMonoidality.lean",
    "lean/Mutations/MissingSphericalDimensionDual.lean",
    "lean/Mutations/MissingBalancingTensor.lean",
    "lean/Mutations/MissingRibbonDual.lean",
    "lean/Mutations/MissingFramedKinkCompatibility.lean",
    "lean/Mutations/MissingSphericalCutCyclicity.lean",
    "lean/Mutations/ArbitraryCertifiedMoveAsIsotopy.lean",
    "lean/Mutations/MissingPresentationCompleteness.lean",
    "lean/Mutations/MissingPresentationCompletenessCaveat.lean",
    "scripts/lean_egno_ribbon_axiom_audit.sh",
    "scripts/lean_egno_ribbon_mutation_tests.sh",
    "scripts/lean_presentation_isotopy_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    str(MATRIX.relative_to(REPO_ROOT)),
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
        raise RuntimeError(
            "EGNO category-foundation artifact requires a clean source commit"
        )

    matrix = json.loads(MATRIX.read_text())
    references = json.loads(REFERENCES.read_text())
    counts = matrix["terminal_counts"]
    if counts != {
        "established_or_explicit_standard_input": 12,
        "not_yet_formalized_or_not_yet_derived": 4,
        "total": 16,
    }:
        raise AssertionError("unexpected category obligation denominator")

    capture = references["references"][0]["captured_pdf"]
    capture_path = Path(capture["capture_path_at_capture_time"])
    if not capture_path.exists():
        raise AssertionError("the pinned local EGNO PDF is absent")
    if capture_path.stat().st_size != capture["bytes"]:
        raise AssertionError("the pinned EGNO PDF size changed")
    if sha256_path(capture_path) != capture["sha256"]:
        raise AssertionError("the pinned EGNO PDF hash changed")

    module_text = (
        REPO_ROOT / "lean/TwistedYetter/Fusion/EGNORibbon.lean"
    ).read_text()
    required_contracts = [
        "structure PivotalStructure",
        "monoidal : IsPivotalIso",
        "structure SphericalStructure",
        "dimension_dual",
        "structure SphericalTraceLaws",
        "structure BalancedTwist",
        "structure RibbonStructure",
        "dual : (X : C)",
    ]
    missing = [
        contract for contract in required_contracts
        if contract not in module_text
    ]
    if missing:
        raise AssertionError(f"missing EGNO contracts: {missing}")

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(["./scripts/lean_egno_ribbon_axiom_audit.sh"])
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("EGNO axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 9:
        raise AssertionError(
            f"expected 9 audited declarations, got {audited_declarations}"
        )

    category_mutations = run(
        ["./scripts/lean_egno_ribbon_mutation_tests.sh"]
    )
    category_rejections = [
        line for line in category_mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(category_rejections) != 4:
        raise AssertionError("expected four rejected category mutations")

    presentation_mutations = run(
        ["./scripts/lean_presentation_isotopy_mutation_tests.sh"]
    )
    presentation_rejections = [
        line for line in presentation_mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(presentation_rejections) != 5:
        raise AssertionError("expected five rejected presentation mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-category-foundation.v1",
        "status": "PASS_EGNO_CATEGORY_INTERFACES_AND_KIRBY_BINDINGS",
        "mathematical_status": (
            "PARTIAL_CATEGORY_FOUNDATION_ESTABLISHED_WITH_"
            "EXPLICIT_STANDARD_THEOREM_INPUTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_egno_category_foundation_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_egno_category_foundation_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_egno_category_foundation_v1.py"
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
            "obligation_matrix": {
                "path": str(MATRIX.relative_to(REPO_ROOT)),
                "sha256": sha256_path(MATRIX),
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
                "output_tail": (
                    build_result.stdout + build_result.stderr
                ).strip().splitlines()[-1],
            },
            "axiom_audit": {
                "status": "PASS_NO_SORRYAX_OR_NATIVE_ORACLE",
                "audited_declaration_count": audited_declarations,
            },
            "category_mutations": {
                "status": "PASS_FAIL_CLOSED",
                "rejected_count": len(category_rejections),
                "rejections": category_rejections,
            },
            "presentation_mutations": {
                "status": "PASS_FAIL_CLOSED",
                "rejected_count": len(presentation_rejections),
                "rejections": presentation_rejections,
            },
            "proof_hole_scan": proof_hole_scan(),
            "source_capture": "PASS_LOCAL_EGNO_PDF_HASH_MATCH",
        },
        "established": [
            "PivotalStructure requires a monoidal double-dual isomorphism.",
            "The EGNO left pivotal trace and pivotal dimension are explicit Lean morphisms.",
            "SphericalStructure requires equality of dimensions under duality.",
            "BalancedTwist enforces equation (8.32).",
            "RibbonStructure enforces dual compatibility.",
            "Kirby framing accepts a ribbon twist instead of an arbitrary natural automorphism.",
            "Kirby closure is the pivotal trace attached to a spherical structure.",
            "The final invariant route now exposes its rigidity requirement."
        ],
        "remaining_blockers": [
            "Formalize a finite semisimple fusion-category interface.",
            "Formalize the canonical ribbon-to-spherical pivotal construction of EGNO Proposition 8.10.12.",
            "Derive PivotalTraceCompatibility from a formal pivotal functor.",
            "Derive SphericalMateCompatibility from the formal spherical trace calculus."
        ],
        "explicit_non_claims": matrix["explicit_non_claims"],
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
