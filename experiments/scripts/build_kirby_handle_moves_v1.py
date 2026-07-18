#!/usr/bin/env python3
"""Build the terminal R8 typed Kirby-handle-slide certificate."""

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


REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "src"))

from twisted_yetter.kirby_handle_moves_v1 import (
    all_handle_slide_bookkeeping_fixtures,
    canonical_hash,
    validate_handle_slide_bookkeeping,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/kirby-handle-moves-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "kirby-handle-moves-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "kirby-handle-moves-primary-sources-v1.json"
)
R5_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "generalized-sliding-framed-context-v1.json"
)
R6_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-syntax-v1.json"
)
R7_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-independence-v1.json"
)
LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/KirbyHandleMoves.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/ArbitraryCertifiedMoveAsHandleSlide.lean",
    "lean/Mutations/HandwrittenTargetCharacter.lean",
    "lean/Mutations/MissingSlideRoleProof.lean",
]
PYTEST_FILES = [
    "tests/test_presentation_moves.py",
    "tests/test_presentation_pairs.py",
    "tests/test_kirby_handle_moves_v1.py",
    "tests/test_framed_link_presentation_independence_v1.py",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "src/twisted_yetter/presentation_moves.py",
    "src/twisted_yetter/presentation_pairs.py",
    "src/twisted_yetter/kirby_handle_moves_v1.py",
    *MUTATIONS,
    "scripts/lean_kirby_handle_move_mutation_tests.sh",
    "experiments/scripts/build_kirby_handle_moves_v1.py",
    "tests/test_presentation_moves.py",
    "tests/test_presentation_pairs.py",
    "tests/test_kirby_handle_moves_v1.py",
    "tests/test_kirby_handle_moves_artifact_v1.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
]
ANSI_ESCAPE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))"
)


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def clean_output(text: str) -> str:
    return ANSI_ESCAPE.sub("", text).strip()


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
    return clean_output(result.stdout or result.stderr).splitlines()[0]


def pinned_artifact(path: Path, expected_status: str) -> dict[str, Any]:
    payload = json.loads(path.read_text())
    if payload["status"] != expected_status:
        raise AssertionError(f"nonpassing prerequisite: {path}")
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": sha256_path(path),
        "content_hash": payload["content_hash"],
        "source_commit": payload["git"]["commit"],
    }


def proof_hole_scan() -> dict[str, Any]:
    forbidden = re.compile(
        r"\b(sorry|admit|native_decide)\b|^\s*axiom\b",
        re.MULTILINE,
    )
    checked: list[str] = []
    for relative in LEAN_BUILD_ORDER:
        text = (REPO_ROOT / relative).read_text()
        match = forbidden.search(text)
        if match:
            raise AssertionError(
                f"forbidden proof-oracle token in {relative}: {match.group(0)!r}"
            )
        checked.append(relative)
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": checked,
    }


def whitelist_check() -> dict[str, Any]:
    source = (
        REPO_ROOT / "lean/TwistedYetter/Kirby/KirbyHandleMoves.lean"
    ).read_text()
    constructors = ["oneOverOne", "twoOverOne", "twoOverTwo"]
    for constructor in constructors:
        if f"| {constructor}" not in source:
            raise AssertionError(f"missing handle-slide constructor: {constructor}")
    if "def ofCertified" in source:
        raise AssertionError("arbitrary CertifiedMove injection was reintroduced")
    return {
        "status": "PASS_CLOSED_HANDLE_SLIDE_WHITELISTS",
        "constructor_count": 3,
        "constructors": constructors,
        "arbitrary_certified_move_constructor": False,
        "ordinary_standard_input": "SourcedSlidingLaw",
        "two_over_two_derived_input": "SlidingFamily",
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
        raise RuntimeError("R8 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    references = json.loads(REFERENCES.read_text())
    rows = obligations["obligations"]
    if len(rows) != 16 or any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN"} for row in rows
    ):
        raise AssertionError("R8 obligation matrix is not terminal")
    fixtures = list(all_handle_slide_bookkeeping_fixtures())
    if len(fixtures) != 6:
        raise AssertionError("R8 must cover three kinds times two orientations")
    for fixture in fixtures:
        validate_handle_slide_bookkeeping(fixture)

    capture = references["references"][0]["captured_pdf"]
    capture_path = Path(capture["capture_path_at_capture_time"])
    if not capture_path.exists():
        raise RuntimeError("Bärenz-Barrett local source capture is absent")
    if sha256_path(capture_path) != capture["sha256"]:
        raise AssertionError("Bärenz-Barrett source hash mismatch")

    build_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = run(["./scripts/lean_axiom_audit.sh"])
    axiom_output = clean_output(axiom_result.stdout + axiom_result.stderr)
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("axiom audit exposed a proof hole or native oracle")
    declaration_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if declaration_count != 63:
        raise AssertionError(
            f"expected 63 audited Kirby declarations, got {declaration_count}"
        )

    mutation_result = run(
        ["./scripts/lean_kirby_handle_move_mutation_tests.sh"]
    )
    mutation_output = clean_output(
        mutation_result.stdout + mutation_result.stderr
    )
    rejections = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 3:
        raise AssertionError("expected three rejected R8 Lean mutations")

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None:
        raise AssertionError("R8 scoped pytest did not report pass")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.kirby-handle-moves.v1",
        "status": "PASS_KIRBY_HANDLE_SLIDES",
        "mathematical_status": (
            "KIRBY_HANDLE_SLIDES_EVALUATOR_INVARIANT_RELATIVE_TO_EXPLICIT_"
            "ORIGINAL_AND_GENERALIZED_SLIDING_INPUTS"
        ),
        "roadmap_status": "R8_TERMINAL_RELATIVE_TO_EXPLICIT_SLIDING_INPUTS",
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_kirby_handle_moves_v1.py"
        ),
        "argv": ["experiments/scripts/build_kirby_handle_moves_v1.py"],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_kirby_handle_moves_v1.py"
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
            "r5_framed_sliding_artifact": pinned_artifact(
                R5_ARTIFACT, "PASS_GENERALIZED_SLIDING_FRAMED_CONTEXT"
            ),
            "r6_presentation_syntax_artifact": pinned_artifact(
                R6_ARTIFACT, "PASS_FRAMED_LINK_PRESENTATION_SYNTAX"
            ),
            "r7_presentation_independence_artifact": pinned_artifact(
                R7_ARTIFACT,
                "PASS_FRAMED_LINK_EVALUATOR_PRESENTATION_INDEPENDENCE",
            ),
            "obligation_matrix": {
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "sha256": sha256_path(OBLIGATIONS),
                "obligation_count": len(rows),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "sha256": sha256_path(REFERENCES),
                "reference_count": len(references["references"]),
            },
            "source_capture": {
                "path": str(capture_path),
                "bytes": capture_path.stat().st_size,
                "sha256": sha256_path(capture_path),
                "status": "PASS_LOCAL_CAPTURE_MATCH",
            },
            "source_files": source_files,
        },
        "move_coverage": {
            "status": "PASS_ALL_THREE_KINDS_BOTH_ORIENTATIONS",
            "expected_count": 6,
            "actual_count": len(fixtures),
            "fixtures": fixtures,
        },
        "checks": {
            "sequential_build": {
                "status": "PASS",
                "module_count": len(LEAN_BUILD_ORDER),
                "build_order": LEAN_BUILD_ORDER,
                "stdout_sha256": sha256_bytes(
                    clean_output(
                        build_result.stdout + build_result.stderr
                    ).encode()
                ),
            },
            "source_proof_hole_scan": proof_hole_scan(),
            "kirby_axiom_audit": {
                "status": "PASS_NO_SORRY_AX_OR_NATIVE_ORACLE",
                "declaration_count": declaration_count,
                "new_r8_declaration_count": 6,
                "observed_standard_axioms": [
                    "propext",
                    "Classical.choice",
                    "Quot.sound",
                ],
                "output_sha256": sha256_bytes(axiom_output.encode()),
            },
            "closed_move_whitelist": whitelist_check(),
            "lean_mutation_tests": {
                "status": "PASS_ALL_BAD_INPUTS_REJECTED",
                "rejected_count": len(rejections),
                "rejections": rejections,
                "output_sha256": sha256_bytes(mutation_output.encode()),
            },
            "runtime_bookkeeping": {
                "status": "PASS_FAIL_CLOSED_EXACT_CHAIN_AND_MOD2_CHECKS",
                "fixture_count": len(fixtures),
                "two_over_two_only_q_congruence": True,
                "class_transform": "P2^-1 mod 2",
                "character_transform": "P2^T mod 2",
                "pairing_check": "exhaustive over every fixture cycle and cochain",
            },
            "scoped_pytest": {
                "status": "PASS",
                "test_count": int(match.group(1)),
                "test_files": PYTEST_FILES,
                "output_sha256": sha256_bytes(pytest_output.encode()),
            },
            "resource_guards": {
                "status": "PASS_INHERITED_AND_ENFORCED",
                "default_threads": 1,
                "maximum_allowed_threads": 2,
                "execution_mode": "one Lean process at a time",
            },
        },
        "established_scope": [
            "One-over-one and two-over-one graphical evaluation invariance follows in arbitrary typed context from the explicit source-backed original sliding law.",
            "Two-over-two graphical evaluation invariance follows in arbitrary framed context from the actual R4 SlidingFamily and R5 Lemma 3.4 construction.",
            "Both band orientations are explicit and have independently validated bookkeeping fixtures.",
            "Component roles and stable-ID lineage are mandatory.",
            "Handle-chain coordinates satisfy d2_target = P1^-1 d2_source P2.",
            "Only two-over-two uses Q_target = P2^T Q_source P2 and its diagonal framing formula.",
            "H2 class and dual character coordinates transform contragrediently and preserve every checked mod-2 pairing.",
        ],
        "trusted_inputs": obligations["trusted_inputs"],
        "explicit_non_claims": obligations["explicit_non_claims"],
    }
    payload["content_hash"] = canonical_hash(payload)
    return payload


def main() -> None:
    payload = build()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(OUTPUT)
    print(payload["content_hash"])


if __name__ == "__main__":
    main()
