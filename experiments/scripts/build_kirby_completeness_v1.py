#!/usr/bin/env python3
"""Build the terminal R10 Kirby/Cerf topology-boundary certificate."""

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

from twisted_yetter.kirby_completeness_v1 import (  # noqa: E402
    EXCLUDED_FROM_SPECIAL_MOVIE,
    GENERAL_CERF_MOVE_FAMILIES,
    SPECIAL_MOVE_KINDS,
    build_topology_movie_fixture,
    canonical_hash,
    validate_topology_movie,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/kirby-completeness-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "kirby-completeness-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "kirby-completeness-primary-sources-v1.json"
)
R9_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/kirby-cancellation-v1.json"
)
LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/KirbyCompleteness.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/EvaluatorEqualityInsideKirbyCompleteness.lean",
    "lean/Mutations/MissingKirbyCompletenessCaveat.lean",
    "lean/Mutations/ZeroOneAsTableTwoMove.lean",
    "lean/Mutations/HandwrittenMovieTargetCharacter.lean",
    "lean/Mutations/MissingUniqueFourHandle.lean",
    "lean/Mutations/ArbitraryTopologyMoveInjection.lean",
    "lean/Mutations/MissingInducedH2ChainWitness.lean",
    "lean/Mutations/MissingSpecialManifoldBinding.lean",
    "lean/Mutations/MissingLocalTopologyWitness.lean",
]
PYTEST_FILES = [
    "tests/test_kirby_completeness_v1.py",
    "tests/test_kirby_cancellation_v1.py",
    "tests/test_kirby_cancellation_artifact_v1.py",
    "tests/test_framed_link_presentation_independence_v1.py",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "src/twisted_yetter/kirby_completeness_v1.py",
    *MUTATIONS,
    "scripts/lean_kirby_completeness_mutation_tests.sh",
    "experiments/scripts/build_kirby_completeness_v1.py",
    "tests/test_kirby_completeness_v1.py",
    "tests/test_kirby_completeness_artifact_v1.py",
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
    env["UV_CACHE_DIR"] = str(REPO_ROOT / ".uv-cache")
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
                f"forbidden proof-oracle token in {relative}: "
                f"{match.group(0)!r}"
            )
        checked.append(relative)
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": checked,
    }


def whitelist_check() -> dict[str, Any]:
    source = (
        REPO_ROOT / "lean/TwistedYetter/Kirby/KirbyCompleteness.lean"
    ).read_text()
    general_constructors = [
        "levelIsotopy",
        "oneSlide",
        "twoSlide",
        "threeSlide",
        "zeroOneBirth",
        "zeroOneDeath",
        "oneTwoBirth",
        "oneTwoDeath",
        "twoThreeBirth",
        "twoThreeDeath",
        "threeFourBirth",
        "threeFourDeath",
    ]
    special_constructors = [
        "framedIsotopy",
        "oneOverOne",
        "twoOverOne",
        "twoOverTwo",
        "oneTwoBirth",
        "oneTwoDeath",
        "twoThreeBirth",
        "twoThreeDeath",
    ]
    general_region = source.split("inductive GeneralCerfMove", 1)[1].split(
        "/-- Typed finite composition", 1
    )[0]
    special_region = source.split("inductive TableTwoMove", 1)[1].split(
        "namespace TableTwoMove", 1
    )[0]
    for constructor in general_constructors:
        if f"| {constructor}" not in general_region:
            raise AssertionError(
                f"missing general Cerf constructor: {constructor}"
            )
    for constructor in special_constructors:
        if f"| {constructor}" not in special_region:
            raise AssertionError(
                f"missing special Table 2 constructor: {constructor}"
            )
    forbidden_special = [
        "zeroOneBirth",
        "zeroOneDeath",
        "threeSlide",
        "threeFourBirth",
        "threeFourDeath",
        "fromEquality",
        "fromArbitraryRelation",
    ]
    for constructor in forbidden_special:
        if f"| {constructor}" in special_region:
            raise AssertionError(
                f"general/arbitrary constructor entered Table 2: {constructor}"
            )
    evaluator_tokens = [
        "Diagram.eval",
        "EvaluationState",
        "rawNumerator",
        "evaluatorEquality",
    ]
    if any(token in source for token in evaluator_tokens):
        raise AssertionError("topology boundary contains evaluator state")
    mandatory_fields = [
        "uniqueZeroHandle",
        "uniqueFourHandle",
        "represented_manifold_hash_sound",
        "representation_witness",
        "source_scope_caveat",
        "h2ModelCertificateHash",
        "homologyEquiv",
        "induced_by_chain_map_witness",
        "local_topology_witness",
        "tableTwoConnected",
    ]
    if any(field not in source for field in mandatory_fields):
        raise AssertionError("mandatory topology-boundary field is missing")
    return {
        "status": "PASS_DISTINCT_GENERAL_AND_SPECIAL_CLOSED_WHITELISTS",
        "general_constructor_count": len(general_constructors),
        "general_constructors": general_constructors,
        "special_constructor_count": len(special_constructors),
        "special_constructors": special_constructors,
        "special_excluded_general_or_arbitrary_constructors": forbidden_special,
        "evaluator_state_or_equality_included": False,
        "mandatory_fields": mandatory_fields,
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
        raise RuntimeError("R10 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    references = json.loads(REFERENCES.read_text())
    rows = obligations["obligations"]
    if len(rows) != 34 or any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN"}
        for row in rows
    ):
        raise AssertionError("R10 obligation matrix is not terminal")
    if len(obligations["trusted_inputs"]) != 2:
        raise AssertionError("R10 must expose exactly two topology inputs")

    r9 = json.loads(R9_ARTIFACT.read_text())
    if r9["status"] != (
        "PASS_ALL_BARENZ_BARRETT_TABLE2_LOCAL_KIRBY_MOVES"
    ):
        raise AssertionError("pinned R9 artifact is not passing")

    fixture = build_topology_movie_fixture()
    validate_topology_movie(fixture)

    refs = {
        reference["ref_id"]: reference
        for reference in references["references"]
    }
    expected_refs = {
        "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
        "ref:de-sa-link-calculus-1979",
        "ref:baerenz-barrett-dichromatic-2018",
        "ref:local-r9-kirby-cancellation",
        "ref:local-r8-kirby-handle-moves",
    }
    if set(refs) != expected_refs:
        raise AssertionError("R10 reference denominator is stale")
    gs = refs["ref:gompf-stipsicz-4-manifolds-kirby-calculus"]
    if gs["exact_byte_capture"]["status"] != (
        "NO_REPO_LOCAL_PRIMARY_BYTES"
    ):
        raise AssertionError("GS byte-capture limitation was hidden")
    de_sa = refs["ref:de-sa-link-calculus-1979"]
    if de_sa["exact_byte_capture"]["status"] != (
        "METADATA_ONLY_NO_CHAPTER_BYTES"
    ):
        raise AssertionError("de Sa access limitation was hidden")
    bb_capture = refs[
        "ref:baerenz-barrett-dichromatic-2018"
    ]["captured_pdf"]
    capture_path = Path(bb_capture["capture_path_at_capture_time"])
    if not capture_path.exists():
        raise RuntimeError("Bärenz-Barrett local source capture is absent")
    if sha256_path(capture_path) != bb_capture["sha256"]:
        raise AssertionError("Bärenz-Barrett source hash mismatch")

    build_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = run(["./scripts/lean_axiom_audit.sh"])
    axiom_output = clean_output(axiom_result.stdout + axiom_result.stderr)
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("axiom audit exposed a proof hole or native oracle")
    declaration_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if declaration_count != 80:
        raise AssertionError(
            f"expected 80 audited Kirby declarations, got {declaration_count}"
        )

    mutation_result = run(
        ["./scripts/lean_kirby_completeness_mutation_tests.sh"]
    )
    mutation_output = clean_output(
        mutation_result.stdout + mutation_result.stderr
    )
    rejections = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != len(MUTATIONS):
        raise AssertionError(
            f"expected {len(MUTATIONS)} rejected R10 Lean mutations"
        )

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None:
        raise AssertionError("R10 scoped pytest did not report pass")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.kirby-completeness-boundary.v1",
        "status": "PASS_KIRBY_CERF_TOPOLOGY_BOUNDARY",
        "mathematical_status": (
            "R10_TOPOLOGY_BOUNDARY_ESTABLISHED_AS_TWO_EXPLICIT_"
            "SOURCE_BACKED_INPUTS_NOT_REPROVED_IN_LEAN"
        ),
        "roadmap_status": "R10_TERMINAL_R11_NOT_STARTED",
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_kirby_completeness_v1.py"
        ),
        "argv": ["experiments/scripts/build_kirby_completeness_v1.py"],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_kirby_completeness_v1.py"
        ),
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": version(["lake", "env", "lean", "--version"]),
            "lake": version(["lake", "--version"]),
            "uv": version(["uv", "--version"]),
            "mathlib_tag": "v4.29.1",
            "mathlib_commit": git(
                "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"
            ),
        },
        "inputs": {
            "r9_local_move_artifact": {
                "path": str(R9_ARTIFACT.relative_to(REPO_ROOT)),
                "sha256": sha256_path(R9_ARTIFACT),
                "content_hash": r9["content_hash"],
                "source_commit": r9["git"]["commit"],
            },
            "obligation_matrix": {
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "sha256": sha256_path(OBLIGATIONS),
                "obligation_count": len(rows),
                "trusted_input_count": len(obligations["trusted_inputs"]),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "sha256": sha256_path(REFERENCES),
                "reference_count": len(references["references"]),
            },
            "byte_pinned_primary_source": {
                "path_at_capture_time": str(capture_path),
                "bytes": capture_path.stat().st_size,
                "sha256": sha256_path(capture_path),
                "status": "PASS_BARENZ_BARRETT_CAPTURE_MATCH",
            },
            "source_capture_limitations": {
                "gompf_stipsicz": gs["exact_byte_capture"],
                "de_sa": de_sa["exact_byte_capture"],
                "status": "PASS_LIMITATIONS_NOT_HIDDEN",
            },
            "source_files": source_files,
        },
        "topology_boundary": {
            "status": "PASS_TWO_LAYERS_SEPARATELY_VISIBLE",
            "general_cerf": fixture["completeness_boundary"][
                "general_cerf"
            ],
            "table_two_link_refinement": fixture[
                "completeness_boundary"
            ]["table_two_link_refinement"],
            "general_move_family_count": len(
                GENERAL_CERF_MOVE_FAMILIES
            ),
            "special_directed_constructor_count": len(SPECIAL_MOVE_KINDS),
            "special_excluded_general_moves": list(
                EXCLUDED_FROM_SPECIAL_MOVIE
            ),
            "derived_from_general_cerf_in_lean": False,
            "evaluator_equality_included": False,
        },
        "lean_certificate": {
            "status": "PASS_LEAN_KERNEL_AND_NEGATIVE_MUTATIONS",
            "build_order": LEAN_BUILD_ORDER,
            "build_output": clean_output(
                build_result.stdout + build_result.stderr
            ),
            "audited_declaration_count": declaration_count,
            "axiom_audit": {
                "status": "PASS_NO_SORRYAX_OR_NATIVE_ORACLE",
                "output": axiom_output,
            },
            "proof_hole_scan": proof_hole_scan(),
            "mutation_rejections": rejections,
            "mutation_count": len(rejections),
        },
        "runtime_certificate": {
            "status": "PASS_HASHED_MOVIE_AND_H2_TRANSPORT",
            "fixture": fixture,
            "special_move_coverage": (
                "PASS_EIGHT_OF_EIGHT_DIRECTED_CONSTRUCTORS"
            ),
            "composite_h2_transport": fixture[
                "composite_h2_transport"
            ],
        },
        "checks": {
            "whitelists": whitelist_check(),
            "scoped_pytest": {
                "status": "PASS",
                "files": PYTEST_FILES,
                "passed_count": int(match.group(1)),
                "output": pytest_output,
            },
            "source_scope_honesty": {
                "status": "PASS_NO_SCOPE_COLLAPSE",
                "general_cerf_and_table_two_are_distinct_inputs": True,
                "gs_bytes_locally_pinned": False,
                "de_sa_bytes_locally_pinned": False,
                "baerenz_barrett_bytes_locally_pinned": True,
            },
        },
        "trusted_topology_inputs": obligations["trusted_inputs"],
        "explicit_non_claims": obligations["explicit_non_claims"],
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


if __name__ == "__main__":
    result = build()
    print(
        json.dumps(
            {
                "output": str(OUTPUT.relative_to(REPO_ROOT)),
                "status": result["status"],
                "mathematical_status": result["mathematical_status"],
                "content_hash": result["content_hash"],
                "git": result["git"],
            },
            indent=2,
            sort_keys=True,
        )
    )
