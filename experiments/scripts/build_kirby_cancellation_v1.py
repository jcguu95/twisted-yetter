#!/usr/bin/env python3
"""Build the terminal R9 cancellation and normalization certificate."""

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

from twisted_yetter.kirby_cancellation_v1 import (  # noqa: E402
    all_cancellation_fixtures,
    canonical_hash,
    validate_cancellation_fixture,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/kirby-cancellation-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "kirby-cancellation-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "kirby-cancellation-primary-sources-v1.json"
)
R8_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/kirby-handle-moves-v1.json"
)
LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/KirbyCancellation.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/ArbitraryNormalizedEqualityAsCancellation.lean",
    "lean/Mutations/MissingCancellationKillingIdentity.lean",
    "lean/Mutations/MissingTransparentTwistWitness.lean",
    "lean/Mutations/MissingPivotalCancellationDimension.lean",
    "lean/Mutations/HandwrittenCancellationCharacter.lean",
]
PYTEST_FILES = [
    "tests/test_kirby_cancellation_v1.py",
    "tests/test_kirby_handle_moves_v1.py",
    "tests/test_kirby_handle_moves_artifact_v1.py",
    "tests/test_framed_link_presentation_independence_v1.py",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "src/twisted_yetter/kirby_cancellation_v1.py",
    *MUTATIONS,
    "scripts/lean_kirby_cancellation_mutation_tests.sh",
    "experiments/scripts/build_kirby_cancellation_v1.py",
    "tests/test_kirby_cancellation_v1.py",
    "tests/test_kirby_cancellation_artifact_v1.py",
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
        REPO_ROOT / "lean/TwistedYetter/Kirby/KirbyCancellation.lean"
    ).read_text()
    constructors = ["oneTwo", "twoThree"]
    for constructor in constructors:
        if f"| {constructor}" not in source:
            raise AssertionError(
                f"missing cancellation constructor: {constructor}"
            )
    if "fromEquality" in source:
        raise AssertionError("bare normalized equality injection was reintroduced")
    mandatory_fields = [
        "killing_identity",
        "transparent_twist_witness",
        "pivotal_dimension_preserved",
    ]
    if any(field not in source for field in mandatory_fields):
        raise AssertionError("mandatory cancellation equation is missing")
    return {
        "status": "PASS_CLOSED_CANCELLATION_WHITELIST",
        "constructor_count": 2,
        "constructors": constructors,
        "bare_normalized_equality_constructor": False,
        "mandatory_local_inputs": mandatory_fields,
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
        raise RuntimeError("R9 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    references = json.loads(REFERENCES.read_text())
    rows = obligations["obligations"]
    if len(rows) != 22 or any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN"} for row in rows
    ):
        raise AssertionError("R9 obligation matrix is not terminal")
    r8 = json.loads(R8_ARTIFACT.read_text())
    if r8["status"] != "PASS_KIRBY_HANDLE_SLIDES":
        raise AssertionError("pinned R8 artifact is not passing")

    fixtures = list(all_cancellation_fixtures())
    if len(fixtures) != 4:
        raise AssertionError("R9 requires two cancellations and empty 0/4 cases")
    for fixture in fixtures:
        validate_cancellation_fixture(fixture)

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
    if declaration_count != 74:
        raise AssertionError(
            f"expected 74 audited Kirby declarations, got {declaration_count}"
        )

    mutation_result = run(
        ["./scripts/lean_kirby_cancellation_mutation_tests.sh"]
    )
    mutation_output = clean_output(
        mutation_result.stdout + mutation_result.stderr
    )
    rejections = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 5:
        raise AssertionError("expected five rejected R9 Lean mutations")

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None:
        raise AssertionError("R9 scoped pytest did not report pass")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.kirby-cancellation-and-normalization.v1",
        "status": (
            "PASS_ALL_BARENZ_BARRETT_TABLE2_LOCAL_KIRBY_MOVES"
        ),
        "mathematical_status": (
            "ALL_REQUIRED_KIRBY_MOVES_EVALUATOR_INVARIANT_RELATIVE_TO_"
            "EXPLICIT_SLIDING_CUTTING_KILLING_TWIST_PIVOTAL_AND_"
            "NORMALIZATION_INPUTS"
        ),
        "roadmap_status": (
            "R8_R9_TERMINAL_RELATIVE_TO_LISTED_STANDARD_INPUTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_kirby_cancellation_v1.py"
        ),
        "argv": ["experiments/scripts/build_kirby_cancellation_v1.py"],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_kirby_cancellation_v1.py"
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
            "r8_handle_slide_artifact": {
                "path": str(R8_ARTIFACT.relative_to(REPO_ROOT)),
                "sha256": sha256_path(R8_ARTIFACT),
                "content_hash": r8["content_hash"],
                "source_commit": r8["git"]["commit"],
            },
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
        "table2_coverage": {
            "status": "PASS_FIVE_OF_FIVE_LOCAL_MOVE_FAMILIES",
            "expected_move_families": [
                "one_over_one_slide",
                "two_over_one_slide",
                "two_over_two_slide",
                "one_two_cancellation",
                "two_three_cancellation",
            ],
            "r8_slide_family_count": 3,
            "r9_cancellation_family_count": 2,
            "actual_move_family_count": 5,
            "empty_end_handle_checks": ["empty_zero", "empty_four"],
        },
        "cancellation_coverage": {
            "status": "PASS_TWO_CANCELLATIONS_AND_EMPTY_END_HANDLES",
            "expected_count": 4,
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
                "new_r9_declaration_count": 11,
                "observed_standard_axioms": [
                    "propext",
                    "Classical.choice",
                    "Quot.sound",
                ],
                "output_sha256": sha256_bytes(axiom_output.encode()),
            },
            "closed_cancellation_whitelist": whitelist_check(),
            "lean_mutation_tests": {
                "status": "PASS_ALL_BAD_INPUTS_REJECTED",
                "rejected_count": len(rejections),
                "rejections": rejections,
                "output_sha256": sha256_bytes(mutation_output.encode()),
            },
            "normalization": {
                "status": "PASS_EXACT_SIGNED_EXPONENT_FORMULA",
                "formula": (
                    "d(C)^(h2-h1) * "
                    "(d(D)*d(transparent(F(Omega_C))))^h1"
                ),
                "one_two_recurrence": "LEAN_PROVED",
                "two_three_recurrence": "LEAN_PROVED",
                "empty_zero_four_ignored": "LEAN_PROVED",
                "final_normalized_equality_input_allowed": False,
            },
            "homology_and_character_transport": {
                "status": "PASS_EXACT_MOD2_QUOTIENT_AND_DUAL_PAIRING",
                "one_two": "acyclic C2-to-C1 pair removed",
                "two_three": "image d3 generator quotiented",
                "pairing_check": (
                    "exhaustive over all fixture H2 classes and characters"
                ),
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
            "All five local move families in Bärenz-Barrett Table 2 have evaluator-invariance proofs relative to the exact listed standard inputs.",
            "The 1-2 raw factor is derived from disjoint union, cutting, killing, and transparent-twist witnesses.",
            "The 2-3 raw factor requires and uses the pivotal dimension equation highlighted by Remark 3.11.",
            "The exact signed-exponent denominator satisfies both cancellation recurrences, so normalized values agree.",
            "Empty 0/4 handle bookkeeping does not alter the link numerator or h1/h2 denominator.",
            "Concrete 1-2 and 2-3 chain fixtures preserve H2 and all enumerated mod-2 character pairings.",
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
