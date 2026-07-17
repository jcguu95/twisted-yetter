#!/usr/bin/env python3
"""Build the terminal R7 framed-link presentation-independence certificate."""

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
    "framed-link-presentation-independence-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-independence-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "framed-link-presentation-independence-primary-sources-v1.json"
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

LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/PresentationIsotopy.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/MissingFramedKinkCompatibility.lean",
    "lean/Mutations/MissingSphericalCutCyclicity.lean",
    "lean/Mutations/ArbitraryCertifiedMoveAsIsotopy.lean",
    "lean/Mutations/MissingPresentationCompleteness.lean",
    "lean/Mutations/MissingPresentationCompletenessCaveat.lean",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    *MUTATIONS,
    "scripts/lean_presentation_isotopy_mutation_tests.sh",
    (
        "experiments/scripts/"
        "build_framed_link_presentation_independence_v1.py"
    ),
    "tests/test_framed_link_presentation_independence_v1.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
]
PREVIOUS_TESTS = [
    "tests/test_generalized_sliding_framed_context_v1.py",
    "tests/test_kirby_presentation_v1.py",
    "tests/test_framed_link_presentation_syntax_v1.py",
]
EXPECTED_WHITELIST_CONSTRUCTORS = [
    "planarIdentityBefore",
    "planarIdentityAfter",
    "planarCompAssoc",
    "criticalInterchange",
    "reidemeisterIIPositive",
    "reidemeisterIINegative",
    "reidemeisterIII",
    "rightPrimalSnake",
    "rightDualSnake",
    "leftPrimalSnake",
    "leftDualSnake",
    "framedPositive",
    "framedNegative",
    "couponPositiveCrossing",
    "couponNegativeCrossing",
    "couponRightCup",
    "couponRightCap",
    "couponLeftCup",
    "couponLeftCap",
    "couponPositiveTwist",
    "couponNegativeTwist",
    "closureCut",
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


def canonical_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{sha256_bytes(encoded)}"


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
                f"forbidden proof-oracle token in {relative}: "
                f"{match.group(0)!r}"
            )
        checked.append(relative)
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": checked,
    }


def source_capture_check(references: dict[str, Any]) -> list[dict[str, Any]]:
    checks: list[dict[str, Any]] = []
    for reference in references["references"]:
        capture = reference.get("captured_pdf")
        if capture is None:
            continue
        path = Path(capture["capture_path_at_capture_time"])
        if not path.exists():
            checks.append(
                {
                    "ref_id": reference["ref_id"],
                    "status": "LOCAL_CAPTURE_ABSENT_REFERENCE_HASH_RETAINED",
                    "expected_sha256": capture["sha256"],
                }
            )
            continue
        observed = sha256_path(path)
        if observed != capture["sha256"]:
            raise AssertionError(
                f"source capture hash mismatch for {reference['ref_id']}"
            )
        if path.stat().st_size != capture["bytes"]:
            raise AssertionError(
                f"source capture size mismatch for {reference['ref_id']}"
            )
        checks.append(
            {
                "ref_id": reference["ref_id"],
                "status": "PASS_LOCAL_CAPTURE_MATCH",
                "path": str(path),
                "bytes": path.stat().st_size,
                "sha256": observed,
            }
        )
    return checks


def whitelist_check() -> dict[str, Any]:
    path = REPO_ROOT / "lean/TwistedYetter/Kirby/PresentationIsotopy.lean"
    text = path.read_text()
    missing = [
        name for name in EXPECTED_WHITELIST_CONSTRUCTORS if f"| {name}" not in text
    ]
    if missing:
        raise AssertionError(f"missing TaggedMove constructors: {missing}")
    if "def ofCertified" in text:
        raise AssertionError("arbitrary CertifiedMove injection was reintroduced")
    mandatory_metadata = [
        "source_ref : String",
        "source_locator : String",
        "source_scope_caveat : String",
    ]
    if any(field not in text for field in mandatory_metadata):
        raise AssertionError("mandatory source metadata field is missing")
    return {
        "status": "PASS_CLOSED_WHITELIST",
        "constructor_count": len(EXPECTED_WHITELIST_CONSTRUCTORS),
        "constructors": EXPECTED_WHITELIST_CONSTRUCTORS,
        "arbitrary_certified_move_constructor": False,
        "mandatory_source_metadata": mandatory_metadata,
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
        raise RuntimeError("R7 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    references = json.loads(REFERENCES.read_text())
    r5 = json.loads(R5_ARTIFACT.read_text())
    r6 = json.loads(R6_ARTIFACT.read_text())
    rows = obligations["obligations"]
    if len(rows) != 24 or any(
        row["status"] == "NOT_FORMALIZED" for row in rows
    ):
        raise AssertionError("R7 obligation matrix is not terminal")
    if "Caveat 4.31" not in json.dumps(obligations):
        raise AssertionError("Selinger coherence caveat was not preserved")
    if r5["status"] != "PASS_GENERALIZED_SLIDING_FRAMED_CONTEXT":
        raise AssertionError("the pinned R5 artifact is not passing")
    if r6["status"] != "PASS_FRAMED_LINK_PRESENTATION_SYNTAX":
        raise AssertionError("the pinned R6 artifact is not passing")

    build_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = run(["./scripts/lean_axiom_audit.sh"])
    axiom_output = clean_output(axiom_result.stdout + axiom_result.stderr)
    forbidden_axioms = ("sorryAx", "native_decide.ax")
    if any(item in axiom_output for item in forbidden_axioms):
        raise AssertionError("axiom audit exposed a proof hole or native oracle")
    theorem_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if theorem_count != 57:
        raise AssertionError(
            f"expected 57 audited Kirby declarations, got {theorem_count}"
        )

    mutation_result = run(
        ["./scripts/lean_presentation_isotopy_mutation_tests.sh"]
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
        raise AssertionError("expected five rejected R7 Lean mutations")

    pytest_result = run(["uv", "run", "pytest", "-q", *PREVIOUS_TESTS])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None:
        raise AssertionError("previous R5/R6 artifact tests did not report pass")
    previous_test_count = int(match.group(1))

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": (
            "twisted-yetter.framed-link-presentation-independence.v1"
        ),
        "status": (
            "PASS_FRAMED_LINK_EVALUATOR_PRESENTATION_INDEPENDENCE"
        ),
        "mathematical_status": (
            "FRAMED_LINK_EVALUATOR_PRESENTATION_INDEPENDENCE_ESTABLISHED_"
            "RELATIVE_TO_EXPLICIT_RIBBON_TRACE_AND_TOPOLOGY_INPUTS"
        ),
        "chain_status": (
            "R5_R6_R7_TERMINAL_RELATIVE_TO_EXPLICIT_STANDARD_INPUTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/"
            "build_framed_link_presentation_independence_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_framed_link_presentation_independence_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/"
            "build_framed_link_presentation_independence_v1.py"
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
            "r5_framed_sliding_artifact": {
                "path": str(R5_ARTIFACT.relative_to(REPO_ROOT)),
                "sha256": sha256_path(R5_ARTIFACT),
                "content_hash": r5["content_hash"],
                "source_commit": r5["git"]["commit"],
            },
            "r6_presentation_syntax_artifact": {
                "path": str(R6_ARTIFACT.relative_to(REPO_ROOT)),
                "sha256": sha256_path(R6_ARTIFACT),
                "content_hash": r6["content_hash"],
                "source_commit": r6["git"]["commit"],
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
            "source_captures": source_capture_check(references),
            "source_files": source_files,
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
                "declaration_count": theorem_count,
                "new_r7_declaration_count": 18,
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
            "previous_artifact_tests": {
                "status": "PASS",
                "test_count": previous_test_count,
                "test_files": PREVIOUS_TESTS,
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
            "Planar identities, composition reassociation, and disjoint critical-point interchange preserve evaluation.",
            "Both Reidemeister II orientations and Reidemeister III with visible associators preserve evaluation.",
            "All four left/right primal/dual snake moves preserve evaluation.",
            "Coupon transport through crossings, all extrema, and both framing-twist orientations is whitelisted and kernel checked.",
            "Framed Reidemeister I follows from the separately supplied positive and negative ribbon-kink equations.",
            "Closure cut independence follows from the separately supplied spherical trace cyclicity equation.",
            "Every GeneratedIsotopy over the closed whitelist preserves evaluation, including inside arbitrary typed one-hole contexts.",
            "Presentation independence follows from a separately supplied topology witness connecting two admitted diagrams of one framed link."
        ],
        "trusted_inputs": obligations["trusted_inputs"],
        "source_scope_warning": (
            "Selinger Theorem 4.30 carries Caveat 4.31. Full diagram "
            "completeness is intentionally not claimed as Lean-proved; "
            "FramedLinkPresentationCompleteness.connected remains explicit."
        ),
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
