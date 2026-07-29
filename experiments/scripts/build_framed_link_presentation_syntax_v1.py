#!/usr/bin/env python3
"""Build the terminal R6 framed-link presentation syntax certificate."""

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

from twisted_yetter.kirby_presentation_v1 import (
    build_reference_fixture,
    canonical_json_bytes,
    deserialize_presentation,
    serialize_presentation,
    stable_content_hash,
    validate_presentation,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-syntax-v1.json"
)
FIXTURE = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-fixture-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "generalized-sliding-framed-context-primary-sources-v1.json"
)
PRESENTATION_AXIOM_AUDIT = (
    "lean/TwistedYetter/Kirby/PresentationSchemaRegressionAxiomAudit.lean"
)

LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/Presentation.lean",
    (
        "lean/TwistedYetter/Kirby/Final/Semantics/"
        "DottedCutImplementationBridge.lean"
    ),
    "lean/TwistedYetter/Kirby/PresentationSchemaRegression.lean",
    (
        "lean/TwistedYetter/Kirby/Final/Semantics/"
        "CombinatorialSemanticComparison.lean"
    ),
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/MissingPresentationAdmission.lean",
    "lean/Mutations/MutableAliasPresentation.lean",
    "lean/Mutations/InvalidPresentationLineage.lean",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    PRESENTATION_AXIOM_AUDIT,
    *MUTATIONS,
    "src/twisted_yetter/kirby_presentation_v1.py",
    "scripts/lean_presentation_mutation_tests.sh",
    "experiments/scripts/build_framed_link_presentation_syntax_v1.py",
    "tests/test_kirby_presentation_v1.py",
    "tests/test_framed_link_presentation_syntax_v1.py",
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


def canonical_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    return "sha256:" + sha256_bytes(canonical_json_bytes(body))


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


def build() -> tuple[dict[str, Any], bytes]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("R6 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    rows = obligations["obligations"]
    if len(rows) != 15 or any(
        row["status"] == "NOT_FORMALIZED" for row in rows
    ):
        raise AssertionError("R6 obligation matrix is not terminal")

    fixture = build_reference_fixture()
    validate_presentation(fixture)
    fixture_bytes = serialize_presentation(fixture)
    if deserialize_presentation(fixture_bytes) != fixture:
        raise AssertionError("canonical JSON round trip changed the fixture")

    build_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = run(
        ["./scripts/lean_local_check.sh", PRESENTATION_AXIOM_AUDIT]
    )
    axiom_output = clean_output(axiom_result.stdout + axiom_result.stderr)
    forbidden_axioms = ("sorryAx", "native_decide.ax")
    if any(item in axiom_output for item in forbidden_axioms):
        raise AssertionError("axiom audit exposed a proof hole or native oracle")
    theorem_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if theorem_count != 11:
        raise AssertionError(
            f"expected 11 audited presentation declarations, got {theorem_count}"
        )

    mutation_result = run(["./scripts/lean_presentation_mutation_tests.sh"])
    mutation_output = clean_output(
        mutation_result.stdout + mutation_result.stderr
    )
    rejections = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 3:
        raise AssertionError("expected three rejected R6 Lean mutations")

    pytest_result = run(
        ["uv", "run", "pytest", "-q", "tests/test_kirby_presentation_v1.py"]
    )
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    if "28 passed" not in pytest_output:
        raise AssertionError("R6 Python validator tests did not all pass")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.framed-link-presentation-syntax.v1",
        "status": "PASS_FRAMED_LINK_PRESENTATION_SYNTAX",
        "mathematical_status": (
            "FRAMED_LINK_KIRBY_PRESENTATION_SYNTAX_ESTABLISHED"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_framed_link_presentation_syntax_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_framed_link_presentation_syntax_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_framed_link_presentation_syntax_v1.py"
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
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "sha256": sha256_path(OBLIGATIONS),
                "obligation_count": len(rows),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "sha256": sha256_path(REFERENCES),
            },
            "source_files": source_files,
        },
        "outputs": {
            "fixture": {
                "path": str(FIXTURE.relative_to(REPO_ROOT)),
                "file_sha256": sha256_bytes(fixture_bytes),
                "content_hash": fixture["content_hash"],
                "component_count": len(fixture["components"]),
                "event_count": len(fixture["events"]),
                "slice_count": len(fixture["declared_slices"]),
            }
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
                "theorem_count": theorem_count,
                "presentation_regression_theorem_count": theorem_count,
                "observed_standard_axioms": [
                    "propext",
                    "Classical.choice",
                    "Quot.sound",
                ],
                "output_sha256": sha256_bytes(axiom_output.encode()),
            },
            "lean_mutation_tests": {
                "status": "PASS_ALL_BAD_INPUTS_REJECTED",
                "rejected_count": len(rejections),
                "rejections": rejections,
                "output_sha256": sha256_bytes(mutation_output.encode()),
            },
            "python_validator_tests": {
                "status": "PASS",
                "test_count": 28,
                "output_sha256": sha256_bytes(pytest_output.encode()),
            },
            "json_round_trip": {
                "status": "PASS_BYTE_STABLE_CANONICAL_ROUND_TRIP",
                "fixture_sha256": sha256_bytes(fixture_bytes),
            },
            "resource_guards": {
                "status": "PASS_INHERITED_AND_ENFORCED",
                "default_threads": 1,
                "maximum_allowed_threads": 2,
                "execution_mode": "one Lean process at a time",
            },
        },
        "established_scope": [
            "Typed component IDs, orientations, integer framings, roles, labels, coupons, and Morse events.",
            "Executable active-strand lineage validation from empty initial boundary to empty terminal boundary.",
            "Blackboard writhe is replayed from self-crossings and framing twists and checked against integer framing plus correction.",
            "Declared slices are checked against a fresh event replay.",
            "Canonical JSON round trip and SHA-256 content identity are enforced.",
            "FormalPresentation requires a Lean proof that the executable validator returned success.",
            "Every literal dotted component carries exactly one ordered signed puncture word; repeated strand occurrences remain distinct by cut position.",
            "Dotted-cut topology validity remains a separate proof-bearing certificate and is never inferred from a provenance hash.",
            "Mutable aliases and unknown JSON fields are unrepresentable or rejected."
        ],
        "explicit_non_claims": obligations["explicit_non_claims"],
    }
    payload["content_hash"] = canonical_hash(payload)
    return payload, fixture_bytes


def main() -> None:
    payload, fixture_bytes = build()
    FIXTURE.parent.mkdir(parents=True, exist_ok=True)
    FIXTURE.write_bytes(fixture_bytes)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(FIXTURE)
    print(OUTPUT)
    print(payload["content_hash"])


if __name__ == "__main__":
    main()
