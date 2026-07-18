#!/usr/bin/env python3
"""Build the v2 four-manifold invariant target certificate."""

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

from twisted_yetter.four_manifold_invariant_target_v2 import (  # noqa: E402
    MATHEMATICAL_STATUS,
    OPEN_CONDITIONS,
    build_target_runtime,
    canonical_hash,
    validate_target_runtime,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v2.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "four-manifold-invariant-target-obligation-matrix-v2.json"
)
PREDECESSOR = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v1.json"
)
LEAN_BUILD_ORDER = (
    "lean/TwistedYetter/Kirby/HandleChainHomology.lean",
    "lean/TwistedYetter/Kirby/KirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    "lean/TwistedYetter.lean",
)
MUTATION_SCRIPTS = (
    ("scripts/lean_kirby_completeness_mutation_tests.sh", 9),
    ("scripts/lean_homologically_twisted_invariant_mutation_tests.sh", 10),
    ("scripts/lean_four_manifold_invariant_target_mutation_tests.sh", 3),
)
EXPECTED_AXIOM_DECLARATION_COUNT = 16
EXPECTED_PYTEST_COUNT = 10
PYTEST_FILES = ("tests/test_four_manifold_invariant_target_v2.py",)
AUDITED_FILES = (
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTargetAxiomAudit.lean",
    "lean/Mutations/HandwrittenMovieTargetCharacter.lean",
    "lean/Mutations/MissingInducedH2ChainWitness.lean",
    "scripts/lean_kirby_completeness_mutation_tests.sh",
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "src/twisted_yetter/four_manifold_invariant_target_v2.py",
    "experiments/scripts/build_four_manifold_invariant_target_v2.py",
    "tests/test_four_manifold_invariant_target_v2.py",
    "tests/test_four_manifold_invariant_target_artifact_v2.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
)
PROOF_FILES = (
    "lean/TwistedYetter/Kirby/HandleChainHomology.lean",
    "lean/TwistedYetter/Kirby/KirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
)
ANSI_ESCAPE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))"
)


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def clean_output(text: str) -> str:
    return ANSI_ESCAPE.sub("", text).strip()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def run(argv: list[str]) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(REPO_ROOT / ".uv-cache")
    env["PYTHONPATH"] = os.pathsep.join(
        part
        for part in (str(REPO_ROOT / "src"), env.get("PYTHONPATH", ""))
        if part
    )
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
    for relative in PROOF_FILES:
        match = forbidden.search((REPO_ROOT / relative).read_text())
        if match:
            raise AssertionError(
                f"forbidden proof oracle in {relative}: {match.group(0)!r}"
            )
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": list(PROOF_FILES),
    }


def axiom_audit() -> dict[str, Any]:
    result = run(
        ["./scripts/lean_four_manifold_invariant_target_axiom_audit.sh"]
    )
    output = clean_output(result.stdout + result.stderr)
    declarations = len(
        re.findall(r"^'TwistedYetter\.", output, flags=re.MULTILINE)
    )
    if declarations != EXPECTED_AXIOM_DECLARATION_COUNT:
        raise AssertionError(
            f"expected {EXPECTED_AXIOM_DECLARATION_COUNT} declarations, "
            f"got {declarations}"
        )
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    observed: set[str] = set()
    for raw in re.findall(
        r"depends on axioms: \[(.*?)\]", output, flags=re.DOTALL
    ):
        observed.update(
            item.strip()
            for item in re.sub(r"\s+", " ", raw).split(",")
            if item.strip()
        )
    unexpected = sorted(observed - allowed)
    if unexpected:
        raise AssertionError(f"unexpected target axioms: {unexpected}")
    return {
        "status": "PASS_ONLY_STANDARD_LEAN_AXIOMS",
        "audited_declaration_count": declarations,
        "allowed_axioms": sorted(allowed),
        "observed_axioms": sorted(observed),
        "unexpected_axioms": unexpected,
        "output": output,
    }


def mutation_audit() -> tuple[int, list[str]]:
    rejections: list[str] = []
    for script, expected_count in MUTATION_SCRIPTS:
        result = run([f"./{script}"])
        output = clean_output(result.stdout + result.stderr)
        observed = [
            line
            for line in output.splitlines()
            if line.startswith("PASS expected rejection:")
        ]
        if len(observed) != expected_count:
            raise AssertionError(
                f"{script} expected {expected_count} rejections, "
                f"got {len(observed)}"
            )
        rejections.extend(observed)
    return len(rejections), rejections


def validate_inputs() -> tuple[dict[str, Any], dict[str, Any]]:
    obligations = json.loads(OBLIGATIONS.read_text())
    conditions = obligations.get("conditions", [])
    if (
        obligations.get("status")
        != "TARGET_CONTRACT_FROZEN_WITH_THREE_OPEN_CONDITIONS"
        or len(conditions) != 6
        or sum(
            str(row.get("status", "")).startswith("OPEN_")
            for row in conditions
        )
        != 3
    ):
        raise AssertionError("v2 target obligation denominator changed")
    h2_rows = [
        row
        for row in conditions
        if row.get("condition_id") == "chain_derived_marked_h2_transport"
    ]
    if (
        len(h2_rows) != 1
        or h2_rows[0].get("status") != "ESTABLISHED_GENERIC_MECHANISM"
        or "remaining_boundary" not in h2_rows[0]
    ):
        raise AssertionError("chain-derived H2 scope is not explicit")

    predecessor = json.loads(PREDECESSOR.read_text())
    if predecessor.get("content_hash") != canonical_hash(predecessor):
        raise AssertionError("stale v1 target predecessor")
    if predecessor.get("git", {}).get("dirty") is not False:
        raise AssertionError("dirty v1 target predecessor")
    return obligations, predecessor


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("v2 target artifact requires a clean source commit")

    obligations, predecessor = validate_inputs()
    runtime = build_target_runtime()
    validate_target_runtime(runtime)

    lean_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom = axiom_audit()
    mutation_count, mutation_rejections = mutation_audit()
    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != EXPECTED_PYTEST_COUNT:
        raise AssertionError("v2 target scoped pytest denominator changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": file_sha256(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v2",
        "status": (
            "PASS_TARGET_STATED_CHAIN_DERIVED_H2_GAP_CLOSED_"
            "THREE_HARD_CONDITIONS_OPEN"
        ),
        "mathematical_status": MATHEMATICAL_STATUS,
        "roadmap_status": (
            "THREE_FOUNDATION_CONDITIONS_ESTABLISHED_"
            "THREE_CONCRETE_CONDITIONS_OPEN"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_four_manifold_invariant_target_v2.py"
        ),
        "argv": [
            "experiments/scripts/build_four_manifold_invariant_target_v2.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_four_manifold_invariant_target_v2.py"
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
            "predecessor_artifact": {
                "path": str(PREDECESSOR.relative_to(REPO_ROOT)),
                "schema": predecessor["schema"],
                "status": predecessor["status"],
                "content_hash": predecessor["content_hash"],
                "file_sha256": file_sha256(PREDECESSOR),
                "source_commit": predecessor["git"]["commit"],
            },
            "obligation_matrix": {
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(OBLIGATIONS),
                "condition_count": len(obligations["conditions"]),
                "open_condition_count": len(OPEN_CONDITIONS),
            },
            "source_files": source_files,
        },
        "lean_certificate": {
            "status": "PASS_BUILD_AXIOM_AUDIT_AND_MUTATION_REJECTIONS",
            "build_order": list(LEAN_BUILD_ORDER),
            "build_output": clean_output(
                lean_result.stdout + lean_result.stderr
            ),
            "axiom_audit": axiom,
            "proof_hole_scan": proof_hole_scan(),
            "mutation_count": mutation_count,
            "mutation_rejections": mutation_rejections,
        },
        "runtime_certificate": runtime,
        "checks": {
            "scoped_pytest": {
                "status": "PASS",
                "files": list(PYTEST_FILES),
                "passed_count": int(match.group(1)),
                "output": pytest_output,
            },
        },
        "admission": {
            "status": "REPO_LOCAL_GOAL_EVIDENCE_ONLY",
            "ctl_theorem_claim_admitted": False,
            "ctl_manifest_written": False,
        },
        "explicit_nonclaims": obligations["explicit_non_claims"],
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
