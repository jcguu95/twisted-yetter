#!/usr/bin/env python3
"""Build the v3 four-manifold invariant target certificate."""

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

from twisted_yetter.four_manifold_invariant_target_v3 import (  # noqa: E402
    MATHEMATICAL_STATUS,
    OPEN_CONDITIONS,
    build_target_runtime,
    canonical_hash,
    validate_target_runtime,
)
from twisted_yetter.source_backed_kirby_completeness_v1 import (  # noqa: E402
    DOMAIN_AXIOM,
    validate_runtime as validate_source_runtime,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v3.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "four-manifold-invariant-target-obligation-matrix-v3.json"
)
PREDECESSOR = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v2.json"
)
SOURCE_COMPLETENESS = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "source-backed-special-kirby-completeness-v1.json"
)
LEAN_BUILD_ORDER = (
    "lean/TwistedYetter/Kirby/SourceBackedKirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    "lean/TwistedYetter.lean",
)
MUTATION_SCRIPTS = (
    ("scripts/lean_kirby_completeness_mutation_tests.sh", 9),
    ("scripts/lean_homologically_twisted_invariant_mutation_tests.sh", 10),
    ("scripts/lean_four_manifold_invariant_target_mutation_tests.sh", 3),
    ("scripts/lean_source_backed_kirby_completeness_mutation_tests.sh", 3),
)
PYTEST_FILES = ("tests/test_four_manifold_invariant_target_v3.py",)
EXPECTED_PYTEST_COUNT = 9
EXPECTED_TARGET_AXIOM_DECLARATIONS = 18
EXPECTED_SOURCE_AXIOM_DECLARATIONS = 7
AUDITED_FILES = (
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTargetAxiomAudit.lean",
    "lean/TwistedYetter/Kirby/"
    "SourceBackedKirbyCompletenessAxiomAudit.lean",
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_source_backed_kirby_completeness_axiom_audit.sh",
    "src/twisted_yetter/four_manifold_invariant_target_v3.py",
    "experiments/scripts/build_four_manifold_invariant_target_v3.py",
    "tests/test_four_manifold_invariant_target_v3.py",
    "tests/test_four_manifold_invariant_target_artifact_v3.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
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


def parse_axiom_audit(
    script: str,
    expected_declarations: int,
    allowed_custom: set[str],
) -> dict[str, Any]:
    result = run([f"./{script}"])
    output = clean_output(result.stdout + result.stderr)
    declarations = len(
        re.findall(r"^'TwistedYetter\.", output, flags=re.MULTILINE)
    )
    if declarations != expected_declarations:
        raise AssertionError(
            f"{script}: expected {expected_declarations} declarations, "
            f"got {declarations}"
        )
    standard_allowed = {"propext", "Classical.choice", "Quot.sound"}
    observed_standard: set[str] = set()
    observed_custom: set[str] = set()
    for raw in re.findall(
        r"depends on axioms: \[(.*?)\]", output, flags=re.DOTALL
    ):
        for item in (
            entry.strip()
            for entry in re.sub(r"\s+", " ", raw).split(",")
            if entry.strip()
        ):
            if item.startswith("TwistedYetter."):
                observed_custom.add(item)
            else:
                observed_standard.add(item)
    unexpected_standard = sorted(observed_standard - standard_allowed)
    unexpected_custom = sorted(observed_custom - allowed_custom)
    if unexpected_standard or unexpected_custom:
        raise AssertionError(
            f"{script}: unexpected axioms: "
            f"{unexpected_standard + unexpected_custom}"
        )
    if observed_custom != allowed_custom:
        raise AssertionError(
            f"{script}: custom axiom denominator changed: "
            f"{sorted(observed_custom)}"
        )
    return {
        "status": "PASS_EXACT_AXIOM_DENOMINATOR",
        "audited_declaration_count": declarations,
        "observed_standard_axioms": sorted(observed_standard),
        "unexpected_axioms": unexpected_standard,
        "observed_custom_axioms": sorted(observed_custom),
        "observed_custom_axiom_count": len(observed_custom),
        "unexpected_custom_axioms": unexpected_custom,
        "output": output,
    }


def proof_boundary_scan() -> dict[str, Any]:
    no_oracle = re.compile(r"\b(sorry|admit|native_decide)\b")
    for relative in LEAN_BUILD_ORDER:
        match = no_oracle.search((REPO_ROOT / relative).read_text())
        if match:
            raise AssertionError(
                f"forbidden proof oracle in {relative}: {match.group(0)!r}"
            )
    source = (REPO_ROOT / LEAN_BUILD_ORDER[0]).read_text()
    source_axioms = re.findall(
        r"^\s*axiom\s+([A-Za-z0-9_]+)", source, re.MULTILINE
    )
    if source_axioms != ["standardSpecialKirbyCalculusConnected"]:
        raise AssertionError(f"domain axiom declarations: {source_axioms!r}")
    for relative in LEAN_BUILD_ORDER[1:]:
        if re.search(r"^\s*axiom\b", (REPO_ROOT / relative).read_text(), re.M):
            raise AssertionError(f"unexpected axiom declaration in {relative}")
    return {
        "status": "PASS_ONE_WHITELISTED_DOMAIN_AXIOM_NO_PROOF_HOLES",
        "domain_axiom_declarations": source_axioms,
        "checked_files": list(LEAN_BUILD_ORDER),
    }


def validate_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    obligations = json.loads(OBLIGATIONS.read_text())
    conditions = obligations.get("conditions", [])
    if (
        obligations.get("status")
        != "TARGET_CONTRACT_FROZEN_WITH_TWO_OPEN_CONDITIONS"
        or len(conditions) != 6
        or sum(
            str(row.get("status", "")).startswith("OPEN_")
            for row in conditions
        )
        != 2
    ):
        raise AssertionError("v3 target obligation denominator changed")

    predecessor = json.loads(PREDECESSOR.read_text())
    if predecessor.get("content_hash") != canonical_hash(predecessor):
        raise AssertionError("stale v2 target predecessor")
    if predecessor.get("git", {}).get("dirty") is not False:
        raise AssertionError("dirty v2 target predecessor")

    source = json.loads(SOURCE_COMPLETENESS.read_text())
    if source.get("content_hash") != canonical_hash(source):
        raise AssertionError("stale source-completeness predecessor")
    validate_source_runtime(source["runtime_certificate"])
    if (
        source.get("git", {}).get("dirty") is not False
        or source["runtime_certificate"].get("domain_axiom_count") != 1
    ):
        raise AssertionError("source-completeness predecessor boundary changed")
    return obligations, predecessor, source


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
                f"{script}: expected {expected_count}, got {len(observed)}"
            )
        rejections.extend(observed)
    return len(rejections), rejections


def predecessor_record(path: Path, payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "schema": payload["schema"],
        "status": payload["status"],
        "content_hash": payload["content_hash"],
        "file_sha256": file_sha256(path),
        "source_commit": payload["git"]["commit"],
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
        raise RuntimeError("v3 target artifact requires a clean source commit")

    obligations, predecessor, source = validate_inputs()
    runtime = build_target_runtime()
    validate_target_runtime(runtime)
    lean_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    target_axiom = parse_axiom_audit(
        "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
        EXPECTED_TARGET_AXIOM_DECLARATIONS,
        set(),
    )
    source_axiom = parse_axiom_audit(
        "scripts/lean_source_backed_kirby_completeness_axiom_audit.sh",
        EXPECTED_SOURCE_AXIOM_DECLARATIONS,
        {DOMAIN_AXIOM},
    )
    mutation_count, mutation_rejections = mutation_audit()
    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != EXPECTED_PYTEST_COUNT:
        raise AssertionError("v3 target scoped pytest denominator changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": file_sha256(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v3",
        "status": (
            "PASS_TARGET_STATED_SOURCE_COMPLETENESS_GAP_CLOSED_"
            "TWO_CONCRETE_CONDITIONS_OPEN"
        ),
        "mathematical_status": MATHEMATICAL_STATUS,
        "roadmap_status": (
            "FOUR_FOUNDATION_CONDITIONS_ESTABLISHED_"
            "TWO_CONCRETE_CONDITIONS_OPEN"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_four_manifold_invariant_target_v3.py"
        ),
        "argv": [
            "experiments/scripts/build_four_manifold_invariant_target_v3.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_four_manifold_invariant_target_v3.py"
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
            "target_predecessor": predecessor_record(
                PREDECESSOR, predecessor
            ),
            "source_completeness_artifact": {
                **predecessor_record(SOURCE_COMPLETENESS, source),
                "domain_axiom_count": source["runtime_certificate"][
                    "domain_axiom_count"
                ],
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
            "status": (
                "PASS_BUILD_SEPARATE_AXIOM_AUDITS_AND_MUTATION_REJECTIONS"
            ),
            "build_order": list(LEAN_BUILD_ORDER),
            "build_output": clean_output(
                lean_result.stdout + lean_result.stderr
            ),
            "target_axiom_audit": target_axiom,
            "source_axiom_audit": source_axiom,
            "proof_boundary_scan": proof_boundary_scan(),
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
            }
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
