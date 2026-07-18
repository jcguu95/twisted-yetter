#!/usr/bin/env python3
"""Build the explicit four-manifold invariant target certificate."""

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

from twisted_yetter.four_manifold_invariant_target_v1 import (  # noqa: E402
    MATHEMATICAL_STATUS,
    OPEN_CONDITIONS,
    RUNTIME_STATUS,
    build_target_runtime,
    canonical_hash,
    validate_target_runtime,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "four-manifold-invariant-target-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "four-manifold-invariant-target-primary-sources-v1.json"
)
PREDECESSOR_ARTIFACTS = (
    "experiments/results/lean-kirby/kirby-cancellation-v1.json",
    "experiments/results/lean-kirby/kirby-completeness-v1.json",
    "experiments/results/lean-kirby/homologically-twisted-invariant-v1.json",
    "experiments/results/lean-kirby/"
    "homologically-twisted-kirby-formalization-package-v1.json",
)
LEAN_BUILD_ORDER = (
    "lean/TwistedYetter/Kirby/KirbyCancellation.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    "lean/TwistedYetter.lean",
)
MUTATIONS = (
    "lean/Mutations/PromoteFourManifoldInvariantTarget.lean",
    "lean/Mutations/DropFourManifoldInvariantTargetCondition.lean",
    "lean/Mutations/RequireCraneYetterIdentificationForTarget.lean",
)
PYTEST_FILES = ("tests/test_four_manifold_invariant_target_v1.py",)
EXPECTED_PYTEST_COUNT = 9
EXPECTED_AXIOM_DECLARATION_COUNT = 8
AUDITED_FILES = (
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTargetAxiomAudit.lean",
    "src/twisted_yetter/four_manifold_invariant_target_v1.py",
    *MUTATIONS,
    "scripts/lean_four_manifold_invariant_target_axiom_audit.sh",
    "scripts/lean_four_manifold_invariant_target_mutation_tests.sh",
    "experiments/scripts/build_four_manifold_invariant_target_v1.py",
    "tests/test_four_manifold_invariant_target_v1.py",
    "tests/test_four_manifold_invariant_target_artifact_v1.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
)
ANSI_ESCAPE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))"
)


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def clean_output(text: str) -> str:
    return ANSI_ESCAPE.sub("", text).strip()


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
    checked = [
        LEAN_BUILD_ORDER[0],
        LEAN_BUILD_ORDER[1],
    ]
    for relative in checked:
        match = forbidden.search((REPO_ROOT / relative).read_text())
        if match:
            raise AssertionError(
                f"forbidden proof oracle in {relative}: {match.group(0)!r}"
            )
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": checked,
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
            f"expected {EXPECTED_AXIOM_DECLARATION_COUNT} target "
            f"declarations, got {declarations}"
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


def contract_check() -> dict[str, Any]:
    cancellation = (REPO_ROOT / LEAN_BUILD_ORDER[0]).read_text()
    target = (REPO_ROOT / LEAN_BUILD_ORDER[1]).read_text()
    required_tokens = (
        "def threeHandleWeight",
        "theorem twoThreeFactor_mul_threeHandleWeight",
        "theorem denominator_ratio_addTwoThree",
        "theorem raw_with_explicit_three_handle",
        "inductive TargetCondition",
        "def requiredTargetConditions",
        "def openConstructionConditions",
        "theorem current_target_has_open_conditions",
        "structure FourManifoldInvariantInputs",
        "theorem four_manifold_invariant_target",
    )
    joined = cancellation + "\n" + target
    missing = [token for token in required_tokens if token not in joined]
    if missing:
        raise AssertionError(f"target Lean contract is incomplete: {missing}")
    forbidden_promotions = (
        "def currentFourManifoldInvariantInputs",
        "theorem four_manifold_invariant_established",
    )
    present = [token for token in forbidden_promotions if token in target]
    if present:
        raise AssertionError(f"premature target promotion: {present}")
    return {
        "status": "PASS_TARGET_STATED_WITHOUT_CONCRETE_PROMOTION",
        "required_token_count": len(required_tokens),
        "forbidden_promotion_count": 0,
    }


def predecessor_inputs() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for relative in PREDECESSOR_ARTIFACTS:
        path = REPO_ROOT / relative
        payload = json.loads(path.read_text())
        if payload.get("content_hash") != canonical_hash(payload):
            raise AssertionError(f"stale predecessor content hash: {relative}")
        if payload.get("git", {}).get("dirty") is not False:
            raise AssertionError(f"dirty predecessor artifact: {relative}")
        records.append(
            {
                "path": relative,
                "schema": payload["schema"],
                "status": payload["status"],
                "content_hash": payload["content_hash"],
                "file_sha256": file_sha256(path),
                "source_commit": payload["git"]["commit"],
            }
        )
    return records


def validate_inputs() -> tuple[dict[str, Any], dict[str, Any]]:
    obligations = json.loads(OBLIGATIONS.read_text())
    references = json.loads(REFERENCES.read_text())
    conditions = obligations.get("conditions", [])
    if (
        obligations.get("status")
        != "TARGET_CONTRACT_FROZEN_WITH_FOUR_OPEN_CONDITIONS"
        or len(conditions) != 6
        or sum(
            str(row.get("status", "")).startswith("OPEN_")
            for row in conditions
        )
        != 4
    ):
        raise AssertionError("target obligation denominator changed")
    if (
        references.get("status")
        != "TARGET_SOURCES_AND_EXACT_OPEN_BOUNDARIES_RECORDED"
        or len(references.get("references", [])) != 4
    ):
        raise AssertionError("target reference denominator changed")
    capture = references["references"][0]["captured_pdf"]
    capture_path = Path(capture["capture_path_at_capture_time"])
    if (
        not capture_path.is_file()
        or capture_path.stat().st_size != capture["bytes"]
        or file_sha256(capture_path) != "sha256:" + capture["sha256"]
    ):
        raise AssertionError("Bärenz-Barrett source capture mismatch")
    return obligations, references


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("target artifact requires a clean source commit")

    obligations, references = validate_inputs()
    runtime = build_target_runtime()
    validate_target_runtime(runtime)
    predecessors = predecessor_inputs()

    lean_result = run(
        ["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER]
    )
    axiom = axiom_audit()
    mutation_result = run(
        ["./scripts/lean_four_manifold_invariant_target_mutation_tests.sh"]
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
        raise AssertionError("target mutation rejection denominator changed")

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != EXPECTED_PYTEST_COUNT:
        raise AssertionError("target scoped pytest denominator changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": file_sha256(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.four-manifold-invariant-target.v1",
        "status": (
            "PASS_TARGET_STATED_SIMPLE_THREE_HANDLE_GAP_CLOSED_"
            "FOUR_HARD_CONDITIONS_OPEN"
        ),
        "mathematical_status": MATHEMATICAL_STATUS,
        "roadmap_status": (
            "SIMPLE_FOUNDATION_GAPS_CLOSED_NEXT_CONCRETE_CONSTRUCTION"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_four_manifold_invariant_target_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_four_manifold_invariant_target_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_four_manifold_invariant_target_v1.py"
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
            "predecessor_artifacts": predecessors,
            "obligation_matrix": {
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(OBLIGATIONS),
                "condition_count": len(obligations["conditions"]),
                "open_condition_count": len(OPEN_CONDITIONS),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(REFERENCES),
                "reference_count": len(references["references"]),
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
            "mutation_count": len(rejections),
            "mutation_rejections": rejections,
        },
        "runtime_certificate": runtime,
        "checks": {
            "contract": contract_check(),
            "scoped_pytest": {
                "status": "PASS",
                "files": list(PYTEST_FILES),
                "passed_count": int(match.group(1)),
                "output": pytest_output,
            },
        },
        "admission": {
            "status": "REPO_LOCAL_GOAL_EVIDENCE_ONLY",
            "ctl_claim_admitted": False,
            "ctl_manifest_written": False,
        },
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
