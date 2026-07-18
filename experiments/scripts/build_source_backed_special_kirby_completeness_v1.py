#!/usr/bin/env python3
"""Build the source-backed special Kirby completeness certificate."""

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

from twisted_yetter.source_backed_kirby_completeness_v1 import (  # noqa: E402
    DOMAIN_AXIOM,
    MATHEMATICAL_STATUS,
    build_runtime,
    canonical_hash,
    validate_runtime,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "source-backed-special-kirby-completeness-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "source-backed-special-kirby-completeness-v1.json"
)
LEAN_BUILD_ORDER = (
    "lean/TwistedYetter/Kirby/SourceBackedKirbyCompleteness.lean",
    "lean/TwistedYetter/Kirby/FourManifoldInvariantTarget.lean",
    "lean/TwistedYetter.lean",
)
MUTATIONS = (
    "lean/Mutations/SourceCompletenessAsEnrichedMovie.lean",
    "lean/Mutations/MissingMovieEnrichmentSound.lean",
    "lean/Mutations/EvaluatorEqualityInsideSourceCompleteness.lean",
)
PYTEST_FILES = ("tests/test_source_backed_kirby_completeness_v1.py",)
EXPECTED_PYTEST_COUNT = 9
EXPECTED_AXIOM_DECLARATION_COUNT = 7
AUDITED_FILES = (
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/"
    "SourceBackedKirbyCompletenessAxiomAudit.lean",
    *MUTATIONS,
    "scripts/lean_source_backed_kirby_completeness_axiom_audit.sh",
    "scripts/lean_source_backed_kirby_completeness_mutation_tests.sh",
    "src/twisted_yetter/source_backed_kirby_completeness_v1.py",
    "experiments/scripts/"
    "build_source_backed_special_kirby_completeness_v1.py",
    "tests/test_source_backed_kirby_completeness_v1.py",
    "tests/test_source_backed_kirby_completeness_artifact_v1.py",
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


def proof_boundary_scan() -> dict[str, Any]:
    source = (REPO_ROOT / LEAN_BUILD_ORDER[0]).read_text()
    forbidden = re.compile(r"\b(sorry|admit|native_decide)\b")
    match = forbidden.search(source)
    if match:
        raise AssertionError(f"forbidden proof oracle: {match.group(0)!r}")
    declarations = re.findall(r"^\s*axiom\s+([A-Za-z0-9_]+)", source, re.M)
    if declarations != ["standardSpecialKirbyCalculusConnected"]:
        raise AssertionError(
            f"domain axiom declarations changed: {declarations!r}"
        )
    return {
        "status": (
            "PASS_EXACTLY_ONE_WHITELISTED_DOMAIN_AXIOM_NO_PROOF_HOLES"
        ),
        "domain_axiom_declarations": declarations,
        "checked_file": LEAN_BUILD_ORDER[0],
    }


def axiom_audit() -> dict[str, Any]:
    result = run(
        ["./scripts/lean_source_backed_kirby_completeness_axiom_audit.sh"]
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
    unexpected_custom = sorted(observed_custom - {DOMAIN_AXIOM})
    if unexpected_standard or unexpected_custom:
        raise AssertionError(
            "unexpected axioms: "
            f"standard={unexpected_standard}, custom={unexpected_custom}"
        )
    if observed_custom != {DOMAIN_AXIOM}:
        raise AssertionError("expected topology domain axiom was not observed")
    return {
        "status": "PASS_EXACTLY_ONE_EXPECTED_CUSTOM_DOMAIN_AXIOM",
        "audited_declaration_count": declarations,
        "observed_standard_axioms": sorted(observed_standard),
        "unexpected_standard_axioms": unexpected_standard,
        "observed_custom_axioms": sorted(observed_custom),
        "unexpected_custom_axioms": unexpected_custom,
        "output": output,
    }


def validate_reference_ledger() -> dict[str, Any]:
    ledger = json.loads(REFERENCES.read_text())
    references = ledger.get("references", [])
    if (
        ledger.get("status")
        != "EXACT_SPECIAL_KIRBY_DOMAIN_AXIOM_SOURCE_BOUNDARY_RECORDED"
        or len(references) != 3
        or ledger.get("formalized_statement", {}).get("lean_axiom")
        != DOMAIN_AXIOM
    ):
        raise AssertionError("source-backed Kirby reference ledger changed")
    capture = references[0]["captured_pdf"]
    path = Path(capture["capture_path_at_capture_time"])
    revalidated = (
        path.is_file()
        and path.stat().st_size == capture["bytes"]
        and file_sha256(path) == "sha256:" + capture["sha256"]
    )
    if not revalidated:
        raise AssertionError("Bärenz-Barrett PDF capture mismatch")
    return {
        "path": str(REFERENCES.relative_to(REPO_ROOT)),
        "file_sha256": file_sha256(REFERENCES),
        "reference_count": len(references),
        "captured_pdf_revalidated": True,
        "captured_pdf_sha256": "sha256:" + capture["sha256"],
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
            "source-backed Kirby artifact requires a clean source commit"
        )

    runtime = build_runtime()
    validate_runtime(runtime)
    reference_record = validate_reference_ledger()
    lean_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom = axiom_audit()
    mutation_result = run(
        ["./scripts/lean_source_backed_kirby_completeness_mutation_tests.sh"]
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
        raise AssertionError("source Kirby mutation denominator changed")
    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != EXPECTED_PYTEST_COUNT:
        raise AssertionError("source Kirby pytest denominator changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": file_sha256(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": (
            "twisted-yetter.source-backed-special-kirby-completeness.v1"
        ),
        "status": (
            "PASS_ONE_SOURCE_BACKED_TOPOLOGY_DOMAIN_AXIOM_"
            "CHAIN_ENRICHMENT_REMAINS_OPEN"
        ),
        "mathematical_status": MATHEMATICAL_STATUS,
        "four_manifold_invariant_established": False,
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/"
            "build_source_backed_special_kirby_completeness_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_source_backed_special_kirby_completeness_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/"
            "build_source_backed_special_kirby_completeness_v1.py"
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
            "reference_ledger": reference_record,
            "source_files": source_files,
        },
        "lean_certificate": {
            "status": (
                "PASS_BUILD_ONE_DOMAIN_AXIOM_AUDIT_AND_MUTATION_REJECTIONS"
            ),
            "build_order": list(LEAN_BUILD_ORDER),
            "build_output": clean_output(
                lean_result.stdout + lean_result.stderr
            ),
            "axiom_audit": axiom,
            "proof_boundary_scan": proof_boundary_scan(),
            "mutation_count": len(rejections),
            "mutation_rejections": rejections,
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
            "status": "REPO_LOCAL_DOMAIN_AXIOM_EVIDENCE_ONLY",
            "ctl_theorem_claim_admitted": False,
            "ctl_manifest_written": False,
        },
        "explicit_nonclaims": runtime["explicit_nonclaims"],
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
