#!/usr/bin/env python3
"""Build the terminal R12 computation-artifact import certificate."""

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

from twisted_yetter.computation_artifact_import_v1 import (  # noqa: E402
    BLOCKED_STATUS,
    EXPECTED_CHUNK_ARTIFACTS,
    EXPECTED_ROWS,
    EXPECTED_TOTAL_SECTORS,
    KNOWN_BLOCKERS,
    RUNTIME_STATUS,
    build_computation_import_runtime,
    canonical_hash,
    file_sha256,
    validate_computation_import_runtime,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "computation-artifact-import-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "computation-artifact-import-obligation-matrix-v1.json"
)
MANIFEST = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "computation-artifact-import-manifest-v1.json"
)
R11_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "homologically-twisted-invariant-v1.json"
)
LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/ComputationArtifactImporter.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/DirtyArtifactAsExactR12.lean",
    "lean/Mutations/RoundedArtifactAsExactR12.lean",
    "lean/Mutations/MissingR11BindingR12.lean",
    "lean/Mutations/MissingEvaluatorClosureR12.lean",
    "lean/Mutations/IncompleteDistributionR12.lean",
    "lean/Mutations/InconclusiveArtifactAsExactR12.lean",
    "lean/Mutations/MutableAliasArtifactAsExactR12.lean",
    "lean/Mutations/StructuralAggregatePromotionR12.lean",
    "lean/Mutations/Figure21ExactValueProjectionR12.lean",
    "lean/Mutations/Figure21ExactDispositionR12.lean",
]
PYTEST_FILES = [
    "tests/test_computation_artifact_import_v1.py",
    "tests/test_homologically_twisted_invariant_v1.py",
    "tests/test_figure21_rank2_rank3_standard_comparison_v1.py",
    "tests/test_current_low_rank_figure21_terminal_package_v1.py",
]
EXPECTED_PYTEST_COUNT = 34
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "src/twisted_yetter/computation_artifact_import_v1.py",
    *MUTATIONS,
    "scripts/lean_computation_artifact_import_mutation_tests.sh",
    "experiments/scripts/build_computation_artifact_import_v1.py",
    "tests/test_computation_artifact_import_v1.py",
    "tests/test_computation_artifact_import_artifact_v1.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    str(MANIFEST.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
]
ANSI_ESCAPE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))"
)


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )


def clean_output(text: str) -> str:
    return ANSI_ESCAPE.sub("", text).strip()


def run(argv: list[str]) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(REPO_ROOT / ".uv-cache")
    env["PYTHONPATH"] = os.pathsep.join(
        part
        for part in (str(REPO_ROOT), env.get("PYTHONPATH", ""))
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
    checked = [LEAN_BUILD_ORDER[0]]
    for relative in checked:
        source = (REPO_ROOT / relative).read_text()
        match = forbidden.search(source)
        if match:
            raise AssertionError(
                f"forbidden proof-oracle token in {relative}: "
                f"{match.group(0)!r}"
            )
    return {
        "status": "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE",
        "checked_files": checked,
    }


def contract_check() -> dict[str, Any]:
    path = (
        REPO_ROOT
        / "lean/TwistedYetter/Kirby/"
        "ComputationArtifactImporter.lean"
    )
    source = path.read_text()
    structural = source.split(
        "structure StructuralAggregateCertificate", 1
    )[1].split("namespace StructuralAggregateCertificate", 1)[0]
    exact = source.split(
        "structure ExactInvariantValueCertificate", 1
    )[1].split("namespace ExactInvariantValueCertificate", 1)[0]
    required_structures = (
        "structure Hash256",
        "structure ArtifactEnvelope",
        "structure ComputationIdentity",
        "structure DistributionCertificate",
        "structure StructuralAggregateCertificate",
        "structure ExactInvariantTarget",
        "structure ExactInvariantValueCertificate",
        "structure TerminalBlockedImport",
        "structure StructuralImportBatch",
    )
    _missing = [item for item in required_structures if item not in source]
    if _missing:
        raise AssertionError(f"R12 missing Lean structures: {_missing}")
    if "outputValue" in structural or "r11BindingIsValid" in structural:
        raise AssertionError("structural aggregate exposes exact value data")
    mandatory_exact_fields = (
        "clean_source",
        "alias_free",
        "pass_status",
        "no_inconclusive",
        "exact_arithmetic",
        "output_sound",
    )
    if any(field not in exact for field in mandatory_exact_fields):
        raise AssertionError("exact importer admission field is missing")
    forbidden_escape_hatches = (
        "fromStructuralAggregate",
        "admitRoundedComplex",
        "assumeCleanSource",
        "assumeR11Binding",
    )
    if any(token in source for token in forbidden_escape_hatches):
        raise AssertionError("R12 importer contains an admission escape hatch")
    return {
        "status": "PASS_EXACT_AND_STRUCTURAL_TYPES_DISJOINT",
        "required_structure_count": len(required_structures),
        "mandatory_exact_fields": list(mandatory_exact_fields),
        "structural_output_value_field": False,
        "structural_r11_binding_field": False,
        "forbidden_escape_hatches": list(forbidden_escape_hatches),
        "terminal_figure21_blocker_count": len(KNOWN_BLOCKERS),
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
        raise RuntimeError("R12 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    if (
        obligations.get("status")
        != "R12_CONTRACT_TERMINAL_IMPLEMENTED_PENDING_GENERATED_CERTIFICATE"
        or len(obligations.get("obligations", [])) != 38
        or len(obligations.get("trusted_inputs", [])) != 3
        or len(obligations.get("explicit_non_claims", [])) != 7
    ):
        raise AssertionError("R12 obligation matrix denominator changed")
    if any(
        row.get("status") in {"UNKNOWN", "NOT_FORMALIZED", "IN_PROGRESS"}
        for row in obligations["obligations"]
    ):
        raise AssertionError("R12 obligation matrix is not terminal")

    runtime = build_computation_import_runtime()
    validate_computation_import_runtime(runtime)
    if runtime["status"] != RUNTIME_STATUS:
        raise AssertionError("R12 runtime status changed")

    lean_result = run(
        ["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER]
    )
    axiom_result = run(["./scripts/lean_axiom_audit.sh"])
    axiom_output = clean_output(
        axiom_result.stdout + axiom_result.stderr
    )
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("R12 axiom audit exposed a proof oracle")
    declaration_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if declaration_count != 103:
        raise AssertionError(
            f"expected 103 audited declarations, got {declaration_count}"
        )

    mutation_result = run(
        ["./scripts/lean_computation_artifact_import_mutation_tests.sh"]
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
            f"expected {len(MUTATIONS)} rejected R12 mutations"
        )

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(
        pytest_result.stdout + pytest_result.stderr
    )
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != EXPECTED_PYTEST_COUNT:
        raise AssertionError("R12 scoped pytest denominator changed")

    r11 = json.loads(R11_ARTIFACT.read_text())
    if (
        r11.get("status")
        != "PASS_HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT"
        or r11.get("git", {}).get("dirty") is not False
        or r11.get("content_hash")
        != runtime["exact_control"]["content_hash"]
    ):
        raise AssertionError("R12 clean R11 predecessor binding changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": file_sha256(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.computation-artifact-import.v1",
        "status": "R12_TERMINAL_WITH_EXPLICIT_BLOCKERS",
        "mathematical_status": (
            "COMPUTATION_IMPORTER_ESTABLISHED_EXACT_CONTROL_VERIFIED_"
            "FIGURE21_NOT_ADMITTED"
        ),
        "roadmap_status": "R12_TERMINAL_WITH_BLOCKERS_R13_NOT_STARTED",
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/"
            "build_computation_artifact_import_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_computation_artifact_import_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_computation_artifact_import_v1.py"
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
            "r11_exact_control": {
                "path": str(R11_ARTIFACT.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(R11_ARTIFACT),
                "content_hash": r11["content_hash"],
                "source_commit": r11["git"]["commit"],
                "source_clean": True,
            },
            "obligation_matrix": {
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(OBLIGATIONS),
                "obligation_count": len(obligations["obligations"]),
                "trusted_input_count": len(obligations["trusted_inputs"]),
                "explicit_nonclaim_count": len(
                    obligations["explicit_non_claims"]
                ),
            },
            "frozen_manifest": {
                "path": str(MANIFEST.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(MANIFEST),
                "row_count": len(EXPECTED_ROWS),
                "blocker_count": len(KNOWN_BLOCKERS),
            },
            "source_files": source_files,
        },
        "lean_certificate": {
            "status": "PASS_KERNEL_AXIOM_AUDIT_AND_MUTATION_REJECTIONS",
            "build_order": LEAN_BUILD_ORDER,
            "build_output": clean_output(
                lean_result.stdout + lean_result.stderr
            ),
            "audited_declaration_count": declaration_count,
            "axiom_audit": {
                "status": "PASS_NO_SORRYAX_OR_NATIVE_ORACLE",
                "output": axiom_output,
            },
            "proof_hole_scan": proof_hole_scan(),
            "mutation_count": len(rejections),
            "mutation_rejections": rejections,
        },
        "runtime_certificate": runtime,
        "checks": {
            "contract": contract_check(),
            "scoped_pytest": {
                "status": "PASS",
                "files": PYTEST_FILES,
                "passed_count": int(match.group(1)),
                "output": pytest_output,
            },
            "denominator_replay": {
                "status": (
                    "PASS_15_ROWS_1832_CHUNKS_ALL_RANGES_AND_HASHES"
                ),
                "row_count": len(EXPECTED_ROWS),
                "chunk_artifact_count": EXPECTED_CHUNK_ARTIFACTS,
                "total_sector_count": EXPECTED_TOTAL_SECTORS,
            },
            "admission_boundary": {
                "status": "PASS_FAIL_CLOSED_TERMINAL_DECISION",
                "exact_control_admitted": True,
                "figure21_structural_imported": True,
                "figure21_exact_value_admitted": False,
                "figure21_disposition": BLOCKED_STATUS,
                "blockers": list(KNOWN_BLOCKERS),
            },
        },
        "trusted_inputs": obligations["trusted_inputs"],
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
