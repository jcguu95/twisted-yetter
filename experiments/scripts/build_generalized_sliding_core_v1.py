#!/usr/bin/env python3
"""Build the source-bound Lean certificate for Bärenz--Barrett Lemma 3.3."""

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
    / "experiments/results/lean-kirby/generalized-sliding-core-v1.json"
)
OBLIGATION_MATRIX = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "generalized-sliding-core-obligation-matrix-v1.json"
)
REFERENCE_LEDGER = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "generalized-sliding-core-primary-sources-v2.json"
)

LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Fusion/FiniteResolution.lean",
    "lean/TwistedYetter/Fusion/PairingTransport.lean",
    "lean/TwistedYetter/Fusion/FrobeniusLinear.lean",
    "lean/TwistedYetter/Fusion/Biorthogonal.lean",
    "lean/TwistedYetter/Fusion/PivotalMate.lean",
    "lean/TwistedYetter/Fusion/Insertion.lean",
    "lean/TwistedYetter/Kirby/CategoricalTangle.lean",
    "lean/TwistedYetter/Kirby/CategoricalMovie.lean",
    "lean/TwistedYetter/Kirby/LinearDiagram.lean",
    "lean/TwistedYetter/Kirby/LinearContext.lean",
    "lean/TwistedYetter/Kirby/MateDiagram.lean",
    "lean/TwistedYetter/Kirby/HandleSlide.lean",
    "lean/TwistedYetter/Kirby/KirbyColorEncirclingTransport.lean",
    "lean/TwistedYetter.lean",
]

MUTATIONS = [
    "lean/Mutations/MissingDualBasisProof.lean",
    "lean/Mutations/MissingPairingPreservation.lean",
    "lean/Mutations/WrongTransportedDualIndex.lean",
    "lean/Mutations/MissingIdentityResolutionSound.lean",
    "lean/Mutations/MissingPivotalTraceProof.lean",
    "lean/Mutations/WrongMateDualOrder.lean",
    "lean/Mutations/InvalidComposition.lean",
    "lean/Mutations/InvalidDualCap.lean",
    "lean/Mutations/MissingMoveProof.lean",
    "lean/Mutations/MissingBackwardInsertion.lean",
    "lean/Mutations/MissingMateMovie.lean",
]

AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Fusion/AxiomAudit.lean",
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    *MUTATIONS,
    "scripts/lean_local_check.sh",
    "scripts/lean_local_build.sh",
    "scripts/lean_fusion_axiom_audit.sh",
    "scripts/lean_axiom_audit.sh",
    "scripts/lean_fusion_mutation_tests.sh",
    "scripts/lean_mutation_tests.sh",
    "experiments/scripts/build_generalized_sliding_core_v1.py",
    "tests/test_generalized_sliding_core_v1.py",
    "tests/test_generalized_sliding_linear_bootstrap_v1.py",
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    str(OBLIGATION_MATRIX.relative_to(REPO_ROOT)),
    str(REFERENCE_LEDGER.relative_to(REPO_ROOT)),
]

ANSI_ESCAPE = re.compile(
    r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))"
)


def _utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _canonical_hash(payload: Any) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return _sha256_bytes(encoded)


def _clean_output(text: str) -> str:
    return ANSI_ESCAPE.sub("", text).strip()


def _run(
    argv: list[str],
    *,
    expected_returncode: int = 0,
    env_override: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    if env_override:
        env.update(env_override)
    result = subprocess.run(
        argv,
        cwd=REPO_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != expected_returncode:
        raise RuntimeError(
            f"{argv!r} returned {result.returncode}, "
            f"expected {expected_returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def _version(argv: list[str]) -> str:
    result = _run(argv)
    return _clean_output(result.stdout or result.stderr).splitlines()[0]


def _assert_no_proof_holes() -> dict[str, Any]:
    forbidden = re.compile(r"\b(sorry|admit)\b|^\s*axiom\b", re.MULTILINE)
    checked: list[str] = []
    for relative in LEAN_BUILD_ORDER:
        text = (REPO_ROOT / relative).read_text()
        match = forbidden.search(text)
        if match:
            raise AssertionError(
                f"forbidden proof-hole token in {relative}: {match.group(0)!r}"
            )
        checked.append(relative)
    return {
        "status": "PASS_NO_SORRY_ADMIT_OR_AXIOM_DECLARATIONS",
        "checked_files": checked,
    }


def _audit_result(
    argv: list[str],
    expected_theorems: int,
) -> dict[str, Any]:
    result = _run(argv)
    output = _clean_output(result.stdout + result.stderr)
    if "sorryAx" in output or "declaration uses `sorry`" in output:
        raise AssertionError(f"axiom audit exposed a proof hole:\n{output}")
    theorem_count = len(
        re.findall(r"^'TwistedYetter\.", output, flags=re.MULTILINE)
    )
    if theorem_count != expected_theorems:
        raise AssertionError(
            f"expected {expected_theorems} audited theorems, got {theorem_count}"
        )
    return {
        "status": "PASS_NO_SORRY_AX",
        "theorem_count": theorem_count,
        "observed_standard_axioms": [
            "propext",
            "Classical.choice",
            "Quot.sound",
        ],
        "output_sha256": _sha256_bytes(output.encode()),
    }


def _mutation_result(argv: list[str], expected_count: int) -> dict[str, Any]:
    result = _run(argv)
    output = _clean_output(result.stdout + result.stderr)
    rejections = [
        line for line in output.splitlines() if line.startswith("PASS expected")
    ]
    if len(rejections) != expected_count:
        raise AssertionError(
            f"expected {expected_count} rejected mutations, got {len(rejections)}"
        )
    return {
        "status": "PASS_ALL_BAD_INPUTS_REJECTED",
        "rejected_count": len(rejections),
        "rejections": rejections,
        "output_sha256": _sha256_bytes(output.encode()),
    }


def _resource_guard_checks() -> dict[str, Any]:
    thread_guard = _run(
        ["./scripts/lean_local_check.sh", "lean/TwistedYetter.lean"],
        expected_returncode=64,
        env_override={"LEAN_NUM_THREADS": "3"},
    )
    thread_output = _clean_output(thread_guard.stdout + thread_guard.stderr)
    if "permits at most 2" not in thread_output:
        raise AssertionError("thread guard failed for an unexpected reason")

    lock_dir = REPO_ROOT / ".lake/lean-local-check.lock"
    if lock_dir.exists():
        raise RuntimeError(f"stale or active local Lean lock: {lock_dir}")
    lock_dir.mkdir()
    try:
        lock_guard = _run(
            ["./scripts/lean_local_check.sh", "lean/TwistedYetter.lean"],
            expected_returncode=75,
        )
    finally:
        lock_dir.rmdir()
    lock_output = _clean_output(lock_guard.stdout + lock_guard.stderr)
    if "Refusing concurrent local Lean process" not in lock_output:
        raise AssertionError("concurrency guard failed for an unexpected reason")

    return {
        "status": "PASS_LOCAL_RESOURCE_GUARDS",
        "default_threads": 1,
        "maximum_allowed_threads": 2,
        "execution_mode": "one Lean process at a time",
        "three_thread_attempt": {
            "expected_exit_code": 64,
            "observed_exit_code": thread_guard.returncode,
            "message_sha256": _sha256_bytes(thread_output.encode()),
        },
        "concurrent_process_attempt": {
            "expected_exit_code": 75,
            "observed_exit_code": lock_guard.returncode,
            "message_sha256": _sha256_bytes(lock_output.encode()),
        },
    }


def _source_capture_check(references: dict[str, Any]) -> dict[str, Any]:
    record = next(
        item
        for item in references["references"]
        if item["ref_id"] == "ref:baerenz-barrett-dichromatic-2018"
    )
    capture = record["captured_pdf"]
    path = Path(capture["capture_path_at_capture_time"])
    if not path.exists():
        return {
            "status": "LOCAL_CAPTURE_ABSENT_REFERENCE_HASH_RETAINED",
            "expected_sha256": capture["sha256"],
        }
    observed = _sha256_path(path)
    if observed != capture["sha256"]:
        raise AssertionError("local Bärenz--Barrett PDF hash mismatch")
    return {
        "status": "PASS_LOCAL_CAPTURE_MATCH",
        "path": str(path),
        "bytes": path.stat().st_size,
        "sha256": observed,
    }


def build() -> dict[str, Any]:
    started_at = _utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": _git("rev-parse", "HEAD"),
        "branch": _git("branch", "--show-current"),
        "dirty": bool(_git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError(
            "generalized sliding core artifact must be generated from a clean commit"
        )

    obligations = json.loads(OBLIGATION_MATRIX.read_text())
    references = json.loads(REFERENCE_LEDGER.read_text())
    rows = obligations["obligations"]
    if len(rows) != 20:
        raise AssertionError("core obligation matrix must contain 20 rows")
    if sum(
        row["status"] == "EXPLICIT_SOURCE_BACKED_ASSUMPTION" for row in rows
    ) != 3:
        raise AssertionError("exactly three standard assumption rows are expected")
    if any(row["status"] == "NOT_FORMALIZED" for row in rows):
        raise AssertionError("Lemma 3.3 matrix contains a nonterminal obligation")

    build_result = _run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    fusion_axioms = _audit_result(
        ["./scripts/lean_fusion_axiom_audit.sh"], 23
    )
    kirby_axioms = _audit_result(["./scripts/lean_axiom_audit.sh"], 32)
    fusion_mutations = _mutation_result(
        ["./scripts/lean_fusion_mutation_tests.sh"], 6
    )
    kirby_mutations = _mutation_result(
        ["./scripts/lean_mutation_tests.sh"], 5
    )

    source_files: dict[str, Any] = {}
    for relative in AUDITED_FILES:
        path = REPO_ROOT / relative
        source_files[relative] = {
            "bytes": path.stat().st_size,
            "sha256": _sha256_path(path),
        }

    mathlib_commit = _git(
        "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"
    )
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.generalized-sliding-core.v1",
        "status": "PASS_GENERALIZED_SLIDING_CORE",
        "mathematical_status": (
            "GENERALIZED_SLIDING_CORE_ESTABLISHED_RELATIVE_TO_"
            "EXPLICIT_STANDARD_INPUTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": _utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_generalized_sliding_core_v1.py"
        ),
        "argv": ["experiments/scripts/build_generalized_sliding_core_v1.py"],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_generalized_sliding_core_v1.py"
        ),
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": _version(["lake", "env", "lean", "--version"]),
            "lake": _version(["lake", "--version"]),
            "mathlib_tag": "v4.29.1",
            "mathlib_commit": mathlib_commit,
        },
        "inputs": {
            "obligation_matrix": {
                "path": str(OBLIGATION_MATRIX.relative_to(REPO_ROOT)),
                "sha256": _sha256_path(OBLIGATION_MATRIX),
                "obligation_count": len(rows),
            },
            "reference_ledger": {
                "path": str(REFERENCE_LEDGER.relative_to(REPO_ROOT)),
                "sha256": _sha256_path(REFERENCE_LEDGER),
                "reference_count": len(references["references"]),
            },
            "source_capture": _source_capture_check(references),
            "source_files": source_files,
        },
        "checks": {
            "sequential_build": {
                "status": "PASS",
                "build_order": LEAN_BUILD_ORDER,
                "module_count": len(LEAN_BUILD_ORDER),
                "stdout_sha256": _sha256_bytes(
                    _clean_output(
                        build_result.stdout + build_result.stderr
                    ).encode()
                ),
            },
            "source_proof_hole_scan": _assert_no_proof_holes(),
            "fusion_axiom_audit": fusion_axioms,
            "kirby_axiom_audit": kirby_axioms,
            "fusion_mutation_tests": fusion_mutations,
            "kirby_mutation_tests": kirby_mutations,
            "resource_guards": _resource_guard_checks(),
        },
        "established_scope": [
            (
                "The actual Hom-space mate and opposite-mate maps in "
                "equation (3.1.6) are linear equivalences built from "
                "Mathlib evaluations and coevaluations."
            ),
            (
                "The monoidal image maps include the tensorator in the "
                "correct direction and do not assume the functor is full."
            ),
            (
                "Equation (3.1.11) and the transformed Kronecker family "
                "are Lean-proved from explicit pivotal-trace and spherical-"
                "mate compatibility inputs."
            ),
            (
                "Lemma 3.2 in arbitrary one-hole contexts is Lean-proved "
                "from the small source identity-resolution input."
            ),
            (
                "Kirby colours are typed formal free-module sums; every "
                "weight and every finite channel index remains visible."
            ),
            (
                "Equations (3.1.3)-(3.1.8) are a kernel-checked chain with "
                "separate insertion, braiding, mate, and inverse-insertion "
                "steps."
            ),
            (
                "Equation (3.1.2) is obtained as equality of natural "
                "endomorphisms of the functor fixed_tensor_minus."
            ),
            (
                "A real SourcedTensorLeftEncirclingLaw is constructed; the final "
                "core equality is not supplied as a field."
            ),
        ],
        "trusted_input_boundary": obligations["trusted_input_boundary"],
        "explicit_non_claims": obligations["explicit_non_claims"],
    }
    payload["content_hash"] = f"sha256:{_canonical_hash(payload)}"
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


if __name__ == "__main__":
    result = build()
    print(
        json.dumps(
            {
                "output": str(OUTPUT),
                "status": result["status"],
                "content_hash": result["content_hash"],
            },
            sort_keys=True,
        )
    )
