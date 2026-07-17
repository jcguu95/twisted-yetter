#!/usr/bin/env python3
"""Build the finite-resolution and pairing-transport Lean certificate."""

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
OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "generalized-sliding-linear-bootstrap-v1.json"
)
OBLIGATION_MATRIX = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "generalized-sliding-linear-obligation-matrix-v1.json"
)
REFERENCE_LEDGER = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "lean-kirby-coupon-bootstrap-primary-sources-v1.json"
)

LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Fusion/FiniteResolution.lean",
    "lean/TwistedYetter/Fusion/PairingTransport.lean",
    "lean/TwistedYetter.lean",
]

MUTATIONS = [
    "lean/Mutations/MissingDualBasisProof.lean",
    "lean/Mutations/MissingPairingPreservation.lean",
    "lean/Mutations/WrongTransportedDualIndex.lean",
]

AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Fusion/AxiomAudit.lean",
    *MUTATIONS,
    "experiments/scripts/build_generalized_sliding_linear_bootstrap_v1.py",
    "tests/test_generalized_sliding_linear_bootstrap_v1.py",
    "scripts/lean_local_check.sh",
    "scripts/lean_local_build.sh",
    "scripts/lean_fusion_axiom_audit.sh",
    "scripts/lean_fusion_mutation_tests.sh",
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
            f"{argv!r} returned {result.returncode}, expected {expected_returncode}\n"
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
    checked = []
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


def build() -> dict[str, Any]:
    started_at = _utc_now()
    started_clock = time.perf_counter()
    git_before = {
        "commit": _git("rev-parse", "HEAD"),
        "branch": _git("branch", "--show-current"),
        "dirty": bool(_git("status", "--porcelain")),
    }

    obligations = json.loads(OBLIGATION_MATRIX.read_text())
    references = json.loads(REFERENCE_LEDGER.read_text())
    rows = obligations["obligations"]
    if len(rows) != 16:
        raise AssertionError("linear obligation matrix must contain exactly 16 rows")
    if sum(row["status"] == "NOT_FORMALIZED" for row in rows) != 3:
        raise AssertionError("exactly three future category/diagram obligations are expected")

    build_result = _run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = _run(["./scripts/lean_fusion_axiom_audit.sh"])
    mutation_result = _run(["./scripts/lean_fusion_mutation_tests.sh"])
    no_holes = _assert_no_proof_holes()
    resource_guards = _resource_guard_checks()

    axiom_output = _clean_output(axiom_result.stdout + axiom_result.stderr)
    if "sorryAx" in axiom_output:
        raise AssertionError("fusion axiom audit contains sorryAx")
    theorem_audit_lines = [
        line
        for line in axiom_output.splitlines()
        if "depends on axioms:" in line or "does not depend on any axioms" in line
    ]
    if len(theorem_audit_lines) != 13:
        raise AssertionError(
            f"expected 13 axiom-audited theorems, found {len(theorem_audit_lines)}"
        )

    mutation_output = _clean_output(mutation_result.stdout + mutation_result.stderr)
    mutation_pass_lines = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(mutation_pass_lines) != len(MUTATIONS):
        raise AssertionError(
            f"expected {len(MUTATIONS)} rejected mutations, "
            f"found {len(mutation_pass_lines)}"
        )

    source_hashes = {
        relative: {
            "sha256": _sha256_path(REPO_ROOT / relative),
            "bytes": (REPO_ROOT / relative).stat().st_size,
        }
        for relative in AUDITED_FILES
    }

    manifest = json.loads((REPO_ROOT / "lake-manifest.json").read_text())
    mathlib = next(
        package for package in manifest["packages"] if package["name"] == "mathlib"
    )
    finished_at = _utc_now()
    elapsed_milliseconds = round((time.perf_counter() - started_clock) * 1000)

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.generalized-sliding-linear-bootstrap.v1",
        "status": "PASS_GENERALIZED_SLIDING_LINEAR_BOOTSTRAP",
        "mathematical_status": (
            "ESTABLISHED_FINITE_RESOLUTION_AND_CONDITIONAL_PAIRING_TRANSPORT"
        ),
        "generator_script": str(Path(__file__).resolve().relative_to(REPO_ROOT)),
        "argv": sys.argv,
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_generalized_sliding_linear_bootstrap_v1.py"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": finished_at,
        "elapsed_milliseconds": elapsed_milliseconds,
        "repo_root": str(REPO_ROOT),
        "git": git_before,
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": _version(["lean", "--version"]),
            "lake": _version(["lake", "--version"]),
            "mathlib_tag": mathlib["inputRev"],
            "mathlib_commit": mathlib["rev"],
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
            "source_files": source_hashes,
        },
        "checks": {
            "sequential_build": {
                "status": "PASS",
                "module_count": len(LEAN_BUILD_ORDER),
                "build_order": LEAN_BUILD_ORDER,
                "stdout_sha256": _sha256_bytes(
                    _clean_output(build_result.stdout + build_result.stderr).encode()
                ),
            },
            "axiom_audit": {
                "status": "PASS_NO_SORRY_AX",
                "theorem_count": len(theorem_audit_lines),
                "observed_standard_axioms": [
                    "propext",
                    "Classical.choice",
                    "Quot.sound",
                ],
                "output_sha256": _sha256_bytes(axiom_output.encode()),
                "theorems": theorem_audit_lines,
            },
            "mutation_tests": {
                "status": "PASS_ALL_BAD_INPUTS_REJECTED",
                "rejected_count": len(mutation_pass_lines),
                "rejections": mutation_pass_lines,
                "output_sha256": _sha256_bytes(mutation_output.encode()),
            },
            "source_proof_hole_scan": no_holes,
            "resource_guards": resource_guards,
        },
        "established_scope": [
            "Finite weighted families have an explicit index type, weights, and reindex-invariant total.",
            "A perfect pairing is an explicit linear equivalence to the linear dual.",
            "DualBasisData binds a complete finite basis to actual paired vectors and exact algebraic dual-basis equality.",
            "Dual-basis coefficients reconstruct every vector by a kernel-checked finite sum.",
            "Linear resolutions remain sound under finite reindexing and linear maps.",
            "Given explicit pairing-preserving primal and dual linear equivalences, transported dual vectors are the canonical dual basis.",
            "Under that supplied transport proof, every insertion channel and the complete reconstructed sum agree after transport.",
        ],
        "conditional_boundary": {
            "status": "LINEAR_SKELETON_PROVED_CATEGORY_INSTANCE_NOT_YET_CONSTRUCTED",
            "interface": "TwistedYetter.Fusion.PairingTransport",
            "required_future_evidence": [
                "Actual categorical left/right mate equivalences on the Hom spaces in Bärenz-Barrett Lemma 3.3.",
                "A pivotal-functor proof that those mate equivalences preserve the relevant trace pairing.",
                "Explicit typed diagrams and a certified equality chain for equations (3.1.2)-(3.1.11).",
                "Construction of TwistedYetter.Kirby.HandleSlide.SourcedSlidingLaw from that chain.",
            ],
        },
        "explicit_non_claims": [
            "This does not define a fusion, pivotal, braided, ribbon, or modular category.",
            "This does not construct categorical mate maps.",
            "This does not prove that a pivotal functor preserves the trace pairing.",
            "This does not formalize Bärenz-Barrett Lemma 3.3 or Lemma 3.4.",
            "This does not construct a SourcedSlidingLaw.",
            "This does not establish handle-slide, Kirby-calculus, or four-manifold invariance.",
        ],
    }
    payload["content_hash"] = f"sha256:{_canonical_hash(payload)}"
    return payload


def main() -> None:
    payload = build()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"wrote {OUTPUT}")


if __name__ == "__main__":
    main()
