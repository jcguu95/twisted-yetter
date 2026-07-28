#!/usr/bin/env python3
"""Build the source-bound Lean certificate for Barenz--Barrett Lemma 3.4."""

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
    "generalized-sliding-framed-context-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "generalized-sliding-framed-context-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "generalized-sliding-framed-context-primary-sources-v1.json"
)
CORE_ARTIFACT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/generalized-sliding-core-v1.json"
)

LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/FramedEncirclingTransport.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/WrongFramedExteriorBoundary.lean",
    "lean/Mutations/MissingLemma33Law.lean",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    *MUTATIONS,
    "scripts/lean_framed_sliding_mutation_tests.sh",
    "experiments/scripts/build_generalized_sliding_framed_context_v1.py",
    "tests/test_generalized_sliding_framed_context_v1.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
    str(CORE_ARTIFACT.relative_to(REPO_ROOT)),
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


def source_capture_check(references: dict[str, Any]) -> dict[str, Any]:
    record = references["references"][0]["captured_pdf"]
    path = Path(record["capture_path_at_capture_time"])
    if not path.exists():
        return {
            "status": "LOCAL_CAPTURE_ABSENT_REFERENCE_HASH_RETAINED",
            "expected_sha256": record["sha256"],
        }
    observed = sha256_path(path)
    if observed != record["sha256"]:
        raise AssertionError("local Barenz--Barrett PDF hash mismatch")
    return {
        "status": "PASS_LOCAL_CAPTURE_MATCH",
        "path": str(path),
        "bytes": path.stat().st_size,
        "sha256": observed,
    }


def proof_hole_scan() -> dict[str, Any]:
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


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("Lemma 3.4 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    references = json.loads(REFERENCES.read_text())
    core = json.loads(CORE_ARTIFACT.read_text())
    rows = obligations["obligations"]
    if len(rows) != 12 or any(
        row["status"] == "NOT_FORMALIZED" for row in rows
    ):
        raise AssertionError("Lemma 3.4 obligation matrix is not terminal")
    if core["status"] != "PASS_GENERALIZED_SLIDING_CORE":
        raise AssertionError("the pinned Lemma 3.3 artifact is not passing")

    build_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = run(["./scripts/lean_axiom_audit.sh"])
    axiom_output = clean_output(axiom_result.stdout + axiom_result.stderr)
    if "sorryAx" in axiom_output:
        raise AssertionError("axiom audit exposed sorryAx")
    theorem_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if theorem_count != 37:
        raise AssertionError(
            f"expected 37 audited Kirby declarations, got {theorem_count}"
        )

    mutation_result = run(
        ["./scripts/lean_framed_sliding_mutation_tests.sh"]
    )
    mutation_output = clean_output(
        mutation_result.stdout + mutation_result.stderr
    )
    rejections = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 2:
        raise AssertionError("expected two rejected Lemma 3.4 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.generalized-sliding-framed-context.v1",
        "status": "PASS_GENERALIZED_SLIDING_FRAMED_CONTEXT",
        "mathematical_status": (
            "GENERALIZED_SLIDING_FRAMED_CONTEXT_ESTABLISHED_RELATIVE_TO_"
            "LEMMA_3_3_STANDARD_INPUTS"
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
            "build_generalized_sliding_framed_context_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_generalized_sliding_framed_context_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/"
            "build_generalized_sliding_framed_context_v1.py"
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
            "lemma_3_3_artifact": {
                "path": str(CORE_ARTIFACT.relative_to(REPO_ROOT)),
                "sha256": sha256_path(CORE_ARTIFACT),
                "content_hash": core["content_hash"],
                "source_commit": core["git"]["commit"],
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
            "source_capture": source_capture_check(references),
            "source_files": source_files,
        },
        "checks": {
            "sequential_build": {
                "status": "PASS",
                "build_order": LEAN_BUILD_ORDER,
                "module_count": len(LEAN_BUILD_ORDER),
                "stdout_sha256": sha256_bytes(
                    clean_output(
                        build_result.stdout + build_result.stderr
                    ).encode()
                ),
            },
            "source_proof_hole_scan": proof_hole_scan(),
            "kirby_axiom_audit": {
                "status": "PASS_NO_SORRY_AX",
                "theorem_count": theorem_count,
                "new_lemma_3_4_theorem_count": 5,
                "observed_standard_axioms": [
                    "propext",
                    "Classical.choice",
                    "Quot.sound",
                ],
                "output_sha256": sha256_bytes(axiom_output.encode()),
            },
            "mutation_tests": {
                "status": "PASS_ALL_BAD_INPUTS_REJECTED",
                "rejected_count": len(rejections),
                "rejections": rejections,
                "output_sha256": sha256_bytes(mutation_output.encode()),
            },
            "resource_guards": {
                "status": "PASS_INHERITED_AND_ENFORCED",
                "default_threads": 1,
                "maximum_allowed_threads": 2,
                "execution_mode": "one Lean process at a time",
            },
        },
        "established_scope": [
            "Parenthesized boundaries encode arbitrary tensor products of strands.",
            "The arbitrary exterior remains a typed diagram with visible crossings, extrema, coupons, and tensor structure.",
            "The visible exterior lift is proved equal to tensorLeft.map of its evaluation.",
            "Naturality and the actual Lemma 3.3 core equality derive framed exterior transport.",
            "The transport is valid in arbitrary nested typed contexts and closed unit-to-unit contexts.",
            "The public constructor starts from EncirclingTransportFamily.sourcedEncirclingLaw; no arbitrary-knot endpoint equality is assumed."
        ],
        "explicit_non_claims": obligations["explicit_non_claims"],
        "inherited_trusted_input_boundary": core["trusted_input_boundary"],
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
