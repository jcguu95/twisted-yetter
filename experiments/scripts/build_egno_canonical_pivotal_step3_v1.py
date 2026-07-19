#!/usr/bin/env python3
"""Build the source-bound certificate for canonical pivotal Step 3."""

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
    "egno-canonical-pivotal-step3-v1.json"
)
ROADMAP = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "egno-canonical-pivotal-primary-sources-v1.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_canonical_pivotal_step3_v1.py",
    "tests/test_egno_canonical_pivotal_step3_v1.py",
    "lean/TwistedYetter/Fusion/EGNORibbon.lean",
    "lean/TwistedYetter/Fusion/EGNOCanonicalPivotal.lean",
    "lean/TwistedYetter/Fusion/EGNOCanonicalPivotalAxiomAudit.lean",
    "lean/TwistedYetter/Fusion/EGNODoubleDualRegression.lean",
    "lean/TwistedYetter/Fusion/AxiomAudit.lean",
    "lean/Mutations/WrongDrinfeldMirror.lean",
    "lean/Mutations/WrongCanonicalInverseTwist.lean",
    "lean/Mutations/WrongDoubleDualOrder.lean",
    "lean/Mutations/MissingDrinfeldNaturalityWitness.lean",
    "lean/Mutations/DrinfeldHomIsNotObjectwiseIso.lean",
    "lean/Mutations/WrongDrinfeldNaturalityTarget.lean",
    "lean/Mutations/WrongMonodromyMirror.lean",
    "lean/Mutations/OrdinaryIdentityIsNotMonodromyTensorator.lean",
    "lean/Mutations/MissingDrinfeldMonodromyDefect.lean",
    "scripts/lean_egno_canonical_pivotal_axiom_audit.sh",
    "scripts/lean_egno_canonical_pivotal_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    str(ROADMAP.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
]


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


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
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


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
    return (result.stdout or result.stderr).strip().splitlines()[0]


def output_tail(result: subprocess.CompletedProcess[str]) -> str:
    lines = (result.stdout + result.stderr).strip().splitlines()
    return lines[-1] if lines else "(no output)"


def proof_hole_scan() -> dict[str, Any]:
    forbidden = re.compile(
        r"\b(sorry|admit|native_decide)\b|^\s*axiom\b",
        re.MULTILINE,
    )
    checked: list[str] = []
    for relative in SOURCE_FILES:
        if not relative.endswith(".lean"):
            continue
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
            "canonical pivotal Step 3 artifact requires a clean source commit"
        )

    roadmap = json.loads(ROADMAP.read_text())
    references = json.loads(REFERENCES.read_text())
    if roadmap["status"] != "STEP_3_ESTABLISHED_STEPS_4_TO_10_EXPLICIT":
        raise AssertionError("unexpected roadmap status")
    statuses = [step["status"] for step in roadmap["steps"]]
    if statuses[:3] != ["ESTABLISHED_IN_LEAN"] * 3:
        raise AssertionError("Steps 1 through 3 must be established")
    if any(status != "NOT_YET_ESTABLISHED" for status in statuses[3:]):
        raise AssertionError("a post-Step-3 obligation was silently promoted")

    capture = references["references"][0]["captured_pdf"]
    capture_path = Path(capture["capture_path_at_capture_time"])
    if not capture_path.exists():
        raise AssertionError("the pinned local EGNO PDF is absent")
    if capture_path.stat().st_size != capture["bytes"]:
        raise AssertionError("the pinned EGNO PDF size changed")
    if sha256_path(capture_path) != capture["sha256"]:
        raise AssertionError("the pinned EGNO PDF hash changed")

    module_text = (
        REPO_ROOT
        / "lean/TwistedYetter/Fusion/EGNOCanonicalPivotal.lean"
    ).read_text()
    required_contracts = [
        "def monodromyIdMonoidal",
        "def drinfeldDoubleDualMonoidal",
        "theorem drinfeldDoubleDual_μ",
        "theorem drinfeld_tensor_defect",
        "theorem balancedTwist_unit",
        "theorem canonicalPivotal_isMonoidal",
        "def canonicalPivotalStructure",
    ]
    missing = [
        contract for contract in required_contracts
        if contract not in module_text
    ]
    if missing:
        raise AssertionError(f"missing Step 3 contracts: {missing}")

    build_result = run(["lake", "build", "TwistedYetter"])
    regression_result = run([
        "lake",
        "build",
        "TwistedYetter.Fusion.EGNODoubleDualRegression",
    ])
    axiom_result = run(
        ["./scripts/lean_egno_canonical_pivotal_axiom_audit.sh"]
    )
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 3 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 19:
        raise AssertionError(
            f"expected 19 audited declarations, got {audited_declarations}"
        )

    mutations = run(
        ["./scripts/lean_egno_canonical_pivotal_mutation_tests.sh"]
    )
    rejections = [
        line for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 9:
        raise AssertionError("expected nine rejected Step 1-3 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-canonical-pivotal-step3.v1",
        "status": "PASS_STEP_3_MONOIDAL_PIVOTAL_STRUCTURE_ESTABLISHED",
        "mathematical_status": (
            "MONOIDAL_PIVOTAL_STRUCTURE_ESTABLISHED_"
            "SPHERICALITY_AND_TRACE_CYCLICITY_OPEN"
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
            "build_egno_canonical_pivotal_step3_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_egno_canonical_pivotal_step3_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/"
            "build_egno_canonical_pivotal_step3_v1.py"
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
            "roadmap": {
                "path": str(ROADMAP.relative_to(REPO_ROOT)),
                "sha256": sha256_path(ROADMAP),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "sha256": sha256_path(REFERENCES),
            },
            "egno_pdf": {
                "path_at_capture_time": str(capture_path),
                "bytes": capture["bytes"],
                "sha256": capture["sha256"],
            },
            "source_files": source_files,
        },
        "checks": {
            "full_lean_build": {
                "status": "PASS",
                "command": "LEAN_NUM_THREADS=1 lake build TwistedYetter",
                "output_tail": output_tail(build_result),
            },
            "minimal_right_dual_regression": {
                "status": "PASS_RIGHT_RIGID_ONLY",
                "command": (
                    "LEAN_NUM_THREADS=1 lake build "
                    "TwistedYetter.Fusion.EGNODoubleDualRegression"
                ),
                "output_tail": output_tail(regression_result),
            },
            "axiom_audit": {
                "status": "PASS_NO_SORRYAX_OR_NATIVE_ORACLE",
                "audited_declaration_count": audited_declarations,
            },
            "mutations": {
                "status": "PASS_FAIL_CLOSED",
                "rejected_count": len(rejections),
                "rejections": rejections,
            },
            "proof_hole_scan": proof_hole_scan(),
            "source_capture": "PASS_LOCAL_EGNO_PDF_HASH_MATCH",
        },
        "established": [
            (
                "The positive double braiding is the tensorator inherited "
                "from the monoidal-opposite round trip."
            ),
            (
                "Transport across the Drinfeld natural isomorphism gives a "
                "coherent monoidal structure on the right double dual."
            ),
            (
                "The Drinfeld tensor defect is exactly positive monodromy, "
                "matching EGNO equation (8.31)."
            ),
            (
                "The balancing law cancels the defect, so theta_X followed "
                "by u_X is a monoidal natural isomorphism."
            ),
            (
                "Every RibbonStructure now determines a kernel-checked "
                "canonical PivotalStructure."
            ),
        ],
        "remaining_blockers": [
            "Derive sphericality from ribbon dual compatibility.",
            "Derive or source-bind spherical trace cyclicity.",
            "Build the finite semisimple fusion and later Kirby interfaces.",
        ],
        "explicit_non_claims": roadmap["explicit_non_claims"],
    }
    payload["content_hash"] = canonical_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return payload


if __name__ == "__main__":
    result = build()
    print(json.dumps({
        "output": str(OUTPUT),
        "status": result["status"],
        "content_hash": result["content_hash"],
    }, indent=2))
