#!/usr/bin/env python3
"""Build the source-bound certificate for canonical pivotal Step 1."""

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
    "egno-canonical-pivotal-step1-v1.json"
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
    "experiments/scripts/build_egno_canonical_pivotal_step1_v1.py",
    "tests/test_egno_canonical_pivotal_step1_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNORibbon.lean",
    "lean/TwistedYetter/Fusion/EGNOCanonicalPivotal.lean",
    "lean/TwistedYetter/Fusion/EGNOCanonicalPivotalAxiomAudit.lean",
    "lean/TwistedYetter/Fusion/AxiomAudit.lean",
    "lean/Mutations/WrongDrinfeldMirror.lean",
    "lean/Mutations/WrongCanonicalInverseTwist.lean",
    "lean/Mutations/WrongDoubleDualOrder.lean",
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
            "canonical pivotal Step 1 artifact requires a clean source commit"
        )

    roadmap = json.loads(ROADMAP.read_text())
    references = json.loads(REFERENCES.read_text())
    if roadmap["status"] != "STEP_1_ESTABLISHED_LATER_STEPS_EXPLICIT":
        raise AssertionError("unexpected roadmap status")
    if roadmap["steps"][0]["status"] != "ESTABLISHED_IN_LEAN":
        raise AssertionError("Step 1 is not established")
    if any(
        step["status"] != "NOT_YET_ESTABLISHED"
        for step in roadmap["steps"][1:]
    ):
        raise AssertionError("a later roadmap step was silently promoted")

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
        "def drinfeldHom",
        "(β_ X (Xᘁ)).hom",
        "def canonicalPivotalHom",
        "iso.hom.app X ≫ drinfeldHom X",
        "theorem canonicalPivotalHom_eq",
    ]
    missing = [
        contract for contract in required_contracts
        if contract not in module_text
    ]
    if missing:
        raise AssertionError(f"missing Step 1 contracts: {missing}")

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(
        ["./scripts/lean_egno_canonical_pivotal_axiom_audit.sh"]
    )
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 1 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 3:
        raise AssertionError(
            f"expected 3 audited declarations, got {audited_declarations}"
        )

    mutations = run(
        ["./scripts/lean_egno_canonical_pivotal_mutation_tests.sh"]
    )
    rejections = [
        line for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 3:
        raise AssertionError("expected three rejected convention mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-canonical-pivotal-step1.v1",
        "status": "PASS_STEP_1_OBJECTWISE_CANONICAL_PIVOTAL_FORMULA",
        "mathematical_status": (
            "OBJECTWISE_FORMULA_ESTABLISHED_"
            "NATURALITY_INVERTIBILITY_MONOIDALITY_OPEN"
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
            "build_egno_canonical_pivotal_step1_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_egno_canonical_pivotal_step1_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/"
            "build_egno_canonical_pivotal_step1_v1.py"
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
                "output_tail": (
                    build_result.stdout + build_result.stderr
                ).strip().splitlines()[-1],
            },
            "axiom_audit": {
                "status": "PASS_NO_SORRYAX_OR_NATIVE_ORACLE",
                "audited_declaration_count": audited_declarations,
            },
            "convention_mutations": {
                "status": "PASS_FAIL_CLOSED",
                "rejected_count": len(rejections),
                "rejections": rejections,
            },
            "proof_hole_scan": proof_hole_scan(),
            "source_capture": "PASS_LOCAL_EGNO_PDF_HASH_MATCH",
        },
        "established": [
            "The non-strict Drinfeld morphism has the EGNO (8.30) crossing and dual order.",
            "The objectwise canonical pivotal candidate is theta_X followed by u_X.",
            "Mirror braiding, inverse twist, and left/right double-dual conflation fail closed."
        ],
        "remaining_blockers": [
            "Prove naturality of the Drinfeld and canonical pivotal components.",
            "Construct and prove an objectwise inverse.",
            "Construct the monoidal double-dual functor.",
            "Prove canonical pivotal monoidality and sphericality."
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
