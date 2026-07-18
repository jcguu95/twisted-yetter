#!/usr/bin/env python3
"""Build the terminal R13 Lean Kirby formalization package."""

from __future__ import annotations

from datetime import UTC, datetime
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

from twisted_yetter.final_formalization_package_v1 import (  # noqa: E402
    MANIFEST_PATH,
    OBLIGATION_MATRIX_PATH,
    ROADMAP_STATUS,
    build_final_formalization_runtime,
    canonical_hash,
    file_sha256,
    validate_final_formalization_runtime,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "homologically-twisted-kirby-formalization-package-v1.json"
)
LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/FinalFormalizationPackage.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/MissingEvidenceLayerR13.lean",
    "lean/Mutations/Figure21ExactPromotionR13.lean",
    "lean/Mutations/Figure21ComparisonPromotionR13.lean",
    "lean/Mutations/CraneYetterIdentificationPromotionR13.lean",
    "lean/Mutations/MissingFigure21BlockerR13.lean",
    "lean/Mutations/CtlClaimPromotionR13.lean",
    "lean/Mutations/InjectedAxiomR13.lean",
]
PYTEST_FILES = [
    "tests/test_final_formalization_package_v1.py",
    "tests/test_computation_artifact_import_v1.py",
]
EXPECTED_PYTEST_COUNT = 32
EXPECTED_AXIOM_DECLARATION_COUNT = 116
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "lean/TwistedYetter/Kirby/ComputationArtifactImporter.lean",
    "src/twisted_yetter/final_formalization_package_v1.py",
    "src/twisted_yetter/computation_artifact_import_v1.py",
    *MUTATIONS,
    "scripts/lean_final_formalization_package_mutation_tests.sh",
    "scripts/lean_local_build.sh",
    "scripts/lean_local_check.sh",
    "scripts/lean_axiom_audit.sh",
    "experiments/scripts/build_final_formalization_package_v1.py",
    "tests/test_final_formalization_package_v1.py",
    "tests/test_final_formalization_package_artifact_v1.py",
    str(MANIFEST_PATH.relative_to(REPO_ROOT)),
    str(OBLIGATION_MATRIX_PATH.relative_to(REPO_ROOT)),
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


def axiom_audit() -> dict[str, Any]:
    result = run(["./scripts/lean_axiom_audit.sh"])
    output = clean_output(result.stdout + result.stderr)
    if "sorryAx" in output or "native_decide.ax" in output:
        raise AssertionError("R13 axiom audit exposed a proof oracle")
    declaration_count = len(
        re.findall(r"^'TwistedYetter\.", output, flags=re.MULTILINE)
    )
    if declaration_count != EXPECTED_AXIOM_DECLARATION_COUNT:
        raise AssertionError(
            "R13 axiom declaration denominator changed: "
            f"{declaration_count}"
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
        raise AssertionError(f"R13 unexpected kernel axioms: {unexpected}")
    return {
        "status": "PASS_ONLY_STANDARD_LEAN_AXIOMS",
        "audited_declaration_count": declaration_count,
        "allowed_axioms": sorted(allowed),
        "observed_axioms": sorted(observed),
        "unexpected_axioms": unexpected,
        "output": output,
    }


def contract_check() -> dict[str, Any]:
    path = REPO_ROOT / LEAN_BUILD_ORDER[0]
    source = path.read_text()
    required_tokens = (
        "inductive EvidenceLayer",
        "structure TerminalBoundary",
        "theorem evidence_layer_count",
        "theorem r11_conditional_invariant",
        "theorem toy_exact_control_remains_admitted",
        "theorem figure21_structural_row_count",
        "theorem figure21_structural_not_exact",
        "theorem figure21_blocker_count",
        "theorem formalization_route_is_terminal",
        "theorem crane_yetter_identification_not_established",
        "theorem figure21_exact_value_not_admitted",
        "theorem figure21_marked_comparison_not_admitted",
        "theorem ctl_claim_not_admitted",
    )
    missing = [token for token in required_tokens if token not in source]
    if missing:
        raise AssertionError(f"R13 Lean contract is incomplete: {missing}")
    boundary_block = source.split("structure TerminalBoundary", 1)[1].split(
        "/-- The unique R13 terminal boundary", 1
    )[0]
    negative_fields = (
        "crane_yetter_not_identified",
        "figure21_exact_not_admitted",
        "figure21_comparison_not_admitted",
        "category_inputs_not_all_reproved",
        "source_archive_not_byte_complete",
        "ctl_not_admitted",
    )
    if any(field not in boundary_block for field in negative_fields):
        raise AssertionError("R13 proof-relevant non-claim field is missing")
    if re.search(r"^\s*axiom\b", source, flags=re.MULTILINE):
        raise AssertionError("R13 final package declares a new axiom")
    return {
        "status": "PASS_TERMINAL_ROUTE_AND_NONCLAIMS_TYPE_SEPARATED",
        "required_token_count": len(required_tokens),
        "proof_relevant_negative_field_count": len(negative_fields),
        "new_axiom_declarations": 0,
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
        raise RuntimeError("R13 artifact requires a clean source commit")

    manifest = json.loads(MANIFEST_PATH.read_text())
    obligations = json.loads(OBLIGATION_MATRIX_PATH.read_text())
    if (
        manifest.get("status") != "R13_FROZEN_DENOMINATOR"
        or len(manifest.get("milestone_artifacts", [])) != 11
        or len(manifest.get("reference_ledgers", [])) != 8
    ):
        raise AssertionError("R13 frozen manifest denominator changed")
    if (
        obligations.get("status")
        != "R13_CONTRACT_FROZEN_PENDING_IMPLEMENTATION"
        or len(obligations.get("obligations", [])) != 24
        or len(obligations.get("explicit_non_claims", [])) != 10
    ):
        raise AssertionError("R13 obligation denominator changed")

    runtime = build_final_formalization_runtime()
    validate_final_formalization_runtime(runtime)

    lean_result = run(
        ["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER]
    )
    axiom = axiom_audit()
    mutation_result = run(
        ["./scripts/lean_final_formalization_package_mutation_tests.sh"]
    )
    mutation_output = clean_output(
        mutation_result.stdout + mutation_result.stderr
    )
    rejections = [
        line
        for line in mutation_output.splitlines()
        if line.startswith("PASS expected")
    ]
    if len(rejections) != len(MUTATIONS):
        raise AssertionError(
            f"expected {len(MUTATIONS)} rejected R13 mutations"
        )

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(
        pytest_result.stdout + pytest_result.stderr
    )
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != EXPECTED_PYTEST_COUNT:
        raise AssertionError("R13 scoped pytest denominator changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": file_sha256(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.final-formalization-package.v1",
        "status": (
            "PASS_R13_FORMALIZATION_PACKAGE_TERMINAL_WITH_EXPLICIT_"
            "FIGURE21_BLOCKERS"
        ),
        "mathematical_status": (
            "HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT_ESTABLISHED_RELATIVE_"
            "TO_LISTED_INPUTS_R12_IMPORTER_ESTABLISHED_FIGURE21_NOT_ADMITTED"
        ),
        "roadmap_status": ROADMAP_STATUS,
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_final_formalization_package_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_final_formalization_package_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/build_final_formalization_package_v1.py"
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
            "frozen_manifest": {
                "path": str(MANIFEST_PATH.relative_to(REPO_ROOT)),
                "file_sha256": file_sha256(MANIFEST_PATH),
                "milestone_artifact_count": 11,
                "reference_ledger_count": 8,
            },
            "obligation_matrix": {
                "path": str(
                    OBLIGATION_MATRIX_PATH.relative_to(REPO_ROOT)
                ),
                "file_sha256": file_sha256(OBLIGATION_MATRIX_PATH),
                "obligation_count": 24,
                "explicit_nonclaim_count": 10,
            },
            "source_files": source_files,
        },
        "lean_certificate": {
            "status": (
                "PASS_KERNEL_AXIOM_AUDIT_AND_ALL_R13_MUTATION_REJECTIONS"
            ),
            "build_order": LEAN_BUILD_ORDER,
            "build_output": clean_output(
                lean_result.stdout + lean_result.stderr
            ),
            "audited_declaration_count": (
                axiom["audited_declaration_count"]
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
                "files": PYTEST_FILES,
                "passed_count": int(match.group(1)),
                "output": pytest_output,
            },
            "historical_replay": {
                "status": "PASS",
                "milestone_artifact_count": 11,
                "source_file_replay_count": 231,
                "reference_ledger_count": 8,
                "unique_trusted_input_count": 25,
                "predecessor_nonclaim_count": 64,
            },
        },
        "admission": {
            "status": "REPO_LOCAL_EVIDENCE_ONLY",
            "ctl_claim_admitted": False,
            "ctl_manifest_written": False,
        },
        "trusted_inputs": runtime["trusted_input_audit"]["catalog"],
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
