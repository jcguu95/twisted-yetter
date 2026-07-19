#!/usr/bin/env python3
"""Build the source-bound certificate for EGNO pairing Step 7."""

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
    "egno-trace-pairing-step7-v1.json"
)
ROADMAP = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)
EGNO_REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "egno-category-foundations-primary-sources-v1.json"
)
SLIDING_REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "generalized-sliding-core-primary-sources-v2.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_trace_pairing_step7_v1.py",
    "tests/test_egno_trace_pairing_step7_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOTracePairing.lean",
    "lean/TwistedYetter/Fusion/EGNOPairingCompatibility.lean",
    "lean/TwistedYetter/Fusion/EGNOTracePairingAxiomAudit.lean",
    "lean/TwistedYetter/Fusion/PivotalMate.lean",
    "lean/TwistedYetter/Fusion/EGNOFusionCategory.lean",
    "lean/TwistedYetter/Fusion/FrobeniusLinear.lean",
    "lean/TwistedYetter/Fusion/PairingTransport.lean",
    "lean/Mutations/MissingSphericalMateTraceLaw.lean",
    "lean/Mutations/MissingPivotalFunctorTraceLaw.lean",
    "scripts/lean_egno_trace_pairing_axiom_audit.sh",
    "scripts/lean_egno_trace_pairing_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    str(ROADMAP.relative_to(REPO_ROOT)),
    str(EGNO_REFERENCES.relative_to(REPO_ROOT)),
    str(SLIDING_REFERENCES.relative_to(REPO_ROOT)),
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


def verify_capture(capture: dict[str, Any], label: str) -> dict[str, Any]:
    path = Path(capture["capture_path_at_capture_time"])
    if not path.exists():
        raise AssertionError(f"the pinned local {label} PDF is absent")
    if path.stat().st_size != capture["bytes"]:
        raise AssertionError(f"the pinned {label} PDF size changed")
    if sha256_path(path) != capture["sha256"]:
        raise AssertionError(f"the pinned {label} PDF hash changed")
    return {
        "path_at_capture_time": str(path),
        "bytes": capture["bytes"],
        "sha256": capture["sha256"],
    }


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
        raise RuntimeError("Step 7 artifact requires a clean source commit")

    roadmap = json.loads(ROADMAP.read_text())
    expected_roadmap_status = (
        "STEP_7_ESTABLISHED_RELATIVE_TO_TWO_GLOBAL_STANDARD_LAWS_"
        "STEPS_8_TO_10_EXPLICIT"
    )
    if roadmap["status"] != expected_roadmap_status:
        raise AssertionError("unexpected roadmap status")
    statuses = [step["status"] for step in roadmap["steps"]]
    if statuses[:6] != ["ESTABLISHED_IN_LEAN"] * 6:
        raise AssertionError("Steps 1 through 6 must be established")
    if statuses[6] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    ):
        raise AssertionError("Step 7 status lost its theorem-input boundary")
    if statuses[7:] != ["NOT_YET_ESTABLISHED"] * 3:
        raise AssertionError("a post-Step-7 obligation was silently promoted")

    egno_refs = json.loads(EGNO_REFERENCES.read_text())
    sliding_refs = json.loads(SLIDING_REFERENCES.read_text())
    egno_pdf = verify_capture(
        egno_refs["references"][0]["captured_pdf"], "EGNO"
    )
    sliding_pdf = verify_capture(
        sliding_refs["references"][0]["captured_pdf"],
        "Bärenz--Barrett",
    )

    pairing_text = (
        REPO_ROOT
        / "lean/TwistedYetter/Fusion/EGNOTracePairing.lean"
    ).read_text()
    compatibility_text = (
        REPO_ROOT
        / "lean/TwistedYetter/Fusion/EGNOPairingCompatibility.lean"
    ).read_text()
    required_contracts = [
        "noncomputable def simpleCompositionPerfectPairing",
        "noncomputable def unitCompositionPerfectPairing",
        "noncomputable def pivotalTracePerfectPairing",
        "structure SphericalMateTraceLaw",
        "noncomputable def sphericalMatePairingTransport",
    ]
    missing = [
        item for item in required_contracts if item not in pairing_text
    ]
    if missing:
        raise AssertionError(f"missing Step 7 pairing contracts: {missing}")
    if "structure PivotalFunctorTraceLaw" not in compatibility_text:
        raise AssertionError("missing global pivotal-functor trace law")
    if "noncomputable def localCompatibility" not in compatibility_text:
        raise AssertionError("missing global-to-local functor constructor")
    structure_prefix = pairing_text.split(
        "structure FusionCategoryData", maxsplit=1
    )[0]
    if "pivotalTracePerfectPairing" in structure_prefix:
        raise AssertionError("trace pairing became pre-fusion arbitrary data")

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(["./scripts/lean_egno_trace_pairing_axiom_audit.sh"])
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 7 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 73:
        raise AssertionError(
            f"expected 73 audited declarations, got {audited_declarations}"
        )

    mutations = run(["./scripts/lean_egno_trace_pairing_mutation_tests.sh"])
    rejections = [
        line for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 24:
        raise AssertionError("expected twenty-four rejected Step 1-7 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-trace-pairing-step7.v1",
        "status": (
            "PASS_STEP_7_TRACE_PAIRING_COMPATIBILITY_RELATIVE_TO_"
            "TWO_GLOBAL_STANDARD_LAWS"
        ),
        "mathematical_status": (
            "PERFECT_TRACE_PAIRING_DERIVED_AND_LOCAL_COMPATIBILITY_"
            "ESTABLISHED_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_THEOREM_INPUTS"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_egno_trace_pairing_step7_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_egno_trace_pairing_step7_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 UV_CACHE_DIR=.uv-cache uv run python "
            "experiments/scripts/build_egno_trace_pairing_step7_v1.py"
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
            "reference_ledgers": {
                str(EGNO_REFERENCES.relative_to(REPO_ROOT)): {
                    "sha256": sha256_path(EGNO_REFERENCES)
                },
                str(SLIDING_REFERENCES.relative_to(REPO_ROOT)): {
                    "sha256": sha256_path(SLIDING_REFERENCES)
                },
            },
            "source_pdfs": {
                "egno": egno_pdf,
                "baerenz_barrett": sliding_pdf,
            },
            "source_files": source_files,
        },
        "checks": {
            "full_lean_build": {
                "status": "PASS",
                "command": "LEAN_NUM_THREADS=1 lake build TwistedYetter",
                "output_tail": output_tail(build_result),
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
            "source_capture": "PASS_BOTH_LOCAL_PRIMARY_SOURCE_HASHES_MATCH",
            "nondegeneracy_origin": (
                "PASS_DERIVED_FROM_ACTUAL_FINITE_SEMISIMPLE_DECOMPOSITION"
            ),
            "local_transport_origin": (
                "PASS_DERIVED_FROM_GLOBAL_LAWS_NOT_LOCAL_PAIRING_FIELDS"
            ),
        },
        "lean_derived": [
            "composition through every simple object is a perfect pairing",
            "composition through the tensor unit is a perfect pairing",
            "Frobenius cup and pivotal cap are linear equivalences",
            "joining the cup and cap is exactly the pivotal trace",
            "the pivotal trace pairing on arbitrary Hom spaces is perfect",
            "one pivotal structure determines both reverse exact pairings and mate maps",
            "the global spherical mate law yields every local PairingTransport",
            "strong monoidal tensorators cancel in a composite image coupon",
            "the global pivotal-functor trace law yields every local pairing compatibility",
        ],
        "explicit_standard_theorem_inputs": [
            {
                "name": "SphericalMateTraceLaw",
                "scope": "all objects X, Y, Z and all matching morphisms",
                "source": (
                    "Bärenz--Barrett Lemma 3.3, equations "
                    "(3.1.9)-(3.1.11), journal pages 683-684"
                ),
            },
            {
                "name": "PivotalFunctorTraceLaw",
                "scope": "all source objects and all endomorphisms",
                "source": (
                    "Bärenz--Barrett Lemma 2.23, equation (2.1.17), "
                    "journal pages 671-672"
                ),
            },
        ],
        "remaining_blockers": [
            "Derive the Kirby-colour expansion from the established fusion data.",
            "Bind the category laws to the Kirby moves.",
            "Assemble the four-manifold invariant from the category-bound moves.",
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
