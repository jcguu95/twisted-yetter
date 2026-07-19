#!/usr/bin/env python3
"""Build the source-bound certificate for EGNO Kirby-colour Step 8."""

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
    "egno-kirby-color-step8-v1.json"
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
    "generalized-sliding-framed-context-primary-sources-v1.json"
)
YETTER_REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "twisted-yetter-premodular-formula-conjecture-primary-sources-v1.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_kirby_color_step8_v1.py",
    "tests/test_egno_kirby_color_step8_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOTensorAutomorphism.lean",
    "lean/TwistedYetter/Kirby/EGNOKirbyColorExpansion.lean",
    "lean/TwistedYetter/Kirby/EGNOKirbyColorExpansionAxiomAudit.lean",
    "lean/Mutations/MissingTensorAutomorphismMonoidality.lean",
    "lean/Mutations/FreeTensorAutomorphismScalarTable.lean",
    "lean/Mutations/WrongOrdinaryKirbyColorWeight.lean",
    "lean/Mutations/KirbyColorIsNotCategoryObject.lean",
    "scripts/lean_egno_kirby_color_axiom_audit.sh",
    "scripts/lean_egno_kirby_color_mutation_tests.sh",
    "scripts/lean_egno_trace_pairing_axiom_audit.sh",
    "scripts/lean_egno_trace_pairing_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    str(ROADMAP.relative_to(REPO_ROOT)),
    str(EGNO_REFERENCES.relative_to(REPO_ROOT)),
    str(SLIDING_REFERENCES.relative_to(REPO_ROOT)),
    str(YETTER_REFERENCES.relative_to(REPO_ROOT)),
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


def check_roadmap(roadmap: dict[str, Any]) -> None:
    if roadmap["status"] != "STEP_8_ESTABLISHED_STEPS_9_TO_10_EXPLICIT":
        raise AssertionError("unexpected roadmap status")
    statuses = [step["status"] for step in roadmap["steps"]]
    if statuses[:6] != ["ESTABLISHED_IN_LEAN"] * 6:
        raise AssertionError("Steps 1 through 6 must be established")
    if statuses[6] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    ):
        raise AssertionError("Step 7 lost its explicit theorem-input boundary")
    if statuses[7] != "ESTABLISHED_IN_LEAN":
        raise AssertionError("Step 8 is not established")
    if statuses[8:] != ["NOT_YET_ESTABLISHED"] * 2:
        raise AssertionError("a post-Step-8 obligation was silently promoted")


def check_contracts() -> None:
    automorphism_text = (
        REPO_ROOT
        / "lean/TwistedYetter/Fusion/EGNOTensorAutomorphism.lean"
    ).read_text()
    colour_text = (
        REPO_ROOT
        / "lean/TwistedYetter/Kirby/EGNOKirbyColorExpansion.lean"
    ).read_text()
    required_automorphism_contracts = [
        "structure TensorIdentityAutomorphism",
        "theorem tensor_hom",
        "theorem unit_hom",
        "noncomputable def automorphismSimpleScalar",
        "theorem automorphism_app_eq_smul_identity",
        "theorem automorphismSimpleScalar_ne_zero",
        "noncomputable def automorphismSimpleUnit",
        "noncomputable def automorphismScalarPower",
    ]
    missing = [
        item
        for item in required_automorphism_contracts
        if item not in automorphism_text
    ]
    if missing:
        raise AssertionError(f"missing tensor-automorphism contracts: {missing}")
    automorphism_fields = automorphism_text.split(
        "structure TensorIdentityAutomorphism", maxsplit=1
    )[1].split("namespace TensorIdentityAutomorphism", maxsplit=1)[0]
    if "simpleScalar" in automorphism_fields:
        raise AssertionError("a caller-supplied simple scalar table was admitted")

    required_colour_contracts = [
        "noncomputable def ordinary",
        "noncomputable def integralCharacter",
        "theorem integralCharacter_zero",
        "theorem integralCharacter_identity",
        "noncomputable def diagramExpansion",
        "theorem eval_diagramExpansion",
        "theorem eval_ordinary_expansion",
        "theorem eval_integralCharacter_expansion",
    ]
    missing = [
        item for item in required_colour_contracts if item not in colour_text
    ]
    if missing:
        raise AssertionError(f"missing Kirby-colour contracts: {missing}")
    if "weight := data.quantumDimension" not in colour_text:
        raise AssertionError("ordinary colour is not pinned to quantum dimension")
    if "WeightedFamily K S C" not in colour_text:
        raise AssertionError("Kirby colour lost its formal weighted-family type")


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("Step 8 artifact requires a clean source commit")

    roadmap = json.loads(ROADMAP.read_text())
    check_roadmap(roadmap)
    check_contracts()

    egno_refs = json.loads(EGNO_REFERENCES.read_text())
    sliding_refs = json.loads(SLIDING_REFERENCES.read_text())
    yetter_refs = json.loads(YETTER_REFERENCES.read_text())
    egno_pdf = verify_capture(
        egno_refs["references"][0]["captured_pdf"], "EGNO"
    )
    sliding_pdf = verify_capture(
        sliding_refs["references"][0]["captured_pdf"],
        "Bärenz--Barrett",
    )
    yetter_snapshot = yetter_refs["references"][0]["snapshot"]

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(["./scripts/lean_egno_kirby_color_axiom_audit.sh"])
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 8 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 94:
        raise AssertionError(
            f"expected 94 audited declarations, got {audited_declarations}"
        )

    mutations = run(["./scripts/lean_egno_kirby_color_mutation_tests.sh"])
    rejections = [
        line
        for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 28:
        raise AssertionError("expected twenty-eight rejected Step 1-8 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-kirby-color-step8.v1",
        "status": "PASS_STEP_8_KIRBY_COLOR_EXPANSION",
        "mathematical_status": (
            "ORDINARY_AND_INTEGRAL_CHARACTER_KIRBY_COLOR_EXPANSIONS_"
            "DERIVED_FROM_RIBBON_FUSION_DATA_AND_A_MONOIDAL_IDENTITY_"
            "AUTOMORPHISM"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/build_egno_kirby_color_step8_v1.py"
        ),
        "argv": [
            "experiments/scripts/build_egno_kirby_color_step8_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 UV_CACHE_DIR=.uv-cache uv run python "
            "experiments/scripts/build_egno_kirby_color_step8_v1.py"
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
                str(YETTER_REFERENCES.relative_to(REPO_ROOT)): {
                    "sha256": sha256_path(YETTER_REFERENCES)
                },
            },
            "source_pdfs": {
                "egno": egno_pdf,
                "baerenz_barrett": sliding_pdf,
                "yetter": {
                    "status": "HASHED_REMOTE_SNAPSHOT_LEDGER_ONLY",
                    "arxiv_version": yetter_snapshot["pdf_url"],
                    "bytes_status": "NOT_STORED_IN_REPOSITORY",
                    "sha256": yetter_snapshot["sha256"],
                },
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
            "local_source_capture": (
                "PASS_EGNO_AND_BAERENZ_BARRETT_LOCAL_PDF_HASHES_MATCH"
            ),
            "scalar_origin": "PASS_DERIVED_BY_SCHUR_NOT_CALLER_SUPPLIED",
            "scalar_invertibility": (
                "PASS_DERIVED_FROM_NATURAL_ISOMORPHISM"
            ),
            "ordinary_weight_origin": (
                "PASS_DERIVED_FROM_CANONICAL_RIBBON_QUANTUM_DIMENSION"
            ),
            "colour_representation": (
                "PASS_FORMAL_FINITE_WEIGHTED_FAMILY_NOT_CATEGORY_OBJECT"
            ),
        },
        "lean_derived": [
            "monoidality gives the tensor and unit laws of the identity automorphism",
            "Schur's lemma gives the unique scalar action on every listed simple",
            "the natural isomorphism makes each simple scalar nonzero",
            "integral powers are powers of a derived field unit",
            "ordinary Kirby coefficients are the canonical ribbon quantum dimensions",
            "twisted coefficients are dim(s) times the derived scalar to the integral exponent",
            "zero exponent and the identity automorphism recover the ordinary colour",
            "evaluation of a formal colour is the exact finite weighted diagram sum",
        ],
        "remaining_blockers": [
            "Bind the derived colour and pairing laws to category-level Kirby moves.",
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
    print(
        json.dumps(
            {
                "output": str(OUTPUT),
                "status": result["status"],
                "content_hash": result["content_hash"],
            },
            indent=2,
        )
    )
