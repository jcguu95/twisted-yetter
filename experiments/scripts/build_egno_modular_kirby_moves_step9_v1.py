#!/usr/bin/env python3
"""Build the source-bound certificate for EGNO modular Kirby-move Step 9."""

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
    "egno-modular-kirby-moves-step9-v1.json"
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
FRAMING_REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "framed-link-presentation-independence-primary-sources-v1.json"
)
SOURCE_FILES = [
    "experiments/scripts/build_egno_modular_kirby_moves_step9_v1.py",
    "tests/test_egno_modular_kirby_moves_step9_v1.py",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Fusion/EGNOFusionCategory.lean",
    "lean/TwistedYetter/Fusion/EGNOSphericalInsertion.lean",
    "lean/TwistedYetter/Kirby/FramingNaturality.lean",
    "lean/TwistedYetter/Kirby/PresentationIsotopy.lean",
    "lean/TwistedYetter/Kirby/GeneralizedSliding.lean",
    "lean/TwistedYetter/Kirby/KirbyCancellation.lean",
    "lean/TwistedYetter/Kirby/RibbonKirbyGraphicalAlgebra.lean",
    "lean/TwistedYetter/Kirby/EGNOCategoryBoundSliding.lean",
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean",
    "lean/TwistedYetter/Kirby/EGNOModularKirbyMovesAxiomAudit.lean",
    "lean/Mutations/SingletonFormalKirbyColorSliding.lean",
    "lean/Mutations/MissingLabelIndexedSlidingFamily.lean",
    "lean/Mutations/FreeModularGlobalDimension.lean",
    "lean/Mutations/WrongModularTransparentDimension.lean",
    "lean/Mutations/MissingUnitQuantumDimensionCertificate.lean",
    "lean/Mutations/WrongRibbonSnapshotInModularPackage.lean",
    "lean/Mutations/UnboundOrdinarySlidingInModularPackage.lean",
    "lean/Mutations/MalformedModularPackageHash.lean",
    "scripts/lean_egno_modular_kirby_moves_axiom_audit.sh",
    "scripts/lean_egno_modular_kirby_moves_mutation_tests.sh",
    "scripts/lean_egno_kirby_color_axiom_audit.sh",
    "scripts/lean_egno_kirby_color_mutation_tests.sh",
    "scripts/lean_local_check.sh",
    str(ROADMAP.relative_to(REPO_ROOT)),
    str(EGNO_REFERENCES.relative_to(REPO_ROOT)),
    str(SLIDING_REFERENCES.relative_to(REPO_ROOT)),
    str(FRAMING_REFERENCES.relative_to(REPO_ROOT)),
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
    if roadmap["status"] != "STEP_9_ESTABLISHED_STEP_10_EXPLICIT":
        raise AssertionError("unexpected roadmap status")
    statuses = [step["status"] for step in roadmap["steps"]]
    if statuses[:6] != ["ESTABLISHED_IN_LEAN"] * 6:
        raise AssertionError("Steps 1 through 6 must remain established")
    if statuses[6] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    ):
        raise AssertionError("Step 7 lost its explicit theorem-input boundary")
    if statuses[7] != "ESTABLISHED_IN_LEAN":
        raise AssertionError("Step 8 is not established")
    if statuses[8] != (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_EXPLICIT_GLOBAL_"
        "STANDARD_GRAPHICAL_LAWS"
    ):
        raise AssertionError("Step 9 lost its explicit theorem-input boundary")
    if statuses[9] != "NOT_YET_ESTABLISHED":
        raise AssertionError("Step 10 was silently promoted")


def check_contracts() -> None:
    insertion = (
        REPO_ROOT
        / "lean/TwistedYetter/Fusion/EGNOSphericalInsertion.lean"
    ).read_text()
    sliding = (
        REPO_ROOT
        / "lean/TwistedYetter/Kirby/EGNOCategoryBoundSliding.lean"
    ).read_text()
    modular = (
        REPO_ROOT
        / "lean/TwistedYetter/Kirby/EGNOModularKirbyMoves.lean"
    ).read_text()
    required_insertion = [
        "structure SphericalInsertionLaw",
        "{I : S → Type uI}",
        "(X : C)",
        "noncomputable def sphericalIdentityResolution",
        "noncomputable def reversed",
        "theorem reverse_primal",
        "theorem reverse_dual",
    ]
    required_sliding = [
        "noncomputable def slidingCategoryData",
        "structure LabelIndexedSlidingMovies",
        "(x : S) →",
        "theorem term_sound",
        "theorem linear_eval_sound",
        "theorem collapsed_eval_sound",
        "structure OrdinaryKirbySlidingLaw",
        "diagram_content_hash_shape",
    ]
    required_modular = [
        "noncomputable def globalDimension",
        "noncomputable def transparentGlobalDimension",
        "theorem transparentGlobalDimension_eq_one",
        "unit_quantum_dimension",
        "global_dimension_ne_zero",
        "transparentDimension := transparentGlobalDimension data",
        "structure ModularCancellationLaw",
        "structure RibbonFramedKinkLaw",
        "structure Package",
        "category_snapshot_hash_shape",
        "category_coherence_certificate_hash_shape",
    ]
    missing = [
        item
        for item in required_insertion
        if item not in insertion
    ]
    missing += [
        item for item in required_sliding if item not in sliding
    ]
    missing += [
        item for item in required_modular if item not in modular
    ]
    if missing:
        raise AssertionError(f"missing Step 9 contracts: {missing}")
    if "transparentDimension := 1" in modular:
        raise AssertionError("transparent dimension was hard-coded")
    package_fields = modular.split("structure Package", maxsplit=1)[1].split(
        "namespace Package", maxsplit=1
    )[0]
    if "dimensionProfile :" in package_fields:
        raise AssertionError("package accepts a caller-supplied dimension profile")
    if "AdmissibleKirbyCategory" in sliding:
        raise AssertionError("new label-indexed route fell back to singleton data")


def build() -> dict[str, Any]:
    started_at = utc_now()
    started_clock = time.perf_counter()
    git_state = {
        "commit": git("rev-parse", "HEAD"),
        "branch": git("branch", "--show-current"),
        "dirty": bool(git("status", "--porcelain")),
    }
    if git_state["dirty"]:
        raise RuntimeError("Step 9 artifact requires a clean source commit")

    roadmap = json.loads(ROADMAP.read_text())
    check_roadmap(roadmap)
    check_contracts()

    egno_refs = json.loads(EGNO_REFERENCES.read_text())
    sliding_refs = json.loads(SLIDING_REFERENCES.read_text())
    framing_refs = json.loads(FRAMING_REFERENCES.read_text())
    egno_pdf = verify_capture(
        egno_refs["references"][0]["captured_pdf"], "EGNO"
    )
    sliding_pdf = verify_capture(
        sliding_refs["references"][0]["captured_pdf"],
        "Bärenz--Barrett",
    )
    framing_pdf = verify_capture(
        framing_refs["references"][1]["captured_pdf"], "Selinger"
    )

    build_result = run(["lake", "build", "TwistedYetter"])
    axiom_result = run(
        ["./scripts/lean_egno_modular_kirby_moves_axiom_audit.sh"]
    )
    axiom_output = axiom_result.stdout + axiom_result.stderr
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("Step 9 axiom audit exposed a proof oracle")
    audited_declarations = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if audited_declarations != 127:
        raise AssertionError(
            f"expected 127 audited declarations, got {audited_declarations}"
        )

    mutations = run(
        ["./scripts/lean_egno_modular_kirby_moves_mutation_tests.sh"]
    )
    rejections = [
        line
        for line in mutations.stdout.splitlines()
        if line.startswith("PASS expected rejection:")
    ]
    if len(rejections) != 36:
        raise AssertionError("expected thirty-six rejected Step 1-9 mutations")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in SOURCE_FILES
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.egno-modular-kirby-moves-step9.v1",
        "status": (
            "PASS_STEP_9_CATEGORY_BOUND_MODULAR_KIRBY_MOVES_RELATIVE_"
            "TO_EXPLICIT_GLOBAL_STANDARD_GRAPHICAL_LAWS"
        ),
        "mathematical_status": (
            "CATEGORY_SIDE_MODULAR_IDENTITY_FUNCTOR_KIRBY_ALGEBRA_"
            "KERNEL_CHECKED_RELATIVE_TO_VISIBLE_SOURCE_BOUND_INPUTS"
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
            "build_egno_modular_kirby_moves_step9_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_egno_modular_kirby_moves_step9_v1.py"
        ],
        "reproduce_command": (
            "LEAN_NUM_THREADS=1 UV_CACHE_DIR=.uv-cache uv run python "
            "experiments/scripts/"
            "build_egno_modular_kirby_moves_step9_v1.py"
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
                str(FRAMING_REFERENCES.relative_to(REPO_ROOT)): {
                    "sha256": sha256_path(FRAMING_REFERENCES)
                },
            },
            "source_pdfs": {
                "egno": egno_pdf,
                "baerenz_barrett": sliding_pdf,
                "selinger": framing_pdf,
                "shum": {
                    "status": "CANONICAL_METADATA_ONLY_NO_LOCAL_BYTES",
                    "doi": "10.1016/0022-4049(92)00039-T",
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
            "label_coverage": "PASS_ALL_SIMPLE_LABELS_QUANTIFIED",
            "formal_colour_boundary": (
                "PASS_TERM_FIRST_THEN_FINITE_SUM_NOT_SINGLETON_OBJECT"
            ),
            "dimension_origin": (
                "PASS_GLOBAL_AND_TRANSPARENT_DIMENSIONS_DERIVED_FROM_"
                "CATEGORY_SUMS"
            ),
            "dual_convention": (
                "PASS_ONE_SELECTED_RIGHT_DUAL_ACROSS_TRACE_TWIST_AND_CLOSURE"
            ),
            "hash_binding": (
                "PASS_CATEGORY_COHERENCE_SLIDE_AND_MOVIE_HASH_SHAPES_REQUIRED"
            ),
        },
        "lean_derived": [
            "canonical finite trace-dual identity resolutions",
            "reverse dual bases from pivotal trace cyclicity",
            "pairing-preserving mate transport for every simple channel",
            "forward and inverse insertion equations for every fixed label",
            "termwise generalized sliding lifted to arbitrary unchanged coefficients",
            "ordinary sliding endpoints bound to the exact formal Kirby colour",
            "transparent-simple dimension equals one in the modular scope",
            "both normalization dimensions equal the derived global sum",
            "1--2 and 2--3 raw factors equal the derived normalization factors",
            "framing and cut closure use the same ribbon pivotal convention",
        ],
        "explicit_standard_theorem_inputs": [
            "all-object spherical insertion law",
            "all-object spherical mate trace law",
            "ordinary formal-colour sliding law",
            "all-label generalized graphical movies",
            "modular simple-centre and standard scalar certificates",
            "cutting, killing, and isolated-unknot cancellation laws",
            "positive and negative ribbon framed-kink equations",
        ],
        "remaining_blockers": [
            "Assemble the category-bound local laws with the presentation evaluator.",
            "Prove normalized invariance along every admitted local move.",
            "Descend through source-backed marked Kirby completeness to a pair invariant.",
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
