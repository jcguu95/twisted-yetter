#!/usr/bin/env python3
"""Build the terminal R11 conditional Kirby-invariant certificate."""

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

from twisted_yetter.homologically_twisted_invariant_v1 import (  # noqa: E402
    ALPHA_DENOMINATOR,
    PROOF_OBJECT_KIND,
    canonical_hash,
    build_invariant_runtime_fixture,
    validate_invariant_runtime,
)
from twisted_yetter.kirby_completeness_v1 import (  # noqa: E402
    SPECIAL_MOVE_KINDS,
)


OUTPUT = (
    REPO_ROOT
    / "experiments/results/lean-kirby/"
    "homologically-twisted-invariant-v1.json"
)
OBLIGATIONS = (
    REPO_ROOT
    / "experiments/inputs/lean-kirby/"
    "homologically-twisted-invariant-obligation-matrix-v1.json"
)
REFERENCES = (
    REPO_ROOT
    / "experiments/inputs/references/"
    "homologically-twisted-kirby-invariant-sources-v1.json"
)
PREDECESSORS = {
    "r7_framed_link_presentation": (
        REPO_ROOT
        / "experiments/results/lean-kirby/"
        "framed-link-presentation-independence-v1.json"
    ),
    "r8_handle_moves": (
        REPO_ROOT
        / "experiments/results/lean-kirby/kirby-handle-moves-v1.json"
    ),
    "r9_cancellation": (
        REPO_ROOT
        / "experiments/results/lean-kirby/kirby-cancellation-v1.json"
    ),
    "r10_completeness": (
        REPO_ROOT
        / "experiments/results/lean-kirby/kirby-completeness-v1.json"
    ),
}
EXPECTED_PREDECESSOR_STATUS = {
    "r7_framed_link_presentation":
        "PASS_FRAMED_LINK_EVALUATOR_PRESENTATION_INDEPENDENCE",
    "r8_handle_moves": "PASS_KIRBY_HANDLE_SLIDES",
    "r9_cancellation":
        "PASS_ALL_BARENZ_BARRETT_TABLE2_LOCAL_KIRBY_MOVES",
    "r10_completeness": "PASS_KIRBY_CERF_TOPOLOGY_BOUNDARY",
}
LEAN_BUILD_ORDER = [
    "lean/TwistedYetter/Kirby/HomologicallyTwistedInvariant.lean",
    "lean/TwistedYetter.lean",
]
MUTATIONS = [
    "lean/Mutations/ArbitraryNormalizedEqualityAsR11Step.lean",
    "lean/Mutations/DirectFinalInvariantInjection.lean",
    "lean/Mutations/CraneYetterIdentificationInjection.lean",
    "lean/Mutations/HandwrittenR11TargetAlpha.lean",
    "lean/Mutations/MissingR11SingleSnapshotCoherence.lean",
    "lean/Mutations/MissingR11DecorationWitness.lean",
    "lean/Mutations/MissingR11LocalBindingHashes.lean",
    "lean/Mutations/WrongR11OrdinarySlideKind.lean",
    "lean/Mutations/MissingR11MarkedTransportSound.lean",
    "lean/Mutations/MissingR11SourceScopeCaveat.lean",
]
PYTEST_FILES = [
    "tests/test_homologically_twisted_invariant_v1.py",
    "tests/test_kirby_completeness_v1.py",
    "tests/test_kirby_completeness_artifact_v1.py",
    "tests/test_kirby_cancellation_v1.py",
    "tests/test_kirby_cancellation_artifact_v1.py",
    "tests/test_kirby_handle_moves_v1.py",
    "tests/test_kirby_handle_moves_artifact_v1.py",
    "tests/test_framed_link_presentation_independence_v1.py",
]
AUDITED_FILES = [
    *LEAN_BUILD_ORDER,
    "lean/TwistedYetter/Kirby/AxiomAudit.lean",
    "src/twisted_yetter/homologically_twisted_invariant_v1.py",
    *MUTATIONS,
    "scripts/lean_homologically_twisted_invariant_mutation_tests.sh",
    "experiments/scripts/build_homologically_twisted_invariant_v1.py",
    "tests/test_homologically_twisted_invariant_v1.py",
    "tests/test_homologically_twisted_invariant_artifact_v1.py",
    str(OBLIGATIONS.relative_to(REPO_ROOT)),
    str(REFERENCES.relative_to(REPO_ROOT)),
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


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def clean_output(text: str) -> str:
    return ANSI_ESCAPE.sub("", text).strip()


def run(argv: list[str]) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(REPO_ROOT / ".uv-cache")
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
    checked: list[str] = []
    for relative in LEAN_BUILD_ORDER:
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


def contract_check() -> dict[str, Any]:
    source = (
        REPO_ROOT
        / "lean/TwistedYetter/Kirby/"
        "HomologicallyTwistedInvariant.lean"
    ).read_text()
    bridge = source.split("inductive EvaluatedTableTwoStep", 1)[1].split(
        "namespace EvaluatedTableTwoStep", 1
    )[0]
    constructors = [
        "framedIsotopy",
        "oneOverOne",
        "twoOverOne",
        "twoOverTwo",
        "oneTwoBirth",
        "oneTwoDeath",
        "twoThreeBirth",
        "twoThreeDeath",
    ]
    for constructor in constructors:
        if f"| {constructor}" not in bridge:
            raise AssertionError(f"missing R11 constructor: {constructor}")
    forbidden = [
        "fromEquality",
        "normalizedEquality",
        "finalInvariant",
        "craneYetterIdentification",
    ]
    if any(token in bridge for token in forbidden):
        raise AssertionError("R11 bridge contains an equality escape hatch")
    mandatory = [
        "single_snapshot_witness",
        "decoration_representation_witness",
        "raw_numerator_sound",
        "graphical_kind_sound",
        "graphical_orientation_sound",
        "graphical_move_id_sound",
        "graphical_source_hash_sound",
        "graphical_target_hash_sound",
        "marked_transport_sound",
        "movie_invariant",
        "presentation_independent",
        "same_pair_value",
        "homologically_twisted_kirby_invariant_established",
    ]
    if any(token not in source for token in mandatory):
        raise AssertionError("R11 mandatory contract field/theorem is missing")
    return {
        "status": "PASS_CLOSED_EIGHT_CONSTRUCTOR_R11_BRIDGE",
        "constructor_count": len(constructors),
        "constructors": constructors,
        "forbidden_equality_or_identification_apis": forbidden,
        "mandatory_fields_and_theorems": mandatory,
        "ordinary_slide_kind_binding": True,
        "slide_orientation_and_hash_binding": True,
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
        raise RuntimeError("R11 artifact requires a clean source commit")

    obligations = json.loads(OBLIGATIONS.read_text())
    rows = obligations["obligations"]
    if len(rows) != 38 or any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN", "BLOCKED"}
        for row in rows
    ):
        raise AssertionError("R11 obligation matrix is not terminal")
    if len(obligations["trusted_inputs"]) != 4:
        raise AssertionError("R11 must expose exactly four input classes")

    references = json.loads(REFERENCES.read_text())
    refs = {
        reference["ref_id"]: reference
        for reference in references["references"]
    }
    expected_refs = {
        "ref:yetter-homologically-twisted-1993",
        "ref:local-r7-framed-link-presentation-independence",
        "ref:local-r8-kirby-handle-moves",
        "ref:local-r9-kirby-cancellation",
        "ref:local-r10-kirby-completeness",
    }
    if set(refs) != expected_refs:
        raise AssertionError("R11 reference denominator is stale")
    yetter = refs["ref:yetter-homologically-twisted-1993"]
    if yetter["captured_pdf"]["repo_local_bytes"] is not False:
        raise AssertionError("Yetter byte-capture limitation was hidden")
    caveat = yetter["scope_caveat"]
    for required in (
        "simply-connected",
        "Z2",
        "Uq(sl2)",
        "do not state the arbitrary-category",
    ):
        if required not in caveat:
            raise AssertionError("Yetter theorem scope caveat is incomplete")

    predecessor_records: dict[str, Any] = {}
    for name, path in PREDECESSORS.items():
        predecessor = json.loads(path.read_text())
        if predecessor["status"] != EXPECTED_PREDECESSOR_STATUS[name]:
            raise AssertionError(f"{name} predecessor status changed")
        ledger_ref = refs[
            {
                "r7_framed_link_presentation":
                    "ref:local-r7-framed-link-presentation-independence",
                "r8_handle_moves": "ref:local-r8-kirby-handle-moves",
                "r9_cancellation": "ref:local-r9-kirby-cancellation",
                "r10_completeness": "ref:local-r10-kirby-completeness",
            }[name]
        ]
        if predecessor["content_hash"] != ledger_ref["content_hash"]:
            raise AssertionError(f"{name} content hash changed")
        if sha256_path(path) != ledger_ref["sha256"]:
            raise AssertionError(f"{name} file hash changed")
        predecessor_records[name] = {
            "path": str(path.relative_to(REPO_ROOT)),
            "status": predecessor["status"],
            "content_hash": predecessor["content_hash"],
            "sha256": sha256_path(path),
            "source_commit": predecessor["git"]["commit"],
        }

    runtime = build_invariant_runtime_fixture()
    validate_invariant_runtime(runtime)

    build_result = run(["./scripts/lean_local_build.sh", *LEAN_BUILD_ORDER])
    axiom_result = run(["./scripts/lean_axiom_audit.sh"])
    axiom_output = clean_output(axiom_result.stdout + axiom_result.stderr)
    if "sorryAx" in axiom_output or "native_decide.ax" in axiom_output:
        raise AssertionError("axiom audit exposed a proof hole or native oracle")
    declaration_count = len(
        re.findall(r"^'TwistedYetter\.", axiom_output, flags=re.MULTILINE)
    )
    if declaration_count != 89:
        raise AssertionError(
            f"expected 89 audited declarations, got {declaration_count}"
        )

    mutation_result = run(
        [
            "./scripts/"
            "lean_homologically_twisted_invariant_mutation_tests.sh"
        ]
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
            f"expected {len(MUTATIONS)} rejected R11 mutations"
        )

    pytest_result = run(["uv", "run", "pytest", "-q", *PYTEST_FILES])
    pytest_output = clean_output(pytest_result.stdout + pytest_result.stderr)
    match = re.search(r"(\d+) passed", pytest_output)
    if match is None or int(match.group(1)) != 76:
        raise AssertionError("R11 scoped pytest denominator changed")

    source_files = {
        relative: {
            "bytes": (REPO_ROOT / relative).stat().st_size,
            "sha256": sha256_path(REPO_ROOT / relative),
        }
        for relative in AUDITED_FILES
    }
    payload: dict[str, Any] = {
        "schema": (
            "twisted-yetter.homologically-twisted-kirby-invariant.v1"
        ),
        "status": "PASS_HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT",
        "mathematical_status": (
            "HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT_"
            "ESTABLISHED_UNDER_LISTED_AXIOMS"
        ),
        "roadmap_status": "R11_TERMINAL_R12_NOT_STARTED",
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round(
            (time.perf_counter() - started_clock) * 1000
        ),
        "repo_root": str(REPO_ROOT),
        "git": git_state,
        "generator_script": (
            "experiments/scripts/"
            "build_homologically_twisted_invariant_v1.py"
        ),
        "argv": [
            "experiments/scripts/"
            "build_homologically_twisted_invariant_v1.py"
        ],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 uv run python "
            "experiments/scripts/"
            "build_homologically_twisted_invariant_v1.py"
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
            "predecessor_artifacts": predecessor_records,
            "obligation_matrix": {
                "path": str(OBLIGATIONS.relative_to(REPO_ROOT)),
                "sha256": sha256_path(OBLIGATIONS),
                "obligation_count": len(rows),
                "trusted_input_count": len(obligations["trusted_inputs"]),
            },
            "reference_ledger": {
                "path": str(REFERENCES.relative_to(REPO_ROOT)),
                "sha256": sha256_path(REFERENCES),
                "reference_count": len(references["references"]),
            },
            "yetter_primary_source_capture": {
                "arxiv_id": yetter["arxiv_id"],
                "sha256": yetter["captured_pdf"]["sha256"],
                "bytes": yetter["captured_pdf"]["bytes"],
                "pages": yetter["captured_pdf"]["pages"],
                "repo_local_bytes": False,
                "status":
                    "HASH_AND_LOCATORS_RECORDED_BYTES_NOT_REPO_LOCAL",
                "scope_caveat": caveat,
            },
            "source_files": source_files,
        },
        "invariant_contract": {
            "status": "PASS_PRESENTATION_INDEPENDENT_PAIR_VALUE",
            "category_contract":
                "AdmissibleKirbyCategory",
            "presentation_contract":
                "DecoratedKirbyPresentation",
            "local_bridge":
                "EvaluatedTableTwoStep",
            "prescription":
                "HomologicallyTwistedKirbyPrescription",
            "marked_pair_system":
                "MarkedPairPresentationSystem",
            "terminal_theorem": (
                "MarkedPairPresentationSystem."
                "homologically_twisted_kirby_invariant_established"
            ),
            "local_directed_constructor_count": len(SPECIAL_MOVE_KINDS),
            "local_proof_object_kinds": PROOF_OBJECT_KIND,
            "bare_normalized_equality_constructor": False,
            "handwritten_target_alpha_field": False,
            "crane_yetter_identification_field": False,
        },
        "lean_certificate": {
            "status": "PASS_LEAN_KERNEL_AND_NEGATIVE_MUTATIONS",
            "build_order": LEAN_BUILD_ORDER,
            "build_output": clean_output(
                build_result.stdout + build_result.stderr
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
            "predecessor_binding": {
                "status": "PASS_R7_R8_R9_R10_HASH_BOUND",
                "predecessor_count": len(predecessor_records),
            },
            "source_scope_honesty": {
                "status":
                    "PASS_YETTER_SCOPE_NOT_UPGRADED",
                "yetter_pdf_hash_recorded": True,
                "yetter_pdf_repo_local": False,
                "yetter_theorem_11_used_as_general_identification":
                    False,
                "arbitrary_category_result_is_conditional": True,
            },
            "runtime_denominator": {
                "status": "PASS_EXACT_ALL_ALPHA_ALL_DIRECTED_MOVES",
                "move_count": len(SPECIAL_MOVE_KINDS),
                "alpha_count_per_move": ALPHA_DENOMINATOR,
                "checked_move_alpha_count":
                    len(SPECIAL_MOVE_KINDS) * ALPHA_DENOMINATOR,
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
