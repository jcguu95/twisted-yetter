from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-kirby-color-step8-v1.json"
)
ROADMAP = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_step8_artifact_is_content_addressed_and_clean() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == "PASS_STEP_8_KIRBY_COLOR_EXPANSION"
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_step8_preserves_exact_scope() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    historical = json.loads(
        git_bytes(
            artifact["git"]["commit"],
            str(ROADMAP.relative_to(ROOT)),
        )
    )
    statuses = [step["status"] for step in historical["steps"]]
    assert statuses[:6] == ["ESTABLISHED_IN_LEAN"] * 6
    assert statuses[6] == (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    )
    assert statuses[7] == "ESTABLISHED_IN_LEAN"
    assert statuses[8:] == ["NOT_YET_ESTABLISHED"] * 2


def test_scalar_and_weight_are_derived() -> None:
    checks = json.loads(ARTIFACT.read_text())["checks"]
    assert checks["scalar_origin"] == (
        "PASS_DERIVED_BY_SCHUR_NOT_CALLER_SUPPLIED"
    )
    assert checks["scalar_invertibility"] == (
        "PASS_DERIVED_FROM_NATURAL_ISOMORPHISM"
    )
    assert checks["ordinary_weight_origin"] == (
        "PASS_DERIVED_FROM_CANONICAL_RIBBON_QUANTUM_DIMENSION"
    )


def test_colour_is_formal_and_evaluation_is_explicit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["checks"]["colour_representation"] == (
        "PASS_FORMAL_FINITE_WEIGHTED_FAMILY_NOT_CATEGORY_OBJECT"
    )
    assert (
        "evaluation of a formal colour is the exact finite weighted diagram sum"
        in artifact["lean_derived"]
    )


def test_step8_guards_and_axiom_audit_passed() -> None:
    checks = json.loads(ARTIFACT.read_text())["checks"]
    assert checks["mutations"]["rejected_count"] == 28
    assert checks["axiom_audit"]["audited_declaration_count"] == 94
    assert checks["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
