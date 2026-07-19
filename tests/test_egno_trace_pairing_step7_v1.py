from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-trace-pairing-step7-v1.json"
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


def test_step7_artifact_is_content_addressed_and_clean() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_STEP_7_TRACE_PAIRING_COMPATIBILITY_RELATIVE_TO_"
        "TWO_GLOBAL_STANDARD_LAWS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_step7_preserves_exact_scope() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    historical = json.loads(
        git_bytes(commit, str(ROADMAP.relative_to(ROOT)))
    )
    statuses = [step["status"] for step in historical["steps"]]
    assert statuses[:6] == ["ESTABLISHED_IN_LEAN"] * 6
    assert statuses[6] == (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    )
    assert statuses[7:] == ["NOT_YET_ESTABLISHED"] * 3


def test_nondegeneracy_is_derived() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["checks"]["nondegeneracy_origin"] == (
        "PASS_DERIVED_FROM_ACTUAL_FINITE_SEMISIMPLE_DECOMPOSITION"
    )
    assert (
        "the pivotal trace pairing on arbitrary Hom spaces is perfect"
        in artifact["lean_derived"]
    )


def test_two_global_laws_are_not_hidden() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    laws = artifact["explicit_standard_theorem_inputs"]
    assert [law["name"] for law in laws] == [
        "SphericalMateTraceLaw",
        "PivotalFunctorTraceLaw",
    ]
    assert laws[0]["scope"].startswith("all objects")
    assert laws[1]["scope"].startswith("all source objects")


def test_guards_and_axiom_audit_passed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    checks = artifact["checks"]
    assert checks["mutations"]["rejected_count"] == 24
    assert checks["axiom_audit"]["audited_declaration_count"] == 73
    assert checks["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )
    assert checks["source_capture"] == (
        "PASS_BOTH_LOCAL_PRIMARY_SOURCE_HASHES_MATCH"
    )


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
