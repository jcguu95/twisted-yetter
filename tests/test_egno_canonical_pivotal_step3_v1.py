from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-canonical-pivotal-step3-v1.json"
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


def test_step3_artifact_is_content_addressed_and_clean() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_STEP_3_MONOIDAL_PIVOTAL_STRUCTURE_ESTABLISHED"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_exactly_steps_1_through_3_are_established() -> None:
    roadmap = json.loads(ROADMAP.read_text())
    statuses = [step["status"] for step in roadmap["steps"]]
    assert statuses[:3] == ["ESTABLISHED_IN_LEAN"] * 3
    assert all(status == "NOT_YET_ESTABLISHED" for status in statuses[3:])
    artifact = json.loads(ARTIFACT.read_text())
    assert "SPHERICALITY_AND_TRACE_CYCLICITY_OPEN" in (
        artifact["mathematical_status"]
    )


def test_step3_guards_and_axiom_audit_passed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    checks = artifact["checks"]
    assert checks["mutations"]["rejected_count"] == 9
    assert checks["axiom_audit"]["audited_declaration_count"] == 19
    assert checks["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )
    assert artifact["definition_boundary"]["status"] == (
        "SOURCE_CHARACTERIZATION_ADOPTED"
    )
    assert "braiding-free" in (
        artifact["definition_boundary"]["not_independently_established"]
    )


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
