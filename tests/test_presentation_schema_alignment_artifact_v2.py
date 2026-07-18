from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-schema-alignment-v2.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode()
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    ).stdout


def test_artifact_is_content_addressed_and_scope_honest() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "PASS_PYTHON_LEAN_PRESENTATION_SCHEMA_AND_EXECUTION_ALIGNED"
    )
    assert artifact["git"]["dirty_before_generation"] is False
    assert artifact["target_impact"]["presentation_input_alignment"] == (
        "ESTABLISHED"
    )
    assert artifact["target_impact"]["four_manifold_invariant"] == (
        "NOT_YET_ESTABLISHED"
    )


def test_evidence_denominators_and_hash_boundary_are_explicit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    checks = artifact["checks"]
    assert checks["python_and_artifact_tests"]["test_count"] == 15
    assert checks["lean_kernel_regressions"]["theorem_count"] == 7
    assert checks["lean_runtime_replay"]["fail_closed_mutation_count"] == 2
    assert artifact["trust_boundary"]["lean_kernel_recomputes_sha256"] is False
    assert "EXTERNAL_ADMISSION_GATE" in artifact["trust_boundary"]["status"]
    assert any(
        "does not establish a four-manifold invariant" in statement
        for statement in artifact["explicit_nonclaims"]
    )


def test_every_recorded_source_replays_from_the_pinned_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, record in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == record["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            record["sha256"]
        ), relative


def test_formal_identity_and_provenance_hash_are_distinct() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    fixture = artifact["inputs"]["fixture"]
    assert fixture["content_hash"] != fixture["source_snapshot_hash"]
    semantics = artifact["checks"]["shared_semantics"]
    assert semantics["formal_identity_uses_content_hash"] is True
    assert semantics["provenance_hash_is_not_formal_identity"] is True
