from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.four_manifold_invariant_target_v2 import (
    MATHEMATICAL_STATUS,
    canonical_hash,
    validate_target_runtime,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v2.json"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_v2_artifact_is_clean_content_addressed_and_not_promoted() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_TARGET_STATED_CHAIN_DERIVED_H2_GAP_CLOSED_"
        "THREE_HARD_CONDITIONS_OPEN"
    )
    assert artifact["mathematical_status"] == MATHEMATICAL_STATUS
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["runtime_certificate"][
        "four_manifold_invariant_established"
    ] is False


def test_v2_runtime_certificate_revalidates() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    runtime = artifact["runtime_certificate"]
    validate_target_runtime(runtime)
    assert runtime["condition_counts"] == {
        "required": 6,
        "established": 3,
        "open": 3,
    }


def test_v2_lean_certificate_has_no_proof_oracle() -> None:
    certificate = json.loads(ARTIFACT.read_text())["lean_certificate"]
    assert certificate["axiom_audit"]["audited_declaration_count"] == 16
    assert certificate["axiom_audit"]["unexpected_axioms"] == []
    assert certificate["mutation_count"] == 22
    assert len(certificate["mutation_rejections"]) == 22
    assert certificate["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )


def test_v2_inputs_and_predecessor_are_hash_pinned() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    inputs = artifact["inputs"]
    assert inputs["obligation_matrix"]["condition_count"] == 6
    assert inputs["obligation_matrix"]["open_condition_count"] == 3
    predecessor = inputs["predecessor_artifact"]
    old = json.loads((ROOT / predecessor["path"]).read_text())
    assert old["content_hash"] == predecessor["content_hash"]


def test_v2_source_files_replay_from_clean_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            metadata["sha256"]
        ), relative


def test_v2_artifact_does_not_admit_ctl_theorem_claim() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["admission"] == {
        "status": "REPO_LOCAL_GOAL_EVIDENCE_ONLY",
        "ctl_theorem_claim_admitted": False,
        "ctl_manifest_written": False,
    }
