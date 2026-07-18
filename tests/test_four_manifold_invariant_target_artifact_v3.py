from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.four_manifold_invariant_target_v3 import (
    canonical_hash,
    validate_target_runtime,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v3.json"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_v3_artifact_is_clean_content_addressed_and_not_promoted() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_TARGET_STATED_SOURCE_COMPLETENESS_GAP_CLOSED_"
        "TWO_CONCRETE_CONDITIONS_OPEN"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["runtime_certificate"][
        "four_manifold_invariant_established"
    ] is False


def test_v3_runtime_and_exact_condition_counts_revalidate() -> None:
    runtime = json.loads(ARTIFACT.read_text())["runtime_certificate"]
    validate_target_runtime(runtime)
    assert runtime["condition_counts"] == {
        "required": 6,
        "established": 4,
        "open": 2,
    }


def test_v3_pins_both_predecessor_artifacts() -> None:
    inputs = json.loads(ARTIFACT.read_text())["inputs"]
    assert inputs["target_predecessor"]["schema"].endswith(".v2")
    assert inputs["source_completeness_artifact"]["schema"].endswith(".v1")
    assert inputs["source_completeness_artifact"][
        "domain_axiom_count"
    ] == 1


def test_v3_lean_audits_keep_topology_axiom_separate() -> None:
    lean = json.loads(ARTIFACT.read_text())["lean_certificate"]
    assert lean["target_axiom_audit"]["unexpected_axioms"] == []
    assert lean["source_axiom_audit"][
        "observed_custom_axiom_count"
    ] == 1
    assert lean["source_axiom_audit"]["unexpected_custom_axioms"] == []


def test_v3_source_files_replay_from_clean_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(artifact["git"]["commit"], relative)
        assert len(data) == metadata["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            metadata["sha256"]
        ), relative


def test_v3_does_not_admit_ctl_theorem_claim() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["admission"] == {
        "status": "REPO_LOCAL_GOAL_EVIDENCE_ONLY",
        "ctl_theorem_claim_admitted": False,
        "ctl_manifest_written": False,
    }
