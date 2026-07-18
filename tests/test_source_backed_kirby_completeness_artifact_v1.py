from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.source_backed_kirby_completeness_v1 import (
    DOMAIN_AXIOM,
    canonical_hash,
    validate_runtime,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "source-backed-special-kirby-completeness-v1.json"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_artifact_is_clean_content_addressed_and_honest() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_ONE_SOURCE_BACKED_TOPOLOGY_DOMAIN_AXIOM_"
        "CHAIN_ENRICHMENT_REMAINS_OPEN"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["four_manifold_invariant_established"] is False


def test_runtime_revalidates() -> None:
    runtime = json.loads(ARTIFACT.read_text())["runtime_certificate"]
    validate_runtime(runtime)
    assert runtime["domain_axioms"] == [DOMAIN_AXIOM]


def test_axiom_audit_finds_exactly_one_custom_domain_axiom() -> None:
    audit = json.loads(ARTIFACT.read_text())["lean_certificate"][
        "axiom_audit"
    ]
    assert audit["audited_declaration_count"] == 7
    assert audit["observed_custom_axioms"] == [DOMAIN_AXIOM]
    assert audit["unexpected_custom_axioms"] == []
    assert audit["unexpected_standard_axioms"] == []


def test_mutations_and_proof_boundary_are_checked() -> None:
    certificate = json.loads(ARTIFACT.read_text())["lean_certificate"]
    assert certificate["mutation_count"] == 3
    assert len(certificate["mutation_rejections"]) == 3
    assert certificate["proof_boundary_scan"]["status"] == (
        "PASS_EXACTLY_ONE_WHITELISTED_DOMAIN_AXIOM_NO_PROOF_HOLES"
    )


def test_sources_are_pinned_and_capture_is_rechecked() -> None:
    inputs = json.loads(ARTIFACT.read_text())["inputs"]
    assert inputs["reference_ledger"]["reference_count"] == 3
    assert inputs["reference_ledger"]["captured_pdf_revalidated"] is True


def test_source_files_replay_from_clean_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            metadata["sha256"]
        ), relative


def test_artifact_does_not_admit_ctl_theorem_claim() -> None:
    assert json.loads(ARTIFACT.read_text())["admission"] == {
        "status": "REPO_LOCAL_DOMAIN_AXIOM_EVIDENCE_ONLY",
        "ctl_theorem_claim_admitted": False,
        "ctl_manifest_written": False,
    }
