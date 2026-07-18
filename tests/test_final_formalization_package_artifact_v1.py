from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.computation_artifact_import_v1 import KNOWN_BLOCKERS
from twisted_yetter.final_formalization_package_v1 import (
    canonical_hash,
    validate_final_formalization_runtime,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "homologically-twisted-kirby-formalization-package-v1.json"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_r13_artifact_is_terminal_clean_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["status"] == (
        "PASS_R13_FORMALIZATION_PACKAGE_TERMINAL_WITH_EXPLICIT_"
        "FIGURE21_BLOCKERS"
    )
    assert artifact["mathematical_status"] == (
        "HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT_ESTABLISHED_RELATIVE_"
        "TO_LISTED_INPUTS_R12_IMPORTER_ESTABLISHED_FIGURE21_NOT_ADMITTED"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_r13_runtime_certificate_revalidates() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    runtime = artifact["runtime_certificate"]

    validate_final_formalization_runtime(runtime)
    assert runtime["milestone_audit"]["artifact_count"] == 11
    assert runtime["milestone_audit"][
        "historical_source_file_replay_count"
    ] == 231
    assert runtime["trusted_input_audit"]["unique_count"] == 25
    assert runtime["predecessor_nonclaim_audit"]["nonclaim_count"] == 64


def test_lean_certificate_has_no_oracles_and_rejects_mutations() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    certificate = artifact["lean_certificate"]

    assert certificate["audited_declaration_count"] == 116
    assert certificate["mutation_count"] == 7
    assert len(certificate["mutation_rejections"]) == 7
    assert certificate["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )
    assert certificate["axiom_audit"]["unexpected_axioms"] == []


def test_final_boundary_preserves_all_nonclaims() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    boundary = artifact["runtime_certificate"]["terminal_boundary"]

    assert boundary["formalization_route_terminal"] is True
    assert boundary["figure21_terminal_blockers"] == list(KNOWN_BLOCKERS)
    assert boundary["figure21_exact_value_admitted"] is False
    assert boundary["figure21_marked_comparison_admitted"] is False
    assert boundary["crane_yetter_identification_established"] is False
    assert boundary["source_byte_complete_archive"] is False
    assert boundary["ctl_claim_admitted"] is False


def test_source_files_replay_from_the_clean_r13_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]

    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            metadata["sha256"]
        ), relative


def test_frozen_inputs_and_scoped_tests_are_recorded() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    inputs = artifact["inputs"]
    tests = artifact["checks"]["scoped_pytest"]

    assert inputs["frozen_manifest"]["milestone_artifact_count"] == 11
    assert inputs["frozen_manifest"]["reference_ledger_count"] == 8
    assert inputs["obligation_matrix"]["obligation_count"] == 24
    assert inputs["obligation_matrix"]["explicit_nonclaim_count"] == 10
    assert tests["status"] == "PASS"
    assert tests["passed_count"] > 0


def test_artifact_makes_no_ctl_admission() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["admission"]["ctl_claim_admitted"] is False
    assert artifact["admission"]["ctl_manifest_written"] is False
    assert artifact["admission"]["status"] == "REPO_LOCAL_EVIDENCE_ONLY"
