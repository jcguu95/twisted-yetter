from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.computation_artifact_import_v1 import (
    BLOCKED_STATUS,
    EXPECTED_CHUNK_ARTIFACTS,
    EXPECTED_ROWS,
    EXPECTED_TOTAL_SECTORS,
    KNOWN_BLOCKERS,
    canonical_hash,
    validate_computation_import_runtime,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "computation-artifact-import-v1.json"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_r12_artifact_is_terminal_clean_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["status"] == "R12_TERMINAL_WITH_EXPLICIT_BLOCKERS"
    assert artifact["mathematical_status"] == (
        "COMPUTATION_IMPORTER_ESTABLISHED_EXACT_CONTROL_VERIFIED_"
        "FIGURE21_NOT_ADMITTED"
    )
    assert artifact["roadmap_status"] == (
        "R12_TERMINAL_WITH_BLOCKERS_R13_NOT_STARTED"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_runtime_certificate_revalidates_without_promoting_figure21() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    runtime = artifact["runtime_certificate"]

    validate_computation_import_runtime(runtime)
    assert runtime["exact_control"]["source_clean"] is True
    assert runtime["exact_control"]["r11_semantic_binding"] is True
    assert runtime["admission"]["figure21_exact_value_admitted"] is False
    assert runtime["admission"]["figure21_disposition"] == BLOCKED_STATUS
    assert tuple(runtime["admission"]["blockers"]) == KNOWN_BLOCKERS


def test_all_figure21_structural_denominators_are_recorded() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    replay = artifact["checks"]["denominator_replay"]
    batch = artifact["runtime_certificate"]["figure21_structural_batch"]

    assert replay["row_count"] == len(EXPECTED_ROWS) == 15
    assert replay["chunk_artifact_count"] == EXPECTED_CHUNK_ARTIFACTS
    assert replay["total_sector_count"] == EXPECTED_TOTAL_SECTORS
    assert batch["observed_total_sector_count"] == EXPECTED_TOTAL_SECTORS
    assert all(
        row["expected_sector_count"] == row["observed_sector_count"]
        for row in batch["rows"]
    )


def test_lean_certificate_has_no_holes_and_rejects_all_mutations() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    certificate = artifact["lean_certificate"]

    assert certificate["audited_declaration_count"] == 103
    assert certificate["mutation_count"] == 10
    assert len(certificate["mutation_rejections"]) == 10
    assert certificate["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )
    assert "sorryAx" not in certificate["axiom_audit"]["output"]
    assert "native_decide.ax" not in certificate["axiom_audit"]["output"]


def test_exact_and_structural_lean_contracts_are_disjoint() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    contract = artifact["checks"]["contract"]

    assert contract["status"] == (
        "PASS_EXACT_AND_STRUCTURAL_TYPES_DISJOINT"
    )
    assert contract["required_structure_count"] == 9
    assert contract["structural_output_value_field"] is False
    assert contract["structural_r11_binding_field"] is False
    assert contract["terminal_figure21_blocker_count"] == 6


def test_source_files_replay_from_the_clean_r12_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]

    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            metadata["sha256"]
        ), relative


def test_scoped_tests_and_obligation_denominators_are_fixed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    tests = artifact["checks"]["scoped_pytest"]
    obligations = artifact["inputs"]["obligation_matrix"]

    assert tests["passed_count"] == 34
    assert "34 passed" in tests["output"]
    assert obligations["obligation_count"] == 38
    assert obligations["trusted_input_count"] == 3
    assert obligations["explicit_nonclaim_count"] == 7


def test_nonclaims_preserve_every_current_r12_boundary() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    nonclaims = "\n".join(artifact["explicit_non_claims"])

    assert "not promote structurally complete distributions" in nonclaims
    assert "not certify the draft Figure 21 transcription" in nonclaims
    assert "seal the transitive evaluator source closure" in nonclaims
    assert "without a marked H2 identification" in nonclaims
    assert "not make a CTL claim" in nonclaims
