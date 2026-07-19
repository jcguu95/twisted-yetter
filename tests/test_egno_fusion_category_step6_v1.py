from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-fusion-category-step6-v1.json"
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


def test_step6_artifact_is_content_addressed_and_clean() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_STEP_6_FINITE_SEMISIMPLE_FUSION_INTERFACE_ESTABLISHED"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_step6_artifact_preserves_its_historical_scope() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    historical = json.loads(
        git_bytes(commit, str(ROADMAP.relative_to(ROOT)))
    )
    statuses = [step["status"] for step in historical["steps"]]
    assert statuses[:6] == ["ESTABLISHED_IN_LEAN"] * 6
    assert all(status == "NOT_YET_ESTABLISHED" for status in statuses[6:])


def test_step6_guards_and_axiom_audit_passed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    checks = artifact["checks"]
    assert checks["mutations"]["rejected_count"] == 22
    assert checks["axiom_audit"]["audited_declaration_count"] == 57
    assert checks["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )
    assert checks["source_capture"] == "PASS_LOCAL_EGNO_PDF_HASH_MATCH"


def test_scalarization_and_decomposition_are_derived() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    checks = artifact["checks"]
    assert checks["closed_scalar_origin"] == (
        "PASS_SCHUR_DERIVED_NOT_CALLER_FIELD"
    )
    assert checks["identity_resolution_origin"] == (
        "PASS_ACTUAL_BIPRODUCT_ISOMORPHISM_NOT_NUMERICAL_TABLE"
    )
    derived = artifact["proof_scope"]["derived_not_assumed"]
    assert "K-linear scalar equivalence K ≃ End(1)" in derived
    assert "finite identity resolutions" in derived


def test_pairing_and_kirby_layers_remain_explicitly_open() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    joined = " ".join(artifact["remaining_blockers"])
    assert "nondegenerate trace pairing" in joined
    assert "Kirby-colour expansion" in joined
    assert "assemble the invariant" in joined


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
