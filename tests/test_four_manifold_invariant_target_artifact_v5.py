from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v5.json"
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


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_v5_is_content_addressed_and_not_promoted() -> None:
    artifact = load_artifact()
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "PASS_TEN_FOUNDATION_CONDITIONS_ESTABLISHED_"
        "TWO_SOURCE_BOUND_INSTANCES_OPEN"
    )
    assert artifact["git"]["dirty_before_generation"] is False
    assert artifact["admission"]["ctl_theorem_claim_admitted"] is False


def test_exact_ten_two_target_partition() -> None:
    ledger = load_artifact()["target_condition_ledger"]
    assert ledger["counts"] == {"required": 12, "established": 10, "open": 2}
    assert ledger["required_conditions"] == (
        ledger["established_conditions"] + ledger["open_conditions"]
    )
    assert ledger["open_conditions"] == [
        "sourceBoundEvaluatorCompilerInstance",
        "sourceBoundGeometricH2CompilerInstance",
    ]


def test_old_semantic_shortcuts_are_closed() -> None:
    boundaries = load_artifact()["compiler_boundaries"]
    categorical = boundaries["categorical_event_compiler"]
    assert categorical["whole_diagram_is_direct_input"] is False
    assert categorical["raw_numerator_is_direct_input"] is False
    assert categorical["primitive_sign_is_type_indexed"] is True
    assert categorical["event_context_is_coherence_only"] is True
    h2 = boundaries["geometric_h2_compiler"]
    assert h2["final_identity_is_direct_input"] is False
    assert h2["actual_chain_equivalence_required"] is True
    assert h2["coordinate_naturality_square_required"] is True
    assert h2["identity_is_derived"] is True


def test_exact_test_and_axiom_denominators() -> None:
    checks = load_artifact()["checks"]
    assert checks["categorical_compiler"]["mutation_count"] == 3
    assert checks["geometric_h2_compiler"]["mutation_count"] == 2
    assert checks["target"]["mutation_count"] == 5
    assert checks["target"]["custom_axiom_count"] == 1
    assert checks["categorical_compiler"]["proof_oracle_count"] == 0
    assert checks["geometric_h2_compiler"]["proof_oracle_count"] == 0


def test_every_recorded_source_replays_from_the_pinned_commit() -> None:
    artifact = load_artifact()
    commit = artifact["git"]["commit"]
    for relative, record in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == record["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            record["sha256"]
        ), relative
