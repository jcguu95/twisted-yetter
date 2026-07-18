from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "presentation-execution-trace-v1.json"
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


def test_checkpoint_is_content_addressed_and_scope_honest() -> None:
    artifact = load_artifact()
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "PASS_CLOSED_TYPED_PRESENTATION_EXECUTION_ESTABLISHED"
    )
    assert artifact["git"]["dirty_before_generation"] is False
    assert artifact["axiom_boundary"][
        "categorical_event_interpretation_assumed"
    ] is False
    assert any(
        "does not establish a four-manifold invariant" in statement
        for statement in artifact["explicit_nonclaims"]
    )


def test_exact_trace_and_mutation_denominators_are_recorded() -> None:
    checks = load_artifact()["checks"]
    trace = checks["closed_trace_runtime_replay"]
    assert trace["event_count"] == trace["trace_step_count"] == 12
    assert trace["trace_state_count"] == trace["declared_slice_count"] == 13
    assert trace["initial_boundary"] == trace["terminal_boundary"] == []
    assert checks["trace_kernel_theorems"]["theorem_count"] == 6
    assert checks["fail_closed_mutations"]["total_mutation_count"] == 10
    assert checks["fail_closed_mutations"][
        "missing_execution_trace_rejected"
    ] is True


def test_target_ledger_remains_explicitly_incomplete() -> None:
    artifact = load_artifact()
    ledger = artifact["checks"]["target_condition_ledger"]
    assert ledger == {
        "required": 10,
        "established_foundation": 8,
        "open_construction": 2,
        "closed_typed_presentation_execution": "ESTABLISHED",
    }
    gaps = artifact["remaining_construction_gaps"]
    assert {gap["condition"] for gap in gaps} == {
        "sourceBoundEvaluatorCompilerInstance",
        "sourceBoundGeometricH2CompilerInstance",
    }
    assert all(gap["status"] == "OPEN" for gap in gaps)


def test_every_recorded_source_replays_from_the_pinned_commit() -> None:
    artifact = load_artifact()
    commit = artifact["git"]["commit"]
    for relative, record in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == record["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            record["sha256"]
        ), relative
