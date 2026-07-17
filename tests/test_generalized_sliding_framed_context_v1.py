from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "generalized-sliding-framed-context-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "generalized-sliding-framed-context-obligation-matrix-v1.json"
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


def test_framed_context_artifact_is_clean_terminal_and_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == "PASS_GENERALIZED_SLIDING_FRAMED_CONTEXT"
    assert artifact["mathematical_status"] == (
        "GENERALIZED_SLIDING_FRAMED_CONTEXT_ESTABLISHED_RELATIVE_TO_"
        "LEMMA_3_3_STANDARD_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["checks"]["kirby_axiom_audit"]["theorem_count"] == 37
    assert artifact["checks"]["kirby_axiom_audit"][
        "new_lemma_3_4_theorem_count"
    ] == 5
    assert artifact["checks"]["mutation_tests"]["rejected_count"] == 2


def test_pinned_source_hashes_replay_from_the_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_every_obligation_is_terminal_without_new_sliding_axiom() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    rows = matrix["obligations"]
    assert len(rows) == 12
    assert not any(row["status"] == "NOT_FORMALIZED" for row in rows)
    statuses = {row["obligation_id"]: row["status"] for row in rows}
    assert statuses["arbitrary-exterior-naturality"] == (
        "LEAN_PROVED_FROM_LEMMA_3_3"
    )
    assert statuses["actual-sliding-family-constructor"] == (
        "LEAN_CONSTRUCTED_FROM_ACTUAL_LEMMA_3_3_FAMILY"
    )
    guards = "\n".join(matrix["silent_failure_guards"])
    assert "wrong target boundary" in guards
    assert "derived from Lemma 3.3" in guards


def test_scope_covers_framing_but_excludes_later_stages() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    scope = "\n".join(artifact["established_scope"])
    nonclaims = "\n".join(artifact["explicit_non_claims"])
    assert "crossings, extrema, coupons" in scope
    assert "arbitrary nested typed contexts" in scope
    assert "serializable framed-link" in nonclaims
    assert "Reidemeister" in nonclaims
    assert "four-manifold invariance" in nonclaims
