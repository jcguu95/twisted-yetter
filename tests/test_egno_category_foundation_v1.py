from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/egno-category-foundation-v1.json"
)
MATRIX = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-category-foundation-obligation-matrix-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "egno-category-foundations-primary-sources-v1.json"
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


def test_artifact_is_content_addressed_and_clean() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_EGNO_CATEGORY_INTERFACES_AND_KIRBY_BINDINGS"
    )
    assert artifact["mathematical_status"] == (
        "PARTIAL_CATEGORY_FOUNDATION_ESTABLISHED_WITH_"
        "EXPLICIT_STANDARD_THEOREM_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_scope_is_partial_and_four_blockers_remain_visible() -> None:
    matrix = json.loads(MATRIX.read_text())
    assert matrix["terminal_counts"] == {
        "established_or_explicit_standard_input": 12,
        "not_yet_formalized_or_not_yet_derived": 4,
        "total": 16,
    }
    artifact = json.loads(ARTIFACT.read_text())
    assert len(artifact["remaining_blockers"]) == 4
    nonclaims = "\n".join(artifact["explicit_non_claims"])
    assert "fusion-category layer is not complete" in nonclaims
    assert "No concrete category" in nonclaims


def test_negative_checks_reject_all_missing_category_laws() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["checks"]["category_mutations"]["rejected_count"] == 4
    assert artifact["checks"]["presentation_mutations"]["rejected_count"] == 5
    assert artifact["checks"]["axiom_audit"][
        "audited_declaration_count"
    ] == 9


def test_egno_source_capture_is_hash_pinned() -> None:
    references = json.loads(REFERENCES.read_text())
    capture = references["references"][0]["captured_pdf"]
    assert capture["sha256"] == (
        "5d3cfde5b6ec7b8aef10d020f1627377b482ee8ee352feb368eff6e477ebc0dc"
    )
    assert capture["bytes"] == 6216438
    assert capture["pages"] == 362


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
