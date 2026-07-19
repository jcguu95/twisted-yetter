from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-canonical-pivotal-step1-v1.json"
)
ROADMAP = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "egno-canonical-pivotal-primary-sources-v1.json"
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
        "PASS_STEP_1_OBJECTWISE_CANONICAL_PIVOTAL_FORMULA"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_only_step_1_is_established() -> None:
    roadmap = json.loads(ROADMAP.read_text())
    assert roadmap["steps"][0]["status"] == "ESTABLISHED_IN_LEAN"
    assert all(
        step["status"] == "NOT_YET_ESTABLISHED"
        for step in roadmap["steps"][1:]
    )
    artifact = json.loads(ARTIFACT.read_text())
    assert "NATURALITY_INVERTIBILITY_MONOIDALITY_OPEN" in (
        artifact["mathematical_status"]
    )


def test_three_convention_mutations_are_rejected() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    checks = artifact["checks"]
    assert checks["convention_mutations"]["rejected_count"] == 3
    assert checks["axiom_audit"]["audited_declaration_count"] == 3


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
