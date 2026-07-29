from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.kirby_presentation_v1 import (
    deserialize_presentation,
    stable_content_hash,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-syntax-v1.json"
)
FIXTURE = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-fixture-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-obligation-matrix-v1.json"
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


def test_r6_artifact_is_clean_terminal_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == "PASS_FRAMED_LINK_PRESENTATION_SYNTAX"
    assert artifact["mathematical_status"] == (
        "FRAMED_LINK_KIRBY_PRESENTATION_SYNTAX_ESTABLISHED"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["checks"]["kirby_axiom_audit"]["theorem_count"] == 11
    assert artifact["checks"]["lean_mutation_tests"]["rejected_count"] == 3
    assert artifact["checks"]["python_validator_tests"]["test_count"] == 28


def test_generated_fixture_matches_both_hash_layers_and_round_trips() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    raw = FIXTURE.read_bytes()
    fixture = deserialize_presentation(raw)
    record = artifact["outputs"]["fixture"]
    assert hashlib.sha256(raw).hexdigest() == record["file_sha256"]
    assert fixture["content_hash"] == record["content_hash"]
    assert fixture["content_hash"] == stable_content_hash(fixture)
    assert record["slice_count"] == record["event_count"] + 1
    assert fixture["declared_slices"][0]["active_strands"] == []
    assert fixture["declared_slices"][-1]["active_strands"] == []
    assert len(fixture["dotted_cuts"]) == 1
    assert [
        puncture["cut_position"]
        for puncture in fixture["dotted_cuts"][0]["punctures"]
    ] == [0, 1]


def test_all_roles_and_framing_relations_are_materialized() -> None:
    fixture = json.loads(FIXTURE.read_text())
    assert {item["role"] for item in fixture["components"]} == {
        "ordinary",
        "dotted",
        "specially_dotted",
    }
    for component in fixture["components"]:
        assert (
            component["blackboard_writhe"]
            + component["framing_correction"]
            == component["integer_framing"]
        )


def test_pinned_sources_replay_from_the_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_obligation_matrix_is_terminal_and_nonclaims_are_preserved() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    assert len(matrix["obligations"]) == 15
    assert not any(
        row["status"] == "NOT_FORMALIZED" for row in matrix["obligations"]
    )
    guards = "\n".join(matrix["silent_failure_guards"])
    nonclaims = "\n".join(matrix["explicit_non_claims"])
    assert "native_decide is not used" in guards
    assert "alias" in guards
    assert "Reidemeister" in nonclaims
    assert "four-manifold invariance" in nonclaims
