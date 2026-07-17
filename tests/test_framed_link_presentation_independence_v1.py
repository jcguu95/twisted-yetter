from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-independence-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-independence-obligation-matrix-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "framed-link-presentation-independence-primary-sources-v1.json"
)
LEAN_SOURCE = (
    ROOT / "lean/TwistedYetter/Kirby/PresentationIsotopy.lean"
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


def test_r7_artifact_is_clean_terminal_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_FRAMED_LINK_EVALUATOR_PRESENTATION_INDEPENDENCE"
    )
    assert artifact["mathematical_status"] == (
        "FRAMED_LINK_EVALUATOR_PRESENTATION_INDEPENDENCE_ESTABLISHED_"
        "RELATIVE_TO_EXPLICIT_RIBBON_TRACE_AND_TOPOLOGY_INPUTS"
    )
    assert artifact["chain_status"] == (
        "R5_R6_R7_TERMINAL_RELATIVE_TO_EXPLICIT_STANDARD_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)
    audit = artifact["checks"]["kirby_axiom_audit"]
    assert audit["declaration_count"] == 57
    assert audit["new_r7_declaration_count"] == 18
    assert artifact["checks"]["lean_mutation_tests"]["rejected_count"] == 5


def test_closed_whitelist_has_no_arbitrary_certified_move_escape() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    whitelist = artifact["checks"]["closed_move_whitelist"]
    assert whitelist["status"] == "PASS_CLOSED_WHITELIST"
    assert whitelist["constructor_count"] == 22
    assert whitelist["arbitrary_certified_move_constructor"] is False
    source = LEAN_SOURCE.read_text()
    assert "inductive TaggedMove" in source
    assert "def ofCertified" not in source
    assert ".step (CertifiedMove.refl" not in source


def test_all_obligations_are_terminal_and_inputs_remain_visible() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    rows = matrix["obligations"]
    assert len(rows) == 24
    assert not any(row["status"] == "NOT_FORMALIZED" for row in rows)
    inputs = {item["input_id"]: item for item in matrix["trusted_inputs"]}
    assert set(inputs) == {
        "ribbon-kink-compatibility",
        "spherical-trace-cyclicity",
        "framed-presentation-topology-completeness",
    }
    assert "Caveat 4.31" in inputs[
        "framed-presentation-topology-completeness"
    ]["caveat"]
    assert "arbitrary CertifiedMove injection is impossible" in inputs[
        "framed-presentation-topology-completeness"
    ]["not_assumed"]


def test_source_hashes_and_coherence_caveat_are_preserved() -> None:
    ledger = json.loads(REFERENCES.read_text())
    references = {item["ref_id"]: item for item in ledger["references"]}
    baerenz = references["ref:baerenz-barrett-dichromatic-2018"]
    selinger = references["ref:selinger-graphical-languages-2010"]
    shum = references["ref:shum-tortile-1994"]
    assert baerenz["captured_pdf"]["sha256"] == (
        "cf14c9d316c563cbf1bceec0b5309b561083585dc702fd24f579eadb216ff5de"
    )
    assert selinger["captured_pdf"]["sha256"] == (
        "7ecac08962c1238739d2e4eb2da79ed197347d9046a136e1c39840e7a4d0bc44"
    )
    assert "Caveat 4.31" in selinger["scope_caveat"]
    assert "simple-signature" in shum["scope_caveat"]
    assert "NO_LOCAL_BYTE_CAPTURE" in shum["content_hash_status"]


def test_pinned_sources_replay_from_the_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_r5_and_r6_are_hash_pinned_inputs_not_chat_memory() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    for key in (
        "r5_framed_sliding_artifact",
        "r6_presentation_syntax_artifact",
    ):
        record = artifact["inputs"][key]
        path = ROOT / record["path"]
        payload = json.loads(path.read_text())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == record["sha256"]
        assert payload["content_hash"] == record["content_hash"]
        assert payload["git"]["commit"] == record["source_commit"]


def test_nonclaims_prevent_scope_upgrade() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    nonclaims = "\n".join(artifact["explicit_non_claims"])
    assert "full topological proof" in nonclaims
    assert "Shum Theorem 6.1" in nonclaims
    assert "R6 serialized presentation" in nonclaims
    assert "Kirby handle slide" in nonclaims
    assert "four-manifold" in nonclaims
