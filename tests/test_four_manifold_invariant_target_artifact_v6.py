from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "four-manifold-invariant-target-v6.json"
)
TOPOLOGY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedKirbyCompleteness."
    "standardSpecialKirbyCalculusConnected"
)
HOMOLOGY_AXIOM = (
    "TwistedYetter.Kirby.SourceBackedHandleChainNaturality."
    "standardHandleChainNaturalityInput"
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


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    ).stdout


def test_v6_is_content_addressed_and_not_promoted() -> None:
    artifact = load_artifact()
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "PASS_ELEVEN_FOUNDATION_CONDITIONS_ESTABLISHED_"
        "ONE_SOURCE_BOUND_EVALUATOR_INSTANCE_OPEN"
    )
    assert artifact["git"]["dirty_before_generation"] is False
    assert artifact["admission"]["ctl_theorem_claim_admitted"] is False


def test_exact_eleven_one_partition() -> None:
    ledger = load_artifact()["target_condition_ledger"]
    assert ledger["counts"] == {"required": 12, "established": 11, "open": 1}
    assert ledger["required_conditions"] == (
        ledger["established_conditions"] + ledger["open_conditions"]
    )
    assert ledger["open_conditions"] == [
        "sourceBoundEvaluatorCompilerInstance"
    ]


def test_exact_two_domain_axioms_and_no_hidden_result() -> None:
    boundary = load_artifact()["domain_axiom_boundary"]
    assert boundary["count"] == 2
    assert boundary["axioms"] == sorted([TOPOLOGY_AXIOM, HOMOLOGY_AXIOM])
    assert boundary["homology_axiom_contains_chain_equivalences"] is True
    assert boundary["homology_axiom_contains_coordinate_naturality"] is True
    assert boundary["homology_axiom_contains_final_h2_identity"] is False
    assert boundary["homology_axiom_contains_evaluator_equality"] is False
    assert boundary["geometric_h2_semantics_external"] is True


def test_exact_mutation_and_axiom_denominators() -> None:
    checks = load_artifact()["checks"]
    assert checks["categorical_compiler"]["mutation_count"] == 3
    assert checks["geometric_h2_mechanism"]["mutation_count"] == 2
    assert checks["handle_chain_domain"]["mutation_count"] == 2
    assert checks["target"]["mutation_count"] == 5
    assert checks["categorical_compiler"]["custom_domain_axiom_count"] == 0
    assert (
        checks["geometric_h2_mechanism"]["custom_domain_axiom_count"] == 0
    )
    assert checks["handle_chain_domain"]["custom_domain_axioms"] == [
        HOMOLOGY_AXIOM
    ]
    assert checks["target"]["custom_domain_axioms"] == sorted(
        [TOPOLOGY_AXIOM, HOMOLOGY_AXIOM]
    )


def test_every_recorded_source_replays_from_pinned_commit() -> None:
    artifact = load_artifact()
    commit = artifact["git"]["commit"]
    for relative, record in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == record["bytes"], relative
        assert "sha256:" + hashlib.sha256(data).hexdigest() == (
            record["sha256"]
        ), relative


def test_only_remaining_obligation_is_categorical() -> None:
    artifact = load_artifact()
    obligations = artifact["remaining_instance_obligations"]
    assert len(obligations) == 1
    assert obligations[0]["condition"] == (
        "sourceBoundEvaluatorCompilerInstance"
    )
    assert obligations[0]["status"] == "OPEN"
    assert any(
        "geometric semantics" in claim
        for claim in artifact["explicit_nonclaims"]
    )
