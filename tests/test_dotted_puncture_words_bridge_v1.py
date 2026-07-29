from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dotted-puncture-words-implementation-bridge-v1.json"
)
LEDGER = (
    ROOT
    / "experiments/results/lean-kirby/"
    "independent-combinatorial-semantic-comparison-blocker-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def test_bridge_artifact_is_content_addressed_and_scoped() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_DOTTED_PUNCTURE_AND_CLOSING_HANDLE_IMPLEMENTATION_BRIDGE"
    )
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert set(artifact["resolved_blockers"]) == {
        "DOTTED_PUNCTURE_WORDS_MISSING",
        "CLOSING_THREE_HANDLE_DATA_MISSING",
    }
    assert artifact["checks"]["topology_certificate_is_proof_bearing"] is True
    assert artifact["checks"]["aggregated_incidence_used_to_infer_words"] is False
    assert artifact["checks"]["closing_boundary_movie_is_proof_bearing"] is True
    assert (
        artifact["checks"]["closing_boundary_movie_source_is_exactly_bound"]
        is True
    )
    assert (
        artifact["checks"]["three_handle_count_is_derived_from_boundary_genus"]
        is True
    )
    assert (
        artifact["checks"]["bare_formal_presentation_is_accepted_as_closed"]
        is False
    )
    assert artifact["checks"]["new_axioms_added_for_closing_bridge"] == 0


def test_ledger_keeps_all_remaining_semantic_blockers_visible() -> None:
    ledger = json.loads(LEDGER.read_text())
    assert ledger["content_hash"] == canonical_hash(ledger)
    assert {item["id"] for item in ledger["blockers"]} == {
        "PRIMAL_DUAL_HOMOLOGY_CONVENTION_MISMATCH",
    }
    assert {item["id"] for item in ledger["semantic_warnings"]} == {
        "PUNCTURE_DIRECTION_SIGN_RELATION_NOT_NORMATIVE",
    }
    assert "DOTTED_PUNCTURE_WORDS_MISSING" in ledger["resolved_blockers"]
    assert "CLOSING_THREE_HANDLE_DATA_MISSING" in ledger["resolved_blockers"]


def test_frozen_semantic_hashes_still_match_disk() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    directory = (
        ROOT / "lean/TwistedYetter/Kirby/Final/Semantics/Independent"
    )
    observed = {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(directory.glob("*.lean"))
    }
    assert observed == artifact["checks"]["frozen_semantics_hashes"]
