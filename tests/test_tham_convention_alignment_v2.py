from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INDEPENDENT = (
    ROOT / "lean/TwistedYetter/Kirby/Final/Semantics/Independent"
)
MANIFEST = INDEPENDENT / "semantic-freeze-combinatorial-v2.json"
HOMOLOGY = INDEPENDENT / "Homology.lean"
EVALUATOR = INDEPENDENT / "Evaluator.lean"
MOVES = INDEPENDENT / "Moves.lean"
BRIDGE = (
    ROOT
    / "lean/TwistedYetter/Kirby/Final/Semantics/"
    "CompleteSemanticConformance.lean"
)
REVISION = (
    ROOT
    / "experiments/results/lean-kirby/"
    "frozen-semantic-convention-alignment-v2.json"
)
COMPARISON = (
    ROOT
    / "experiments/results/lean-kirby/"
    "independent-combinatorial-semantic-comparison-v2.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def test_v2_hash_seal_is_current_and_v1_is_preserved() -> None:
    manifest = json.loads(MANIFEST.read_text())
    observed = {
        path.name: hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(INDEPENDENT.glob("*.lean"))
    }
    assert manifest["supersedes"] == "semantic-freeze-combinatorial-v1.json"
    assert manifest["hash_policy"]["required_prefix"] == "000"
    assert observed == manifest["files"]
    assert all(digest.startswith("000") for digest in observed.values())
    assert (
        INDEPENDENT / "semantic-freeze-combinatorial-v1.json"
    ).is_file()


def test_transpose_is_computed_and_tham_chain_condition_is_derived() -> None:
    homology = HOMOLOGY.read_text()
    assert "def transposeAddHom" in homology
    assert "def thamBoundaryTwo" in homology
    assert "def thamBoundaryThree" in homology
    assert "theorem transpose_adjoint" in homology
    assert "theorem boundary_squared_zero" in homology
    body = re.search(
        r"structure TurnedOverBoundaryCertificate.*?"
        r"namespace TurnedOverBoundaryCertificate",
        homology,
        flags=re.S,
    )
    assert body is not None
    assert "thamBoundaryTwo :" not in body.group(0)
    assert "thamBoundaryThree :" not in body.group(0)


def test_evaluator_can_only_read_tham_cycles_and_reverses_counts() -> None:
    evaluator = EVALUATOR.read_text()
    assert "(cycle : ThamTwoCycles turnedOver)" in evaluator
    assert "characterWeight 𝒞η turnedOver labeling cycle" in evaluator
    assert (
        "diagram.handles.hThree\n"
        "      diagram.handles.hTwo\n"
        "      diagram.handles.hOne"
    ) in evaluator
    assert "(cycle : PrimalTwoCycles" not in evaluator


def test_every_move_carries_both_transports_and_turnover_naturality() -> None:
    moves = MOVES.read_text()
    assert "structure MoveHomologyTransport" in moves
    assert "primal :" in moves
    assert "tham :" in moves
    assert "turnover_natural :" in moves
    assert "theorem ElementaryMove.thamMarkingTransport" in moves
    for constructor in (
        "framedIsotopy",
        "oneOverOne",
        "twoOverOne",
        "twoOverTwo",
        "cancellation",
    ):
        assert f"| {constructor}" in moves


def test_bridge_forces_primal_marking_through_turnover() -> None:
    bridge = BRIDGE.read_text()
    assert "frozenAlpha : PrimalKirbyH₂ source.primalBoundary" in bridge
    assert "source.turnover.equiv marking.frozenAlpha" in bridge
    assert "marking.frozenThamCycle" in bridge
    assert "marking.frozenCycle" not in bridge
    assert "final_evaluator_equality" not in bridge
    assert re.search(r"\b(sorry|admit)\b", bridge) is None


def test_revision_artifact_is_hash_bound_and_scoped() -> None:
    artifact = json.loads(REVISION.read_text())
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == "FROZEN_SEMANTICS_V2_CONVENTION_ALIGNED"
    assert artifact["admission"]["ctl_admitted"] is False
    assert artifact["admission"]["reason"] == (
        "CTL_VERIFICATION_BLOCKED_MISSING_SIBLING_PROVIDER"
    )
    assert artifact["claims"]["new_four_manifold_theorem"] is False
    assert artifact["claims"]["legacy_numerics_recertified"] is False


def test_current_comparison_ledger_resolves_only_the_convention_blocker() -> None:
    ledger = json.loads(COMPARISON.read_text())
    assert ledger["content_hash"] == canonical_hash(ledger)
    assert ledger["status"] == "PASS_CONVENTION_ALIGNMENT_HARD_GATE"
    assert "PRIMAL_DUAL_HOMOLOGY_CONVENTION_MISMATCH" in (
        ledger["resolved_blockers"]
    )
    assert ledger["admission_status"] == (
        "NO_CONCRETE_CASE_ADMITTED_WITHOUT_COMPLETE_CERTIFICATE"
    )
    assert {warning["id"] for warning in ledger["remaining_semantic_warnings"]} == {
        "PUNCTURE_DIRECTION_SIGN_RELATION_NOT_NORMATIVE"
    }
