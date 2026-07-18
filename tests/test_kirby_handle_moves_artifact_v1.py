from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.kirby_handle_moves_v1 import (
    canonical_hash,
    validate_handle_slide_bookkeeping,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT / "experiments/results/lean-kirby/kirby-handle-moves-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "kirby-handle-moves-obligation-matrix-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "kirby-handle-moves-primary-sources-v1.json"
)
LEAN_SOURCE = ROOT / "lean/TwistedYetter/Kirby/KirbyHandleMoves.lean"


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_r8_artifact_is_terminal_clean_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["status"] == "PASS_KIRBY_HANDLE_SLIDES"
    assert artifact["mathematical_status"] == (
        "KIRBY_HANDLE_SLIDES_EVALUATOR_INVARIANT_RELATIVE_TO_EXPLICIT_"
        "ORIGINAL_AND_GENERALIZED_SLIDING_INPUTS"
    )
    assert artifact["roadmap_status"] == (
        "R8_TERMINAL_RELATIVE_TO_EXPLICIT_SLIDING_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_all_six_move_orientation_fixtures_revalidate() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    coverage = artifact["move_coverage"]

    assert coverage["status"] == "PASS_ALL_THREE_KINDS_BOTH_ORIENTATIONS"
    assert coverage["expected_count"] == coverage["actual_count"] == 6
    for fixture in coverage["fixtures"]:
        validate_handle_slide_bookkeeping(fixture)


def test_closed_whitelists_have_no_generic_move_escape() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    whitelist = artifact["checks"]["closed_move_whitelist"]
    source = LEAN_SOURCE.read_text()

    assert whitelist["constructor_count"] == 3
    assert whitelist["arbitrary_certified_move_constructor"] is False
    assert "inductive OrdinaryHandleSlide" in source
    assert "inductive TwoHandleOverTwoSlide" in source
    assert "def ofCertified" not in source


def test_chain_and_character_conventions_are_not_conflated() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    runtime = artifact["checks"]["runtime_bookkeeping"]

    assert runtime["two_over_two_only_q_congruence"] is True
    assert runtime["class_transform"] == "P2^-1 mod 2"
    assert runtime["character_transform"] == "P2^T mod 2"
    for fixture in artifact["move_coverage"]["fixtures"]:
        has_q = (
            fixture["handle_chain"]["source_q2_linking_matrix"] is not None
        )
        assert has_q is (fixture["kind"] == "two_over_two")


def test_obligations_and_source_capture_are_pinned() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    ledger = json.loads(REFERENCES.read_text())

    assert matrix["status"] == (
        "R8_TERMINAL_RELATIVE_TO_EXPLICIT_SLIDING_INPUTS"
    )
    assert len(matrix["obligations"]) == 16
    assert not any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN"}
        for row in matrix["obligations"]
    )
    baerenz = ledger["references"][0]
    assert baerenz["captured_pdf"]["sha256"] == (
        "cf14c9d316c563cbf1bceec0b5309b561083585dc702fd24f579eadb216ff5de"
    )
    assert any(
        "Table 2" in locator["locator"]
        for locator in baerenz["locators"]
    )


def test_pinned_sources_replay_from_r8_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]

    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_nonclaims_block_scope_upgrade() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    nonclaims = "\n".join(artifact["explicit_non_claims"])

    assert "does not re-prove Bärenz-Barrett Lemma 3.1" in nonclaims
    assert "bookkeeping only" in nonclaims
    assert "handle cancellations" in nonclaims
    assert "four-manifold invariant" in nonclaims
    assert "specially-dotted evaluator" in nonclaims
