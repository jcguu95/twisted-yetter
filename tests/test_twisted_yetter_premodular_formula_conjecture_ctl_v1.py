from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = (
    ROOT
    / "experiments/results/theory/"
    "twisted-yetter-premodular-formula-conjecture-transcript-v1.json"
)
REFERENCE_LEDGER = (
    ROOT
    / "experiments/inputs/references/"
    "twisted-yetter-premodular-formula-conjecture-primary-sources-v1.json"
)
NOTE = (
    ROOT
    / "ctl-dogfood/lab-notes/"
    "2026-07-16-twisted-yetter-premodular-formula-conjecture-self-review.json"
)
SUBJECT = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/"
    "argument-proposal-twisted-yetter-premodular-sector-quadratic-ansatz.json"
)
DGNO = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/"
    "paper-dgno-0906-0620.json"
)
EDGE_ROOT = ROOT / "ctl-dogfood/subject-layer/edges"


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_transcript_preserves_exact_visible_proposal_and_provenance() -> None:
    transcript = load(TRANSCRIPT)
    note = load(NOTE)
    frozen = note["provenance"]["transcript_artifact"]
    assert hashlib.sha256(TRANSCRIPT.read_bytes()).hexdigest() == frozen["sha256"]
    assert transcript["status"] == "ARCHIVAL_SOURCE_ONLY"
    assert transcript["formal_evidence"] is False
    assert transcript["message_counts"] == {
        "total": 5,
        "user": 1,
        "assistant_visible": 4,
        "assistant_final_answers": 1,
    }
    assert len(transcript["messages"]) == 5
    assert transcript["provenance"]["model_verified_from_turn_context"] == (
        "gpt-5.6-sol"
    )
    assert transcript["provenance"][
        "reasoning_effort_verified_from_turn_context"
    ] == "medium"
    assert transcript["provenance"]["user_later_described_effort_as"] == "ultra"


def test_note_is_unambiguously_not_a_claim_or_project_conclusion() -> None:
    note = load(NOTE)
    status = note["epistemic_status"]
    assert note["mathematical_status"] == (
        "LAYERED_ANSATZ_NOT_THEOREM_NOT_CLAIM"
    )
    assert status["formal_mathematical_claim_made"] is False
    assert status["formal_mathematical_theorem_claim_made"] is False
    assert status["machine_checked_premodular_computational_statement_made"] is False
    assert status["project_conclusion_adopted"] is False
    assert status["expert_review_completed"] is False
    assert note["ctl_storage_semantics"]["mathematical_claim_semantics"] is False
    assert "NOT A THEOREM" in note["top_notice"]
    assert len(note["explicit_non_claims"]) >= 12


def test_review_keeps_sector_and_quadratic_hypotheses_separate() -> None:
    note = load(NOTE)
    levels = {row["id"]: row for row in note["candidate_hierarchy"]}
    assert levels["level-1-schematic-transparent-sector-ansatz"]["status"] == (
        "PLAUSIBLE_SCHEMATIC_ANSATZ_NOT_SOURCE_PROVED"
    )
    assert levels["level-2-sectorwise-quadratic-refinement"]["status"] == (
        "STRONGER_CONJECTURE_NOT_IMPLIED_BY_LEVEL_0_OR_LEVEL_1"
    )
    assert len(
        levels["level-2-sectorwise-quadratic-refinement"][
            "required_hypotheses"
        ]
    ) == 6
    assert levels["level-3-zero-safe-block-ansatz"]["status"] == (
        "CONDITIONAL_ZERO_SAFE_REFORMULATION_NOT_GENERAL_FORMULA"
    )


def test_material_corrections_close_known_silent_failure_routes() -> None:
    note = load(NOTE)
    corrections = note["material_corrections_to_the_initial_proposal"]
    text = " ".join(
        row["initial_form"] + " " + row["corrected_form"] + " " + row["reason"]
        for row in corrections
    ).lower()
    assert len(corrections) == 7
    for needle in (
        "rep(g)",
        "simply connected",
        "quadratic",
        "denominator",
        "connected-sum",
        "radical",
        "classifying-map",
    ):
        assert needle in text
    assert note["review_verdict"]["initial_unqualified_answer_accepted_as_written"] is False
    assert note["review_verdict"]["accepted_for_object_store"] is True


def test_yetter_arbitrary_a_gap_and_source_scope_are_machine_visible() -> None:
    note = load(NOTE)
    ledger = load(REFERENCE_LEDGER)
    frozen = note["reference_ledger"]
    assert hashlib.sha256(REFERENCE_LEDGER.read_bytes()).hexdigest() == frozen["sha256"]
    assert note["coefficient_group_warning"]["status"] == (
        "INTERPRETIVE_GENERALIZATION_REQUIRES_DERIVATION"
    )
    assert "Z/2" in note["coefficient_group_warning"]["warning"]
    assert ledger["status"] == (
        "CURATED_PRIMARY_SOURCE_LEDGER_WITH_EXPLICIT_INTERPRETATION_GAPS"
    )
    assert len(ledger["references"]) == 5
    assert all(reference["locators"] for reference in ledger["references"])


def test_subject_and_dgno_reference_keep_guardrails_visible() -> None:
    subject = load(SUBJECT)
    dgno = load(DGNO)
    assert subject["status"] == "conjectural_self_reviewed_not_claim"
    guardrail = subject["current_view_hints"]["guardrail"].lower()
    assert "not a theorem" in guardrail
    assert "not a" in guardrail and "claim" in guardrail
    assert len(subject["formula_layers"]) == 3
    assert dgno["subject_kind"] == "ty:paper"
    assert "does not construct" in dgno["scope_note"].lower()


def test_edges_connect_only_the_declared_note_candidates_and_sources() -> None:
    paths = sorted(EDGE_ROOT.glob("premodular-formula-conjecture-*.json"))
    assert len(paths) == 8
    edges = [load(path) for path in paths]
    source = (
        "subject:twisted-yetter:argument-proposal:"
        "premodular-sector-quadratic-ansatz"
    )
    assert {edge["source"] for edge in edges} == {source}
    assert {edge["target"] for edge in edges} == {
        "claim:lab-note:2026-07-16-twisted-yetter-premodular-formula-conjecture-self-review",
        "subject:twisted-yetter:argument-proposal:modular-quadratic-block-formula",
        "subject:twisted-yetter:argument-proposal:stable-no-go-simply-connected-closed-4-manifolds",
        "subject:twisted-yetter:paper:yetter-hepth-9311082",
        "subject:twisted-yetter:paper:dgno-0906-0620",
        "subject:twisted-yetter:paper:baerenz-barrett-1601-03580",
        "subject:twisted-yetter:paper:reutter-2001-02288",
        "subject:twisted-yetter:paper:tham-2108-13467",
    }
