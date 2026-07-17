from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TRANSCRIPT = ROOT / "experiments/results/theory/twisted-yetter-no-go-proof-conversation-transcript-v1.json"
NOTE = ROOT / "ctl-dogfood/lab-notes/2026-07-16-twisted-yetter-stable-no-go-argument-proposal.json"
SUBJECT = ROOT / "ctl-dogfood/subject-layer/definitions/argument-proposal-twisted-yetter-stable-no-go.json"


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_transcript_is_exact_archival_source_not_formal_evidence() -> None:
    value = load(TRANSCRIPT)
    assert value["status"] == "ARCHIVAL_SOURCE_ONLY"
    assert value["epistemic_status"] == "UNREVIEWED_CANDIDATE_ARGUMENT"
    assert value["formal_evidence"] is False
    assert value["message_counts"] == {
        "assistant_final_answers": 3,
        "assistant_visible": 11,
        "total": 14,
        "user": 3,
    }
    assert value["messages"][0]["text"].startswith(
        "我很悲觀，看來這就代表 MTC 是完全沒有用的。"
    )
    assert value["messages"][-1]["text"].startswith("**先釐清名稱**")
    canonical = json.dumps(
        value["messages"], ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    assert hashlib.sha256(canonical).hexdigest() == value["provenance"][
        "messages_canonical_sha256"
    ]


def test_lab_note_cannot_be_read_as_theorem_or_current_adopted_conclusion() -> None:
    value = load(NOTE)
    assert value["status"] == "OPEN_EXPERT_REVIEW"
    assert value["mathematical_status"] == "PROPOSED_NO_GO_ARGUMENT"
    assert value["formal_theorem_claim_made"] is False
    assert value["project_conclusion_adopted"] is False
    assert value["user_assessment"]["expert_verification"] is False
    assert len(value["proof_obligations"]) == 3
    non_claims = " ".join(value["explicit_non_claims"]).lower()
    assert "not an established theorem" in non_claims
    assert "not expert verification" in non_claims


def test_subject_is_argument_proposal_with_visible_guardrail() -> None:
    value = load(SUBJECT)
    assert value["subject_kind"] == "ty:argument-proposal"
    assert value["status"] == "open_expert_review"
    guardrail = value["current_view_hints"]["guardrail"].lower()
    assert "not a theorem" in guardrail
    assert "not the project's accepted current conclusion" in guardrail
