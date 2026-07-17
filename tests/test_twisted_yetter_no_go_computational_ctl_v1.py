from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUDIT = (
    ROOT
    / "experiments/results/theory/"
    "twisted-yetter-stable-no-go-computational-audit-v1.json"
)
NOTE = (
    ROOT
    / "ctl-dogfood/lab-notes/"
    "2026-07-16-twisted-yetter-stable-no-go-computational-compatibility-audit.json"
)
SUBJECT = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/"
    "claim-cluster-twisted-yetter-stable-no-go-computational-compatibility.json"
)
REUTTER = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/paper-reutter-2001-02288.json"
)
EDGE_ROOT = ROOT / "ctl-dogfood/subject-layer/edges"


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_ctl_note_matches_the_frozen_audit_bytes_and_counts() -> None:
    audit = load(AUDIT)
    note = load(NOTE)
    artifact = note["frozen_audit_artifact"]
    assert hashlib.sha256(AUDIT.read_bytes()).hexdigest() == artifact["sha256"]
    assert artifact["content_hash"] == audit["content_hash"]
    assert artifact["generator_commit"] == audit["git_commit"]
    note_counts = note["machine_checked_denominator"]
    audit_counts = audit["established_computational_theorem"][
        "machine_checked_counts"
    ]
    for key in (
        "retained_evidence_group_count",
        "figure21_pointed_realization_count",
        "figure21_raw_graph_exact_pointed_rows",
        "figure21_normalized_exact_pointed_rows",
        "figure21_nonidentity_presentation_correction_rows",
        "figure21_certified_h2_marked_pointwise_rows",
        "declared_control_comparison_units_excluding_figure21_distributions",
        "certified_counterexample_count",
    ):
        assert note_counts[key] == audit_counts[key]
    assert note_counts["comparison_named_artifact_count"] == len(
        audit["comparison_file_inventory"]
    )


def test_ctl_note_establishes_only_computational_statement() -> None:
    note = load(NOTE)
    assert note["formal_mathematical_theorem_claim_made"] is False
    assert note["machine_checked_computational_statement_made"] is True
    assert note["project_no_go_conclusion_adopted"] is False
    assert note["conditional_mathematical_theorem"]["status"] == (
        "CONDITIONAL_PROPOSITION_NOT_YET_ESTABLISHED_AS_PROJECT_THEOREM"
    )
    assert len(note["conditional_mathematical_theorem"]["proof_obligations"]) == 3
    non_claims = " ".join(note["explicit_non_claims"]).lower()
    assert "does not establish the mathematical no-go theorem" in non_claims
    assert "no full premodular figure 21" in non_claims


def test_figure21_caveats_are_top_level_and_machine_readable() -> None:
    note = load(NOTE)
    findings = {
        row["id"]: row["status"] for row in note["data_quality_findings"]
    }
    assert findings["figure21-rank2-global-phase"] == (
        "RESOLVED_AS_INDEPENDENTLY_CALIBRATED_PRESENTATION_NORMALIZATION"
    )
    assert findings["figure21-h2-marking"] == "NOT_CERTIFIED"
    assert findings["figure21-source"] == (
        "DRAFT_USER_TRANSCRIPTION_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM"
    )
    assert note["evidence_scope"]["figure21_tractable_route"] == (
        "MODULAR_SHORTCUT_MTC_ONLY"
    )
    assert note["evidence_scope"]["figure21_premodular_full_evaluation"] == (
        "NOT_COMPUTABLE_WITH_CURRENT_BACKEND"
    )


def test_subject_and_reference_keep_the_guardrails_visible() -> None:
    subject = load(SUBJECT)
    reutter = load(REUTTER)
    assert subject["subject_kind"] == "ty:claim-cluster"
    guardrail = subject["current_view_hints"]["guardrail"].lower()
    assert "not a topological no-go theorem" in guardrail
    assert "15 of 15" in guardrail
    assert "no full premodular run" in guardrail
    assert reutter["subject_kind"] == "ty:paper"
    assert "do not by themselves establish" in reutter["scope_note"].lower()


def test_subject_edges_connect_audit_to_note_proposal_data_and_references() -> None:
    paths = sorted(EDGE_ROOT.glob("stable-no-go-computational-audit-*.json"))
    assert len(paths) == 6
    edges = [load(path) for path in paths]
    assert all(
        edge["source"]
        == "subject:twisted-yetter:claim-cluster:stable-no-go-computational-compatibility"
        for edge in edges
    )
    assert {edge["target"] for edge in edges} == {
        "claim:lab-note:2026-07-16-twisted-yetter-stable-no-go-computational-compatibility-audit",
        "subject:twisted-yetter:argument-proposal:stable-no-go-simply-connected-closed-4-manifolds",
        "subject:twisted-yetter:claim-cluster:figure21-pointed-modular-comparison",
        "subject:twisted-yetter:paper:yetter-hepth-9311082",
        "subject:twisted-yetter:paper:ruberman-strle-2210-16260",
        "subject:twisted-yetter:paper:reutter-2001-02288",
    }
