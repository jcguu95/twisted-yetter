from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/akbulut-yasui/"
    "figure21-pointed-ordinary-normalization-audit-v1.json"
)
NOTE = (
    ROOT
    / "ctl-dogfood/lab-notes/"
    "2026-07-16-figure21-pointed-ordinary-normalization-audit.json"
)
FIGURE21_NOTE = (
    ROOT
    / "ctl-dogfood/lab-notes/"
    "2026-07-16-figure21-pointed-modular-comparison.json"
)
SUBJECT = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/"
    "claim-cluster-figure21-pointed-modular-comparison.json"
)
EDGE_ROOT = ROOT / "ctl-dogfood/subject-layer/edges"


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def test_normalization_note_pins_exact_clean_artifact() -> None:
    artifact = load(ARTIFACT)
    note = load(NOTE)
    frozen = note["frozen_normalization_artifact"]
    assert hashlib.sha256(ARTIFACT.read_bytes()).hexdigest() == frozen["sha256"]
    assert frozen["content_hash"] == artifact["content_hash"]
    assert frozen["git_blob"] == "3ef1ae7d1c6f1a0f76a57b7db3b135cf2509cefd"
    assert frozen["git_dirty_before_output_write"] is False


def test_normalization_note_preserves_raw_and_normalized_denominators() -> None:
    note = load(NOTE)
    result = note["machine_checked_result"]
    assert result["pointed_realization_count"] == 15
    assert result["raw_graph_distribution_match_count"] == 13
    assert result["normalized_distribution_match_count"] == 15
    assert result["nonidentity_presentation_correction_count"] == 2
    assert result["semion_derived_presentation_correction"] == "-1+0i"
    assert result["certified_h2_marked_pointwise_row_count"] == 0


def test_normalization_note_keeps_non_circularity_and_scope_visible() -> None:
    note = load(NOTE)
    controls = {
        row["id"]: row["status"] for row in note["anti_silent_fail_controls"]
    }
    assert controls["preserved-ordinary-sum-corrupted-distribution"] == (
        "PASS_NEGATIVE_CONTROL_REJECTED"
    )
    assert note["formal_mathematical_theorem_claim_made"] is False
    non_claims = " ".join(note["explicit_non_claims"]).lower()
    assert "does not provide an h2 coordinate map" in non_claims
    assert "does not establish the conjectural premodular extension" in non_claims


def test_figure21_current_preimages_use_independent_normalization_language() -> None:
    figure21 = load(FIGURE21_NOTE)
    subject = load(SUBJECT)
    comparison = figure21["results"]["same_label_standard_comparison"]
    assert comparison["normalized_matching_row_count"] == 15
    assert comparison["raw_graph_matching_row_count"] == 13
    assert comparison["nonidentity_presentation_correction_row_count"] == 2
    assert "ordinary-aggregate" in subject["current_view_hints"][
        "headline"
    ]
    assert "No H2 marking is certified" in subject["current_view_hints"][
        "guardrail"
    ]


def test_normalization_note_is_linked_to_figure21_and_quadratic_subjects() -> None:
    paths = [
        EDGE_ROOT / "figure21-pointed-comparison-records-normalization-note.json",
        EDGE_ROOT / "quadratic-block-audit-uses-figure21-normalization.json",
    ]
    edges = [load(path) for path in paths]
    target = (
        "claim:lab-note:2026-07-16-"
        "figure21-pointed-ordinary-normalization-audit"
    )
    assert {edge["target"] for edge in edges} == {target}
    assert {edge["source"] for edge in edges} == {
        "subject:twisted-yetter:claim-cluster:figure21-pointed-modular-comparison",
        "subject:twisted-yetter:claim-cluster:quadratic-block-computational-audit",
    }
