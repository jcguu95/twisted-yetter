from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUDIT = (
    ROOT
    / "experiments/results/theory/"
    "twisted-yetter-quadratic-block-prediction-audit-v1.json"
)
NOTE = (
    ROOT
    / "ctl-dogfood/lab-notes/"
    "2026-07-16-twisted-yetter-modular-quadratic-block-prediction-audit.json"
)
PROPOSAL = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/"
    "argument-proposal-twisted-yetter-modular-quadratic-block-formula.json"
)
CLUSTER = (
    ROOT
    / "ctl-dogfood/subject-layer/definitions/"
    "claim-cluster-twisted-yetter-quadratic-block-computational-audit.json"
)
EDGE_ROOT = ROOT / "ctl-dogfood/subject-layer/edges"


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def test_note_pins_the_exact_audit_bytes_and_machine_checked_counts() -> None:
    audit = load(AUDIT)
    note = load(NOTE)
    frozen = note["frozen_audit_artifact"]
    assert hashlib.sha256(AUDIT.read_bytes()).hexdigest() == frozen["sha256"]
    assert frozen["content_hash"] == audit["content_hash"]
    assert frozen["git_blob"] == "a23ddb8fc1a83b25141d9dcc775e6d8335829170"
    note_counts = note["data_quality_and_scope"]
    audit_counts = audit["machine_checked_result"]
    for key, value in note_counts.items():
        assert audit_counts[key] == value


def test_note_separates_the_computational_theorem_from_the_formula_candidate() -> None:
    note = load(NOTE)
    assert note["machine_checked_computational_statement_made"] is True
    assert note["formal_mathematical_theorem_claim_made"] is False
    assert note["candidate_modular_formula"]["epistemic_status"] == (
        "THEOREM_CANDIDATE_NUMERICALLY_SUPPORTED_NOT_PROVED_HERE"
    )
    assert note["established_computational_theorem"]["status"] == (
        "ESTABLISHED_MACHINE_CHECKED_STATEMENT_ABOUT_FROZEN_DATA"
    )
    assert len(note["proof_obligations"]) == 4


def test_eleven_eighths_and_pontryagin_guardrails_are_explicit() -> None:
    note = load(NOTE)
    blocks = note["simply_connected_standard_block_scope"]
    assert blocks["status_of_11_8"] == (
        "OPEN_CONJECTURE_AS_OF_2026_NOT_ASSUMED_AS_THEOREM"
    )
    assert "not logically required" in blocks[
        "direct_prediction_does_not_need_11_8"
    ]
    non_claims = " ".join(note["explicit_non_claims"])
    assert "Pontryagin class p1(TM)" in non_claims
    assert "Pontryagin square" in note["top_notice"]


def test_figure21_remains_distribution_only() -> None:
    note = load(NOTE)
    figure21 = note["figure21_specialization"]
    assert figure21["pointwise_marked_row_count"] == 0
    assert figure21["pointwise_all_alpha_status"] == (
        "BLOCKED_NO_CERTIFIED_H2_COORDINATE_MAP"
    )
    assert "all 15" in figure21["distribution_level_result"]
    assert "Thirteen rows already match raw" in figure21["distribution_level_result"]
    assert figure21["normalization_audit"]["status"] == (
        "PASS_ALL_15_POINTED_ROWS_MATCH_AFTER_INDEPENDENT_"
        "ORDINARY_AGGREGATE_NORMALIZATION"
    )


def test_subjects_keep_the_epistemic_status_visible() -> None:
    proposal = load(PROPOSAL)
    cluster = load(CLUSTER)
    assert proposal["status"] == (
        "open_expert_review_numerically_supported_not_proved"
    )
    assert "not a proved formula" in proposal["current_view_hints"][
        "guardrail"
    ]
    assert proposal["formula_summary"]["premodular_extension"].startswith(
        "CONJECTURAL_NOT_ESTABLISHED"
    )
    assert cluster["status"] == (
        "active_established_computational_result_mathematical_formula_open"
    )
    assert "201" in cluster["current_view_hints"]["headline"]


def test_subject_edges_connect_formula_audit_note_data_and_sources() -> None:
    paths = sorted(EDGE_ROOT.glob("quadratic-block-*.json"))
    assert len(paths) == 9
    edges = [load(path) for path in paths]
    assert {edge["target"] for edge in edges} == {
        "claim:lab-note:2026-07-16-twisted-yetter-modular-quadratic-block-prediction-audit",
        "subject:twisted-yetter:argument-proposal:modular-quadratic-block-formula",
        "subject:twisted-yetter:claim-cluster:stable-no-go-computational-compatibility",
        "subject:twisted-yetter:claim-cluster:figure21-pointed-modular-comparison",
        "subject:twisted-yetter:paper:yetter-hepth-9311082",
        "subject:twisted-yetter:paper:crane-kauffman-yetter-hepth-9409167",
        "subject:twisted-yetter:paper:freedman-topology-four-dimensional-manifolds-1982",
        "subject:twisted-yetter:paper:furuta-monopole-11-8-2001",
        "claim:lab-note:2026-07-16-figure21-pointed-ordinary-normalization-audit",
    }
