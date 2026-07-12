import json
from pathlib import Path

from experiments.scripts.gompf_figure815_morse_sanity import replay_and_analyze


def test_e1_draft_link_sanity_matches_unimodular_signature_target():
    payload = json.loads(
        Path("experiments/inputs/gompf-stipsicz/figure815-e1-morse-draft-v1.json").read_text()
    )

    result = replay_and_analyze(payload)

    assert result["status"] == "pass"
    assert result["component_count"] == 10
    assert result["crossing_counts"] == {
        "total_crossings": 93,
        "missing_explicit_signs_in_input": 93,
        "explicit_sign_mismatches_with_inferred": 0,
    }
    assert result["checks"]["cap_consistent_orientation_solved"] is True
    assert result["checks"]["intercomponent_sums_even"] is True
    assert result["checks"]["determinant_abs_1"] is True
    assert result["checks"]["signature_matches_expected"] is True
    assert result["determinant"] == -1
    assert result["signature"] == -8


def test_k3_e2_draft_link_sanity_matches_unimodular_signature_target():
    payload = json.loads(
        Path("experiments/inputs/gompf-stipsicz/figure815-k3-e2-morse-draft-v1.json").read_text()
    )

    result = replay_and_analyze(payload, expected_component_count=22, expected_signature=-16)

    assert result["status"] == "pass"
    assert result["component_count"] == 22
    assert result["checks"]["determinant_abs_1"] is True
    assert result["checks"]["signature_matches_expected"] is True
    assert result["determinant"] == -1
    assert result["signature"] == -16
