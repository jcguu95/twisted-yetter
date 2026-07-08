import json
from pathlib import Path

from twisted_yetter.yasui_figure2_cp2 import (
    EXPECTED_MATRIX,
    EXPECTED_SIGNATURE,
    analyze_crossing_table,
    load_crossing_table,
    source_oriented_gauss_code,
)


INPUT = Path("experiments/inputs/yasui/figure2-cp2-a1-crossing-table.json")
SANITY_ARTIFACT = Path("experiments/results/yasui/figure2-cp2-a1-pd-sanity-v1.json")


def test_corrected_figure2_pd_bookkeeping_passes() -> None:
    payload = load_crossing_table(INPUT)
    analysis = analyze_crossing_table(payload)

    assert analysis["status"] == "pass"
    assert analysis["arc_occurrence_status"] == "pass"
    assert analysis["bad_arc_counts"] == []
    assert analysis["extra_arc_counts"] == []
    assert analysis["transition_errors"] == []
    assert analysis["sign_adjacency_rule_disagreements"] == []
    assert analysis["intercomponent_odd_sums"] == []


def test_corrected_figure2_linking_matrix_matches_cp2_with_two_three_handles() -> None:
    analysis = analyze_crossing_table(load_crossing_table(INPUT))

    assert analysis["pair_linking_numbers"] == {
        "A--B": 2,
        "A--C": 4,
        "B--C": 2,
    }
    assert analysis["visible_self_writhe_sums"] == {"A": 3}
    assert analysis["recorded_total_framings"] == {"A": 4, "B": 1, "C": 4}
    assert analysis["framing_corrections_from_visible_blackboard_writhe"] == {
        "A": 1,
        "B": 1,
        "C": 4,
    }
    assert analysis["framing_plus_intercomponent_linking_matrix"] == [
        list(row) for row in EXPECTED_MATRIX
    ]
    assert analysis["determinant"] == 0
    assert analysis["rank"] == 1
    assert analysis["nullity"] == 2
    assert analysis["signature_triple_positive_negative_zero"] == list(EXPECTED_SIGNATURE)
    assert analysis["signature"] == 1


def test_source_oriented_gauss_code_has_one_event_per_arc_transition() -> None:
    payload = load_crossing_table(INPUT)
    component_words, crossing_signs, records = source_oriented_gauss_code(payload)

    assert [len(word) for word in component_words] == [20, 10, 12]
    assert len(crossing_signs) == 21
    assert len(records) == 21
    assert sorted(abs(entry) for word in component_words for entry in word) == [
        crossing_index
        for crossing_index in range(1, 22)
        for _ in range(2)
    ]


def test_sanity_artifact_regression() -> None:
    payload = json.loads(SANITY_ARTIFACT.read_text())
    exact = payload["exact_output"]

    assert payload["schema"] == "twisted-yetter.certificate.v1"
    assert payload["status"] == "pass"
    assert exact["schema"] == "twisted-yetter.yasui-figure2-cp2-pd-sanity.v1"
    assert exact["status"] == "pass"
    assert exact["framing_plus_intercomponent_linking_matrix"] == [
        list(row) for row in EXPECTED_MATRIX
    ]
