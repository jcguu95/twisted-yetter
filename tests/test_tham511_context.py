import json
from pathlib import Path

from twisted_yetter.yasui_figure2_cp2 import (
    EXPECTED_RELATIONS,
    analyze_crossing_table,
    load_crossing_table,
    relation_vector,
    tham511_context,
)


INPUT = Path("experiments/inputs/yasui/figure2-cp2-a1-crossing-table.json")
CONTEXT_ARTIFACT = Path("experiments/results/yasui/figure2-cp2-a1-tham511-context-v1.json")
COMPARISON_ARTIFACT = Path(
    "experiments/results/yasui/figure2-cp2-a1-su2-2-tham511-comparison-v1.json"
)


def test_tham511_context_records_radical_relations_and_h2_quotient() -> None:
    payload = load_crossing_table(INPUT)
    analysis = analyze_crossing_table(payload)
    context = tham511_context(payload, analysis)

    assert context["status"] == "WORKING_HYPOTHESIS_NOT_THEOREM"
    assert context["source_handle_counts"] == {"0": 1, "1": 0, "2": 3, "3": 2, "4": 1}
    assert context["tham511_dual_upside_down_handle_counts"] == {
        "0": 1,
        "1": 2,
        "2": 3,
        "3": 0,
        "4": 1,
    }
    assert context["dual_upside_down_interpretation"]["original_three_handles"] == (
        "interpreted as Tham 5.11 one-handle maps"
    )
    assert context["dual_upside_down_interpretation"]["special_dotted_projector_status"] == (
        "not present in this Yasui Figure 2 input; no cut-and-vacuum "
        "projection rule is applied"
    )
    assert all(check["is_in_radical"] for check in context["radical_relation_checks"])
    assert context["dual_d2_rank"] == 2
    assert context["h2_kernel"]["rank"] == 1
    assert context["h2_kernel"]["component_pullback_to_h"] == {
        "A": 2,
        "B": 1,
        "C": 2,
    }
    assert [
        relation_vector(relation, ("A", "B", "C"))
        for relation in EXPECTED_RELATIONS
    ] == [[1, -2, 0], [0, -2, 1]]


def test_tham511_context_allows_only_z2_assignments_descending_from_h() -> None:
    context = tham511_context(
        load_crossing_table(INPUT),
        analyze_crossing_table(load_crossing_table(INPUT)),
    )

    assert context["legal_character_assignments"]["assignments"] == [
        {
            "h_label": 0,
            "component_order": ["A", "B", "C"],
            "component_omega_labels": [0, 0, 0],
            "component_omega_labels_by_id": {"A": 0, "B": 0, "C": 0},
        },
        {
            "h_label": 1,
            "component_order": ["A", "B", "C"],
            "component_omega_labels": [0, 1, 0],
            "component_omega_labels_by_id": {"A": 0, "B": 1, "C": 0},
        },
    ]


def test_tham511_context_artifact_regression() -> None:
    context = json.loads(CONTEXT_ARTIFACT.read_text())

    assert context["schema"] == "twisted-yetter.tham511-handle-context.v1"
    assert context["status"] == "WORKING_HYPOTHESIS_NOT_THEOREM"
    assert context["mathematical_status"] == "WORKING_HYPOTHESIS_NOT_THEOREM"
    assert context["normalization_working_hypothesis"]["total_factor"] == (
        "GLOBAL_DIMENSION^-2"
    )
    assert context["normalization_working_hypothesis"]["one_handle_factor"] == (
        "GLOBAL_DIMENSION^-1 per dual Tham 5.11 one-handle"
    )


def test_sage_comparison_artifact_if_present() -> None:
    if not COMPARISON_ARTIFACT.exists():
        return

    comparison = json.loads(COMPARISON_ARTIFACT.read_text())
    assert comparison["schema"] == "twisted-yetter.yasui-figure2-cp2-a1-su2-2-tham511.v1"
    if comparison["status"] == "pass":
        assert all(row["normalized_matches_standard"] for row in comparison["rows"])
    elif comparison["status"] == "needs-review":
        assert comparison["status"] == "needs-review"
        assert comparison["halt_downstream_twisted_work"] is True
        assert "review PD-to-braid conversion" in comparison["comparison_interpretation"]
        assert comparison["normalization_working_hypothesis"][
            "special_dotted_projector_status"
        ].startswith("not present")
    else:
        assert comparison["status"] == "blocked"
        assert comparison["halt_downstream_twisted_work"] is True
        assert comparison["blocker"]["kind"] == "sage-link-braid-conversion-timeout"
        assert comparison["blocker"]["interpretation"].startswith(
            "No corrected source-PD RT value was produced"
        )
