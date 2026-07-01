import json
from pathlib import Path


ARTIFACT = Path("experiments/results/sage-stress/su2-6-kirby-slide-stress-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_su2_6_kirby_slide_stress_records_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2-6-kirby-slide-stress.v1"
    assert exact["category_id"] == "SU(2)_6"
    assert "Kirby-slide evidence" in exact["claim_level"]
    assert "arbitrary multi-component colored link evaluator" in exact["not_scope"]
    assert exact["knot_count"] == 4
    assert exact["scenario_count"] == 5
    assert exact["comparison_count"] == 160


def test_su2_6_colored_jones_normalization_is_calibrated() -> None:
    exact = _exact_output()
    controls = exact["normalization_controls"]

    assert [control["name"] for control in controls] == [
        "sage_colored_jones_matches_su2_2_trefoil_calibration"
    ]
    assert controls[0]["status"] == "pass"
    assert controls[0]["actual_reduced_colored_jones"]["display"] == "-1"


def test_su2_6_knot_inputs_are_nontrivial_at_the_root() -> None:
    exact = _exact_output()
    controls = exact["nontriviality_controls"]

    assert [control["knot"]["name"] for control in controls] == [
        "right_trefoil",
        "left_trefoil",
        "figure_eight",
        "torus_2_5",
    ]
    assert {control["status"] for control in controls} == {"pass"}
    assert all(control["non_unit_labels"] for control in controls)


def test_su2_6_all_kirby_slide_comparisons_pass_exactly() -> None:
    exact = _exact_output()
    comparisons = exact["comparisons"]

    assert len(comparisons) == 160
    assert {comparison["status"] for comparison in comparisons} == {"pass"}
    assert {comparison["difference"]["display"] for comparison in comparisons} == {"0"}

    knots = {comparison["knot"]["name"] for comparison in comparisons}
    scenarios = {comparison["scenario"]["name"] for comparison in comparisons}
    assert knots == {"right_trefoil", "left_trefoil", "figure_eight", "torus_2_5"}
    assert scenarios == {
        "slide_over_plus_one_unknot",
        "slide_over_minus_one_unknot",
        "slide_over_two_plus_one_unlinks",
        "slide_over_plus_and_minus_unlinks",
        "slide_over_three_mixed_unlinks",
    }


def test_su2_6_slide_labels_transform_by_universal_group_addition() -> None:
    exact = _exact_output()

    for comparison in exact["comparisons"]:
        before = comparison["omega_labels_before"]
        after = comparison["omega_labels_after"]
        assert after[0] == sum(before) % 2
        assert after[1:] == before[1:]
