import json
from pathlib import Path


ARTIFACT = Path("experiments/results/sage-stress/su2-6-nontrivial-slide-stress-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_su2_6_nontrivial_slide_stress_records_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2-6-nontrivial-slide-stress.v1"
    assert exact["category_id"] == "SU(2)_6"
    assert "nontrivial-over-nontrivial Kirby-slide evidence" in exact["claim_level"]
    assert "arbitrary multi-component colored link evaluator" in exact["not_scope"]
    assert exact["knot_count"] == 3
    assert exact["framing_case_count"] == 5
    assert exact["unique_colored_jones_braid_count"] == 3
    assert exact["comparison_count"] == 180


def test_su2_6_nontrivial_slide_formula_is_recorded() -> None:
    exact = _exact_output()
    formula = exact["formula"]

    assert formula["before_fixed_labels"] == "RT_i(K,fK) * RT_j(L,fL)"
    assert formula["after_fixed_labels"] == "(RT_i(K,fK)/d_i) * sum_k N_ij^k RT_k(L,fL)"
    assert formula["omega_label_transform"] == "a,b -> a+b mod 2, b"


def test_su2_6_nontrivial_over_nontrivial_comparisons_pass_exactly() -> None:
    exact = _exact_output()
    comparisons = exact["comparisons"]

    assert len(comparisons) == 180
    assert {comparison["status"] for comparison in comparisons} == {"pass"}
    assert {comparison["difference"]["display"] for comparison in comparisons} == {"0"}

    slid = {comparison["knot_slid"]["name"] for comparison in comparisons}
    slid_over = {comparison["knot_slid_over"]["name"] for comparison in comparisons}
    assert slid == {"right_trefoil", "figure_eight", "torus_2_5"}
    assert slid_over == {"right_trefoil", "figure_eight", "torus_2_5"}
    assert any(
        comparison["knot_slid"]["name"] != comparison["knot_slid_over"]["name"]
        for comparison in comparisons
    )


def test_su2_6_nontrivial_slide_labels_transform_by_universal_group_addition() -> None:
    exact = _exact_output()

    for comparison in exact["comparisons"]:
        before = comparison["omega_labels_before"]
        after = comparison["omega_labels_after"]
        assert after == [sum(before) % 2, before[1]]
