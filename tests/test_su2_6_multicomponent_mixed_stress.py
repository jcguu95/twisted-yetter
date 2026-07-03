import json
from decimal import Decimal
from pathlib import Path


ARTIFACT = Path("experiments/results/sage-stress/su2-6-multicomponent-mixed-stress-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_su2_6_multicomponent_mixed_stress_records_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2-6-multicomponent-mixed-stress.v1"
    assert exact["category_id"] == "SU(2)_6"
    assert "multi-component mixed fixed-label" in exact["claim_level"]
    assert "independent colored-link oracle" in exact["not_scope"]
    assert "Yasui diagram admission" in exact["not_scope"]


def test_su2_6_multicomponent_mixed_stress_cases_pass() -> None:
    exact = _exact_output()
    cases = {case["case_id"]: case for case in exact["case_outputs"]}

    assert set(cases) == {
        "pure-commutator-borromean-like",
        "two-component-zero-linking-3braid",
    }
    assert {case["status"] for case in cases.values()} == {"pass"}
    assert {case["comparison_count"] for case in cases.values()} == {36}
    assert {len(case["sample_failures"]) for case in cases.values()} == {0}
    assert cases["pure-commutator-borromean-like"]["linking_matrix"] == [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0],
    ]
    assert cases["two-component-zero-linking-3braid"]["linking_matrix"] == [
        [0, 0],
        [0, 0],
    ]
    assert cases["pure-commutator-borromean-like"]["ordinary_jones_polynomial"] != "1"
    assert cases["two-component-zero-linking-3braid"]["ordinary_jones_polynomial"] != "1"


def test_su2_6_multicomponent_mixed_stress_is_numerically_tight() -> None:
    exact = _exact_output()

    assert Decimal(exact["max_abs_difference"]) < Decimal("1e-10")
    assert all(
        Decimal(case["max_abs_difference"]) < Decimal("1e-10")
        for case in exact["case_outputs"]
    )


def test_su2_6_multicomponent_mixed_stress_samples_component_transport() -> None:
    exact = _exact_output()

    sampled_moves = {
        row["move"]
        for case in exact["case_outputs"]
        for row in case["sample_rows"]
    }
    assert "pure-conjugation-A12" in sampled_moves
    assert "component-transport-conjugation-sigma1" in sampled_moves
    assert "positive-markov-stabilization" in sampled_moves
