import json
from fractions import Fraction
from pathlib import Path


ARTIFACT = Path("experiments/results/mtc-candidates/su2-6-modular-supported-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def _negated_coefficients(cyclotomic: dict[str, object]) -> list[str]:
    return [str(-Fraction(coefficient)) for coefficient in cyclotomic["coefficients"]]


def test_su2_6_modular_supported_artifact_records_scope() -> None:
    exact = _exact_output()

    assert exact["category_id"] == "SU(2)_6"
    assert "restricted supported evaluator" in exact["claim_level"]
    assert "arbitrary colored link evaluator" in exact["not_scope"]
    assert "F/R-symbol traces" in exact["not_scope"]


def test_su2_6_modular_data_controls_all_pass() -> None:
    exact = _exact_output()
    controls = exact["modular_data_controls"]

    assert [control["name"] for control in controls] == [
        "s_matrix_symmetric",
        "s_square_is_identity",
        "hopf_row_zero_is_dimension",
        "fusion_dimension_algebra",
        "universal_degree_respects_fusion",
        "omega_coefficients_match_degree_characters",
        "simple_current_character_matches_degree",
        "omega_hopf_projector_identity",
        "omega_hopf_pair_closed_form",
    ]
    assert {control["status"] for control in controls} == {"pass"}


def test_su2_6_records_z2_universal_group_and_omega_coefficients() -> None:
    exact = _exact_output()
    data = exact["modular_data"]

    assert data["simple_labels"] == ["0", "1", "2", "3", "4", "5", "6"]
    assert data["universal_group"]["name"] == "Z/2"
    assert data["universal_group"]["degrees"] == {
        "0": 0,
        "1": 1,
        "2": 0,
        "3": 1,
        "4": 0,
        "5": 1,
        "6": 0,
    }

    omega_zero = data["omega_coefficients"]["0"]
    omega_one = data["omega_coefficients"]["1"]
    dimensions = data["quantum_dimensions"]
    assert omega_zero["0"]["display"] == dimensions["0"]["display"]
    assert omega_zero["1"]["display"] == dimensions["1"]["display"]
    assert omega_one["0"]["display"] == dimensions["0"]["display"]
    assert omega_one["1"]["coefficients"] == _negated_coefficients(dimensions["1"])


def test_su2_6_supported_link_class_is_explicitly_narrow() -> None:
    exact = _exact_output()
    supported = exact["supported_link_class"]

    assert supported["supported_diagram_schema"] == "split_union_of_supported_blocks"
    assert [block["kind"] for block in supported["supported_blocks"]] == [
        "framed_unknot",
        "positive_hopf_pair",
    ]
    rejected = supported["explicitly_rejected"]
    assert "arbitrary linking matrix" in rejected
    assert "trefoil or other nontrivial knot component" in rejected
    assert "Hopf-star / one component encircling multiple nontrivial components" in rejected
    assert "fusion channels" in supported["reason_for_rejecting_hopf_star"]


def test_su2_6_supported_evaluator_controls_all_pass() -> None:
    exact = _exact_output()
    controls = exact["supported_evaluator_controls"]

    assert controls["status"] == "pass"
    assert controls["control_count"] == 4
    assert {validation["status"] for validation in controls["validations"]} == {"pass"}
    assert [control["name"] for control in controls["controls"]] == [
        "single-framed-unknot-plus-one",
        "split-two-framed-unlinks",
        "positive-hopf-zero-framed",
        "split-hopf-plus-unknot",
    ]
    assert all(control["status"] == "pass" for control in controls["controls"])
