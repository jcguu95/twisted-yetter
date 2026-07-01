import json
from pathlib import Path


ARTIFACT = Path("experiments/results/mtc-candidates/su3-3-multiplicity-stress-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_su3_3_multiplicity_stress_records_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su3-3-multiplicity-stress.v1"
    assert exact["category_id"] == "SU(3)_3"
    assert "multiplicity-nonfree" in exact["claim_level"]
    assert "arbitrary SU(3)_3 link polynomial" in exact["not_scope"]


def test_su3_3_category_data_records_z3_targets_and_multiplicity() -> None:
    exact = _exact_output()
    data = exact["category_data"]

    assert len(data["simple_labels"]) == 10
    assert data["universal_group"]["name"] == "Z/3"
    assert data["universal_group"]["degree_formula"] == "deg(a,b)=a+2b mod 3"
    assert data["simple_current_targets"] == {"0": "(0,0)", "1": "(3,0)", "2": "(0,3)"}
    assert data["omega_projector_targets"] == {"0": "(0,0)", "1": "(0,3)", "2": "(3,0)"}

    witness = exact["modular_controls"]["multiplicity_witness"]
    assert witness["full_product"] == {
        "(0,0)": 1,
        "(0,3)": 1,
        "(1,1)": 2,
        "(3,0)": 1,
    }
    assert witness["multiplicity"] == 2


def test_su3_3_modular_and_associativity_controls_pass() -> None:
    exact = _exact_output()
    controls = exact["modular_controls"]

    assert controls["status"] == "pass"
    assert controls["associativity_triple_count"] == 1000
    assert {control["status"] for control in controls["controls"]} == {"pass"}
    assert {validation["status"] for validation in exact["validations"]} == {"pass"}


def test_su3_3_meridian_slide_coefficients_cover_all_previous_scenarios() -> None:
    exact = _exact_output()
    controls = exact["meridian_slide_coefficient_controls"]

    assert controls["status"] == "pass"
    assert controls["scenario_count"] == 7
    assert controls["coefficient_check_count"] == 11250
    assert controls["failure_count"] == 0

    for sample in controls["sample_passes"]:
        before = sample["omega_labels_before"]
        framings = sample["scenario"]["slide_framings"]
        after = sample["omega_labels_after"]
        expected = (before[0] - sum(f * b for f, b in zip(framings, before[1:]))) % 3
        assert after[0] == expected
        assert after[1:] == before[1:]
        assert sample["difference"]["display"] == "0"


def test_su3_3_nontrivial_over_nontrivial_coefficients_use_multiplicities() -> None:
    exact = _exact_output()
    controls = exact["nontrivial_over_nontrivial_coefficient_controls"]

    assert controls["status"] == "pass"
    assert controls["coefficient_check_count"] == 900
    assert controls["failure_count"] == 0
    assert controls["formula"]["omega_label_transform"] == "a,b -> a+b mod 3, b"
    assert any(
        sample["left_fixed_label"] == "(1,1)" and sample["right_output_label"] == "(1,1)"
        for sample in controls["sample_passes"]
    )
