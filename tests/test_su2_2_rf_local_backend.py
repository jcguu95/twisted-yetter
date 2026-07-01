import json
from pathlib import Path


ARTIFACT = Path("experiments/results/local-piece/su2-2-rf-local-backend-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_rf_backend_records_b1_prime_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2_2-rf-local-backend.v1"
    assert exact["category_id"] == "SU(2)_2"
    assert exact["claim_level"] == (
        "B1-prime explicit R/F backend / fixed all-sigma braid closures"
    )
    assert "explicit R/F fusion-path matrices" in exact["scope"]
    assert "Omega expansion" in exact["not_scope"]
    assert "mixed simple labels" in exact["not_scope"]
    assert exact["example_count"] == 7
    assert exact["move_regression_count"] == 4


def test_rf_backend_calibrates_r_and_f_symbols() -> None:
    exact = _exact_output()
    convention = exact["convention"]
    controls = exact["rf_controls"]

    assert convention["r_sigma_sigma"]["0"]["display"] == "zeta16^2"
    assert convention["r_sigma_sigma"]["2"]["display"] == "-zeta16^6"
    assert convention["theta_sigma"]["display"] == "zeta16^3"
    assert {control["status"] for control in controls} == {"pass"}
    assert {control["name"] for control in controls} == {
        "f_matrix_is_involutive",
        "two_strand_sigma_unknot_calibration",
        "two_strand_sigma_hopf_calibration",
        "two_strand_sigma_trefoil_calibration",
        "b3_braid_relation",
    }


def test_rf_backend_examples_match_oracle_fixed_sigma_values() -> None:
    exact = _exact_output()
    examples = {item["case_id"]: item for item in exact["examples"]}

    assert set(examples) == {
        "sigma-unknot-one-strand",
        "sigma-unlink-two-strand-identity",
        "sigma-unknot-two-strand-sigma1",
        "sigma-hopf",
        "sigma-right-trefoil",
        "sigma-figure-eight",
        "sigma-figure-eight-plus-one-framed",
    }
    assert {item["status"] for item in examples.values()} == {"pass"}
    for item in examples.values():
        assert item["rf_value"] == item["oracle_fixed_sigma_value"]
        assert item["difference"]["display"] == "0"

    assert examples["sigma-hopf"]["rf_value"]["display"] == "0"
    assert examples["sigma-right-trefoil"]["rf_value"]["display"] == "zeta16^6 - zeta16^2"
    assert examples["sigma-figure-eight"]["rf_value"]["display"] == "zeta16^6 - zeta16^2"


def test_rf_backend_move_regressions_are_local_matrix_equalities() -> None:
    exact = _exact_output()
    regressions = exact["move_regressions"]

    assert {item["status"] for item in regressions} == {"pass"}
    assert {item["name"] for item in regressions} == {
        "rf-r-r-inverse-cancellation",
        "rf-trefoil-positive-markov",
        "rf-trefoil-negative-markov",
        "rf-figure-eight-conjugation",
    }
    for item in regressions:
        assert item["rf_difference"]["display"] == "0"
        assert item["oracle_difference"]["display"] == "0"
        assert item["left"]["rf_value"] == item["left"]["oracle_value"]
        assert item["right"]["rf_value"] == item["right"]["oracle_value"]


def test_rf_backend_artifact_is_float_free() -> None:
    payload = json.loads(ARTIFACT.read_text())
    _assert_no_float(payload)


def _assert_no_float(value: object) -> None:
    if isinstance(value, float):
        raise AssertionError(f"float found in exact payload: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_float(item)
    if isinstance(value, list):
        for item in value:
            _assert_no_float(item)
