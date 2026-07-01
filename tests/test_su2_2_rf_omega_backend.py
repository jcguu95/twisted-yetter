import json
from pathlib import Path


ARTIFACT = Path("experiments/results/local-piece/su2-2-rf-omega-backend-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_rf_omega_backend_records_b2_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2_2-rf-omega-backend.v1"
    assert exact["category_id"] == "SU(2)_2"
    assert exact["claim_level"] == (
        "B2 explicit R/F backend with Omega expansion / supported braid closures"
    )
    assert "Omega_0/Omega_1 expansion" in exact["scope"]
    assert "sigma sublinks needing more than three selected strands" in exact["not_scope"]
    assert exact["case_count"] == 6
    assert exact["move_regression_count"] == 4


def test_rf_omega_backend_fixed_label_checks_all_match_oracle() -> None:
    exact = _exact_output()

    for case in exact["evaluations"]:
        assert case["status"] == "pass"
        assert {item["status"] for item in case["fixed_label_checks"]} == {"pass"}
        for item in case["fixed_label_checks"]:
            assert item["rf_value"] == item["oracle_value"]
            assert item["difference"]["display"] == "0"


def test_rf_omega_backend_recovers_known_omega_values() -> None:
    exact = _exact_output()
    cases = {case["case_id"]: case for case in exact["evaluations"]}

    assert _omega_values(cases["omega-cp2"]) == {
        (0,): "2*zeta16^3",
        (1,): "-2*zeta16^3",
    }
    assert _omega_values(cases["omega-right-trefoil"]) == {
        (0,): "0",
        (1,): "4",
    }
    assert _omega_values(cases["omega-figure-eight"]) == {
        (0,): "0",
        (1,): "4",
    }
    assert _omega_values(cases["omega-positive-hopf"]) == {
        (0, 0): "4",
        (0, 1): "4",
        (1, 0): "4",
        (1, 1): "4",
    }


def test_rf_omega_backend_omega_checks_match_oracle() -> None:
    exact = _exact_output()

    for case in exact["evaluations"]:
        assert {item["status"] for item in case["omega_checks"]} == {"pass"}
        for item in case["omega_checks"]:
            assert item["rf_value"] == item["oracle_value"]
            assert item["difference"]["display"] == "0"


def test_rf_omega_backend_move_regressions_pass_for_omega_values() -> None:
    exact = _exact_output()
    regressions = exact["move_regressions"]

    assert {item["status"] for item in regressions} == {"pass"}
    assert {item["name"] for item in regressions} == {
        "omega-r-r-inverse-cancellation",
        "omega-trefoil-positive-markov",
        "omega-trefoil-negative-markov",
        "omega-figure-eight-conjugation",
    }
    for regression in regressions:
        assert {item["status"] for item in regression["comparisons"]} == {"pass"}
        for item in regression["comparisons"]:
            assert item["rf_difference"]["display"] == "0"
            assert item["oracle_difference"]["display"] == "0"
            assert item["left_rf_value"] == item["left_oracle_value"]
            assert item["right_rf_value"] == item["right_oracle_value"]


def test_rf_omega_backend_artifact_is_float_free() -> None:
    payload = json.loads(ARTIFACT.read_text())
    _assert_no_float(payload)


def _omega_values(case: dict[str, object]) -> dict[tuple[int, ...], str]:
    return {
        tuple(item["omega_labels"]): item["rf_value"]["display"]
        for item in case["omega_checks"]
    }


def _assert_no_float(value: object) -> None:
    if isinstance(value, float):
        raise AssertionError(f"float found in exact payload: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_float(item)
    if isinstance(value, list):
        for item in value:
            _assert_no_float(item)
