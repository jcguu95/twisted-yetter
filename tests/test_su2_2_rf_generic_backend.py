import json
from pathlib import Path


ARTIFACT = Path("experiments/results/local-piece/su2-2-rf-generic-backend-v1.json")


def _exact_output() -> dict[str, object]:
    payload = json.loads(ARTIFACT.read_text())
    assert payload["status"] == "pass"
    exact = payload["exact_output"]
    assert exact["status"] == "pass"
    return exact


def test_rf_generic_backend_records_b3_scope() -> None:
    exact = _exact_output()

    assert exact["schema"] == "twisted-yetter.su2_2-rf-generic-backend.v1"
    assert exact["category_id"] == "SU(2)_2"
    assert exact["claim_level"] == (
        "B3 generic fusion-path backend / sigma sublinks plus Omega expansion"
    )
    assert "arbitrary-length all-sigma" in exact["scope"]
    assert "no hard-coded n<=3 selected-strand cap" in exact["backend"]["sigma_backend"]
    assert "full mixed-label F/R generator matrices" in exact["not_scope"]
    assert exact["case_count"] == 5
    assert exact["move_regression_count"] == 4
    assert exact["max_sigma_selected_strands_checked"] == 5


def test_rf_generic_backend_fusion_path_and_braid_relation_controls_pass() -> None:
    exact = _exact_output()
    path_controls = exact["fusion_path_controls"]
    relation_controls = exact["braid_relation_controls"]

    assert {item["status"] for item in path_controls} == {"pass"}
    assert {item["status"] for item in relation_controls} == {"pass"}
    assert len(relation_controls) == 7

    counts_by_n = {
        item["n_strands"]: item["actual_counts"]
        for item in path_controls
        if item["name"].startswith("all_sigma_fusion_path_counts")
    }
    assert counts_by_n[4] == {"0": 2, "2": 2}
    assert counts_by_n[5] == {"1": 4}
    assert counts_by_n[6] == {"0": 4, "2": 4}


def test_rf_generic_backend_fixed_label_checks_match_oracle() -> None:
    exact = _exact_output()

    high_pressure_checks = []
    for case in exact["evaluations"]:
        assert case["status"] == "pass"
        assert {item["status"] for item in case["fixed_label_checks"]} == {"pass"}
        for item in case["fixed_label_checks"]:
            assert item["rf_value"] == item["oracle_value"]
            assert item["difference"]["display"] == "0"
            if item["sigma_selected_strand_count"] > 3:
                high_pressure_checks.append((case["case_id"], tuple(item["labels"])))

    assert ("generic-mixed-four-sigma-plus-psi", (1, 1, 2)) in high_pressure_checks
    assert ("generic-sigma-five-strand-one-component", (1,)) in high_pressure_checks


def test_rf_generic_backend_records_known_pressure_values() -> None:
    exact = _exact_output()
    cases = {case["case_id"]: case for case in exact["evaluations"]}

    assert _fixed_values(cases["generic-sigma-four-strand-identity"])[(1, 1, 1, 1)] == "4"
    assert _fixed_values(cases["generic-sigma-four-strand-two-component"])[(1, 1)] == "-2"
    assert _fixed_values(cases["generic-mixed-four-sigma-plus-psi"])[(1, 1, 2)] == "2"
    assert _fixed_values(cases["generic-sigma-five-strand-one-component"])[(1,)] == (
        "-zeta16^6 + zeta16^2"
    )

    assert _omega_values(cases["generic-sigma-five-strand-one-component"]) == {
        (0,): "4",
        (1,): "0",
    }
    assert _omega_values(cases["generic-sigma-four-strand-two-component"]) == {
        (0, 0): "8",
        (0, 1): "8",
        (1, 0): "8",
        (1, 1): "-8",
    }


def test_rf_generic_backend_omega_checks_and_moves_match_oracle() -> None:
    exact = _exact_output()

    for case in exact["evaluations"]:
        assert {item["status"] for item in case["omega_checks"]} == {"pass"}
        for item in case["omega_checks"]:
            assert item["rf_value"] == item["oracle_value"]
            assert item["difference"]["display"] == "0"

    assert {item["status"] for item in exact["move_regressions"]} == {"pass"}
    assert {item["name"] for item in exact["move_regressions"]} == {
        "generic-r-r-inverse-cancellation-middle-strands",
        "generic-four-strand-positive-markov",
        "generic-four-strand-negative-markov",
        "generic-four-strand-conjugation",
    }
    for regression in exact["move_regressions"]:
        assert {item["status"] for item in regression["comparisons"]} == {"pass"}
        for item in regression["comparisons"]:
            assert item["rf_difference"]["display"] == "0"
            assert item["oracle_difference"]["display"] == "0"
            assert item["left_rf_value"] == item["left_oracle_value"]
            assert item["right_rf_value"] == item["right_oracle_value"]


def test_rf_generic_backend_artifact_is_float_free() -> None:
    payload = json.loads(ARTIFACT.read_text())
    _assert_no_float(payload)


def _fixed_values(case: dict[str, object]) -> dict[tuple[int, ...], str]:
    return {
        tuple(item["labels"]): item["rf_value"]["display"]
        for item in case["fixed_label_checks"]
    }


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
