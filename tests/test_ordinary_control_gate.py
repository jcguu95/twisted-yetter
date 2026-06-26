import json
from pathlib import Path

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.invariant import (
    NORMALIZATION_NAME,
    SIGNATURE_CORRECTION_NAME,
    compare_exact_outputs,
    evaluate_matrix_statistic,
)
from twisted_yetter.linking_matrix import anti_cp2, cp2, s2x_s2, s4


REPO_ROOT = Path(__file__).resolve().parents[1]
GATE_ARTIFACT = (
    REPO_ROOT / "experiments/results/ordinary-control/n40-ordinary-control-gate.json"
)

TOY_INPUTS = (
    ("S4", s4(), ()),
    ("CP2", cp2(), (0,)),
    ("anti-CP2", anti_cp2(), (0,)),
    ("S2xS2", s2x_s2(), (0, 0)),
)


def test_alpha_zero_ordinary_path_is_stable_on_all_n40_toys() -> None:
    convention_names = set()

    for name, presentation, alpha_zero in TOY_INPUTS:
        output = evaluate_matrix_statistic(
            presentation,
            alpha_zero,
            claim_level="ordinary-control-input",
        )

        assert output["status"] == "inconclusive", name
        assert output["claim_level"] == "ordinary-control-input", name
        assert output["ordinary_path_selected"] is True, name
        assert output["decoration_mod2"] == list(alpha_zero), name
        assert output["aggregation"]["value_status"] == "inconclusive", name

        sector = output["sector_amplitudes"][0]
        assert sector["decoration_mod2"] == list(alpha_zero), name
        assert sector["theta_component_count"] == 0, name
        assert sector["alpha_q_alpha_mod2"] == 0, name
        assert all(color["color"] == "omega" for color in sector["component_colors"]), name

        convention_record = output["formula_convention_record"]
        convention_names.add(
            (
                convention_record["normalization_name"],
                convention_record["signature_correction_name"],
            )
        )

        sanity_by_name = {check["name"]: check for check in output["sanity_checks"]}
        assert sanity_by_name["alpha_zero_ordinary_path_selection"] == {
            "name": "alpha_zero_ordinary_path_selection",
            "status": "pass",
            "ordinary_path_selected": True,
        }
        assert sanity_by_name["normalization_and_signature_correction_named_only"] == {
            "name": "normalization_and_signature_correction_named_only",
            "status": "pass",
            "normalization_name": NORMALIZATION_NAME,
            "signature_correction_name": SIGNATURE_CORRECTION_NAME,
        }

    assert convention_names == {(NORMALIZATION_NAME, SIGNATURE_CORRECTION_NAME)}


def test_alpha_zero_exact_outputs_are_repeatable_without_float_values() -> None:
    for name, presentation, alpha_zero in TOY_INPUTS:
        left = evaluate_matrix_statistic(
            presentation,
            alpha_zero,
            claim_level="ordinary-control-input",
        )
        right = evaluate_matrix_statistic(
            presentation,
            alpha_zero,
            claim_level="ordinary-control-input",
        )

        comparison = compare_exact_outputs(left, right)

        assert comparison.equal is True, name
        assert comparison.left_hash == comparison.right_hash, name


def test_orientation_reversal_behavior_is_recorded_but_not_numerically_claimed() -> None:
    positive = evaluate_matrix_statistic(cp2(), (0,), claim_level="ordinary-control-input")
    negative = evaluate_matrix_statistic(
        anti_cp2(),
        (0,),
        claim_level="ordinary-control-input",
    )

    comparison = compare_exact_outputs(positive, negative)

    assert comparison.equal is False
    assert positive["ordinary_path_selected"] is True
    assert negative["ordinary_path_selected"] is True
    assert positive["presentation"]["signature"] == 1
    assert negative["presentation"]["signature"] == -1
    assert positive["presentation"]["signature_triple"] == {
        "positive": 1,
        "negative": 0,
        "zero": 0,
    }
    assert negative["presentation"]["signature_triple"] == {
        "positive": 0,
        "negative": 1,
        "zero": 0,
    }
    assert positive["formula_convention_record"] == negative["formula_convention_record"]
    assert positive["aggregation"]["value_status"] == "inconclusive"
    assert negative["aggregation"]["value_status"] == "inconclusive"


def test_n40_gate_certificate_records_pass_and_classification() -> None:
    certificate = json.loads(GATE_ARTIFACT.read_text())

    validate_certificate(certificate)

    exact_output = certificate["exact_output"]
    assert certificate["status"] == "pass"
    assert exact_output["node_id"] == "n40-ordinary-control-gate"
    assert exact_output["verdict"] == "pass"
    assert exact_output["route"] == "allow-nontrivial-decoration-gates"
    assert exact_output["claim_boundary"] == (
        "alpha=0 ordinary formal path and metadata gate only; no numerical "
        "ordinary invariant value is claimed"
    )
    assert exact_output["normalization_mismatch"]["classification"] == "absent"
    assert exact_output["orientation_reversal_behavior"]["classification"] == (
        "recorded-signature-and-framing-sign-change; numerical ordinary value unsupported"
    )
    assert {case["case_id"] for case in exact_output["toy_cases"]} == {
        "S4",
        "CP2",
        "anti-CP2",
        "S2xS2",
    }
    assert all(case["alpha_zero_stable"] is True for case in exact_output["toy_cases"])
