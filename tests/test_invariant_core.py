import json

import pytest

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.invariant import (
    FORMULA_CONTRACT_REFERENCE,
    NORMALIZATION_NAME,
    SIGNATURE_CORRECTION_NAME,
    UNSUPPORTED_NUMERIC_VALUE_REASON,
    FormulaConventionRecord,
    UnsupportedFormulaFeature,
    compare_exact_outputs,
    decoration_aggregation,
    evaluate_matrix_statistic,
    invariant_certificate,
    numerical_invariant_value,
    sector_amplitudes,
)
from twisted_yetter.legacy_prose import legacy_prose_member_ref
from twisted_yetter.linking_matrix import KirbyMatrixPresentation, s2x_s2, s4
from twisted_yetter.su2_level2 import certificate_payload


def test_alpha_zero_selects_ordinary_formal_omega_path() -> None:
    output = evaluate_matrix_statistic(s2x_s2(), (0, 0))

    assert output["status"] == "inconclusive"
    assert output["claim_level"] == "experimental-matrix-statistic"
    assert output["ordinary_path_selected"] is True
    assert output["formula_convention_record"]["normalization_name"] == NORMALIZATION_NAME
    assert (
        output["formula_convention_record"]["signature_correction_name"]
        == SIGNATURE_CORRECTION_NAME
    )
    assert output["claim_boundary"].startswith("experimental matrix-level")

    sector = output["sector_amplitudes"][0]
    assert sector["sector_id"] == "alpha-00"
    assert sector["value_status"] == "inconclusive"
    assert sector["component_colors"] == [
        {"component_id": "s2_a", "color": "omega"},
        {"component_id": "s2_b", "color": "omega"},
    ]
    assert sector["unsupported_reason"] == UNSUPPORTED_NUMERIC_VALUE_REASON


def test_nonzero_decoration_sector_is_inspectable_without_numeric_value() -> None:
    presentation = KirbyMatrixPresentation(
        [[1, 1], [1, 0]],
        component_ids=["left", "right"],
    )

    sectors = sector_amplitudes(presentation, (1, 0))

    assert len(sectors) == 1
    assert sectors[0].sector_id == "alpha-10"
    assert sectors[0].component_colors == (("left", "theta"), ("right", "omega"))
    assert sectors[0].theta_component_count == 1
    assert sectors[0].alpha_q_alpha_mod2 == 1
    assert sectors[0].value_status == "inconclusive"


def test_decoration_aggregation_is_deterministic_and_lexicographic() -> None:
    aggregation = decoration_aggregation(s2x_s2())

    assert aggregation["mode"] == "decoration-aggregation"
    assert aggregation["ordering"] == "lexicographic-mod2-vectors"
    assert [
        item["decoration_mod2"] for item in aggregation["decorations"]
    ] == [[0, 0], [0, 1], [1, 0], [1, 1]]

    repeat = decoration_aggregation(s2x_s2())
    assert json.dumps(aggregation, sort_keys=True) == json.dumps(repeat, sort_keys=True)


def test_decoration_aggregation_deduplicates_and_sorts_inputs() -> None:
    aggregation = decoration_aggregation(s2x_s2(), [(1, 1), (0, 1), (1, 1), (0, 0)])

    assert [
        item["decoration_mod2"] for item in aggregation["decorations"]
    ] == [[0, 0], [0, 1], [1, 1]]


def test_exact_comparison_uses_canonical_json_and_rejects_floats() -> None:
    left = evaluate_matrix_statistic(s4(), ())
    right = evaluate_matrix_statistic(s4(), ())

    comparison = compare_exact_outputs(left, right)

    assert comparison.equal is True
    assert comparison.left_hash == comparison.right_hash

    changed = evaluate_matrix_statistic(s2x_s2(), (1, 0))
    changed_comparison = compare_exact_outputs(left, changed)
    assert changed_comparison.equal is False
    assert changed_comparison.left_hash != changed_comparison.right_hash

    with pytest.raises(TypeError, match="floats"):
        compare_exact_outputs({"bad": 0.5}, {"bad": 0})


def test_invariant_certificate_uses_artifact_v1_and_exact_output() -> None:
    certificate = invariant_certificate(
        s2x_s2(),
        (1, 1),
        command="uv run python -m twisted_yetter.invariant",
        argv=["-m", "twisted_yetter.invariant"],
        git={"commit": "0" * 40, "dirty": False},
        tool_versions={"python": "3.11.0"},
        repo_root="/repo",
    )

    validate_certificate(certificate)

    assert certificate["schema"] == "twisted-yetter.certificate.v1"
    assert certificate["status"] == "inconclusive"
    assert certificate["exact_output"]["node_id"] == "n35-invariant-core"
    assert certificate["exact_output"]["decoration_mod2"] == [1, 1]


def test_unsupported_contract_features_raise_explicit_errors() -> None:
    with pytest.raises(UnsupportedFormulaFeature, match="claim level"):
        evaluate_matrix_statistic(s4(), (), claim_level="closed-4-manifold-invariant")

    altered_category = certificate_payload()
    altered_category["schema"] = "other"
    with pytest.raises(UnsupportedFormulaFeature, match="SU\\(2\\)_2"):
        evaluate_matrix_statistic(s4(), (), category_certificate=altered_category)

    with pytest.raises(UnsupportedFormulaFeature, match="convention record"):
        evaluate_matrix_statistic(
            s4(),
            (),
            formula_convention_record=FormulaConventionRecord(
                formula_contract=legacy_prose_member_ref(
                    "wiki/understandings/other.org"
                )
            ),
        )

    with pytest.raises(UnsupportedFormulaFeature, match="SOURCE NEEDED"):
        numerical_invariant_value(s4(), ())


def test_input_validation_stays_exact_and_mod2() -> None:
    output = evaluate_matrix_statistic(s2x_s2(), (3, -2))

    assert output["decoration_mod2"] == [1, 0]

    with pytest.raises(ValueError, match="length"):
        evaluate_matrix_statistic(s2x_s2(), (1,))

    with pytest.raises(TypeError, match="integers"):
        evaluate_matrix_statistic(s2x_s2(), (True, 0))


def test_output_records_formula_contract_and_matrix_sanity_checks() -> None:
    output = evaluate_matrix_statistic(s2x_s2(), (1, 1), claim_level="presentation-gate-input")

    assert output["formula_convention_record"]["formula_contract"] == FORMULA_CONTRACT_REFERENCE
    assert output["presentation"]["signature_triple"] == {
        "positive": 1,
        "negative": 1,
        "zero": 0,
    }
    assert output["presentation"]["determinant"] == -1
    assert output["presentation"]["parity"] == "even"
    assert [
        check["name"] for check in output["sanity_checks"]
    ] == [
        "input_matrix_symmetric_and_sized",
        "rank_determinant_parity_signature_exact",
        "alpha_zero_ordinary_path_selection",
        "basis_change_convention_recorded",
        "normalization_and_signature_correction_named_only",
        "decoration_vector_mod2",
    ]
