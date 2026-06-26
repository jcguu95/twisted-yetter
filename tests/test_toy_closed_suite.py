import json
from pathlib import Path
from typing import Any

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.invariant import (
    UNSUPPORTED_NUMERIC_VALUE_REASON,
    compare_exact_outputs,
    decoration_aggregation,
    evaluate_matrix_statistic,
)
from twisted_yetter.linking_matrix import (
    KirbyMatrixPresentation,
    anti_cp2,
    cp2,
    cp2_sum_anti_cp2,
    cp2_sum_cp2,
    s2x_s2,
    s4,
)


REPO_ROOT = Path(__file__).resolve().parents[1]
SUITE_ARTIFACT = REPO_ROOT / "experiments/results/toy-suite/n55-toy-closed-suite.json"

TOY_INPUTS = (
    ("S4", s4()),
    ("CP2", cp2()),
    ("anti-CP2", anti_cp2()),
    ("S2xS2", s2x_s2()),
    ("CP2#anti-CP2", cp2_sum_anti_cp2()),
    ("CP2#CP2", cp2_sum_cp2()),
)


def _formal_projection(output: dict[str, Any]) -> dict[str, Any]:
    sector = output["sector_amplitudes"][0]
    presentation = output["presentation"]
    return {
        "status": output["status"],
        "claim_level": output["claim_level"],
        "ordinary_path_selected": output["ordinary_path_selected"],
        "value_status": output["aggregation"]["value_status"],
        "unsupported_reason": output["aggregation"]["unsupported_reason"],
        "presentation_invariants": {
            "size": presentation["size"],
            "rank": presentation["rank"],
            "determinant": presentation["determinant"],
            "signature_triple": presentation["signature_triple"],
            "signature": presentation["signature"],
            "parity": presentation["parity"],
        },
        "formal_decoration_invariants": {
            "theta_component_count": sector["theta_component_count"],
            "alpha_q_alpha_mod2": sector["alpha_q_alpha_mod2"],
            "value_status": sector["value_status"],
        },
    }


def _assert_no_float(value: Any) -> None:
    if isinstance(value, float):
        raise AssertionError(f"unexpected float value: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            _assert_no_float(item)
    elif isinstance(value, list | tuple):
        for item in value:
            _assert_no_float(item)


def _output(
    presentation: KirbyMatrixPresentation,
    decoration: tuple[int, ...],
) -> dict[str, Any]:
    return evaluate_matrix_statistic(
        presentation,
        decoration,
        claim_level="experimental-matrix-statistic",
    )


def test_all_n55_toy_suite_outputs_are_exact_and_formal() -> None:
    for name, presentation in TOY_INPUTS:
        aggregation = decoration_aggregation(
            presentation,
            claim_level="experimental-matrix-statistic",
        )

        _assert_no_float(aggregation)

        assert aggregation["mode"] == "decoration-aggregation", name
        assert aggregation["ordering"] == "lexicographic-mod2-vectors", name
        assert len(aggregation["decorations"]) == 2**presentation.size, name

        for output in aggregation["decorations"]:
            assert output["status"] == "inconclusive", name
            assert output["claim_boundary"] == (
                "experimental matrix-level statistic; not a closed 4-manifold invariant"
            )
            assert output["aggregation"]["value_status"] == "inconclusive", name
            assert output["aggregation"]["unsupported_reason"] == (
                UNSUPPORTED_NUMERIC_VALUE_REASON
            )
            assert output["sector_amplitudes"][0]["value_status"] == "inconclusive", name
            assert output["sector_amplitudes"][0]["unsupported_reason"] == (
                UNSUPPORTED_NUMERIC_VALUE_REASON
            )


def test_trivial_and_nontrivial_decorations_are_visible_in_schema() -> None:
    for name, presentation in TOY_INPUTS:
        decorations = decoration_aggregation(
            presentation,
            claim_level="experimental-matrix-statistic",
        )["decorations"]

        assert decorations[0]["decoration_mod2"] == [0 for _ in range(presentation.size)]
        assert decorations[0]["ordinary_path_selected"] is True
        assert decorations[0]["sector_amplitudes"][0]["theta_component_count"] == 0
        assert all(
            color["color"] == "omega"
            for color in decorations[0]["sector_amplitudes"][0]["component_colors"]
        )

        if presentation.size == 0:
            assert len(decorations) == 1, name
            continue

        nontrivial = [item for item in decorations if any(item["decoration_mod2"])]
        assert nontrivial, name
        assert all(item["ordinary_path_selected"] is False for item in nontrivial), name
        assert all(
            item["sector_amplitudes"][0]["theta_component_count"] > 0
            for item in nontrivial
        ), name
        assert any(
            any(color["color"] == "theta" for color in item["sector_amplitudes"][0]["component_colors"])
            for item in nontrivial
        ), name


def test_formal_equalities_and_differences_are_classified_without_overclaiming() -> None:
    cp2_zero = _output(cp2(), (0,))
    anti_zero = _output(anti_cp2(), (0,))
    s2_a = _output(s2x_s2(), (0, 1))
    s2_b = _output(s2x_s2(), (1, 0))
    indefinite_a = _output(cp2_sum_anti_cp2(), (1, 0))
    indefinite_b = _output(cp2_sum_anti_cp2(), (0, 1))
    positive_axis = _output(cp2_sum_cp2(), (1, 0))
    positive_diagonal = _output(cp2_sum_cp2(), (1, 1))

    assert compare_exact_outputs(cp2_zero, anti_zero).equal is False
    assert compare_exact_outputs(_formal_projection(s2_a), _formal_projection(s2_b)).equal is True
    assert (
        compare_exact_outputs(
            _formal_projection(indefinite_a),
            _formal_projection(indefinite_b),
        ).equal
        is True
    )
    assert (
        compare_exact_outputs(
            _formal_projection(positive_axis),
            _formal_projection(positive_diagonal),
        ).equal
        is False
    )

    classifications = {
        "CP2-vs-anti-CP2-alpha0": (
            "recorded-presentation-metadata-difference; numerical value unsupported"
        ),
        "S2xS2-axis-decorations": (
            "formal-projection-equality; not an unmarked closed invariant claim"
        ),
        "CP2#anti-CP2-axis-decorations": (
            "formal-projection-equality; mod-2 alpha_q_alpha sees both axes equally"
        ),
        "CP2#CP2-axis-vs-diagonal": (
            "formal-projection-difference; experimental matrix-level signal only"
        ),
    }
    assert all("numerical invariant" not in value for value in classifications.values())
    assert all("exotic" not in value for value in classifications.values())


def test_n55_toy_suite_certificate_records_pass_and_inconclusive_boundary() -> None:
    certificate = json.loads(SUITE_ARTIFACT.read_text())

    validate_certificate(certificate)

    exact_output = certificate["exact_output"]
    assert certificate["status"] == "pass"
    assert exact_output["node_id"] == "n55-toy-closed-suite"
    assert exact_output["verdict"] == "pass"
    assert exact_output["route"] == "do-not-route-to-n60"
    assert exact_output["value_status"] == "inconclusive"
    assert exact_output["claim_boundary"] == (
        "exact formal toy-suite outputs only; no numerical twisted Yetter "
        "closed 4-manifold invariant is claimed"
    )
    assert {case["case_id"] for case in exact_output["toy_cases"]} == {
        "S4",
        "CP2",
        "anti-CP2",
        "S2xS2",
        "CP2#anti-CP2",
        "CP2#CP2",
    }
    assert all(case["all_outputs_exact"] is True for case in exact_output["toy_cases"])
    assert all(case["value_status"] == "inconclusive" for case in exact_output["toy_cases"])

    nonempty_cases = [case for case in exact_output["toy_cases"] if case["rank"] > 0]
    assert all(case["trivial_decoration_visible"] is True for case in nonempty_cases)
    assert all(case["nontrivial_decorations_visible"] is True for case in nonempty_cases)

    assert {item["classification"] for item in exact_output["comparisons"]} == {
        "recorded-presentation-metadata-difference; numerical value unsupported",
        "formal-projection-equality; not an unmarked closed invariant claim",
        "formal-projection-equality; mod-2 alpha_q_alpha sees both axes equally",
        "formal-projection-difference; experimental matrix-level signal only",
    }
