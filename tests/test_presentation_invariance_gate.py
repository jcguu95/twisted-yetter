import json
from pathlib import Path
from typing import Any

from twisted_yetter.artifacts import validate_certificate
from twisted_yetter.invariant import (
    UNSUPPORTED_NUMERIC_VALUE_REASON,
    compare_exact_outputs,
    evaluate_matrix_statistic,
)
from twisted_yetter.presentation_moves import PresentationPair, small_presentation_pairs


REPO_ROOT = Path(__file__).resolve().parents[1]
GATE_ARTIFACT = (
    REPO_ROOT / "experiments/results/presentation-gate/n50-presentation-invariance-gate.json"
)


def _gate_projection(output: dict[str, Any]) -> dict[str, Any]:
    sector = output["sector_amplitudes"][0]
    presentation = output["presentation"]
    return {
        "status": output["status"],
        "claim_level": output["claim_level"],
        "claim_boundary": output["claim_boundary"],
        "category": output["category"],
        "formula_convention_record": output["formula_convention_record"],
        "ordinary_path_selected": output["ordinary_path_selected"],
        "aggregation": {
            "mode": output["aggregation"]["mode"],
            "value_status": output["aggregation"]["value_status"],
            "unsupported_reason": output["aggregation"]["unsupported_reason"],
        },
        "presentation_invariants": {
            "size": presentation["size"],
            "rank": presentation["rank"],
            "determinant": presentation["determinant"],
            "signature_triple": presentation["signature_triple"],
            "signature": presentation["signature"],
            "parity": presentation["parity"],
        },
        "formal_sector_invariants": {
            "alpha_q_alpha_mod2": sector["alpha_q_alpha_mod2"],
            "value_status": sector["value_status"],
            "unsupported_reason": sector["unsupported_reason"],
        },
    }


def _pair_outputs(
    pair: PresentationPair, source_decoration: tuple[int, ...]
) -> tuple[dict[str, Any], dict[str, Any], tuple[int, ...]]:
    index = pair.source.decorations_mod2.index(source_decoration)
    target_decoration = pair.transformed_decorations_mod2()[index]
    source_output = evaluate_matrix_statistic(
        pair.source,
        source_decoration,
        claim_level="presentation-gate-input",
    )
    target_output = evaluate_matrix_statistic(
        pair.target,
        target_decoration,
        claim_level="presentation-gate-input",
    )
    return source_output, target_output, target_decoration


def test_pure_handle_slide_basis_change_projected_outputs_agree() -> None:
    for pair in small_presentation_pairs():
        pair.assert_valid()
        for source_decoration in pair.source.decorations_mod2:
            source_output, target_output, target_decoration = _pair_outputs(
                pair,
                source_decoration,
            )

            assert target_decoration in pair.target.decorations_mod2, pair.name
            assert _gate_projection(source_output) == _gate_projection(target_output), (
                pair.name,
                source_decoration,
                target_decoration,
            )


def test_same_manifold_toy_presentations_agree_after_recorded_transform() -> None:
    seen_forms = set()

    for pair in small_presentation_pairs():
        for source_decoration in pair.source.decorations_mod2:
            source_output, target_output, _target_decoration = _pair_outputs(
                pair,
                source_decoration,
            )
            source_projection = _gate_projection(source_output)
            target_projection = _gate_projection(target_output)

            assert source_projection == target_projection, pair.name
            seen_forms.add(
                (
                    pair.metadata["source_form"],
                    source_projection["presentation_invariants"]["signature"],
                    source_projection["presentation_invariants"]["determinant"],
                    source_projection["presentation_invariants"]["parity"],
                )
            )

    assert seen_forms == {
        ("S2xS2 hyperbolic", 0, -1, "even"),
        ("CP2#anti-CP2", 0, -1, "odd"),
        ("CP2#CP2", 2, 1, "odd"),
    }


def test_alpha_zero_remains_stable_under_every_recorded_basis_change() -> None:
    for pair in small_presentation_pairs():
        zero = tuple(0 for _ in range(pair.source.size))
        source_output = evaluate_matrix_statistic(
            pair.source,
            zero,
            claim_level="presentation-gate-input",
        )
        target_output = evaluate_matrix_statistic(
            pair.target,
            zero,
            claim_level="presentation-gate-input",
        )

        assert source_output["ordinary_path_selected"] is True, pair.name
        assert target_output["ordinary_path_selected"] is True, pair.name
        assert source_output["decoration_mod2"] == list(zero), pair.name
        assert target_output["decoration_mod2"] == list(zero), pair.name
        assert _gate_projection(source_output) == _gate_projection(target_output), pair.name


def test_raw_full_artifact_difference_is_classified_not_a_gate_failure() -> None:
    pair = next(pair for pair in small_presentation_pairs() if pair.name == "hyperbolic-shear")
    source_output, target_output, target_decoration = _pair_outputs(pair, (0, 1))

    raw_comparison = compare_exact_outputs(source_output, target_output)
    projected_comparison = compare_exact_outputs(
        _gate_projection(source_output),
        _gate_projection(target_output),
    )

    assert raw_comparison.equal is False
    assert projected_comparison.equal is True
    assert source_output["presentation"]["matrix"] == [[0, 1], [1, 0]]
    assert target_output["presentation"]["matrix"] == [[0, 1], [1, 2]]
    assert source_output["presentation"]["component_ids"] == ["a", "b"]
    assert target_output["presentation"]["component_ids"] == ["a", "a+b"]
    assert source_output["decoration_mod2"] == [0, 1]
    assert list(target_decoration) == [1, 1]
    assert (
        source_output["sector_amplitudes"][0]["unsupported_reason"]
        == UNSUPPORTED_NUMERIC_VALUE_REASON
    )
    assert (
        target_output["sector_amplitudes"][0]["unsupported_reason"]
        == UNSUPPORTED_NUMERIC_VALUE_REASON
    )


def test_n50_gate_certificate_records_pass_and_minimal_failure_examples() -> None:
    certificate = json.loads(GATE_ARTIFACT.read_text())

    validate_certificate(certificate)

    exact_output = certificate["exact_output"]
    assert certificate["status"] == "pass"
    assert exact_output["node_id"] == "n50-presentation-invariance-gate"
    assert exact_output["verdict"] == "pass"
    assert exact_output["route"] == "allow-n55-toy-closed-suite"
    assert exact_output["claim_boundary"] == (
        "presentation gate for experimental matrix-level formal outputs only; "
        "no theorem-level closed 4-manifold invariant is claimed"
    )
    assert exact_output["projection_policy"]["classification"] == (
        "compare basis-invariant formal fields after recorded decoration transform"
    )
    assert {case["pair_id"] for case in exact_output["pair_cases"]} == {
        "hyperbolic-shear",
        "odd-indefinite-swap",
        "odd-positive-shear",
    }
    assert all(case["projected_outputs_equal"] is True for case in exact_output["pair_cases"])
    assert all(case["alpha_zero_stable"] is True for case in exact_output["pair_cases"])

    failure_example = exact_output["failure_examples"][0]
    assert failure_example["classification"] == "raw-presentation-payload-mismatch"
    assert failure_example["minimal_source_matrix"] == [[0, 1], [1, 0]]
    assert failure_example["minimal_target_matrix"] == [[0, 1], [1, 2]]
    assert failure_example["gate_projected_outputs_equal"] is True
