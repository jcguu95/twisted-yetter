import json
from pathlib import Path

import pytest

from twisted_yetter.link_diagram import Component, Crossing, LinkDiagram, StrandRef, hopf_link
from twisted_yetter.su2_link_evaluator import (
    EVALUATOR_CLAIM_LEVEL,
    FRAMING_TWIST_CONVENTION,
    SU2_LINK_EVALUATOR_SCHEMA,
    evaluate_su2_level2_link,
    load_and_evaluate_su2_level2_link,
    stable_evaluator_json,
)
from twisted_yetter.su2_level2 import SQRT2, QuadraticSurd, RootOfUnityPower


TOY_FIXTURE_DIR = Path("experiments/inputs/toy-diagrams")
CORE_ARTIFACT = Path("experiments/results/link-evaluator/su2-level2-core.json")


def test_empty_link_uses_unified_evaluator_entry_point() -> None:
    result = load_and_evaluate_su2_level2_link(TOY_FIXTURE_DIR / "s4-empty.json", {})

    assert result["schema"] == SU2_LINK_EVALUATOR_SCHEMA
    assert result["status"] == "pass"
    assert result["supported_kind"] == "empty"
    assert result["claim"] == EVALUATOR_CLAIM_LEVEL
    assert result["value"] == {
        "kind": "coefficient_times_twist",
        "coefficient": QuadraticSurd(1).to_jsonable(),
        "twist": RootOfUnityPower(16, 0).to_jsonable(),
    }


def test_framed_colored_unknot_records_twist_convention_and_value() -> None:
    result = load_and_evaluate_su2_level2_link(
        TOY_FIXTURE_DIR / "cp2-plus-one-framed-unknot.json",
        {"cp2_h": "2"},
    )

    assert result["status"] == "pass"
    assert result["supported_kind"] == "split_no_crossing"
    assert result["framing_twist_convention"] == FRAMING_TWIST_CONVENTION
    assert result["framing_twist_convention"]["formula"] == (
        "multiply by theta_label^framing for each component"
    )
    assert result["value"] == {
        "kind": "coefficient_times_twist",
        "coefficient": QuadraticSurd(1).to_jsonable(),
        "twist": RootOfUnityPower(16, 8).to_jsonable(),
    }
    assert result["evaluation_details"]["component_factors"] == [
        {
            "component_id": "cp2_h",
            "label": "2",
            "framing": 1,
            "quantum_dimension": QuadraticSurd(1).to_jsonable(),
            "twist_exponent_mod_16": 8,
        }
    ]


def test_split_unlink_is_multiplicative_through_evaluator() -> None:
    result = load_and_evaluate_su2_level2_link(
        TOY_FIXTURE_DIR / "unlink-two-component.json",
        {"u1": "1", "u2": "1"},
    )

    assert result["status"] == "pass"
    assert result["supported_kind"] == "split_no_crossing"
    assert result["value"] == {
        "kind": "coefficient_times_twist",
        "coefficient": QuadraticSurd(2).to_jsonable(),
        "twist": RootOfUnityPower(16, 0).to_jsonable(),
    }


def test_positive_hopf_crossing_control_uses_general_evaluator_path() -> None:
    result = evaluate_su2_level2_link(hopf_link(), {"h1": "1", "h2": "2"})

    assert result["status"] == "pass"
    assert result["supported_kind"] == "positive_hopf"
    assert result["value"] == {
        "kind": "coefficient_times_twist",
        "coefficient": (-SQRT2).to_jsonable(),
        "twist": RootOfUnityPower(16, 0).to_jsonable(),
    }
    assert result["evaluation_details"]["sanity"]["crossing_count"] == 2
    assert result["evaluation_details"]["sanity"]["linking_matrix"] == [[0, 1], [1, 0]]
    assert result["evaluation_details"]["formula"] == (
        "(S_ij / S_00) * product_i theta_label_i^framing_i"
    )


def test_unsupported_crossing_diagram_returns_structured_blocker() -> None:
    unsupported = LinkDiagram(
        "three-component-crossing-not-planar-evaluable",
        components=(Component("a", 0), Component("b", 0), Component("c", 0)),
        crossings=(
            Crossing("x1", 1, StrandRef("a", "a1"), StrandRef("b", "b1")),
            Crossing("x2", 1, StrandRef("a", "a2"), StrandRef("b", "b2")),
        ),
    )

    result = evaluate_su2_level2_link(
        unsupported,
        {"a": "0", "b": "1", "c": "2"},
    )

    assert result["status"] == "blocked"
    assert result["blocker"] == {
        "reason_id": "general-crossing-diagram-unsupported",
        "message": "Hopf controls require exactly two components",
        "required": (
            "positive Hopf-shaped crossing record or future planar adjacency "
            "plus F/R-symbol evaluator"
        ),
        "status": "blocked",
    }
    assert result["claim"]["restriction_reason"].startswith("LinkDiagram currently records")


def test_dotted_components_are_structured_blockers() -> None:
    diagram = LinkDiagram("dotted-unknot", components=(Component("d", 0, dotted=True),))

    result = evaluate_su2_level2_link(diagram, {"d": "0"})

    assert result["status"] == "blocked"
    assert result["blocker"]["reason_id"] == "dotted-components-unsupported"
    assert "dotted Kirby components" in result["blocker"]["message"]


def test_label_mapping_and_unknown_labels_are_rejected() -> None:
    diagram = hopf_link()

    with pytest.raises(ValueError, match="missing=\\['h2'\\]"):
        evaluate_su2_level2_link(diagram, {"h1": "0"})

    with pytest.raises(ValueError, match="extra=\\['x'\\]"):
        evaluate_su2_level2_link(diagram, {"h1": "0", "h2": "1", "x": "2"})

    with pytest.raises(ValueError, match="unknown SU\\(2\\)_2 simple label"):
        evaluate_su2_level2_link(diagram, {"h1": "bad", "h2": "0"})


def test_evaluator_json_is_stable_and_float_free() -> None:
    result = evaluate_su2_level2_link(hopf_link(), {"h1": "0", "h2": "1"})
    encoded = stable_evaluator_json(result)

    assert encoded == json.dumps(result, indent=2, sort_keys=True) + "\n"
    assert json.loads(encoded) == result
    assert_no_float(result)


def test_official_core_artifact_records_supported_and_blocked_cases() -> None:
    artifact = json.loads(CORE_ARTIFACT.read_text())
    exact_output = artifact["exact_output"]

    assert artifact["schema"] == "twisted-yetter.certificate.v1"
    assert artifact["status"] == "pass"
    assert exact_output["schema"] == SU2_LINK_EVALUATOR_SCHEMA
    assert exact_output["node_id"] == "n18b-su2-2-link-evaluator-core"
    assert exact_output["result_count"] == 6
    assert [result["status"] for result in exact_output["results"]] == [
        "pass",
        "pass",
        "pass",
        "pass",
        "pass",
        "blocked",
    ]
    assert exact_output["results"][3]["supported_kind"] == "positive_hopf"
    assert exact_output["results"][-1]["blocker"]["reason_id"] == (
        "general-crossing-diagram-unsupported"
    )
    assert "Kirby color" in exact_output["claim"]["not_scope"]
    assert_no_float(artifact)


def assert_no_float(value: object) -> None:
    if isinstance(value, float):
        raise AssertionError(f"float found in exact JSON payload: {value!r}")
    if isinstance(value, dict):
        for item in value.values():
            assert_no_float(item)
    if isinstance(value, list):
        for item in value:
            assert_no_float(item)
