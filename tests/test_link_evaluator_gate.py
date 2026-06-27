import json
from pathlib import Path

import pytest

from twisted_yetter.link_diagram import Component, Crossing, LinkDiagram, StrandRef, hopf_link
from twisted_yetter.link_evaluator_gate import (
    DEFAULT_GATE_FIXTURES,
    GATE_CLAIM_LEVEL,
    GATE_SCHEMA,
    evaluate_supported_control,
    run_default_gate,
    stable_gate_json,
)


def test_default_gate_runs_all_intended_toy_controls() -> None:
    certificate = run_default_gate()

    assert certificate["schema"] == GATE_SCHEMA
    assert certificate["status"] == "pass"
    assert certificate["node_id"] == "n18-colored-framed-link-evaluator-gate"
    assert certificate["fixture_count"] == 5
    assert certificate["claim"] == GATE_CLAIM_LEVEL
    assert certificate["claim"]["not_scope"].startswith("general colored framed link evaluator")

    results = certificate["results"]
    assert [result["fixture_path"] for result in results] == [
        "experiments/inputs/toy-diagrams/s4-empty.json",
        "experiments/inputs/toy-diagrams/cp2-plus-one-framed-unknot.json",
        "experiments/inputs/toy-diagrams/unlink-two-component.json",
        "experiments/inputs/toy-diagrams/hopf-link.json",
        "experiments/inputs/toy-diagrams/s2x-s2-hopf-zero-framed.json",
    ]
    assert [result["control_kind"] for result in results] == [
        "empty",
        "unknot",
        "unlink",
        "hopf",
        "hopf",
    ]
    assert [result["diagram_id"] for result in results] == [
        "s4-empty-kirby-diagram",
        "cp2-plus-one-framed-unknot",
        "unlink-2",
        "hopf-linking-1",
        "s2x-s2-hopf-zero-framed",
    ]


def test_gate_results_record_labels_expected_values_and_source_boundary() -> None:
    certificate = run_default_gate()
    by_kind = {result["fixture_path"]: result for result in certificate["results"]}

    empty = by_kind["experiments/inputs/toy-diagrams/s4-empty.json"]
    assert empty["labels_by_component"] == {}
    assert empty["expected_value"] == {
        "kind": "dimension_times_twist",
        "dimension": {
            "kind": "Q(sqrt2)",
            "rational": {"type": "integer", "value": "1"},
            "sqrt2": {"type": "integer", "value": "0"},
        },
        "twist": {
            "kind": "root_of_unity_power",
            "symbol": "zeta_16",
            "order": 16,
            "exponent": 0,
        },
    }

    framed_unknot = by_kind[
        "experiments/inputs/toy-diagrams/cp2-plus-one-framed-unknot.json"
    ]
    assert framed_unknot["labels_by_component"] == {"cp2_h": "2"}
    assert framed_unknot["expected_value"]["twist"]["exponent"] == 8
    assert framed_unknot["claim"]["claim_level"].startswith("SOURCE NEEDED")

    hopf = by_kind["experiments/inputs/toy-diagrams/hopf-link.json"]
    assert hopf["labels_by_component"] == {"h1": "1", "h2": "2"}
    assert hopf["expected_value"] == {
        "kind": "Q(sqrt2)",
        "rational": {"type": "integer", "value": "0"},
        "sqrt2": {"type": "integer", "value": "-1"},
    }
    assert "general crossing evaluator" in hopf["claim"]["not_scope"]


def test_gate_certificate_json_is_stable_and_deterministic() -> None:
    first = run_default_gate()
    second = run_default_gate()

    assert first == second
    assert stable_gate_json(first) == stable_gate_json(second)
    assert json.loads(stable_gate_json(first)) == first
    assert stable_gate_json(first) == json.dumps(first, indent=2, sort_keys=True)


def test_gate_fixture_manifest_is_not_glob_order_dependent() -> None:
    assert [entry.fixture_path.name for entry in DEFAULT_GATE_FIXTURES] == [
        "s4-empty.json",
        "cp2-plus-one-framed-unknot.json",
        "unlink-two-component.json",
        "hopf-link.json",
        "s2x-s2-hopf-zero-framed.json",
    ]


def test_gate_rejects_unsupported_general_crossing_diagrams() -> None:
    unsupported = LinkDiagram(
        "three-component-crossing-not-gate-supported",
        components=(Component("a", 0), Component("b", 0), Component("c", 0)),
        crossings=(
            Crossing("x1", 1, StrandRef("a", "a1"), StrandRef("b", "b1")),
            Crossing("x2", 1, StrandRef("a", "a2"), StrandRef("b", "b2")),
        ),
    )

    with pytest.raises(NotImplementedError, match="exactly two components"):
        evaluate_supported_control(
            unsupported,
            {"a": "0", "b": "1", "c": "2"},
            "hopf",
        )

    with pytest.raises(NotImplementedError, match="do not cover crossings"):
        evaluate_supported_control(
            hopf_link(),
            {"h1": "0", "h2": "0"},
            "unlink",
        )


def test_gate_can_run_from_explicit_repo_root() -> None:
    repo_root = Path(__file__).resolve().parents[1]

    assert run_default_gate(repo_root=repo_root) == run_default_gate()
