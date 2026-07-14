from pathlib import Path
import runpy
import sys
import types

import pytest

from experiments.sage.morse_pivotal_contract import (
    test_pivotal_profile as make_test_pivotal_profile,
)
from experiments.sage.ribbon_graph_evaluator import (
    RibbonGraphContractError,
    RibbonGraphEvaluator,
)
from experiments.scripts.special_dotted_morphism import (
    build_vacuum_coupon_graph,
    compile_projected_morphism,
)


class SemionKillingLoopControl:
    labels = (0, 1)
    unit = 0
    category_id = "su2-k2"
    pivotal_profile = make_test_pivotal_profile(category_id=category_id)

    @staticmethod
    def dimension(_label):
        return 1.0

    @staticmethod
    def twist(label):
        return 1.0 if label == 0 else 1.0j

    @staticmethod
    def dual(label):
        return label

    @staticmethod
    def fusion_multiplicity(left, right, output):
        return int(output == (left + right) % 2)

    @staticmethod
    def fusion_outputs(left, right):
        return (((left + right) % 2, 1),)

    @staticmethod
    def f_block(a, b, c, d):
        left = ((a + b) % 2, 0, 0)
        right = ((b + c) % 2, 0, 0)
        matrix = ((1.0 + 0.0j,),)
        return {
            "left_basis": (left,),
            "right_basis": (right,),
            "left_index": {left: 0},
            "right_index": {right: 0},
            "right_to_left": matrix,
            "left_to_right": matrix,
        }

    @staticmethod
    def r_matrix(left, right, _output, positive):
        value = 1.0j if left == right == 1 else 1.0
        if not positive:
            value = 1.0 / value
        return ((value,),)

    @staticmethod
    def reverse_bend(_label):
        return 1.0

    @staticmethod
    def cost_profile():
        return {"f": 1.0, "r": 1.0}


def hopf_special_disk_control():
    forms = [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "red", "at": "far-right"},
        {"kind": "cross", "over": "A.right", "under": "red.left"},
        {"kind": "cross", "over": "red.left", "under": "A.right"},
        {
            "kind": "cap",
            "piece": "red",
            "strands": ["red.left", "red.right"],
        },
        {
            "kind": "cap",
            "piece": "A",
            "strands": ["A.left", "A.right"],
        },
    ]
    component_by_piece = {"A": "A", "red": "red"}
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=["red"],
        component_order=["red", "A"],
    )
    return forms, component_by_piece, ir, build_vacuum_coupon_graph(forms, ir)


def test_modular_killing_loop_is_the_vacuum_projector():
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    evaluator = RibbonGraphEvaluator(
        SemionKillingLoopControl(),
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    vacuum, stats = evaluator.fixed_label_value(graph, {"A": 0})
    nonvacuum, _ = evaluator.fixed_label_value(graph, {"A": 1})
    assert abs(vacuum - 1.0) < 1e-12
    assert abs(nonvacuum) < 1e-12
    assert stats["global_dimension_squared"] == 2.0
    assert stats["normalization"] == (
        "OMEGA_SPECIAL_LOOP_DIVIDED_BY_SUM_D_SQUARED"
    )


def test_canceling_dotted_one_two_handle_pair_has_value_one():
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    category = SemionKillingLoopControl()
    evaluator = RibbonGraphEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    kirby_sum = sum(
        category.dimension(label)
        * evaluator.fixed_label_value(graph, {"A": label})[0]
        for label in category.labels
    )
    assert abs(kirby_sum - 1.0) < 1e-12


def test_total_framings_are_required_explicitly():
    forms, component_by_piece, ir, _graph = hopf_special_disk_control()
    with pytest.raises(RibbonGraphContractError, match="total framings"):
        RibbonGraphEvaluator(
            SemionKillingLoopControl(),
            source_forms=forms,
            component_by_piece=component_by_piece,
            projected_ir=ir,
        )


def test_total_framing_correction_applies_the_ribbon_twist():
    forms, component_by_piece, _ir, _graph = hopf_special_disk_control()
    forms = [
        *forms[:4],
        {"kind": "cup", "piece": "B", "at": "far-right"},
        *forms[4:],
        {
            "kind": "cap",
            "piece": "B",
            "strands": ["B.left", "B.right"],
        },
    ]
    component_by_piece = {**component_by_piece, "B": "B"}
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=["red"],
        component_order=["red", "A", "B"],
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    blackboard = RibbonGraphEvaluator(
        SemionKillingLoopControl(),
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0, "B": 0},
    )
    plus_one = RibbonGraphEvaluator(
        SemionKillingLoopControl(),
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0, "B": 1},
    )
    value_zero, _ = blackboard.fixed_label_value(graph, {"A": 0, "B": 1})
    value_plus_one, stats = plus_one.fixed_label_value(
        graph, {"A": 0, "B": 1}
    )
    assert abs(value_plus_one - 1.0j * value_zero) < 1e-12
    assert stats["framing_corrections"] == {"red": 0, "A": 0, "B": 1}


def test_figure21_runner_preserves_the_frozen_total_framings(monkeypatch):
    category = SemionKillingLoopControl()
    registry = types.ModuleType("experiments.sage.morse_category_registry")
    registry.build_category = lambda _family, _level: (
        category,
        "test semion",
        category.category_id,
    )
    monkeypatch.setitem(
        sys.modules, "experiments.sage.morse_category_registry", registry
    )
    runner = runpy.run_path(
        Path("experiments/sage/figure21_su2_2_full_evaluation.sage.py")
    )
    context = runner["load_context"]()
    expected = {
        "red": 0,
        "purple": -5,
        "mint": -1,
        "pink1": -2,
        "pink2": -2,
        "pink3": -2,
        "pink4": -2,
        "orange": 1,
        "blue": -1,
        "beige": 4,
        "green": 2,
        "black": -1,
    }
    assert context["evaluator"].total_framings == expected
    assert context["evaluator"].visible_self_writhe == {}
    assert context["evaluator"].framing_corrections == expected


def test_killing_loop_backend_fails_closed_on_uncertified_category():
    forms, component_by_piece, ir, _graph = hopf_special_disk_control()
    category = SemionKillingLoopControl()
    category.category_id = "uncertified-semion"
    with pytest.raises(RibbonGraphContractError, match="not certified"):
        RibbonGraphEvaluator(
            category,
            source_forms=forms,
            component_by_piece=component_by_piece,
            projected_ir=ir,
            total_framings={"red": 0, "A": 0},
        )


def test_coupon_graph_must_match_the_projected_ir():
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    evaluator = RibbonGraphEvaluator(
        SemionKillingLoopControl(),
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    graph = dict(graph)
    graph["source_projected_ir_hash"] = "sha256:not-the-ir"
    with pytest.raises(RibbonGraphContractError, match="not built"):
        evaluator.fixed_label_value(graph, {"A": 0})
