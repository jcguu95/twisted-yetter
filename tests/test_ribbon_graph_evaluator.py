import json
from pathlib import Path
import runpy
import sys
import types

import pytest

from experiments.sage.morse_pivotal_contract import (
    test_pivotal_profile as make_test_pivotal_profile,
)
from experiments.sage.pointed_premodular_categories import (
    Rank2Z2SemionModularCategory,
    SnapshotPointedModularCategory,
    SymmetricZ2PremodularCategory,
)
from experiments.sage.ribbon_graph_evaluator import (
    DirectVacuumProjectorEvaluator,
    PointedVacuumProjectorEvaluator,
    RibbonGraphContractError,
    RibbonGraphEvaluator,
    build_vacuum_projector_evaluator,
)
from experiments.scripts.akbulut_yasui_figure21_morse_draft import (
    COMPONENT_BY_PIECE as FIGURE21_COMPONENT_BY_PIECE,
    COMPONENT_ORDER as FIGURE21_COMPONENT_ORDER,
    FRAMING_LABELS as FIGURE21_FRAMING_LABELS,
    build_figure21_right,
)
from experiments.scripts.special_dotted_morphism import (
    build_vacuum_coupon_graph,
    compile_projected_morphism,
)
from experiments.scripts.run_figure21_rank2_semion_modular_evaluation_v1 import (
    generate as generate_figure21_semion_evaluation,
)
from experiments.scripts.run_figure21_standard_pointed_modular_sweep_v1 import (
    _labels_from_id as figure21_labels_from_id,
    _load_figure21 as load_figure21_sweep_context,
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


class SymmetricZ2Control(SymmetricZ2PremodularCategory):
    pass


class NonPointedDimensionControl(SymmetricZ2Control):
    def dimension(self, label):
        return 1.0 if label == 0 else 2.0**0.5


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


def test_direct_projector_matches_modular_killing_loop_control():
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    category = SemionKillingLoopControl()
    killing_loop = RibbonGraphEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    direct = DirectVacuumProjectorEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    for label in category.labels:
        expected = killing_loop.fixed_label_value(graph, {"A": label})[0]
        observed, stats = direct.fixed_label_value(graph, {"A": label})
        assert abs(observed - expected) < 1e-12
        assert stats["backend"] == "DIRECT_HORIZONTAL_VACUUM_PROJECTOR"
        assert stats["normalization"] == (
            "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR"
        )


@pytest.mark.parametrize("fermionic", [False, True])
def test_direct_projector_accepts_degenerate_premodular_z2(fermionic):
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    category = SymmetricZ2Control(fermionic=fermionic)
    direct = DirectVacuumProjectorEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    vacuum, stats = direct.fixed_label_value(graph, {"A": 0})
    nonvacuum, _ = direct.fixed_label_value(graph, {"A": 1})
    assert abs(vacuum - 1.0) < 1e-12
    assert abs(nonvacuum) < 1e-12
    assert stats["category_id"] in {"rep-z2", "svec"}
    with pytest.raises(RibbonGraphContractError, match="not certified"):
        RibbonGraphEvaluator(
            category,
            source_forms=forms,
            component_by_piece=component_by_piece,
            projected_ir=ir,
            total_framings={"red": 0, "A": 0},
        )


@pytest.mark.parametrize("fermionic", [False, True])
def test_pointed_graph_projector_matches_horizontal_direct_backend(fermionic):
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    category = SymmetricZ2Control(fermionic=fermionic)
    horizontal = DirectVacuumProjectorEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    graph_level = PointedVacuumProjectorEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    for label in category.labels:
        expected = horizontal.fixed_label_value(graph, {"A": label})[0]
        observed, stats = graph_level.fixed_label_value(graph, {"A": label})
        assert abs(observed - expected) < 1e-12
        assert stats["projector_rank"] == int(label == category.unit)


def test_pointed_graph_backend_fails_closed_on_nonpointed_category():
    forms, component_by_piece, ir, _graph = hopf_special_disk_control()
    with pytest.raises(RibbonGraphContractError, match="dimension to be one"):
        PointedVacuumProjectorEvaluator(
            NonPointedDimensionControl(fermionic=False),
            source_forms=forms,
            component_by_piece=component_by_piece,
            projected_ir=ir,
            total_framings={"red": 0, "A": 0},
        )


@pytest.mark.parametrize("fermionic", [False, True])
def test_pointed_premodular_backend_evaluates_figure21_coupon(fermionic):
    builder = build_figure21_right()
    ir = compile_projected_morphism(
        builder.forms,
        component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
        special_components=("red",),
        component_order=FIGURE21_COMPONENT_ORDER,
    )
    graph = build_vacuum_coupon_graph(builder.forms, ir)
    category = SymmetricZ2Control(fermionic=fermionic)
    evaluator = PointedVacuumProjectorEvaluator(
        category,
        source_forms=builder.forms,
        component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
        projected_ir=ir,
        total_framings=FIGURE21_FRAMING_LABELS,
    )
    labels = {component: 0 for component in FIGURE21_COMPONENT_ORDER if component != "red"}
    all_unit, all_unit_stats = evaluator.fixed_label_value(graph, labels)
    assert abs(all_unit - 1.0) < 1e-12
    assert all_unit_stats["projector_rank"] == 1

    labels["purple"] = 1
    odd_puncture_word, odd_stats = evaluator.fixed_label_value(graph, labels)
    assert abs(odd_puncture_word) < 1e-12
    assert odd_stats["status"] == "PRUNED_NO_VACUUM"

    labels["black"] = 1
    surviving, surviving_stats = evaluator.fixed_label_value(graph, labels)
    assert abs(abs(surviving) - 1.0) < 1e-12
    assert surviving_stats["projector_rank"] == 1


def test_direct_projector_fails_closed_on_figure21_nonhorizontal_coupon():
    builder = build_figure21_right()
    ir = compile_projected_morphism(
        builder.forms,
        component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
        special_components=("red",),
        component_order=FIGURE21_COMPONENT_ORDER,
    )
    graph = build_vacuum_coupon_graph(builder.forms, ir)
    assert graph["coupon_input_count"] == 29
    with pytest.raises(
        RibbonGraphContractError,
        match="UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR",
    ):
        DirectVacuumProjectorEvaluator(
            SymmetricZ2Control(fermionic=False),
            source_forms=builder.forms,
            component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
            projected_ir=ir,
            total_framings=FIGURE21_FRAMING_LABELS,
        )


def test_backend_selector_prefers_direct_semantics_and_fails_closed():
    forms, component_by_piece, ir, _graph = hopf_special_disk_control()
    direct = build_vacuum_projector_evaluator(
        SymmetricZ2Control(fermionic=False),
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    assert isinstance(direct, DirectVacuumProjectorEvaluator)

    builder = build_figure21_right()
    figure21_ir = compile_projected_morphism(
        builder.forms,
        component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
        special_components=("red",),
        component_order=FIGURE21_COMPONENT_ORDER,
    )
    pointed = build_vacuum_projector_evaluator(
        SymmetricZ2Control(fermionic=True),
        source_forms=builder.forms,
        component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
        projected_ir=figure21_ir,
        total_framings=FIGURE21_FRAMING_LABELS,
    )
    assert isinstance(pointed, PointedVacuumProjectorEvaluator)

    with pytest.raises(
        RibbonGraphContractError,
        match="general nonpointed nonhorizontal premodular contraction",
    ):
        build_vacuum_projector_evaluator(
            NonPointedDimensionControl(fermionic=False),
            source_forms=builder.forms,
            component_by_piece=FIGURE21_COMPONENT_BY_PIECE,
            projected_ir=figure21_ir,
            total_framings=FIGURE21_FRAMING_LABELS,
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


@pytest.mark.parametrize("branch", ["plus", "minus"])
def test_rank2_semion_snapshot_category_is_certified_for_killing_loop(branch):
    forms, component_by_piece, ir, graph = hopf_special_disk_control()
    category = Rank2Z2SemionModularCategory(branch=branch)
    evaluator = RibbonGraphEvaluator(
        category,
        source_forms=forms,
        component_by_piece=component_by_piece,
        projected_ir=ir,
        total_framings={"red": 0, "A": 0},
    )
    vacuum, _stats = evaluator.fixed_label_value(graph, {"A": 0})
    nonvacuum, _stats = evaluator.fixed_label_value(graph, {"A": 1})
    assert abs(vacuum - 1.0) < 1e-12
    assert abs(nonvacuum) < 1e-12


def test_figure21_rank2_semion_runner_prefix_checks_modular_against_pointed():
    artifact = generate_figure21_semion_evaluation(max_sectors=4)
    assert artifact["status"] == (
        "PASS_FIGURE21_RANK2_SEMION_MODULAR_PREFIX_EVALUATION"
    )
    assert artifact["checks"]["modular_equals_pointed_for_each_branch"] is True
    assert artifact["checks"]["full_rank2_z2_sector_space_evaluated"] is False
    assert artifact["results"]["plus"]["sector_count"] == 4
    assert artifact["results"]["minus"]["sector_count"] == 4


def test_figure21_z2xz2_snapshot_negative_crossing_uses_opposite_braiding():
    snapshot = json.loads(
        Path(
            "experiments/results/foundation-v2-safety-substrate/"
            "ribbon-realization-snapshots/"
            "rank4-pointed-z2xz2-q002-snapshot-v1.json"
        ).read_text()
    )
    category = SnapshotPointedModularCategory(snapshot)
    context = load_figure21_sweep_context()
    graph = context["graph"]
    labels_tuple = figure21_labels_from_id(
        tuple(category.labels), 1, len(context["ordinary"])
    )
    labels = dict(zip(context["ordinary"], labels_tuple, strict=True))

    pointed = PointedVacuumProjectorEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    modular = RibbonGraphEvaluator(
        category,
        source_forms=context["forms"],
        component_by_piece=context["source"]["component_by_piece"],
        projected_ir=context["ir"],
        total_framings=context["source"]["framing_labels"],
    )
    pointed_value, pointed_stats = pointed.fixed_label_value(graph, labels)
    modular_value, modular_stats = modular.fixed_label_value(graph, labels)

    assert labels["black"] == "10"
    assert pointed_stats["status"] == "PRUNED_NO_VACUUM"
    assert abs(pointed_value) < 1e-12
    assert abs(modular_value - pointed_value) < 1e-12
    contributions = modular_stats["special_label_contributions"]
    assert [item["blackboard_source_value"] for item in contributions] == [
        1.0 + 0.0j,
        1.0 + 0.0j,
        -1.0 + 0.0j,
        -1.0 + 0.0j,
    ]


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
