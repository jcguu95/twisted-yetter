import json
from pathlib import Path

import pytest

from experiments.sage.morse_fusion_evaluator import (
    expand_vacuum_coupon_graph_term,
    vacuum_coupon_path_basis,
)
from experiments.sage.morse_pivotal_contract import (
    test_pivotal_profile as make_test_pivotal_profile,
)
from experiments.scripts.akbulut_yasui_figure21_morse_draft import (
    COMPONENT_BY_PIECE,
    COMPONENT_ORDER,
    build_figure21_right,
)


class Z2FusionRules:
    labels = (0, 1)
    unit = 0
    pivotal_profile = make_test_pivotal_profile(category_id="test-z2-fusion-rules")

    def dual(self, label):
        return label

    def fusion_multiplicity(self, left, right, output):
        return int((left ^ right) == output)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import (
    build_ribbon_graph_ir_v2,
    build_vacuum_coupon_graph,
    compile_projected_morphism,
    preflight_horizontal_disk_corridor,
    replay_forms,
    validate_ribbon_graph_ir_v2,
)


def zero_puncture_input():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", between=("red1.left", "red1.right"))
    m.cap("A1")
    m.cap("red1")
    return m.forms, {"red1": "red", "A1": "A"}


def one_puncture_input():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", at="far-right")
    m.cross(over="A1.left", under="red1.right")
    m.cross(over="red1.left", under="A1.left")
    m.cap("red1")
    m.cap("A1")
    return m.forms, {"red1": "red", "A1": "A"}


def two_puncture_input():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", at="far-right")
    m.cross(over="A1.left", under="red1.right")
    m.cross(over="red1.left", under="A1.left")
    m.cross(over="A1.left", under="red1.left")
    m.cross(over="red1.right", under="A1.left")
    m.cap("red1")
    m.cap("A1")
    return m.forms, {"red1": "red", "A1": "A"}


@pytest.mark.parametrize(
    ("factory", "expected"),
    [(zero_puncture_input, 0), (one_puncture_input, 1), (two_puncture_input, 2)],
)
def test_special_disk_compiler_counts_small_puncture_controls(factory, expected):
    forms, component_by_piece = factory()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    certificate = ir["special_disk_certificates"][0]
    assert certificate["forced_cut_count"] == expected
    assert certificate["signed_disk_intersections"] in (
        certificate["d2_linking_row"],
        [-value for value in certificate["d2_linking_row"]],
    )
    assert replay_forms(ir["ordinary_forms"])


def test_special_disk_compiler_rejects_self_crossing_special_component():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cross(over="red1.left", under="red1.right")
    m.cap("red1")
    with pytest.raises(ValueError, match="self-crossings"):
        compile_projected_morphism(
            m.forms,
            component_by_piece={"red1": "red"},
            special_components=("red",),
        )


def test_one_puncture_has_a_horizontal_projector_slice():
    forms, component_by_piece = one_puncture_input()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    preflight = preflight_horizontal_disk_corridor(forms, ir)
    assert preflight["status"] == "PASS_COMMON_HORIZONTAL_PROJECTOR_SLICE"
    assert preflight["projector_strands"] == ["A1.left"]


def test_one_puncture_builds_first_class_coupon_with_identity_recovery():
    forms, component_by_piece = one_puncture_input()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    graph = build_vacuum_coupon_graph(forms, ir)
    assert graph["status"] == (
        "PASS_GRAPH_LEVEL_VACUUM_PROJECTOR_COUPON_NOT_EVALUATED"
    )
    assert graph["coupon_input_count"] == 1
    assert graph["coupon_output_count"] == 1
    assert graph["identity_recovery"]["status"] == (
        "PASS_COUPON_IDENTITY_RECOVERS_ONE_CYCLE_PER_ORDINARY_COMPONENT"
    )
    assert graph["identity_recovery"]["component_cycles"]["A"]["cycle_count"] == 1


def test_two_punctures_on_one_strand_fail_closed_as_nonhorizontal():
    forms, component_by_piece = two_puncture_input()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    preflight = preflight_horizontal_disk_corridor(forms, ir)
    assert preflight["status"] == "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR"
    assert preflight["duplicate_active_strands"] == ["A1.left"]
    graph = build_vacuum_coupon_graph(forms, ir)
    assert graph["coupon_input_count"] == 2
    assert graph["coupon_output_count"] == 2
    cut_tokens = [
        token
        for token in graph["ordinary_component_sequences"]["A"]
        if token["kind"] == "coupon-cut"
    ]
    assert len(cut_tokens) == 2
    expanded = expand_vacuum_coupon_graph_term(
        Z2FusionRules(), graph, {"A": 1}, basis_index=0
    )
    assert expanded["status"] == (
        "PASS_TRIVALENT_VACUUM_PROJECTOR_TERM_NOT_CONTRACTED"
    )
    assert expanded["expanded_coupon"]["projection_vertex_count"] == 1
    assert expanded["expanded_coupon"]["inclusion_vertex_count"] == 1
    assert all(
        endpoint["node_id"] != graph["coupon_node_id"]
        for edge in expanded["edges"]
        for endpoint in (edge["from"], edge["to"])
    )


def test_multiple_special_components_parse_but_numeric_support_fails_closed():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("blue1", at="far-right")
    m.cap("blue1")
    m.cap("red1")
    ir = compile_projected_morphism(
        m.forms,
        component_by_piece={"red1": "red", "blue1": "blue"},
        special_components=("red", "blue"),
    )
    assert ir["special_component_count"] == 2
    assert ir["numeric_support"] == (
        "UNSUPPORTED_MULTIPLE_SPECIAL_COMPONENTS_FAIL_CLOSED"
    )


def test_ribbon_graph_v2_builds_multiple_independent_special_coupons():
    m = MorseBuilder()
    m.cup("red1", at="far-left")
    m.cup("A1", between=("red1.left", "red1.right"))
    m.cup("blue1", at="far-right")
    m.cap("blue1")
    m.cap("A1")
    m.cap("red1")
    component_by_piece = {"red1": "red", "blue1": "blue", "A1": "A"}
    ir = compile_projected_morphism(
        m.forms,
        component_by_piece=component_by_piece,
        special_components=("red", "blue"),
    )
    graph = build_ribbon_graph_ir_v2(m.forms, ir)
    report = validate_ribbon_graph_ir_v2(graph)
    assert report["coupon_count"] == 2
    assert graph["special_components"] == ["red", "blue"]
    assert graph["ordinary_components"] == ["A"]
    assert set(graph["coupon_node_ids"]) == {"red", "blue"}
    assert all(
        edge["orientation"] == "from-to" and edge["framing"] == 0
        for edge in graph["edges"]
    )


def test_ribbon_graph_v2_hash_covers_rotation_system():
    forms, component_by_piece = one_puncture_input()
    ir = compile_projected_morphism(
        forms,
        component_by_piece=component_by_piece,
        special_components=("red",),
    )
    graph = build_ribbon_graph_ir_v2(forms, ir)
    graph["nodes"][0]["cyclic_order"] = list(
        reversed(graph["nodes"][0]["cyclic_order"])
    )
    with pytest.raises(ValueError, match="graph hash mismatch"):
        validate_ribbon_graph_ir_v2(graph)


def test_figure21_disk_certificate_regression():
    builder = build_figure21_right()
    ir = compile_projected_morphism(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
        component_order=COMPONENT_ORDER,
    )
    certificate = ir["special_disk_certificates"][0]
    assert len(ir["component_order"]) == 12
    assert ir["crossing_count"] == 106
    assert certificate["red_projection_self_crossings"] == 0
    assert certificate["boundary_crossing_count"] == 78
    assert certificate["inside_arc_interval_count"] == 39
    assert certificate["forced_cut_count"] == 29
    assert certificate["puncture_order_convention"] == (
        "oriented-special-boundary-entry-crossing-order-v2"
    )
    boundary_positions = [
        cut["special_boundary_entry_order_index"]
        for cut in certificate["forced_cuts"]
    ]
    assert boundary_positions == sorted(boundary_positions)
    assert certificate["d2_linking_row"] == [5, 2, 0, 0, 0, 0, 6, -2, 5, -2, 1]
    assert certificate["signed_disk_intersections"] == [
        -5,
        -2,
        0,
        0,
        0,
        0,
        -6,
        2,
        -5,
        2,
        -1,
    ]
    assert certificate["disk_to_linking_orientation_sign"] == -1
    assert ir["vacuum_projectors"][0]["corridor_status"] == "NOT_LINEARIZED"
    preflight = preflight_horizontal_disk_corridor(builder.forms, ir)
    assert preflight["status"] == "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR"
    assert len(preflight["nonmonotone_cut_ids"]) == 8
    graph = build_vacuum_coupon_graph(builder.forms, ir)
    assert graph["coupon_input_count"] == 29
    assert graph["coupon_output_count"] == 29
    assert graph["identity_recovery"]["status"] == (
        "PASS_COUPON_IDENTITY_RECOVERS_ONE_CYCLE_PER_ORDINARY_COMPONENT"
    )
    assert set(graph["identity_recovery"]["component_cycles"]) == set(
        COMPONENT_ORDER
    ) - {"red"}
    repeated = build_vacuum_coupon_graph(builder.forms, ir)
    assert repeated["graph_hash"] == graph["graph_hash"]

    graph_v2 = build_ribbon_graph_ir_v2(builder.forms, ir)
    assert graph_v2["special_components"] == ["red"]
    assert validate_ribbon_graph_ir_v2(graph_v2)["coupon_count"] == 1
    assert graph_v2["graph_hash"] == build_ribbon_graph_ir_v2(
        builder.forms, ir
    )["graph_hash"]

    coupon = next(
        node
        for node in graph["nodes"]
        if node["kind"] == "vacuum-projector-coupon"
    )
    ordinary_components = set(COMPONENT_ORDER) - {"red"}
    all_unit = {component: 0 for component in ordinary_components}
    _, all_unit_basis, all_unit_metadata = vacuum_coupon_path_basis(
        Z2FusionRules(), coupon, all_unit
    )
    assert len(all_unit_basis) == 1
    assert all_unit_metadata["factor_count"] == 29

    odd_purple = dict(all_unit, purple=1)
    _, odd_basis, odd_metadata = vacuum_coupon_path_basis(
        Z2FusionRules(), coupon, odd_purple
    )
    assert odd_basis == ()
    assert odd_metadata["root_multiplicity_rank"] == 0

    expanded = expand_vacuum_coupon_graph_term(
        Z2FusionRules(), graph, all_unit, basis_index=0,
        namespace="figure21-control",
    )
    assert expanded["expanded_coupon"]["factor_count"] == 29
    assert expanded["expanded_coupon"]["basis_rank"] == 1
    assert expanded["expanded_coupon"]["projection_vertex_count"] == 28
    assert expanded["expanded_coupon"]["inclusion_vertex_count"] == 28
    assert sum(node["kind"] == "fusion-coupon" for node in expanded["nodes"]) == 28
    assert sum(node["kind"] == "split-coupon" for node in expanded["nodes"]) == 28
    assert all(node["node_id"] != graph["coupon_node_id"] for node in expanded["nodes"])


def test_figure21_topology_artifact_is_conservative_and_reproducible():
    artifact = json.loads(
        Path(
            "experiments/results/akbulut-yasui/"
            "figure21-right-special-disk-topology-v1.json"
        ).read_text()
    )
    assert artifact["status"] == (
        "MORPHISM_GRAPH_COUPON_CONTROLS_PASS_NOT_EVALUATED"
    )
    assert artifact["mathematical_status"] == (
        "DRAFT_NOT_VERIFIED_AGAINST_PRINTED_DIAGRAM"
    )
    assert artifact["git_dirty"] is False
    assert artifact["link_certificate"]["determinant"] == 1
    assert artifact["link_certificate"]["rank"] == 12
    assert artifact["link_certificate"]["signature"]["signature"] == -8
    certificate = artifact["projected_morphism_ir"]["special_disk_certificates"][0]
    assert certificate["forced_cut_count"] == 29
    assert certificate["signed_disk_intersections"] == [
        -value for value in certificate["d2_linking_row"]
    ]
    assert artifact["corridor_preflight"]["status"] == (
        "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR"
    )
    coupon = artifact["coupon_graph"]
    assert coupon["status"] == (
        "PASS_GRAPH_LEVEL_VACUUM_PROJECTOR_COUPON_NOT_EVALUATED"
    )
    assert coupon["coupon_input_count"] == 29
    assert coupon["coupon_output_count"] == 29
    assert coupon["identity_recovery"]["status"] == (
        "PASS_COUPON_IDENTITY_RECOVERS_ONE_CYCLE_PER_ORDINARY_COMPONENT"
    )
    assert coupon["evaluation_status"] == (
        "NOT_EVALUATED_REQUIRES_COUPON_AWARE_BACKEND"
    )
