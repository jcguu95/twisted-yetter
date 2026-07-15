from experiments.scripts.akbulut_yasui_figure21_morse_draft import (
    COMPONENT_BY_PIECE,
    build_figure21_right,
)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_disk_topology_controls import (
    EXPECTED_TAU_VACUUM_RANKS,
    build_hopf_star,
    build_hopf_winding,
)
from experiments.scripts.morse_pl_lift import (
    apply_special_disk_side_assignment,
    analyze_exact_side_morse_regularity,
    analyze_projection,
    build_blockwise_flat_side_lift,
    build_morse_pl_lift,
    build_projection_bundle,
    certify_exact_side_projection_round_trip,
    certify_puncture_projector_mapping,
    lower_exact_side_projection_to_morse,
    lower_generic_projection_to_morse,
    make_exact_side_projection_lift,
    make_generic_view_projection_lift,
    optimize_special_disk_sides,
    restrict_pl_lift_components,
)


def _small_crossing_control():
    builder = MorseBuilder()
    builder.cup("red1", at="far-left")
    builder.cup("A1", at="far-right")
    builder.cross(over="A1.left", under="red1.right")
    builder.cross(over="red1.left", under="A1.left")
    builder.cap("red1")
    builder.cap("A1")
    return builder


def test_hopf_star_controls_have_expected_combinatorics():
    for valence, expected_rank in list(EXPECTED_TAU_VACUUM_RANKS.items())[:5]:
        forms, component_by_piece = build_hopf_star(valence)
        assert len(component_by_piece) == valence + 1
        assert sum(form["kind"] == "cross" for form in forms) == 2 * valence
        assert expected_rank in {0, 1, 2, 3}
        lift = build_morse_pl_lift(
            forms,
            component_by_piece=component_by_piece,
            special_components=("red",),
        )
        assert lift["integrity"]["component_cycle_counts"] == {
            "red": 1,
            **{f"C{index}": 1 for index in range(1, valence + 1)},
        }


def test_hopf_winding_controls_have_expected_combinatorics():
    for punctures in range(1, 7):
        forms, component_by_piece = build_hopf_winding(punctures)
        assert sum(form["kind"] == "cross" for form in forms) == 2 * punctures
        lift = build_morse_pl_lift(
            forms,
            component_by_piece=component_by_piece,
            special_components=("red",),
        )
        assert lift["integrity"]["component_cycle_counts"] == {"C1": 1, "red": 1}


def test_small_pl_lift_is_two_closed_cycles_and_recovers_xy_crossings():
    builder = _small_crossing_control()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece={"red1": "red", "A1": "A"},
        special_components=("red",),
    )
    assert lift["integrity"]["component_cycle_counts"] == {"A": 1, "red": 1}
    certificate = analyze_projection(lift, "xy")
    assert certificate["status"] == "PASS_XY_COMBINATORIAL_ROUND_TRIP"
    assert certificate["declared_crossing_count"] == 2
    assert certificate["declared_crossings_recovered"] == 2


def test_special_component_is_fixed_in_z_zero():
    builder = _small_crossing_control()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece={"red1": "red", "A1": "A"},
        special_components=("red",),
    )
    red_vertices = [
        vertex for vertex in lift["vertices"] if vertex["component"] == "red"
    ]
    assert red_vertices
    assert all(vertex["position"][2] == 0.0 for vertex in red_vertices)


def test_small_complete_link_can_be_lowered_from_a_generic_view():
    builder = _small_crossing_control()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece={"red1": "red", "A1": "A"},
        special_components=("red",),
    )
    viewed = make_generic_view_projection_lift(
        lift,
        in_plane_angle_degrees=37.0,
        tilt_degrees=11.0,
    )
    report = analyze_projection(viewed, "xz", max_examples=0)
    lowered = lower_generic_projection_to_morse(viewed)
    assert report["status"] == "PASS_XZ_GENERIC_PROJECTION"
    assert lowered["status"] == (
        "PASS_GENERIC_PL_PROJECTION_MORSE_LOWERING_CONTROLS"
    )
    assert lowered["projector_factor_count"] == 0
    assert lowered["projector_gather_plan"] is None
    assert sum(form["kind"] == "vacuum-projector" for form in lowered["forms"]) == 0

    red_only = restrict_pl_lift_components(lift, ("red",))
    assert red_only["integrity"]["component_cycle_counts"] == {"red": 1}
    assert {edge["component"] for edge in red_only["edges"]} == {"red"}


def test_figure21_canonical_lift_recovers_all_106_xy_crossings():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    certificate = analyze_projection(lift, "xy")
    assert certificate["status"] == "PASS_XY_COMBINATORIAL_ROUND_TRIP"
    assert certificate["declared_crossing_count"] == 106
    assert certificate["declared_crossings_recovered"] == 106


def test_figure21_exact_and_near_xz_singularities_are_classified():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    bundle = build_projection_bundle(lift)
    assert bundle["projections"]["xz"]["status"] == (
        "PASS_XZ_ONLY_EXPECTED_SPECIAL_EDGE_ON_SINGULARITY"
    )
    assert bundle["projections"]["near-xz"]["status"] == (
        "PASS_NEAR_XZ_GENERIC_PROJECTION"
    )
    assert bundle["status"] == "PASS_PL_LIFT_PROJECTION_CONTROLS"


def test_figure21_exact_side_optimizer_reduces_and_realizes_punctures():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    baseline = build_projection_bundle(lift)
    optimization = optimize_special_disk_sides(lift, "red")
    optimized_lift = apply_special_disk_side_assignment(lift, optimization)
    optimized = build_projection_bundle(optimized_lift)
    realized = optimized["special_disk_intersections"]["red"]["puncture_count"]
    assert optimization["status"] == "PASS_EXACT_MINIMUM_CUT_SIDE_ASSIGNMENT"
    assert optimization["minimum_puncture_count"] == 29
    assert realized == optimization["minimum_puncture_count"]
    assert realized <= baseline["special_disk_intersections"]["red"]["puncture_count"]
    assert optimized["projections"]["xy"]["status"] == (
        "PASS_XY_COMBINATORIAL_ROUND_TRIP"
    )
    assert optimized["projections"]["near-xz"]["status"] == (
        "PASS_NEAR_XZ_GENERIC_PROJECTION"
    )


def test_figure21_blockwise_flat_lift_keeps_29_punctures_and_valid_projection():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    optimization = optimize_special_disk_sides(lift, "red")
    flattened = build_blockwise_flat_side_lift(lift, optimization)
    bundle = build_projection_bundle(flattened)
    assert bundle["special_disk_intersections"]["red"]["puncture_count"] == 29
    assert bundle["projections"]["xy"]["status"] == (
        "PASS_XY_COMBINATORIAL_ROUND_TRIP"
    )
    side = make_exact_side_projection_lift(flattened, "red", 90.0)
    report = analyze_projection(side, "xz", max_examples=0)
    assert report["status"] == "PASS_XZ_GENERIC_PROJECTION"
    assert report["unexplained_singularity_count"] == 0
    regularity = analyze_exact_side_morse_regularity(side)
    assert regularity["status"] == "PASS_EXACT_SIDE_PL_EVENT_COORDINATE"
    assert regularity["horizontal_edge_count"] == 0


def test_figure21_minimal_local_crossing_heights_preserve_controls():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    optimization = optimize_special_disk_sides(lift, "red")
    flattened = build_blockwise_flat_side_lift(
        lift,
        optimization,
        bump_fraction=0.06,
        crossing_height_mode="minimal-local",
    )
    bundle = build_projection_bundle(flattened)
    assert bundle["special_disk_intersections"]["red"]["puncture_count"] == 29
    assert bundle["projections"]["xy"]["status"] == (
        "PASS_XY_COMBINATORIAL_ROUND_TRIP"
    )
    side = make_exact_side_projection_lift(flattened, "red", 70.0)
    report = analyze_projection(side, "xz", max_examples=0)
    assert report["status"] == "PASS_XZ_GENERIC_PROJECTION"
    assert analyze_exact_side_morse_regularity(side)["horizontal_edge_count"] == 0


def test_figure21_deterministic_block_orders_preserve_controls():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    optimization = optimize_special_disk_sides(lift, "red")
    for strategy in (
        "stable-reverse",
        "projected-mean-ascending",
        "projected-mean-descending",
        "projected-median-ascending",
        "projected-median-descending",
    ):
        flattened = build_blockwise_flat_side_lift(
            lift,
            optimization,
            bump_fraction=0.06,
            crossing_height_mode="minimal-local",
            block_order_strategy=strategy,
            block_order_angle_degrees=70.0,
        )
        bundle = build_projection_bundle(flattened)
        assert bundle["special_disk_intersections"]["red"]["puncture_count"] == 29
        assert bundle["projections"]["xy"]["status"] == (
            "PASS_XY_COMBINATORIAL_ROUND_TRIP"
        )
        side = make_exact_side_projection_lift(flattened, "red", 70.0)
        report = analyze_projection(side, "xz", max_examples=0)
        assert report["status"] == "PASS_XZ_GENERIC_PROJECTION"
        assert analyze_exact_side_morse_regularity(side)["horizontal_edge_count"] == 0


def test_figure21_best_side_projection_lowers_to_one_29_factor_projector():
    builder = build_figure21_right()
    lift = build_morse_pl_lift(
        builder.forms,
        component_by_piece=COMPONENT_BY_PIECE,
        special_components=("red",),
    )
    optimization = optimize_special_disk_sides(lift, "red")
    flattened = build_blockwise_flat_side_lift(
        lift,
        optimization,
        bump_fraction=0.06,
        crossing_height_mode="minimal-local",
        block_order_strategy="projected-mean-descending",
        block_order_angle_degrees=110.0,
    )
    side = make_exact_side_projection_lift(flattened, "red", 70.0)
    lowered = lower_exact_side_projection_to_morse(side)
    round_trip = certify_exact_side_projection_round_trip(
        flattened, side, "red"
    )
    puncture_mapping = certify_puncture_projector_mapping(side, lowered)
    assert round_trip["status"] == "PASS_EXACT_SIDE_PROJECTION_ROUND_TRIP"
    assert all(round_trip["checks"].values())
    assert round_trip["puncture_count"] == 29
    assert round_trip["maximum_forward_residual"] < 1e-9
    assert round_trip["maximum_inverse_residual"] < 1e-9
    assert round_trip["maximum_puncture_residual"] < 1e-9
    assert puncture_mapping["status"] == "PASS_PUNCTURE_PROJECTOR_MAPPING"
    assert all(puncture_mapping["checks"].values())
    assert puncture_mapping["puncture_count"] == 29
    assert puncture_mapping["projector_factor_count"] == 29
    assert lowered["status"] == (
        "PASS_EXACT_SIDE_PROJECTION_MORSE_LOWERING_CONTROLS"
    )
    assert lowered["crossing_count"] == 221
    assert lowered["projector_factor_count"] == 29
    assert lowered["projector_slice_active_count"] == 58
    assert lowered["projector_gather_plan"]["status"] == (
        "PASS_EXPLICIT_IN_DISK_PROJECTOR_ISOTOPY"
    )
    assert lowered["projector_routing_crossing_count_each_way"] == len(
        lowered["projector_gather_plan"]["routing_crossings"]
    )
    assert lowered["projector_gather_plan"]["minimum_boundary_clearance"] > 0
    assert lowered["projector_gather_plan"]["minimum_active_point_clearance"] > 0
    assert lowered["minimum_count"] == lowered["maximum_count"]
    assert lowered["monotone_arc_count"] == 2 * lowered["minimum_count"]
    assert sum(form["kind"] == "vacuum-projector" for form in lowered["forms"]) == 1

    projector_event = next(
        event
        for event in lowered["event_trace"]
        if event["kind"] == "vacuum-projector"
    )
    projector_form_index = next(
        index
        for index, form in enumerate(lowered["forms"])
        if form["kind"] == "vacuum-projector"
    )
    forward = projector_event["routing_crossings"]
    inverse = lowered["forms"][
        projector_form_index + 1 : projector_form_index + 1 + len(forward)
    ]
    assert [
        (form["over"], form["under"]) for form in inverse
    ] == [
        (crossing["over"], crossing["under"])
        for crossing in reversed(forward)
    ]
