from experiments.sage.morse_fusion_evaluator import (
    Leaf,
    LeafState,
    Node,
    NodeState,
    MorseEvaluator,
    _local_node_state,
    _rebuilt_node_state,
    _replace_state,
    analyze_topology,
    compile_right_comb_projector_term,
    fuse_active_pair,
    left_bend_fusion_matrix,
    leaves,
    project_vacuum_interval,
    right_bend_fusion_matrix,
    right_comb_fusion_path_basis,
    right_comb_fusion_path_counts,
    rotation_plan,
    rotate_shape,
    split_active_wire,
    vacuum_coupon_path_basis,
)
from experiments.sage.morse_pivotal_contract import (
    test_pivotal_profile as make_test_pivotal_profile,
)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import (
    compile_projected_morphism,
    insert_horizontal_projector,
    linearize_horizontal_disk_projector,
)


def test_cached_node_state_hash_and_iterative_replacement_preserve_value_semantics():
    a, b, c = LeafState("a"), LeafState("b"), LeafState("c")
    left = NodeState(a, b, 1, 0)
    root = NodeState(left, c, 0, 0)
    replacement = NodeState(a, b, 0, 0)
    observed = _replace_state(root, (0,), replacement)
    expected = NodeState(replacement, c, 0, 0)
    assert observed == expected
    assert hash(observed) == hash(expected)
    assert root.left == left

    _rebuilt_node_state.cache_clear()
    first = _rebuilt_node_state(replacement, c, 0, 0)
    second = _rebuilt_node_state(replacement, c, 0, 0)
    assert first is second
    assert _rebuilt_node_state.cache_info().hits == 1

    _local_node_state.cache_clear()
    first_local = _local_node_state(a, b, 1, 0)
    second_local = _local_node_state(a, b, 1, 0)
    assert first_local is second_local
    assert _local_node_state.cache_info().hits == 1


class SemionCategory:
    labels = (0, 1)
    unit = 0
    pivotal_profile = make_test_pivotal_profile(
        category_id="test-semion",
        reverse_bend_values={"0": [1.0, 0.0], "1": [1.0, 0.0]},
    )

    def dual(self, label):
        return label

    def dimension(self, label):
        return 1.0

    def twist(self, label):
        return 1.0j if label else 1.0

    def fusion_multiplicity(self, left, right, output):
        return int((left ^ right) == output)

    def f_block(self, a, b, c, d):
        left = tuple(
            (x, 0, 0)
            for x in self.labels
            if self.fusion_multiplicity(a, b, x)
            and self.fusion_multiplicity(x, c, d)
        )
        right = tuple(
            (y, 0, 0)
            for y in self.labels
            if self.fusion_multiplicity(b, c, y)
            and self.fusion_multiplicity(a, y, d)
        )
        return {
            "left_basis": left,
            "right_basis": right,
            "left_index": {basis: index for index, basis in enumerate(left)},
            "right_index": {basis: index for index, basis in enumerate(right)},
            "right_to_left": [[1.0]],
            "left_to_right": [[1.0]],
        }

    def r_matrix(self, a, b, c, positive):
        value = 1.0j if a == b == 1 else 1.0
        return [[value if positive else 1 / value]]

    def character(self, character_label, simple_label):
        return 1.0

    def reverse_bend(self, label):
        return 1.0

    def cost_profile(self):
        return {"f": 2.0, "r": 1.0}


class PseudorealSemionCategory(SemionCategory):
    pivotal_profile = make_test_pivotal_profile(
        category_id="test-pseudoreal-semion",
        reverse_bend_values={"0": [1.0, 0.0], "1": [-1.0, 0.0]},
    )

    def reverse_bend(self, label):
        return -1.0 if label else 1.0


class RepA4FusionRules:
    """Fusion ring of Rep(A4), including 3 tensor 3's multiplicity two."""

    labels = (0, 1, 2, 3)
    unit = 0
    pivotal_profile = make_test_pivotal_profile(
        category_id="test-rep-a4-fusion-rules",
        reverse_bend_values={str(label): [1.0, 0.0] for label in range(4)},
    )

    def dual(self, label):
        return {0: 0, 1: 2, 2: 1, 3: 3}[label]

    def dimension(self, label):
        return 3.0 if label == 3 else 1.0

    def reverse_bend(self, label):
        return 1.0

    def fusion_multiplicity(self, left, right, output):
        if left == 0:
            return int(right == output)
        if right == 0:
            return int(left == output)
        if left == 3 and right == 3:
            return 2 if output == 3 else int(output in {0, 1, 2})
        if left == 3 or right == 3:
            return int(output == 3)
        product = {
            (1, 1): 2,
            (1, 2): 0,
            (2, 1): 0,
            (2, 2): 1,
        }[(left, right)]
        return int(output == product)


class TwoCopyBendCategory:
    """Minimal orthonormal F block with a two-dimensional fusion space."""

    labels = (0, 1)
    unit = 0
    pivotal_profile = make_test_pivotal_profile(
        category_id="test-two-copy-bend",
        reverse_bend_values={"0": [1.0, 0.0], "1": [1.0, 0.0]},
    )

    def __init__(self):
        self.q_dimension = 1.0 + 2.0**0.5

    def dual(self, label):
        return label

    def dimension(self, label):
        return self.q_dimension if label else 1.0

    def fusion_multiplicity(self, left, right, output):
        if left == 0:
            return int(right == output)
        if right == 0:
            return int(left == output)
        return 1 if output == 0 else 2

    def f_block(self, a, b, c, d):
        assert (a, b, c, d) == (1, 1, 1, 1)
        basis = (
            (0, 0, 0),
            (1, 0, 0),
            (1, 0, 1),
            (1, 1, 0),
            (1, 1, 1),
        )
        first_column = [
            1.0 / self.q_dimension,
            1.0 / self.q_dimension**0.5,
            0.0,
            0.0,
            1.0 / self.q_dimension**0.5,
        ]
        displacement = [1.0 - first_column[0], *(-x for x in first_column[1:])]
        norm_squared = sum(x * x for x in displacement)
        matrix = [
            [
                float(row == column)
                - 2.0 * displacement[row] * displacement[column] / norm_squared
                for column in range(len(basis))
            ]
            for row in range(len(basis))
        ]
        return {
            "left_basis": basis,
            "right_basis": basis,
            "left_index": {entry: index for index, entry in enumerate(basis)},
            "right_index": {entry: index for index, entry in enumerate(basis)},
            "right_to_left": matrix,
            "left_to_right": matrix,
        }


def unknot_forms(kink=False):
    forms = [{"kind": "cup", "piece": "A", "at": "far-left"}]
    if kink:
        forms.append({"kind": "kink", "strand": "A.left", "sign": "+", "times": 1})
    forms.append({"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]})
    return forms


def block_r2_forms():
    return [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
        {"kind": "cup", "piece": "C", "at": "far-right"},
        {"kind": "cross", "over": "A.right", "under": "B.left"},
        {"kind": "cross", "over": "A.right", "under": "B.right"},
        {"kind": "cross", "over": "A.right", "under": "B.right"},
        {"kind": "cross", "over": "A.right", "under": "B.left"},
        {"kind": "cap", "piece": "C", "strands": ["C.left", "C.right"]},
        {"kind": "cap", "piece": "B", "strands": ["B.left", "B.right"]},
        {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
    ]


def parallel_unlink_forms():
    return [
        {"kind": "cup", "piece": "A", "at": "far-right"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
        {"kind": "cap", "piece": "B", "strands": ["B.left", "B.right"]},
        {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
    ]


def middle_vacuum_projector_forms(repetitions=1):
    forms = [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
    ]
    forms.extend(
        {
            "kind": "vacuum-projector",
            "projector_id": f"middle-{index}",
            "strands": ["A.right", "B.left"],
        }
        for index in range(repetitions)
    )
    forms.extend(
        [
            {"kind": "cap", "piece": "B", "strands": ["B.left", "B.right"]},
            {"kind": "cap", "piece": "A", "strands": ["A.left", "A.right"]},
        ]
    )
    return forms


def trivalent_channel_projector_forms(output_label=0, multiplicity=0):
    return [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
        {
            "kind": "fuse",
            "inputs": ["A.right", "B.left"],
            "output": "coupon.tail",
            "output_label": output_label,
            "multiplicity": multiplicity,
        },
        {
            "kind": "split",
            "input": "coupon.tail",
            "outputs": ["A.right", "B.left"],
            "output_labels": [1, 1],
            "multiplicity": multiplicity,
        },
        {"kind": "cap", "strands": ["B.left", "B.right"]},
        {"kind": "cap", "strands": ["A.left", "A.right"]},
    ]


def test_rotation_plan_preserves_order_and_reaches_target():
    a, b, c, d = (Leaf(name, 0) for name in "abcd")
    source = Node(Node(Node(a, b), c), d)
    target = Node(a, Node(b, Node(c, d)))
    for path, direction in rotation_plan(source, target):
        source = rotate_shape(source, path, direction)
    assert source == target
    assert [leaf.strand for leaf in leaves(source)] == list("abcd")


def test_unknot_and_kink_normalizations():
    evaluator = MorseEvaluator(SemionCategory())
    assert evaluator.fixed_label_value(unknot_forms(), {"A": 1})[0] == 1.0
    assert evaluator.fixed_label_value(unknot_forms(kink=True), {"A": 1})[0] == 1.0j
    assert evaluator.omega_value(tuple(unknot_forms()))[0] == 2.0


def test_compact_state_backend_matches_object_backend_across_core_events():
    category = SemionCategory()
    ordinary = MorseEvaluator(category, state_backend="object")
    compact = MorseEvaluator(
        category, state_backend="compact", compact_state_threshold=8
    )
    cases = (
        (unknot_forms(kink=True), {"A": 1}, None),
        (block_r2_forms(), {"A": 1, "B": 1, "C": 0}, None),
        (middle_vacuum_projector_forms(), {"A": 1, "B": 1}, None),
        (trivalent_channel_projector_forms(), {"A": 1, "B": 1}, None),
        (
            middle_vacuum_projector_forms(),
            {"A": 1, "B": 1},
            {"middle-0": (0, 1)},
        ),
    )
    for forms, labels, path_ranges in cases:
        expected, _ = ordinary.fixed_label_value(
            forms, labels, projector_path_ranges=path_ranges
        )
        observed, stats = compact.fixed_label_value(
            forms, labels, projector_path_ranges=path_ranges
        )
        assert abs(observed - expected) < 1e-12
        assert stats["state_backend"] == "compact-integer-arena"
        assert stats["state_backend_stats"]["node_count"] is not None
    assert stats["state_backend_stats"]["compactions"] > 0


def test_cap_reuses_existing_pair_subtree_without_f_rotation():
    evaluator = MorseEvaluator(SemionCategory())
    value, stats = evaluator.fixed_label_value(
        parallel_unlink_forms(), {"A": 1, "B": 1}
    )
    assert value == 1.0
    assert stats["f_rotations"] == 0
    assert [plan["f_rotations"] for plan in stats["plans"]] == [0, 0]


def test_reversing_pseudoreal_unknot_orientation_preserves_value():
    category = PseudorealSemionCategory()
    ordinary = MorseEvaluator(category)
    reversed_orientation = MorseEvaluator(
        category, reversed_orientation_components=("A",)
    )
    expected = ordinary.fixed_label_value(unknot_forms(), {"A": 1})[0]
    observed = reversed_orientation.fixed_label_value(unknot_forms(), {"A": 1})[0]
    assert abs(observed - expected) < 1e-12


def test_block_planner_uses_two_block_braids_for_r2_pair():
    evaluator = MorseEvaluator(SemionCategory())
    value, stats = evaluator.fixed_label_value(
        block_r2_forms(), {"A": 1, "B": 1, "C": 0}
    )
    assert abs(value - 1.0) < 1e-12
    assert stats["block_r"] == 2


def test_unit_components_are_pruned_without_changing_value():
    evaluator = MorseEvaluator(SemionCategory())
    value, stats = evaluator.fixed_label_value(
        block_r2_forms(), {"A": 1, "B": 0, "C": 0}
    )
    assert abs(value - 1.0) < 1e-12
    assert stats["unit_pruned_components"] == ["B", "C"]


def test_vacuum_projector_keeps_collective_unit_channel_not_individual_units():
    evaluator = MorseEvaluator(SemionCategory())
    value, stats = evaluator.fixed_label_value(
        middle_vacuum_projector_forms(), {"A": 1, "B": 1}
    )
    assert abs(value - 1.0) < 1e-12
    assert stats["vacuum_projectors"] == 1

    vanished, vanished_stats = evaluator.fixed_label_value(
        middle_vacuum_projector_forms(), {"A": 1, "B": 0}
    )
    assert abs(vanished) < 1e-12
    assert vanished_stats["vanishing_reason"] == (
        "empty support after fusion-channel projection"
    )


def test_vacuum_projector_is_idempotent():
    evaluator = MorseEvaluator(SemionCategory())
    once = evaluator.fixed_label_value(
        middle_vacuum_projector_forms(1), {"A": 1, "B": 1}
    )[0]
    twice = evaluator.fixed_label_value(
        middle_vacuum_projector_forms(2), {"A": 1, "B": 1}
    )[0]
    assert abs(once - twice) < 1e-12


def test_vacuum_projector_retains_all_unit_root_path_copies():
    class PathBasisOnly:
        unit = 0
        pivotal_profile = make_test_pivotal_profile(category_id="test-path-basis-only")

    category = PathBasisOnly()
    leaf_trees = [Leaf(name, 2) for name in "abcd"]
    leaf_states = [LeafState(name) for name in "abcd"]
    tree = Node(
        leaf_trees[0], Node(leaf_trees[1], Node(leaf_trees[2], leaf_trees[3]))
    )
    vector = {}
    for inner_channel in (0, 1, 2):
        inner = NodeState(
            leaf_states[2], leaf_states[3], inner_channel, 0
        )
        middle = NodeState(leaf_states[1], inner, 2, 0)
        state = NodeState(leaf_states[0], middle, 0, 0)
        vector[state] = complex(inner_channel + 1)
    projected_tree, projected, stats = project_vacuum_interval(
        category, tree, vector, 0, 4
    )
    assert projected_tree == tree
    assert projected == vector
    assert stats["support_after"] == 3


def test_vacuum_projector_fails_closed_without_orthonormal_basis_claim():
    class UnsafeCategory:
        unit = 0

    tree = Leaf("a", 0)
    vector = {LeafState("a"): 1.0 + 0.0j}
    try:
        project_vacuum_interval(UnsafeCategory(), tree, vector, 0, 1)
    except ValueError as exc:
        assert "no explicit pivotal profile" in str(exc)
    else:
        raise AssertionError("unsafe category adapter was accepted")


def test_right_comb_vacuum_basis_is_collective_and_multiplicity_aware():
    semion = SemionCategory()
    assert right_comb_fusion_path_counts(semion, (1, 1)) == {0: 1}
    assert right_comb_fusion_path_counts(semion, (1, 0)) == {1: 1}

    rep_a4 = RepA4FusionRules()
    counts = right_comb_fusion_path_counts(rep_a4, (3, 3, 3, 3))
    assert counts[0] == 7
    tree, basis = right_comb_fusion_path_basis(
        rep_a4,
        ((f"x{index}", 3) for index in range(4)),
        target=0,
    )
    assert tree is not None
    assert len(basis) == 7
    assert len(set(basis)) == 7


def test_graph_coupon_basis_applies_variance_and_keeps_all_unit_paths():
    coupon = {
        "kind": "vacuum-projector-coupon",
        "factor_order": [
            {
                "cut_id": "cut1",
                "component": "A",
                "variance": "label",
            },
            {
                "cut_id": "cut2",
                "component": "B",
                "variance": "dual",
            },
        ],
    }
    tree, basis, metadata = vacuum_coupon_path_basis(
        SemionCategory(), coupon, {"A": 1, "B": 1}
    )
    assert tree is not None
    assert len(basis) == 1
    assert metadata["root_multiplicity_rank"] == 1
    assert metadata["projector_formula"] == "sum_mu |mu><mu|"

    _, forbidden, forbidden_metadata = vacuum_coupon_path_basis(
        SemionCategory(), coupon, {"A": 1, "B": 0}
    )
    assert forbidden == ()
    assert forbidden_metadata["root_multiplicity_rank"] == 0


def test_explicit_fuse_split_events_realize_a_channel_projector():
    evaluator = MorseEvaluator(SemionCategory())
    expected = evaluator.fixed_label_value(
        parallel_unlink_forms(), {"A": 1, "B": 1}
    )[0]
    observed, stats = evaluator.fixed_label_value(
        trivalent_channel_projector_forms(), {"A": 1, "B": 1}
    )
    assert abs(observed - expected) < 1e-12
    assert stats["fusions"] == 1
    assert stats["splits"] == 1


def test_explicit_trivalent_events_preserve_the_selected_multiplicity_copy():
    category = RepA4FusionRules()
    tree = Node(Leaf("a", 3), Leaf("b", 3))
    state0 = NodeState(LeafState("a"), LeafState("b"), 3, 0)
    state1 = NodeState(LeafState("a"), LeafState("b"), 3, 1)
    fused_tree, fused = fuse_active_pair(
        category,
        tree,
        {state0: 2.0, state1: 3.0},
        (),
        output_strand="tail",
        output_label=3,
        multiplicity=1,
    )
    assert fused_tree == Leaf("tail", 3)
    assert fused == {LeafState("tail"): 3.0}

    split_tree, split = split_active_wire(
        category,
        fused_tree,
        fused,
        (),
        left_strand="a",
        left_label=3,
        right_strand="b",
        right_label=3,
        multiplicity=1,
    )
    assert split_tree == tree
    assert split == {state1: 3.0}


def test_compiled_path_sum_matches_horizontal_vacuum_projector():
    category = SemionCategory()
    evaluator = MorseEvaluator(category)
    prefix = [
        {"kind": "cup", "piece": "A", "at": "far-left"},
        {"kind": "cup", "piece": "B", "at": "far-right"},
    ]
    suffix = [
        {"kind": "cap", "strands": ["B.left", "B.right"]},
        {"kind": "cap", "strands": ["A.left", "A.right"]},
    ]
    horizontal = [
        *prefix,
        {
            "kind": "vacuum-projector",
            "projector_id": "direct",
            "strands": ["A.right", "B.left"],
        },
        *suffix,
    ]
    expected = evaluator.fixed_label_value(
        horizontal, {"A": 1, "B": 1}
    )[0]

    tree, basis = right_comb_fusion_path_basis(
        category,
        (("A.right", 1), ("B.left", 1)),
        target=category.unit,
    )
    observed = 0.0 + 0.0j
    for basis_index, state in enumerate(basis):
        term = compile_right_comb_projector_term(
            tree,
            state,
            unit=category.unit,
            namespace=f"control.mu{basis_index}",
        )
        value, stats = evaluator.fixed_label_value(
            [*prefix, *term, *suffix], {"A": 1, "B": 1}
        )
        assert stats["fusions"] == 1
        assert stats["splits"] == 1
        observed += value
    assert abs(observed - expected) < 1e-12


def test_vacuum_projector_path_ranges_partition_canonical_basis():
    category = TwoCopyBendCategory()
    tree, basis = right_comb_fusion_path_basis(
        category,
        ((f"factor-{index}", 1) for index in range(4)),
        target=category.unit,
    )
    assert tree is not None
    assert len(basis) > 1
    vector = {
        state: complex(index + 1, -(index + 1))
        for index, state in enumerate(basis)
    }

    full_tree, full, full_stats = project_vacuum_interval(
        category, tree, vector, 0, 4
    )
    midpoint = len(basis) // 2
    left_tree, left, left_stats = project_vacuum_interval(
        category, tree, vector, 0, 4, path_range=(0, midpoint)
    )
    right_tree, right, right_stats = project_vacuum_interval(
        category,
        tree,
        vector,
        0,
        4,
        path_range=(midpoint, len(basis)),
    )

    assert full_tree == left_tree == right_tree == tree
    assert {
        state: left.get(state, 0.0) + right.get(state, 0.0)
        for state in full
    } == full
    assert full_stats["canonical_path_basis_rank"] is None
    assert left_stats["canonical_path_basis_rank"] == len(basis)
    assert right_stats["canonical_path_basis_rank"] == len(basis)
    assert left_stats["selected_path_range"] == [0, midpoint]
    assert right_stats["selected_path_range"] == [midpoint, len(basis)]


def test_fixed_label_projector_path_ranges_sum_to_monolithic_value():
    category = SemionCategory()
    evaluator = MorseEvaluator(category)
    forms = middle_vacuum_projector_forms()
    labels = {"A": 1, "B": 1}

    expected, _ = evaluator.fixed_label_value(forms, labels)
    first, first_stats = evaluator.fixed_label_value(
        forms,
        labels,
        projector_path_ranges={"middle-0": (0, 1)},
    )
    empty, empty_stats = evaluator.fixed_label_value(
        forms,
        labels,
        projector_path_ranges={"middle-0": (0, 0)},
    )

    assert abs(first + empty - expected) < 1e-12
    projector_plan = next(
        plan for plan in first_stats["plans"] if plan["kind"] == "vacuum-projector"
    )
    assert projector_plan["canonical_path_basis_rank"] == 1
    assert projector_plan["selected_path_range"] == [0, 1]
    assert empty == 0.0
    assert empty_stats["vanishing_reason"] == (
        "empty support after fusion-channel projection"
    )


def test_compiled_projector_terms_cover_every_rep_a4_unit_path():
    category = RepA4FusionRules()
    tree, basis = right_comb_fusion_path_basis(
        category,
        ((f"x{index}", 3) for index in range(4)),
        target=category.unit,
    )
    programs = [
        compile_right_comb_projector_term(
            tree,
            state,
            unit=category.unit,
            namespace=f"rep-a4.mu{index}",
        )
        for index, state in enumerate(basis)
    ]
    assert len(programs) == 7
    assert all(len(program) == 6 for program in programs)
    signatures = {
        tuple(
            (form["kind"], form["output_label"] if form["kind"] == "fuse" else tuple(form["output_labels"]), form["multiplicity"])
            for form in program
        )
        for program in programs
    }
    assert len(signatures) == 7


def test_explicit_rigidity_events_close_an_internal_channel_to_its_dimension():
    evaluator = MorseEvaluator(RepA4FusionRules())
    forms = [
        {
            "kind": "coevaluation",
            "strands": ["q", "qdual"],
            "labels": [3, 3],
            "dimension_label": 3,
            "at": "far-left",
        },
        {
            "kind": "evaluation",
            "strands": ["q", "qdual"],
            "dimension_label": 3,
        },
    ]
    value, stats = evaluator.fixed_label_value(forms, {})
    assert abs(value - 3.0) < 1e-12
    assert stats["coevaluations"] == 1
    assert stats["evaluations"] == 1


def test_semion_left_and_right_bends_are_unitary_one_by_one():
    category = SemionCategory()
    for bend in (left_bend_fusion_matrix, right_bend_fusion_matrix):
        matrix = bend(category, 1, 1, 0)
        assert matrix["source_basis"] == (0,)
        assert matrix["target_basis"] == (0,)
        assert abs(abs(matrix["entries"][0][0]) - 1.0) < 1e-12
        assert matrix["fs_flag_reversal_included"] is False


def test_bends_keep_both_multiplicity_copies_distinct_and_unitary():
    category = TwoCopyBendCategory()
    for bend in (left_bend_fusion_matrix, right_bend_fusion_matrix):
        matrix = bend(category, 1, 1, 1)
        assert matrix["source_basis"] == (0, 1)
        assert matrix["target_basis"] == (0, 1)
        entries = matrix["entries"]
        for row in range(2):
            for column in range(2):
                gram = sum(
                    entries[index][row].conjugate() * entries[index][column]
                    for index in range(2)
                )
                assert abs(gram - float(row == column)) < 1e-12
        assert abs(entries[0][1]) < 1e-12
        assert abs(entries[1][0]) < 1e-12


def test_horizontal_corridor_identity_and_projector_preserve_collective_vacuum():
    evaluator = MorseEvaluator(SemionCategory())
    base = parallel_unlink_forms()
    expected = evaluator.fixed_label_value(base, {"A": 1, "B": 1})[0]

    identity = insert_horizontal_projector(
        base,
        before_form_index=2,
        strands=("A.left", "B.right"),
        projector_id="corridor-control",
        identity_projector=True,
    )
    assert len(identity["gather"]) == 2
    assert len(identity["inverse_gather"]) == 2
    observed_identity = evaluator.fixed_label_value(
        identity["compiled_forms"], {"A": 1, "B": 1}
    )[0]
    assert abs(observed_identity - expected) < 1e-12

    projected = insert_horizontal_projector(
        base,
        before_form_index=2,
        strands=("A.left", "B.right"),
        projector_id="corridor-control",
    )
    observed_projected = evaluator.fixed_label_value(
        projected["compiled_forms"], {"A": 1, "B": 1}
    )[0]
    assert abs(observed_projected - expected) < 1e-12


def test_one_puncture_special_disk_only_allows_the_unit_label():
    builder = MorseBuilder()
    builder.cup("red1", at="far-left")
    builder.cup("A1", at="far-right")
    builder.cross(over="A1.left", under="red1.right")
    builder.cross(over="red1.left", under="A1.left")
    builder.cap("red1")
    builder.cap("A1")
    ir = compile_projected_morphism(
        builder.forms,
        component_by_piece={"red1": "red", "A1": "A"},
        special_components=("red",),
    )
    linearized = linearize_horizontal_disk_projector(builder.forms, ir)
    assert linearized["status"] == "PASS_HORIZONTAL_DISK_PROJECTOR_LINEARIZATION"
    evaluator = MorseEvaluator(SemionCategory())
    nontrivial = evaluator.fixed_label_value(
        linearized["compiled_forms"], {"A": 1}
    )[0]
    trivial = evaluator.fixed_label_value(
        linearized["compiled_forms"], {"A": 0}
    )[0]
    assert abs(nontrivial) < 1e-12
    assert abs(trivial - 1.0) < 1e-12


def test_topology_joins_multiple_pieces_into_component_a():
    forms = [
        {"kind": "cup", "piece": "A1", "at": "far-left"},
        {"kind": "cup", "piece": "A2", "at": "far-right"},
        {"kind": "cap", "strands": ["A1.right", "A2.left"]},
        {"kind": "cap", "strands": ["A1.left", "A2.right"]},
    ]
    topology = analyze_topology(forms)
    assert topology.component_order == ("A",)
