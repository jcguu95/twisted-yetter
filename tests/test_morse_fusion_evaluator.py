from experiments.sage.morse_fusion_evaluator import (
    Leaf,
    LeafState,
    Node,
    NodeState,
    MorseEvaluator,
    analyze_topology,
    leaves,
    project_vacuum_interval,
    right_comb_fusion_path_basis,
    right_comb_fusion_path_counts,
    rotation_plan,
    rotate_shape,
    vacuum_coupon_path_basis,
)
from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import (
    compile_projected_morphism,
    insert_horizontal_projector,
    linearize_horizontal_disk_projector,
)


class SemionCategory:
    labels = (0, 1)
    unit = 0
    path_basis_is_orthonormal = True

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
    def reverse_bend(self, label):
        return -1.0 if label else 1.0


class RepA4FusionRules:
    """Fusion ring of Rep(A4), including 3 tensor 3's multiplicity two."""

    labels = (0, 1, 2, 3)
    unit = 0
    path_basis_is_orthonormal = True

    def dual(self, label):
        return {0: 0, 1: 2, 2: 1, 3: 3}[label]

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
        path_basis_is_orthonormal = True

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
        assert "orthonormal path basis" in str(exc)
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
