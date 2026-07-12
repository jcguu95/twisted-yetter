from experiments.sage.morse_fusion_evaluator import (
    Leaf,
    Node,
    MorseEvaluator,
    analyze_topology,
    leaves,
    rotation_plan,
    rotate_shape,
)


class SemionCategory:
    labels = (0, 1)
    unit = 0

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


def test_topology_joins_multiple_pieces_into_component_a():
    forms = [
        {"kind": "cup", "piece": "A1", "at": "far-left"},
        {"kind": "cup", "piece": "A2", "at": "far-right"},
        {"kind": "cap", "strands": ["A1.right", "A2.left"]},
        {"kind": "cap", "strands": ["A1.left", "A2.right"]},
    ]
    topology = analyze_topology(forms)
    assert topology.component_order == ("A",)
