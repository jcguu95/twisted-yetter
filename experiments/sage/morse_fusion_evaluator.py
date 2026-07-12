"""Native Morse-diagram RT evaluator using dynamic fusion-tree bases.

The engine consumes the fundamental ``cup``/``cap``/``cross``/``kink`` forms
produced by :mod:`experiments.scripts.morse_dsl`.  It deliberately does not
convert the diagram to a braid.  Category-specific data enter through the
small ``MorseCategory`` protocol documented by :class:`MorseEvaluator`.

This is floating-point research infrastructure.  The implementation supports
fusion multiplicities: basis states retain every trivalent-vertex
multiplicity index, F rotations use complete F blocks, and sibling braids use
complete R blocks.

Current safety boundary: only explicitly recorded category and diagram
controls are validated.  Loaded F/R adapters may also need a documented path-
basis conversion before their cup/cap normalization is compatible with this
engine.
"""

from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
import math
from typing import Any, Iterable


TOLERANCE = 1e-13


@dataclass(frozen=True)
class Leaf:
    strand: str
    label: Any


@dataclass(frozen=True)
class Node:
    left: "Tree"
    right: "Tree"


Tree = Leaf | Node


@dataclass(frozen=True)
class LeafState:
    strand: str


@dataclass(frozen=True)
class NodeState:
    left: "State"
    right: "State"
    output: Any
    multiplicity: int


State = LeafState | NodeState


def leaf_count(tree: Tree) -> int:
    if isinstance(tree, Leaf):
        return 1
    return leaf_count(tree.left) + leaf_count(tree.right)


def leaves(tree: Tree) -> tuple[Leaf, ...]:
    if isinstance(tree, Leaf):
        return (tree,)
    return leaves(tree.left) + leaves(tree.right)


def root_label(tree: Tree, state: State) -> Any:
    if isinstance(tree, Leaf):
        if not isinstance(state, LeafState) or state.strand != tree.strand:
            raise ValueError("leaf/tree state mismatch")
        return tree.label
    if not isinstance(state, NodeState):
        raise ValueError("node/tree state mismatch")
    return state.output


def right_comb(items: Iterable[Tree]) -> Tree:
    items = tuple(items)
    if not items:
        raise ValueError("a nonempty item list is required")
    tree = items[-1]
    for item in reversed(items[:-1]):
        tree = Node(item, tree)
    return tree


def subtree_at(tree: Tree, path: tuple[int, ...]) -> Tree:
    current = tree
    for direction in path:
        if not isinstance(current, Node):
            raise ValueError(f"path descends through a leaf: {path!r}")
        current = current.left if direction == 0 else current.right
    return current


def replace_subtree(tree: Tree, path: tuple[int, ...], replacement: Tree) -> Tree:
    if not path:
        return replacement
    if not isinstance(tree, Node):
        raise ValueError("cannot replace below a leaf")
    direction, rest = path[0], path[1:]
    if direction == 0:
        return Node(replace_subtree(tree.left, rest, replacement), tree.right)
    return Node(tree.left, replace_subtree(tree.right, rest, replacement))


def rotate_shape(tree: Tree, path: tuple[int, ...], direction: str) -> Tree:
    local = subtree_at(tree, path)
    if direction == "left-to-right":
        if not isinstance(local, Node) or not isinstance(local.left, Node):
            raise ValueError("left-to-right rotation needs ((A B) C)")
        replacement = Node(local.left.left, Node(local.left.right, local.right))
    elif direction == "right-to-left":
        if not isinstance(local, Node) or not isinstance(local.right, Node):
            raise ValueError("right-to-left rotation needs (A (B C))")
        replacement = Node(Node(local.left, local.right.left), local.right.right)
    else:
        raise ValueError(f"unknown rotation direction: {direction!r}")
    return replace_subtree(tree, path, replacement)


@lru_cache(maxsize=None)
def rotations_to_right_comb(tree: Tree) -> tuple[tuple[tuple[int, ...], str], ...]:
    """Return a deterministic rotation sequence from TREE to its right comb."""

    current = tree
    steps: list[tuple[tuple[int, ...], str]] = []

    def normalize(path: tuple[int, ...]) -> None:
        nonlocal current
        while True:
            local = subtree_at(current, path)
            if not isinstance(local, Node) or not isinstance(local.left, Node):
                break
            steps.append((path, "left-to-right"))
            current = rotate_shape(current, path, "left-to-right")
        local = subtree_at(current, path)
        if isinstance(local, Node) and isinstance(local.right, Node):
            normalize(path + (1,))

    normalize(())
    expected = right_comb(leaves(tree))
    if current != expected:
        raise AssertionError("right-comb normalization failed")
    return tuple(steps)


def shape_only(tree: Tree) -> Tree:
    if isinstance(tree, Leaf):
        return Leaf(tree.strand, None)
    return Node(shape_only(tree.left), shape_only(tree.right))


@lru_cache(maxsize=None)
def _rotation_plan_shapes(source: Tree, target: Tree) -> tuple[tuple[tuple[int, ...], str], ...]:
    if tuple(leaf.strand for leaf in leaves(source)) != tuple(leaf.strand for leaf in leaves(target)):
        raise ValueError("rotation cannot change leaf order")
    source_steps = rotations_to_right_comb(source)
    target_steps = rotations_to_right_comb(target)
    reverse_target = tuple(
        (path, "right-to-left" if direction == "left-to-right" else "left-to-right")
        for path, direction in reversed(target_steps)
    )
    plan = source_steps + reverse_target
    check = source
    for path, direction in plan:
        check = rotate_shape(check, path, direction)
    if check != target:
        raise AssertionError("rotation plan does not reach target")
    return plan


def rotation_plan(source: Tree, target: Tree) -> tuple[tuple[tuple[int, ...], str], ...]:
    return _rotation_plan_shapes(shape_only(source), shape_only(target))


def grouped_target(tree: Tree, start: int, stop: int, *, split: int | None = None) -> tuple[Tree, tuple[int, ...]]:
    """Group leaves ``[start:stop]`` as one subtree, optionally with two children.

    ``split`` is an absolute leaf index.  When supplied, the grouped subtree is
    ``Node(right_comb(start:split), right_comb(split:stop))``.  The returned
    path locates that grouped subtree in the target tree.
    """

    ordered = leaves(tree)
    if not (0 <= start < stop <= len(ordered)):
        raise ValueError("bad grouped interval")
    if split is None:
        grouped = right_comb(ordered[start:stop])
    else:
        if not (start < split < stop):
            raise ValueError("split must lie strictly inside grouped interval")
        grouped = Node(right_comb(ordered[start:split]), right_comb(ordered[split:stop]))
    items: list[Tree] = [*ordered[:start], grouped, *ordered[stop:]]
    target = right_comb(items)
    wanted = frozenset(leaf.strand for leaf in ordered[start:stop])
    path = find_subtree_path(target, wanted)
    return target, path


def find_subtree_path(tree: Tree, wanted: frozenset[str], path: tuple[int, ...] = ()) -> tuple[int, ...]:
    here = frozenset(leaf.strand for leaf in leaves(tree))
    if here == wanted:
        return path
    if not isinstance(tree, Node):
        raise ValueError(f"no subtree has leaves {sorted(wanted)!r}")
    left_set = frozenset(leaf.strand for leaf in leaves(tree.left))
    if wanted <= left_set:
        return find_subtree_path(tree.left, wanted, path + (0,))
    right_set = frozenset(leaf.strand for leaf in leaves(tree.right))
    if wanted <= right_set:
        return find_subtree_path(tree.right, wanted, path + (1,))
    raise ValueError(f"wanted leaves are not a subtree: {sorted(wanted)!r}")


def matrix_entry(matrix: Any, row: int, column: int) -> complex:
    try:
        return complex(matrix[row, column])
    except (TypeError, IndexError):
        return complex(matrix[row][column])


def _state_at(state: State, path: tuple[int, ...]) -> State:
    current = state
    for direction in path:
        if not isinstance(current, NodeState):
            raise ValueError("state path descends through a leaf")
        current = current.left if direction == 0 else current.right
    return current


def _replace_state(state: State, path: tuple[int, ...], replacement: State) -> State:
    if not path:
        return replacement
    if not isinstance(state, NodeState):
        raise ValueError("cannot replace below a leaf state")
    direction, rest = path[0], path[1:]
    if direction == 0:
        return NodeState(_replace_state(state.left, rest, replacement), state.right, state.output, state.multiplicity)
    return NodeState(state.left, _replace_state(state.right, rest, replacement), state.output, state.multiplicity)


def _prune(vector: dict[State, complex], tolerance: float = TOLERANCE) -> dict[State, complex]:
    return {state: value for state, value in vector.items() if abs(value) > tolerance}


def rotate_vector(category: Any, tree: Tree, vector: dict[State, complex], path: tuple[int, ...], direction: str):
    local_tree = subtree_at(tree, path)
    output: dict[State, complex] = defaultdict(complex)
    for state, amplitude in vector.items():
        local_state = _state_at(state, path)
        if direction == "left-to-right":
            if not isinstance(local_tree, Node) or not isinstance(local_tree.left, Node):
                raise ValueError("bad left-to-right local tree")
            if not isinstance(local_state, NodeState) or not isinstance(local_state.left, NodeState):
                raise ValueError("bad left-to-right local state")
            a_tree, b_tree, c_tree = local_tree.left.left, local_tree.left.right, local_tree.right
            ab_state, c_state = local_state.left, local_state.right
            a_state, b_state = ab_state.left, ab_state.right
            a = root_label(a_tree, a_state)
            b = root_label(b_tree, b_state)
            c = root_label(c_tree, c_state)
            d = local_state.output
            block = category.f_block(a, b, c, d)
            left_key = (ab_state.output, ab_state.multiplicity, local_state.multiplicity)
            left_index = block["left_index"][left_key]
            inverse = block["left_to_right"]
            for right_index, right_key in enumerate(block["right_basis"]):
                coefficient = matrix_entry(inverse, right_index, left_index)
                if abs(coefficient) <= TOLERANCE:
                    continue
                y, bc_mult, ay_mult = right_key
                replacement = NodeState(a_state, NodeState(b_state, c_state, y, bc_mult), d, ay_mult)
                output[_replace_state(state, path, replacement)] += coefficient * amplitude
        elif direction == "right-to-left":
            if not isinstance(local_tree, Node) or not isinstance(local_tree.right, Node):
                raise ValueError("bad right-to-left local tree")
            if not isinstance(local_state, NodeState) or not isinstance(local_state.right, NodeState):
                raise ValueError("bad right-to-left local state")
            a_tree, b_tree, c_tree = local_tree.left, local_tree.right.left, local_tree.right.right
            a_state, bc_state = local_state.left, local_state.right
            b_state, c_state = bc_state.left, bc_state.right
            a = root_label(a_tree, a_state)
            b = root_label(b_tree, b_state)
            c = root_label(c_tree, c_state)
            d = local_state.output
            block = category.f_block(a, b, c, d)
            right_key = (bc_state.output, bc_state.multiplicity, local_state.multiplicity)
            right_index = block["right_index"][right_key]
            matrix = block["right_to_left"]
            for left_index, left_key in enumerate(block["left_basis"]):
                coefficient = matrix_entry(matrix, left_index, right_index)
                if abs(coefficient) <= TOLERANCE:
                    continue
                x, ab_mult, xc_mult = left_key
                replacement = NodeState(NodeState(a_state, b_state, x, ab_mult), c_state, d, xc_mult)
                output[_replace_state(state, path, replacement)] += coefficient * amplitude
        else:
            raise ValueError(f"unknown rotation direction: {direction!r}")
    return rotate_shape(tree, path, direction), _prune(dict(output))


def apply_rotation_plan(category: Any, tree: Tree, vector: dict[State, complex], plan):
    for path, direction in plan:
        tree, vector = rotate_vector(category, tree, vector, path, direction)
    return tree, vector


def braid_siblings(category: Any, tree: Tree, vector: dict[State, complex], path: tuple[int, ...], positive: bool):
    local_tree = subtree_at(tree, path)
    if not isinstance(local_tree, Node):
        raise ValueError("braid needs a node")
    output: dict[State, complex] = defaultdict(complex)
    for state, amplitude in vector.items():
        local_state = _state_at(state, path)
        if not isinstance(local_state, NodeState):
            raise ValueError("braid needs a node state")
        a = root_label(local_tree.left, local_state.left)
        b = root_label(local_tree.right, local_state.right)
        matrix = category.r_matrix(a, b, local_state.output, positive)
        for target_mult in range(category.fusion_multiplicity(b, a, local_state.output)):
            coefficient = matrix_entry(matrix, target_mult, local_state.multiplicity)
            if abs(coefficient) <= TOLERANCE:
                continue
            replacement = NodeState(local_state.right, local_state.left, local_state.output, target_mult)
            output[_replace_state(state, path, replacement)] += coefficient * amplitude
    swapped = replace_subtree(tree, path, Node(local_tree.right, local_tree.left))
    return swapped, _prune(dict(output))


class UnionFind:
    def __init__(self) -> None:
        self.parent: dict[str, str] = {}

    def add(self, item: str) -> None:
        self.parent.setdefault(item, item)

    def find(self, item: str) -> str:
        self.add(item)
        if self.parent[item] != item:
            self.parent[item] = self.find(self.parent[item])
        return self.parent[item]

    def union(self, left: str, right: str) -> None:
        left_root, right_root = self.find(left), self.find(right)
        if left_root != right_root:
            self.parent[right_root] = left_root


def piece_of(strand: str) -> str:
    return strand.rsplit(".", 1)[0]


def side_sign(strand: str) -> int:
    return 1 if strand.endswith(".left") else -1


def canonical_component_name(strands: Iterable[str]) -> str:
    pieces = sorted({piece_of(strand) for strand in strands})
    if pieces and all(piece.startswith("A") for piece in pieces):
        return "A"
    return pieces[0] if len(pieces) == 1 else "+".join(pieces)


@dataclass(frozen=True)
class MorseTopology:
    component_order: tuple[str, ...]
    component_by_strand: dict[str, str]
    piece_orientation: dict[str, int]

    def strand_orientation(self, strand: str) -> int:
        return side_sign(strand) * self.piece_orientation[piece_of(strand)]


def analyze_topology(forms: Iterable[dict[str, Any]]) -> MorseTopology:
    forms = tuple(forms)
    uf = UnionFind()
    pieces: set[str] = set()
    caps: list[tuple[str, str]] = []
    for form in forms:
        if form["kind"] == "cup":
            piece = form["piece"]
            pieces.add(piece)
            left, right = f"{piece}.left", f"{piece}.right"
            uf.union(left, right)
        elif form["kind"] == "cap":
            left, right = form["strands"]
            caps.append((left, right))
            uf.union(left, right)

    graph: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for left, right in caps:
        left_piece, right_piece = piece_of(left), piece_of(right)
        relation = -side_sign(left) * side_sign(right)
        graph[left_piece].append((right_piece, relation))
        graph[right_piece].append((left_piece, relation))
    orientations: dict[str, int] = {}
    for start in sorted(pieces):
        if start in orientations:
            continue
        orientations[start] = 1
        queue = deque([start])
        while queue:
            current = queue.popleft()
            for neighbor, relation in graph[current]:
                expected = orientations[current] * relation
                if neighbor not in orientations:
                    orientations[neighbor] = expected
                    queue.append(neighbor)
                elif orientations[neighbor] != expected:
                    raise ValueError("Morse cap constraints give inconsistent orientations")

    groups: dict[str, list[str]] = defaultdict(list)
    for strand in uf.parent:
        groups[uf.find(strand)].append(strand)
    names = {root: canonical_component_name(strands) for root, strands in groups.items()}
    component_by_strand = {
        strand: names[uf.find(strand)]
        for strand in uf.parent
    }
    component_order = tuple(sorted(set(names.values()), key=lambda name: (name != "A", name)))
    return MorseTopology(component_order, component_by_strand, orientations)


def prune_unit_components(
    forms: Iterable[dict[str, Any]],
    topology: MorseTopology,
    retained_components: frozenset[str],
) -> tuple[dict[str, Any], ...]:
    """Erase tensor-unit components while preserving the surviving planar order."""

    full_order: list[str] = []
    kept_order: list[str] = []
    output: list[dict[str, Any]] = []

    def cup_gap(order: list[str], form: dict[str, Any]) -> int:
        if form.get("at") == "far-left":
            return 0
        if form.get("at") == "far-right":
            return len(order)
        if "between" in form:
            left, right = form["between"]
            return order.index(left) + 1
        if "after" in form:
            return order.index(form["after"]) + 1
        raise ValueError(f"unsupported cup placement: {form!r}")

    for form in forms:
        kind = form["kind"]
        if kind == "cup":
            full_gap = cup_gap(full_order, form)
            piece = form["piece"]
            pair = [f"{piece}.left", f"{piece}.right"]
            component = topology.component_by_strand[pair[0]]
            if component in retained_components:
                kept_gap = sum(
                    strand in kept_order for strand in full_order[:full_gap]
                )
                new_form = {"kind": "cup", "piece": piece}
                if kept_gap == 0:
                    new_form["at"] = "far-left"
                elif kept_gap == len(kept_order):
                    new_form["at"] = "far-right"
                else:
                    new_form["between"] = [kept_order[kept_gap - 1], kept_order[kept_gap]]
                output.append(new_form)
                kept_order[kept_gap:kept_gap] = pair
            full_order[full_gap:full_gap] = pair
        elif kind == "cross":
            over, under = form["over"], form["under"]
            io, iu = full_order.index(over), full_order.index(under)
            if over in kept_order and under in kept_order:
                ko, ku = kept_order.index(over), kept_order.index(under)
                if abs(ko - ku) != 1:
                    raise ValueError("unit pruning produced nonadjacent surviving crossing")
                output.append(dict(form))
                kept_order[ko], kept_order[ku] = kept_order[ku], kept_order[ko]
            full_order[io], full_order[iu] = full_order[iu], full_order[io]
        elif kind == "cap":
            left, right = form["strands"]
            if left in kept_order:
                if right not in kept_order or abs(kept_order.index(left) - kept_order.index(right)) != 1:
                    raise ValueError("unit pruning produced malformed cap")
                output.append(dict(form))
                kept_order = [strand for strand in kept_order if strand not in {left, right}]
            full_order = [strand for strand in full_order if strand not in {left, right}]
        elif kind == "kink":
            if topology.component_by_strand[form["strand"]] in retained_components:
                output.append(dict(form))
        else:
            raise ValueError(f"unsupported form during unit pruning: {form!r}")
    if full_order or kept_order:
        raise ValueError("unit-pruned replay did not close")
    return tuple(output)


def fusion_index(category: Any, left: Any, right: Any, output: Any) -> int:
    multiplicity = category.fusion_multiplicity(left, right, output)
    if multiplicity != 1:
        raise ValueError(
            f"unit insertion/removal expected a unique channel: {left!r}*{right!r}->{output!r}, "
            f"multiplicity={multiplicity}"
        )
    return 0


def insert_pair(category: Any, tree: Tree | None, state: State | None, gap: int, pair_tree: Node, pair_state: NodeState):
    if tree is None:
        if gap != 0 or state is not None:
            raise ValueError("bad empty cup insertion")
        return pair_tree, pair_state
    if state is None:
        raise ValueError("nonempty tree needs state")
    count = leaf_count(tree)
    if not (0 <= gap <= count):
        raise ValueError("cup gap is outside active order")
    current_root = root_label(tree, state)
    if gap == 0:
        mult = fusion_index(category, category.unit, current_root, current_root)
        return Node(pair_tree, tree), NodeState(pair_state, state, current_root, mult)
    if gap == count:
        mult = fusion_index(category, current_root, category.unit, current_root)
        return Node(tree, pair_tree), NodeState(state, pair_state, current_root, mult)
    if not isinstance(tree, Node) or not isinstance(state, NodeState):
        raise ValueError("interior insertion requires a node")
    left_count = leaf_count(tree.left)
    if gap <= left_count:
        new_left, new_left_state = insert_pair(category, tree.left, state.left, gap, pair_tree, pair_state)
        return Node(new_left, tree.right), NodeState(new_left_state, state.right, state.output, state.multiplicity)
    new_right, new_right_state = insert_pair(
        category, tree.right, state.right, gap - left_count, pair_tree, pair_state
    )
    return Node(tree.left, new_right), NodeState(state.left, new_right_state, state.output, state.multiplicity)


_REMOVED = object()
_REJECTED = object()


def remove_pair(category: Any, tree: Tree, state: State, path: tuple[int, ...]):
    if not path:
        if not isinstance(tree, Node) or not isinstance(state, NodeState):
            raise ValueError("cap target is not a pair node")
        if state.output != category.unit or state.multiplicity != 0:
            return _REJECTED, _REJECTED
        return _REMOVED, _REMOVED
    if not isinstance(tree, Node) or not isinstance(state, NodeState):
        raise ValueError("cap path descends through a leaf")
    direction, rest = path[0], path[1:]
    if direction == 0:
        new_tree, new_state = remove_pair(category, tree.left, state.left, rest)
        if new_tree is _REJECTED:
            return _REJECTED, _REJECTED
        if new_tree is _REMOVED:
            sibling_label = root_label(tree.right, state.right)
            if state.output != sibling_label or state.multiplicity != fusion_index(
                category, category.unit, sibling_label, sibling_label
            ):
                return _REJECTED, _REJECTED
            return tree.right, state.right
        return Node(new_tree, tree.right), NodeState(new_state, state.right, state.output, state.multiplicity)
    new_tree, new_state = remove_pair(category, tree.right, state.right, rest)
    if new_tree is _REJECTED:
        return _REJECTED, _REJECTED
    if new_tree is _REMOVED:
        sibling_label = root_label(tree.left, state.left)
        if state.output != sibling_label or state.multiplicity != fusion_index(
            category, sibling_label, category.unit, sibling_label
        ):
            return _REJECTED, _REJECTED
        return tree.left, state.left
    return Node(tree.left, new_tree), NodeState(state.left, new_state, state.output, state.multiplicity)


@dataclass
class EvaluationStats:
    f_rotations: int = 0
    leaf_r: int = 0
    block_r: int = 0
    cups: int = 0
    caps: int = 0
    kinks: int = 0
    max_active_strands: int = 0
    max_state_support: int = 1
    plans: list[dict[str, Any]] | None = None

    def __post_init__(self) -> None:
        if self.plans is None:
            self.plans = []


class MorseEvaluator:
    """Evaluate fixed-label or Kirby-colored closed Morse diagrams.

    A category adapter must provide ``labels``, ``unit``, ``dual(label)``,
    ``dimension(label)``, ``twist(label)``, ``fusion_multiplicity(a,b,c)``,
    ``f_block(a,b,c,d)``, and ``r_matrix(a,b,c,positive)``.  F blocks use the
    repository convention ``right_to_left`` and its inverse
    ``left_to_right`` with basis triples ``(channel, mult_1, mult_2)``.
    ``reverse_bend(label)`` supplies the pivotal correction for a cup whose
    left branch is downward-oriented.
    """

    def __init__(
        self,
        category: Any,
        *,
        f_weight: float | None = None,
        r_weight: float | None = None,
        beam_width: int = 16,
        planner_mode: str = "hybrid",
        reversed_orientation_components: Iterable[str] = (),
    ):
        self.category = category
        profile = getattr(category, "cost_profile", lambda: {"f": 4.0, "r": 1.0})()
        self.f_weight = float(profile["f"] if f_weight is None else f_weight)
        self.r_weight = float(profile["r"] if r_weight is None else r_weight)
        self.beam_width = int(beam_width)
        if planner_mode not in {"hybrid", "sequential"}:
            raise ValueError("planner_mode must be 'hybrid' or 'sequential'")
        self.planner_mode = planner_mode
        self.reversed_orientation_components = frozenset(
            reversed_orientation_components
        )
        if self.beam_width < 1:
            raise ValueError("beam_width must be positive")
        self._pruned_forms_cache: dict[tuple[int, frozenset[str]], tuple[dict[str, Any], ...]] = {}
        self._frontier_plan_cache: dict[tuple[Any, ...], tuple[float, tuple[int, ...]]] = {}

    def _topology(
        self, forms: Iterable[dict[str, Any]], *, allow_missing_reversed=False
    ) -> MorseTopology:
        topology = analyze_topology(forms)
        unknown = self.reversed_orientation_components - set(topology.component_order)
        if unknown and not allow_missing_reversed:
            raise ValueError(f"unknown reversed-orientation components: {sorted(unknown)!r}")
        if not self.reversed_orientation_components:
            return topology
        orientations = dict(topology.piece_orientation)
        for strand, component in topology.component_by_strand.items():
            if component in self.reversed_orientation_components:
                piece = piece_of(strand)
                orientations[piece] = -topology.piece_orientation[piece]
        return MorseTopology(
            topology.component_order, topology.component_by_strand, orientations
        )

    def _stats_payload(self, topology: MorseTopology, stats: EvaluationStats, **extra):
        return {
            "component_order": list(topology.component_order),
            "f_rotations": stats.f_rotations,
            "leaf_r": stats.leaf_r,
            "block_r": stats.block_r,
            "cups": stats.cups,
            "caps": stats.caps,
            "kinks": stats.kinks,
            "max_active_strands": stats.max_active_strands,
            "max_state_support": stats.max_state_support,
            "planner_weights": {"f": self.f_weight, "r": self.r_weight},
            "planner_mode": self.planner_mode,
            "reversed_orientation_components": sorted(
                self.reversed_orientation_components
            ),
            "plans": stats.plans,
            **extra,
        }

    @staticmethod
    def _cup_gap(order: list[str], form: dict[str, Any]) -> int:
        if form.get("at") == "far-left":
            return 0
        if form.get("at") == "far-right":
            return len(order)
        if "between" in form:
            left, right = form["between"]
            if order.index(right) != order.index(left) + 1:
                raise ValueError("cup between strands are not adjacent")
            return order.index(left) + 1
        if "after" in form:
            return order.index(form["after"]) + 1
        raise ValueError(f"unsupported cup placement: {form!r}")

    def _rotate(self, tree, vector, target, stats):
        plan = rotation_plan(tree, target)
        tree, vector = apply_rotation_plan(self.category, tree, vector, plan)
        stats.f_rotations += len(plan)
        return tree, vector, plan

    def _cross_run(self, forms, start, order):
        first = forms[start]
        over = first["over"]
        trial = list(order)
        targets = []
        direction = None
        index = start
        while index < len(forms) and forms[index]["kind"] == "cross" and forms[index]["over"] == over:
            under = forms[index]["under"]
            io, iu = trial.index(over), trial.index(under)
            if abs(io - iu) != 1:
                break
            step_direction = "right" if io < iu else "left"
            if direction is None:
                direction = step_direction
            if step_direction != direction:
                break
            targets.append(under)
            trial[io], trial[iu] = trial[iu], trial[io]
            index += 1
        return index, tuple(targets), direction

    def _cross_target(self, tree: Tree, order: list[str], over: str, targets: tuple[str, ...], direction: str):
        original = list(order)
        over_index = original.index(over)
        if direction == "right":
            expected = tuple(original[over_index + 1 : over_index + 1 + len(targets)])
            if targets != expected:
                raise ValueError("right sweep targets are not the current contiguous block")
            start, stop, split = over_index, over_index + 1 + len(targets), over_index + 1
        else:
            expected = tuple(reversed(original[over_index - len(targets) : over_index]))
            if targets != expected:
                raise ValueError("left sweep targets are not the current contiguous block")
            start, stop, split = over_index - len(targets), over_index + 1, over_index
        return grouped_target(tree, start, stop, split=split)

    def _evaluate_cross_candidate(self, tree: Tree, order: list[str], over: str, targets, direction, block: bool):
        current = tree
        total_f = 0
        if block:
            target, path = self._cross_target(current, order, over, targets, direction)
            total_f += len(rotation_plan(current, target))
            swapped = subtree_at(target, path)
            assert isinstance(swapped, Node)
            current = replace_subtree(target, path, Node(swapped.right, swapped.left))
            return current, total_f, 1, path
        trial_order = list(order)
        paths = []
        for under in targets:
            io, iu = trial_order.index(over), trial_order.index(under)
            lo = min(io, iu)
            target, path = grouped_target(current, lo, lo + 2, split=lo + 1)
            total_f += len(rotation_plan(current, target))
            local = subtree_at(target, path)
            assert isinstance(local, Node)
            current = replace_subtree(target, path, Node(local.right, local.left))
            trial_order[io], trial_order[iu] = trial_order[iu], trial_order[io]
            paths.append(path)
        return current, total_f, len(targets), tuple(paths)

    def _plan_cross_frontier(self, tree: Tree, order: list[str], over: str, targets, direction: str):
        """Beam-search all leaf/block/hybrid frontiers for one uniform sweep."""

        cache_key = (shape_only(tree), tuple(order), over, tuple(targets), direction, self.f_weight, self.r_weight)
        cached = self._frontier_plan_cache.get(cache_key)
        if cached is not None:
            cached_cost, cached_segments = cached
            return cached_cost, None, None, cached_segments, None

        # cost, progress, tree, order, segment sizes, F count
        beam = [(0.0, 0, tree, tuple(order), (), 0)]
        completed = []
        while beam:
            expanded = []
            for cost, progress, current, current_order_tuple, segments, f_count in beam:
                if progress == len(targets):
                    completed.append((cost, current, current_order_tuple, segments, f_count))
                    continue
                current_order = list(current_order_tuple)
                remaining = len(targets) - progress
                for length in range(1, remaining + 1):
                    block_targets = tuple(targets[progress : progress + length])
                    target_tree, path = self._cross_target(
                        current, current_order, over, block_targets, direction
                    )
                    f_steps = len(rotation_plan(current, target_tree))
                    local = subtree_at(target_tree, path)
                    assert isinstance(local, Node)
                    next_tree = replace_subtree(target_tree, path, Node(local.right, local.left))
                    next_order = list(current_order)
                    for under in block_targets:
                        io, iu = next_order.index(over), next_order.index(under)
                        next_order[io], next_order[iu] = next_order[iu], next_order[io]
                    expanded.append(
                        (
                            cost + f_steps * self.f_weight + self.r_weight,
                            progress + length,
                            next_tree,
                            tuple(next_order),
                            segments + (length,),
                            f_count + f_steps,
                        )
                    )
            if not expanded:
                break
            best_by_state = {}
            for item in expanded:
                key = (item[1], shape_only(item[2]))
                if key not in best_by_state or item[0] < best_by_state[key][0]:
                    best_by_state[key] = item
            beam = sorted(best_by_state.values(), key=lambda item: item[0])[: self.beam_width]
        if not completed:
            raise ValueError("cross-frontier planner found no complete path")
        selected = min(completed, key=lambda item: item[0])
        self._frontier_plan_cache[cache_key] = (selected[0], selected[3])
        return selected

    def fixed_label_value(self, forms: Iterable[dict[str, Any]], component_labels: dict[str, Any], *, _unit_pruned=False):
        forms = forms if isinstance(forms, tuple) else tuple(forms)
        topology = self._topology(
            forms, allow_missing_reversed=_unit_pruned
        )
        missing = set(topology.component_order) - set(component_labels)
        if missing:
            raise ValueError(f"missing component labels: {sorted(missing)!r}")
        if not _unit_pruned:
            retained = frozenset(
                component
                for component in topology.component_order
                if component_labels[component] != self.category.unit
            )
            if len(retained) != len(topology.component_order):
                cache_key = (id(forms), retained)
                pruned = self._pruned_forms_cache.get(cache_key)
                if pruned is None:
                    pruned = prune_unit_components(forms, topology, retained)
                    self._pruned_forms_cache[cache_key] = pruned
                value, stats = self.fixed_label_value(
                    pruned,
                    {component: component_labels[component] for component in retained},
                    _unit_pruned=True,
                )
                stats = dict(stats)
                stats["unit_pruned_components"] = sorted(set(topology.component_order) - retained)
                stats["original_component_order"] = list(topology.component_order)
                return value, stats
        order: list[str] = []
        tree: Tree | None = None
        vector: dict[State | None, complex] = {None: 1.0 + 0.0j}
        stats = EvaluationStats()
        index = 0
        while index < len(forms):
            form = forms[index]
            kind = form["kind"]
            if kind == "cup":
                gap = self._cup_gap(order, form)
                piece = form["piece"]
                left_strand, right_strand = f"{piece}.left", f"{piece}.right"
                component = topology.component_by_strand[left_strand]
                label = component_labels[component]
                left_label = label if topology.strand_orientation(left_strand) > 0 else self.category.dual(label)
                right_label = label if topology.strand_orientation(right_strand) > 0 else self.category.dual(label)
                pair_tree = Node(Leaf(left_strand, left_label), Leaf(right_strand, right_label))
                pair_state = NodeState(
                    LeafState(left_strand), LeafState(right_strand), self.category.unit,
                    fusion_index(self.category, left_label, right_label, self.category.unit),
                )
                coefficient = math.sqrt(float(self.category.dimension(label)))
                if topology.strand_orientation(left_strand) < 0:
                    coefficient *= complex(self.category.reverse_bend(label))
                new_vector: dict[State, complex] = {}
                new_tree = None
                for state, amplitude in vector.items():
                    inserted_tree, inserted_state = insert_pair(
                        self.category, tree, state, gap, pair_tree, pair_state
                    )
                    new_tree = inserted_tree
                    new_vector[inserted_state] = new_vector.get(inserted_state, 0.0 + 0.0j) + coefficient * amplitude
                tree = new_tree
                vector = _prune(new_vector)
                order[gap:gap] = [left_strand, right_strand]
                stats.cups += 1
                index += 1
            elif kind == "cap":
                if tree is None:
                    raise ValueError("cap on empty diagram")
                left, right = form["strands"]
                left_index, right_index = order.index(left), order.index(right)
                if abs(left_index - right_index) != 1:
                    raise ValueError("cap strands are not adjacent")
                lo = min(left_index, right_index)
                try:
                    path = find_subtree_path(tree, frozenset((left, right)))
                    plan = ()
                except ValueError:
                    target, path = grouped_target(tree, lo, lo + 2, split=lo + 1)
                    tree, vector, plan = self._rotate(tree, vector, target, stats)
                label = component_labels[topology.component_by_strand[left]]
                coefficient = math.sqrt(float(self.category.dimension(label)))
                geometric_left = order[lo]
                if topology.strand_orientation(geometric_left) < 0:
                    coefficient /= complex(self.category.reverse_bend(label))
                new_vector: dict[State | None, complex] = defaultdict(complex)
                new_tree = None
                for state, amplitude in vector.items():
                    removed_tree, removed_state = remove_pair(self.category, tree, state, path)
                    if removed_tree is _REJECTED:
                        continue
                    if removed_tree is _REMOVED:
                        if path:
                            continue
                        new_tree = None
                        new_vector[None] += coefficient * amplitude
                    else:
                        new_tree = removed_tree
                        new_vector[removed_state] += coefficient * amplitude
                tree = new_tree
                vector = _prune(dict(new_vector))
                order = [strand for strand in order if strand not in {left, right}]
                stats.caps += 1
                stats.plans.append({"kind": "cap", "form_index": index, "f_rotations": len(plan)})
                index += 1
            elif kind == "cross":
                if tree is None:
                    raise ValueError("crossing on empty diagram")
                end, targets, direction = self._cross_run(forms, index, order)
                if not targets or direction is None:
                    raise ValueError("failed to parse crossing run")
                sequential_tree, seq_f, seq_r, _ = self._evaluate_cross_candidate(
                    tree, order, form["over"], targets, direction, False
                )
                sequential_cost = seq_f * self.f_weight + seq_r * self.r_weight
                full_block_cost = None
                if len(targets) > 1:
                    _, full_f, _, _ = self._evaluate_cross_candidate(
                        tree, order, form["over"], targets, direction, True
                    )
                    full_block_cost = full_f * self.f_weight + self.r_weight
                if self.planner_mode == "sequential":
                    chosen_cost = sequential_cost
                    frontier = (1,) * len(targets)
                else:
                    chosen_cost, _, _, frontier, _ = self._plan_cross_frontier(
                        tree, order, form["over"], targets, direction
                    )
                chosen_f = 0
                progress = 0
                for length in frontier:
                    block_targets = tuple(targets[progress : progress + length])
                    target, path = self._cross_target(
                        tree, order, form["over"], block_targets, direction
                    )
                    tree, vector, plan = self._rotate(tree, vector, target, stats)
                    chosen_f += len(plan)
                    tree, vector = braid_siblings(
                        self.category, tree, vector, path, direction == "right"
                    )
                    if length == 1:
                        stats.leaf_r += 1
                    else:
                        stats.block_r += 1
                    for under in block_targets:
                        io, iu = order.index(form["over"]), order.index(under)
                        order[io], order[iu] = order[iu], order[io]
                    progress += length
                strategy = (
                    "sequential" if all(length == 1 for length in frontier)
                    else "block" if len(frontier) == 1
                    else "hybrid"
                )
                stats.plans.append(
                    {
                        "kind": "cross-run",
                        "form_start": index,
                        "form_stop": end,
                        "over": form["over"],
                        "targets": list(targets),
                        "direction": direction,
                        "strategy": strategy,
                        "frontier_segment_sizes": list(frontier),
                        "candidate_costs": {
                            "sequential": sequential_cost,
                            "full_block": full_block_cost,
                            "selected_frontier": chosen_cost,
                        },
                        "chosen_f_rotations": chosen_f,
                    }
                )
                index = end
            elif kind == "kink":
                strand = form["strand"]
                component = topology.component_by_strand[strand]
                label = component_labels[component]
                exponent = int(form.get("times", 1)) * (1 if form["sign"] in {"+", 1, "+1"} else -1)
                factor = complex(self.category.twist(label)) ** exponent
                vector = {state: factor * amplitude for state, amplitude in vector.items()}
                stats.kinks += abs(exponent)
                index += 1
            else:
                raise ValueError(f"unsupported Morse form: {form!r}")

            stats.max_active_strands = max(stats.max_active_strands, len(order))
            stats.max_state_support = max(stats.max_state_support, len(vector))

            if not vector:
                return 0.0 + 0.0j, self._stats_payload(
                    topology,
                    stats,
                    vanished_at_form=index,
                    vanishing_reason="empty support after fusion-channel projection",
                )

        if order or tree is not None:
            raise ValueError(f"Morse diagram did not close: {order!r}")
        value = complex(vector.get(None, 0.0 + 0.0j))
        return value, self._stats_payload(topology, stats)

    def omega_value(self, forms, character_assignments: dict[str, Any] | None = None):
        topology = self._topology(forms)
        character_assignments = character_assignments or {
            component: 0 for component in topology.component_order
        }
        total = 0.0 + 0.0j
        sectors = 0
        aggregate_stats = {"max_state_support": 0, "max_active_strands": 0}
        for labels in product(self.category.labels, repeat=len(topology.component_order)):
            assignment = dict(zip(topology.component_order, labels, strict=True))
            coefficient = 1.0 + 0.0j
            for component, label in assignment.items():
                coefficient *= complex(self.category.dimension(label))
                coefficient *= complex(self.category.character(character_assignments[component], label))
            if abs(coefficient) <= TOLERANCE:
                continue
            value, stats = self.fixed_label_value(forms, assignment)
            total += coefficient * value
            sectors += 1
            aggregate_stats["max_state_support"] = max(aggregate_stats["max_state_support"], stats["max_state_support"])
            aggregate_stats["max_active_strands"] = max(aggregate_stats["max_active_strands"], stats["max_active_strands"])
        return total, {
            "component_order": list(topology.component_order),
            "sector_count": sectors,
            **aggregate_stats,
        }
