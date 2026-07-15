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
import copy
from dataclasses import dataclass, field
from functools import lru_cache
from itertools import product
import math
from typing import Any, Iterable, Mapping

from experiments.sage.morse_pivotal_contract import (
    require_pivotal_capabilities,
    required_capabilities_for_forms,
)


TOLERANCE = 1e-13


def _is_ribbon_category_v2(category: Any) -> bool:
    return getattr(category, "contract_version", None) == (
        "twisted-yetter.ribbon-fusion-category.v2"
    )


def right_bend_fusion_matrix(category: Any, a: Any, b: Any, c: Any) -> dict[str, Any]:
    """Curry ``V_c^{a b}`` to ``V_a^{c dual(b)}`` in the path basis.

    The map is the composition of a right coevaluation with one ordinary
    F-move.  Rows are target multiplicity indices and columns are source
    multiplicity indices.  This is the counterclockwise/right-leg bend in
    the convention used here; no Frobenius--Schur flag reversal is included.
    """

    source_size = int(category.fusion_multiplicity(a, b, c))
    dual_b = category.dual(b)
    target_size = int(category.fusion_multiplicity(c, dual_b, a))
    if source_size != target_size:
        raise ValueError(
            "right bend violates Frobenius reciprocity: "
            f"N_{{{a},{b}}}^{c}={source_size}, "
            f"N_{{{c},dual({b})}}^{a}={target_size}"
        )
    if source_size == 0:
        raise ValueError("right bend needs an admissible fusion channel")
    block = category.f_block(a, b, dual_b, a)
    vacuum = (category.unit, 0, 0)
    vacuum_column = block["right_index"].get(vacuum)
    if vacuum_column is None:
        raise ValueError("right bend F block has no right-associated vacuum basis state")
    scale = math.sqrt(
        float(category.dimension(a))
        * float(category.dimension(b))
        / float(category.dimension(c))
    )
    entries = tuple(
        tuple(
            scale
            * complex(
                block["right_to_left"][
                    block["left_index"][(c, source, target)]
                ][vacuum_column]
            )
            for source in range(source_size)
        )
        for target in range(target_size)
    )
    return {
        "source_basis": tuple(range(source_size)),
        "target_basis": tuple(range(target_size)),
        "entries": entries,
        "source_space": (a, b, c),
        "target_space": (c, dual_b, a),
        "normalization": "sqrt(d_a*d_b/d_c)",
        "fs_flag_reversal_included": False,
    }


def left_bend_fusion_matrix(category: Any, a: Any, b: Any, c: Any) -> dict[str, Any]:
    """Curry ``V_c^{a b}`` to ``V_b^{dual(a) c}`` in the path basis.

    This is the clockwise/left-leg companion of
    :func:`right_bend_fusion_matrix`.  It is obtained from a left
    coevaluation and the inverse ordinary F-move.  Frobenius--Schur flag
    reversals remain explicit and are not folded into this matrix.
    """

    source_size = int(category.fusion_multiplicity(a, b, c))
    dual_a = category.dual(a)
    target_size = int(category.fusion_multiplicity(dual_a, c, b))
    if source_size != target_size:
        raise ValueError(
            "left bend violates Frobenius reciprocity: "
            f"N_{{{a},{b}}}^{c}={source_size}, "
            f"N_{{dual({a}),{c}}}^{b}={target_size}"
        )
    if source_size == 0:
        raise ValueError("left bend needs an admissible fusion channel")
    block = category.f_block(dual_a, a, b, b)
    vacuum = (category.unit, 0, 0)
    vacuum_column = block["left_index"].get(vacuum)
    if vacuum_column is None:
        raise ValueError("left bend F block has no left-associated vacuum basis state")
    scale = math.sqrt(
        float(category.dimension(a))
        * float(category.dimension(b))
        / float(category.dimension(c))
    )
    entries = tuple(
        tuple(
            scale
            * complex(
                block["left_to_right"][
                    block["right_index"][(c, source, target)]
                ][vacuum_column]
            )
            for source in range(source_size)
        )
        for target in range(target_size)
    )
    return {
        "source_basis": tuple(range(source_size)),
        "target_basis": tuple(range(target_size)),
        "entries": entries,
        "source_space": (a, b, c),
        "target_space": (dual_a, c, b),
        "normalization": "sqrt(d_a*d_b/d_c)",
        "fs_flag_reversal_included": False,
    }


@dataclass(frozen=True, slots=True)
class Leaf:
    strand: str
    label: Any
    _cached_hash: int = field(init=False, repr=False, compare=False, hash=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "_cached_hash", hash((self.strand, self.label)))

    def __hash__(self) -> int:
        return self._cached_hash


@dataclass(frozen=True, slots=True)
class Node:
    left: "Tree"
    right: "Tree"
    _cached_hash: int = field(init=False, repr=False, compare=False, hash=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "_cached_hash", hash((self.left, self.right)))

    def __hash__(self) -> int:
        return self._cached_hash


Tree = Leaf | Node


@dataclass(frozen=True, slots=True)
class LeafState:
    strand: str
    _cached_hash: int = field(init=False, repr=False, compare=False, hash=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "_cached_hash", hash(self.strand))

    def __hash__(self) -> int:
        return self._cached_hash


@dataclass(frozen=True, slots=True)
class NodeState:
    left: "State"
    right: "State"
    output: Any
    multiplicity: int
    _cached_hash: int = field(init=False, repr=False, compare=False, hash=False)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "_cached_hash",
            hash((self.left, self.right, self.output, self.multiplicity)),
        )

    def __hash__(self) -> int:
        return self._cached_hash


State = LeafState | NodeState


@lru_cache(maxsize=65_536)
def _rebuilt_node_state(
    left: State, right: State, output: Any, multiplicity: int
) -> NodeState:
    return NodeState(left, right, output, multiplicity)


@lru_cache(maxsize=65_536)
def _local_node_state(
    left: State, right: State, output: Any, multiplicity: int
) -> NodeState:
    return NodeState(left, right, output, multiplicity)


def right_comb_fusion_path_counts(category: Any, factor_labels: Iterable[Any]) -> dict[Any, int]:
    """Count right-comb fusion paths by root label, including multiplicity.

    The empty tensor product has one path to the tensor unit.  For a nonempty
    word ``X_1 ... X_n`` the basis tree is ``X_1 (X_2 (... X_n))``.  This
    dynamic count is deliberately separate from explicit path enumeration so
    a large coupon can be rejected or ranked without materializing its basis.
    """

    labels = tuple(factor_labels)
    if not labels:
        return {category.unit: 1}
    counts: dict[Any, int] = {labels[-1]: 1}
    for left in reversed(labels[:-1]):
        next_counts: dict[Any, int] = defaultdict(int)
        for right, path_count in counts.items():
            for output in category.labels:
                multiplicity = int(
                    category.fusion_multiplicity(left, right, output)
                )
                if multiplicity < 0:
                    raise ValueError("fusion multiplicities must be nonnegative")
                next_counts[output] += path_count * multiplicity
        counts = {
            output: count for output, count in next_counts.items() if count
        }
    return counts


def right_comb_fusion_path_basis(
    category: Any,
    factors: Iterable[tuple[str, Any]],
    *,
    target: Any,
    max_intermediate_paths: int = 100_000,
) -> tuple[Tree | None, tuple[State | None, ...]]:
    """Enumerate a right-comb path basis with a fail-closed size bound.

    Each factor is ``(stable_id, label)``.  Distinct trivalent-vertex
    multiplicity indices produce distinct states.  The empty tensor has one
    unit-root path represented by ``(None, (None,))``.
    """

    factors = tuple(factors)
    if max_intermediate_paths < 1:
        raise ValueError("max_intermediate_paths must be positive")
    if not factors:
        return None, (None,) if target == category.unit else ()

    last_id, last_label = factors[-1]
    tree: Tree = Leaf(last_id, last_label)
    basis_by_root: dict[Any, list[State]] = {
        last_label: [LeafState(last_id)]
    }
    for factor_id, left_label in reversed(factors[:-1]):
        left_tree = Leaf(factor_id, left_label)
        next_basis: dict[Any, list[State]] = defaultdict(list)
        for right_label, right_states in basis_by_root.items():
            for output in category.labels:
                multiplicity = int(
                    category.fusion_multiplicity(
                        left_label, right_label, output
                    )
                )
                if multiplicity < 0:
                    raise ValueError("fusion multiplicities must be nonnegative")
                for right_state in right_states:
                    for copy in range(multiplicity):
                        next_basis[output].append(
                            NodeState(
                                LeafState(factor_id),
                                right_state,
                                output,
                                copy,
                            )
                        )
        path_count = sum(len(states) for states in next_basis.values())
        if path_count > max_intermediate_paths:
            raise ValueError(
                "right-comb basis exceeds max_intermediate_paths: "
                f"{path_count} > {max_intermediate_paths}"
            )
        tree = Node(left_tree, tree)
        basis_by_root = dict(next_basis)
    return tree, tuple(basis_by_root.get(target, ()))


def vacuum_coupon_path_basis(
    category: Any,
    coupon_node: dict[str, Any],
    component_labels: dict[str, Any],
    *,
    max_intermediate_paths: int = 100_000,
) -> tuple[Tree | None, tuple[State | None, ...], dict[str, Any]]:
    """Instantiate a graph-level vacuum coupon in its orthonormal path basis.

    The returned basis realizes
    ``P_1 = sum_mu |mu><mu|`` on the ordered tensor word recorded by the
    coupon.  Variance is applied before fusion: a ``dual`` factor receives the
    dual of its component label.  No global-dimension normalization occurs.
    """

    if coupon_node.get("kind") != "vacuum-projector-coupon":
        raise ValueError("expected a vacuum-projector-coupon node")
    if not _is_ribbon_category_v2(category):
        require_pivotal_capabilities(category, {"vacuum_projector"})

    factors: list[tuple[str, Any]] = []
    factor_metadata = []
    for factor in coupon_node.get("factor_order", ()):
        component = factor["component"]
        if component not in component_labels:
            raise ValueError(f"missing coupon component label: {component!r}")
        label = component_labels[component]
        variance = factor["variance"]
        if variance == "dual":
            oriented_label = category.dual(label)
        elif variance == "label":
            oriented_label = label
        else:
            raise ValueError(f"unknown coupon factor variance: {variance!r}")
        cut_id = factor["cut_id"]
        factors.append((cut_id, oriented_label))
        factor_metadata.append(
            {
                "cut_id": cut_id,
                "component": component,
                "variance": variance,
                "label": label,
                "oriented_label": oriented_label,
            }
        )

    counts = right_comb_fusion_path_counts(
        category, (label for _, label in factors)
    )
    tree, basis = right_comb_fusion_path_basis(
        category,
        factors,
        target=category.unit,
        max_intermediate_paths=max_intermediate_paths,
    )
    expected_rank = counts.get(category.unit, 0)
    if len(basis) != expected_rank:
        raise AssertionError(
            "enumerated vacuum basis rank disagrees with dynamic fusion count"
        )
    normalization = (
        "PAIRING_INVERSE_PATH_BASIS_IDEMPOTENT_NO_D_FACTOR"
        if _is_ribbon_category_v2(category)
        else "ORTHONORMAL_PATH_BASIS_IDEMPOTENT_NO_D_FACTOR"
    )
    formula = (
        "sum_mu_nu |mu> G^-1[mu,nu] <nu|"
        if _is_ribbon_category_v2(category)
        else "sum_mu |mu><mu|"
    )
    return tree, basis, {
        "normalization": normalization,
        "factor_count": len(factors),
        "factor_order": factor_metadata,
        "root_label": category.unit,
        "root_multiplicity_rank": expected_rank,
        "projector_term_count": expected_rank,
        "projector_formula": formula,
    }


def compile_right_comb_projector_term(
    tree: Tree | None,
    basis_state: State | None,
    *,
    unit: Any,
    namespace: str,
) -> tuple[dict[str, Any], ...]:
    """Compile one ``|mu><mu|`` term into explicit fuse/split forms.

    ``tree`` must be a right comb whose root is the tensor unit.  The emitted
    program consumes the factor wires from right to left and recreates them
    from left to right.  It contains no F, R, dimension, or handle
    normalization coefficients; those remain the evaluator's responsibility.
    """

    if tree is None:
        if basis_state is not None:
            raise ValueError("empty projector tree needs the empty basis state")
        return ()
    if basis_state is None:
        raise ValueError("nonempty projector tree needs a basis state")
    if root_label(tree, basis_state) != unit:
        raise ValueError("projector basis state does not end at the tensor unit")

    ordered_leaves = leaves(tree)
    if len(ordered_leaves) == 1:
        if ordered_leaves[0].label != unit:
            raise ValueError("one-factor vacuum path must itself be the unit")
        return ()

    spine: list[tuple[Leaf, Tree, NodeState]] = []
    current_tree = tree
    current_state = basis_state
    while isinstance(current_tree, Node):
        if not isinstance(current_tree.left, Leaf):
            raise ValueError("projector compiler requires a right-comb tree")
        if not isinstance(current_state, NodeState):
            raise ValueError("projector state does not match its right-comb tree")
        spine.append((current_tree.left, current_tree.right, current_state))
        current_tree = current_tree.right
        current_state = current_state.right
    if not isinstance(current_state, LeafState):
        raise ValueError("projector right-comb tail does not end in a leaf state")

    forms: list[dict[str, Any]] = []
    tail_wire = ordered_leaves[-1].strand
    projection_wire_by_index: dict[int, str] = {}
    for index in range(len(spine) - 1, -1, -1):
        left_leaf, _right_tree, node_state = spine[index]
        output_wire = f"{namespace}.projection.acc{index:03d}"
        forms.append(
            {
                "kind": "fuse",
                "inputs": [left_leaf.strand, tail_wire],
                "output": output_wire,
                "output_label": node_state.output,
                "multiplicity": node_state.multiplicity,
                "projector_role": "projection",
                "projector_basis_index": namespace,
                "right_comb_vertex_index": index,
            }
        )
        projection_wire_by_index[index] = output_wire
        tail_wire = output_wire

    current_wire = projection_wire_by_index[0]
    for index, (left_leaf, right_tree, node_state) in enumerate(spine):
        if index + 1 < len(spine):
            right_wire = f"{namespace}.inclusion.acc{index + 1:03d}"
        else:
            right_wire = ordered_leaves[-1].strand
        right_state = node_state.right
        forms.append(
            {
                "kind": "split",
                "input": current_wire,
                "outputs": [left_leaf.strand, right_wire],
                "output_labels": [
                    left_leaf.label,
                    root_label(right_tree, right_state),
                ],
                "multiplicity": node_state.multiplicity,
                "projector_role": "inclusion",
                "projector_basis_index": namespace,
                "right_comb_vertex_index": index,
            }
        )
        current_wire = right_wire
    return tuple(forms)


def expand_vacuum_coupon_graph_term(
    category: Any,
    coupon_graph: dict[str, Any],
    component_labels: dict[str, Any],
    *,
    basis_index: int,
    namespace: str = "vacuum-coupon",
    max_intermediate_paths: int = 100_000,
) -> dict[str, Any]:
    """Replace one high-valence vacuum coupon by a trivalent basis term.

    The external graph is unchanged.  Incoming coupon ports feed the
    projection tree, its unit root is joined to the inclusion tree, and the
    inclusion leaves feed the original outgoing ports.  The result is a
    category-instantiated ribbon morphism graph, not yet a contracted scalar.
    """

    coupon_id = coupon_graph["coupon_node_id"]
    coupon_nodes = [
        node
        for node in coupon_graph["nodes"]
        if node["node_id"] == coupon_id
    ]
    if len(coupon_nodes) != 1:
        raise ValueError("coupon graph must contain exactly one named coupon")
    coupon_node = coupon_nodes[0]
    tree, basis, basis_metadata = vacuum_coupon_path_basis(
        category,
        coupon_node,
        component_labels,
        max_intermediate_paths=max_intermediate_paths,
    )
    if not (0 <= basis_index < len(basis)):
        raise ValueError(
            f"coupon basis_index {basis_index} is outside rank {len(basis)}"
        )
    basis_state = basis[basis_index]
    term_forms = compile_right_comb_projector_term(
        tree,
        basis_state,
        unit=category.unit,
        namespace=f"{namespace}.mu{basis_index:06d}",
    )
    factors = list(coupon_node["factor_order"])
    factor_count = len(factors)
    nodes = [
        copy.deepcopy(node)
        for node in coupon_graph["nodes"]
        if node["node_id"] != coupon_id
    ]
    projection_nodes: dict[int, dict[str, Any]] = {}
    inclusion_nodes: dict[int, dict[str, Any]] = {}
    input_targets: dict[str, dict[str, str]] = {}
    output_sources: dict[str, dict[str, str]] = {}
    internal_edges: list[dict[str, Any]] = []

    if factor_count == 1:
        cut_id = factors[0]["cut_id"]
        node_id = f"trivalent:{namespace}:mu{basis_index:06d}:unit-identity"
        nodes.append(
            {
                "node_id": node_id,
                "kind": "unit-channel-identity",
                "label": category.unit,
                "ports": ["in", "out"],
            }
        )
        input_targets[cut_id] = {"node_id": node_id, "port": "in"}
        output_sources[cut_id] = {"node_id": node_id, "port": "out"}
    elif factor_count > 1:
        projection_forms = {
            form["right_comb_vertex_index"]: form
            for form in term_forms
            if form["kind"] == "fuse"
        }
        inclusion_forms = {
            form["right_comb_vertex_index"]: form
            for form in term_forms
            if form["kind"] == "split"
        }
        expected_vertices = set(range(factor_count - 1))
        if set(projection_forms) != expected_vertices or set(inclusion_forms) != expected_vertices:
            raise AssertionError("compiled projector term has an incomplete right comb")

        for index in range(factor_count - 1):
            projection = projection_forms[index]
            inclusion = inclusion_forms[index]
            p_id = f"trivalent:{namespace}:mu{basis_index:06d}:p{index:03d}"
            i_id = f"trivalent:{namespace}:mu{basis_index:06d}:i{index:03d}"
            projection_nodes[index] = {
                "node_id": p_id,
                "kind": "fusion-coupon",
                "left_label": inclusion["output_labels"][0],
                "right_label": inclusion["output_labels"][1],
                "output_label": projection["output_label"],
                "multiplicity": projection["multiplicity"],
                "ports": ["left-in", "right-in", "out"],
                "right_comb_vertex_index": index,
            }
            inclusion_nodes[index] = {
                "node_id": i_id,
                "kind": "split-coupon",
                "input_label": projection["output_label"],
                "left_label": inclusion["output_labels"][0],
                "right_label": inclusion["output_labels"][1],
                "multiplicity": inclusion["multiplicity"],
                "ports": ["in", "left-out", "right-out"],
                "right_comb_vertex_index": index,
            }
        nodes.extend(projection_nodes.values())
        nodes.extend(inclusion_nodes.values())

        for index, factor in enumerate(factors):
            cut_id = factor["cut_id"]
            if index < factor_count - 1:
                input_targets[cut_id] = {
                    "node_id": projection_nodes[index]["node_id"],
                    "port": "left-in",
                }
                output_sources[cut_id] = {
                    "node_id": inclusion_nodes[index]["node_id"],
                    "port": "left-out",
                }
            else:
                input_targets[cut_id] = {
                    "node_id": projection_nodes[index - 1]["node_id"],
                    "port": "right-in",
                }
                output_sources[cut_id] = {
                    "node_id": inclusion_nodes[index - 1]["node_id"],
                    "port": "right-out",
                }

        edge_index = 0
        for index in range(factor_count - 2):
            internal_edges.append(
                {
                    "edge_id": f"edge:{namespace}:mu{basis_index:06d}:internal:{edge_index:04d}",
                    "component": "__vacuum_projector__",
                    "from": {
                        "node_id": projection_nodes[index + 1]["node_id"],
                        "port": "out",
                    },
                    "to": {
                        "node_id": projection_nodes[index]["node_id"],
                        "port": "right-in",
                    },
                }
            )
            edge_index += 1
        internal_edges.append(
            {
                "edge_id": f"edge:{namespace}:mu{basis_index:06d}:internal:{edge_index:04d}",
                "component": "__vacuum_projector__",
                "from": {"node_id": projection_nodes[0]["node_id"], "port": "out"},
                "to": {"node_id": inclusion_nodes[0]["node_id"], "port": "in"},
                "label": category.unit,
                "role": "projector-unit-root",
            }
        )
        edge_index += 1
        for index in range(factor_count - 2):
            internal_edges.append(
                {
                    "edge_id": f"edge:{namespace}:mu{basis_index:06d}:internal:{edge_index:04d}",
                    "component": "__vacuum_projector__",
                    "from": {
                        "node_id": inclusion_nodes[index]["node_id"],
                        "port": "right-out",
                    },
                    "to": {
                        "node_id": inclusion_nodes[index + 1]["node_id"],
                        "port": "in",
                    },
                }
            )
            edge_index += 1
    else:
        raise ValueError("graph-level coupon term needs at least one factor")

    edges = []
    for edge in coupon_graph["edges"]:
        rewritten = copy.deepcopy(edge)
        if rewritten["to"]["node_id"] == coupon_id:
            port = rewritten["to"]["port"]
            if not port.startswith("input:"):
                raise ValueError(f"unexpected incoming coupon port: {port!r}")
            rewritten["to"] = input_targets[port.removeprefix("input:")]
        if rewritten["from"]["node_id"] == coupon_id:
            port = rewritten["from"]["port"]
            if not port.startswith("output:"):
                raise ValueError(f"unexpected outgoing coupon port: {port!r}")
            rewritten["from"] = output_sources[port.removeprefix("output:")]
        edges.append(rewritten)
    edges.extend(internal_edges)
    if any(
        endpoint["node_id"] == coupon_id
        for edge in edges
        for endpoint in (edge["from"], edge["to"])
    ):
        raise AssertionError("trivalent expansion left a high-valence coupon edge")
    incoming_degree: dict[tuple[str, str], int] = defaultdict(int)
    outgoing_degree: dict[tuple[str, str], int] = defaultdict(int)
    for edge in edges:
        outgoing_degree[(edge["from"]["node_id"], edge["from"]["port"])] += 1
        incoming_degree[(edge["to"]["node_id"], edge["to"]["port"])] += 1
    for node in nodes:
        if node["kind"] == "fusion-coupon":
            expected_in, expected_out = ("left-in", "right-in"), ("out",)
        elif node["kind"] == "split-coupon":
            expected_in, expected_out = ("in",), ("left-out", "right-out")
        elif node["kind"] == "unit-channel-identity":
            expected_in, expected_out = ("in",), ("out",)
        else:
            continue
        if any(incoming_degree[(node["node_id"], port)] != 1 for port in expected_in):
            raise AssertionError(
                f"trivalent node has a malformed incoming port: {node['node_id']}"
            )
        if any(outgoing_degree[(node["node_id"], port)] != 1 for port in expected_out):
            raise AssertionError(
                f"trivalent node has a malformed outgoing port: {node['node_id']}"
            )

    result = {
        **{
            key: copy.deepcopy(value)
            for key, value in coupon_graph.items()
            if key not in {"nodes", "edges", "node_count", "edge_count", "graph_hash"}
        },
        "schema": "twisted-yetter.trivalent-vacuum-projector-graph.v1",
        "status": "PASS_TRIVALENT_VACUUM_PROJECTOR_TERM_NOT_CONTRACTED",
        "nodes": nodes,
        "edges": edges,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "expanded_coupon": {
            "source_coupon_node_id": coupon_id,
            "basis_index": basis_index,
            "basis_rank": len(basis),
            "factor_count": factor_count,
            "projection_vertex_count": max(factor_count - 1, 0),
            "inclusion_vertex_count": max(factor_count - 1, 0),
            "normalization": basis_metadata["normalization"],
            "projector_formula": basis_metadata["projector_formula"],
        },
        "evaluation_status": "NOT_CONTRACTED_REQUIRES_TRIVALENT_GRAPH_LOWERING",
    }
    return result


def leaf_count(tree: Tree) -> int:
    if isinstance(tree, Leaf):
        return 1
    return leaf_count(tree.left) + leaf_count(tree.right)


def leaves(tree: Tree) -> tuple[Leaf, ...]:
    if isinstance(tree, Leaf):
        return (tree,)
    return leaves(tree.left) + leaves(tree.right)


def root_label(tree: Tree, state: Any, state_backend: Any | None = None) -> Any:
    if state_backend is not None:
        return state_backend.root_label(tree, state)
    if isinstance(tree, Leaf):
        if not isinstance(state, LeafState) or state.strand != tree.strand:
            raise ValueError("leaf/tree state mismatch")
        return tree.label
    if not isinstance(state, NodeState):
        raise ValueError("node/tree state mismatch")
    return state.output


class ObjectStateBackend:
    name = "object-tree"

    @staticmethod
    def clear() -> None:
        _rebuilt_node_state.cache_clear()
        _local_node_state.cache_clear()

    @staticmethod
    def leaf(strand: str) -> LeafState:
        return LeafState(strand)

    @staticmethod
    def node(left: State, right: State, output: Any, multiplicity: int) -> NodeState:
        return _local_node_state(left, right, output, multiplicity)

    @staticmethod
    def is_leaf(state: Any) -> bool:
        return isinstance(state, LeafState)

    @staticmethod
    def is_node(state: Any) -> bool:
        return isinstance(state, NodeState)

    @staticmethod
    def strand(state: LeafState) -> str:
        return state.strand

    @staticmethod
    def left(state: NodeState) -> State:
        return state.left

    @staticmethod
    def right(state: NodeState) -> State:
        return state.right

    @staticmethod
    def output(state: NodeState) -> Any:
        return state.output

    @staticmethod
    def multiplicity(state: NodeState) -> int:
        return state.multiplicity

    @staticmethod
    def root_label(tree: Tree, state: State) -> Any:
        return root_label(tree, state)

    @staticmethod
    def zipper(state: State, path: tuple[int, ...]):
        return _state_zipper(state, path)

    @staticmethod
    def rebuild(ancestors: list[tuple[NodeState, int]], replacement: State) -> State:
        return _rebuild_state(ancestors, replacement)

    @staticmethod
    def cache_stats() -> dict[str, Any]:
        rebuild = _rebuilt_node_state.cache_info()
        local = _local_node_state.cache_info()
        return {
            "node_count": None,
            "rebuild_hits": rebuild.hits,
            "rebuild_misses": rebuild.misses,
            "local_hits": local.hits,
            "local_misses": local.misses,
        }

    @staticmethod
    def maybe_compact(vector: dict[Any, complex]) -> dict[Any, complex]:
        return vector


class CompactStateArena:
    """Hash-consed integer representation of fusion-basis states."""

    name = "compact-integer-arena"

    def __init__(self, *, compact_threshold: int = 750_000) -> None:
        self.compact_threshold = int(compact_threshold)
        if self.compact_threshold < 1:
            raise ValueError("compact_threshold must be positive")
        self._kind: list[int] = []
        self._strand: list[str | None] = []
        self._left: list[int] = []
        self._right: list[int] = []
        self._output: list[Any] = []
        self._multiplicity: list[int] = []
        self._leaf_ids: dict[str, int] = {}
        self._node_ids: dict[tuple[int, int, Any, int], int] = {}
        self._node_hits = 0
        self._node_misses = 0
        self._compactions = 0
        self._peak_node_count = 0

    def clear(self) -> None:
        threshold = self.compact_threshold
        self.__init__(compact_threshold=threshold)

    def leaf(self, strand: str) -> int:
        state_id = self._leaf_ids.get(strand)
        if state_id is not None:
            return state_id
        state_id = len(self._kind)
        self._leaf_ids[strand] = state_id
        self._kind.append(0)
        self._strand.append(strand)
        self._left.append(-1)
        self._right.append(-1)
        self._output.append(None)
        self._multiplicity.append(-1)
        self._peak_node_count = max(self._peak_node_count, len(self._kind))
        return state_id

    def node(self, left: int, right: int, output: Any, multiplicity: int) -> int:
        key = (left, right, output, multiplicity)
        state_id = self._node_ids.get(key)
        if state_id is not None:
            self._node_hits += 1
            return state_id
        self._node_misses += 1
        state_id = len(self._kind)
        self._node_ids[key] = state_id
        self._kind.append(1)
        self._strand.append(None)
        self._left.append(left)
        self._right.append(right)
        self._output.append(output)
        self._multiplicity.append(multiplicity)
        self._peak_node_count = max(self._peak_node_count, len(self._kind))
        return state_id

    def is_leaf(self, state: int) -> bool:
        return self._kind[state] == 0

    def is_node(self, state: int) -> bool:
        return self._kind[state] == 1

    def strand(self, state: int) -> str:
        strand = self._strand[state]
        if strand is None:
            raise ValueError("node state has no strand")
        return strand

    def left(self, state: int) -> int:
        return self._left[state]

    def right(self, state: int) -> int:
        return self._right[state]

    def output(self, state: int) -> Any:
        return self._output[state]

    def multiplicity(self, state: int) -> int:
        return self._multiplicity[state]

    def root_label(self, tree: Tree, state: int) -> Any:
        if isinstance(tree, Leaf):
            if not self.is_leaf(state) or self.strand(state) != tree.strand:
                raise ValueError("leaf/tree state mismatch")
            return tree.label
        if not self.is_node(state):
            raise ValueError("node/tree state mismatch")
        return self.output(state)

    def zipper(
        self, state: int, path: tuple[int, ...]
    ) -> tuple[int, list[tuple[int, int]]]:
        ancestors: list[tuple[int, int]] = []
        current = state
        for direction in path:
            if not self.is_node(current):
                raise ValueError("state path descends through a leaf")
            ancestors.append((current, direction))
            current = self.left(current) if direction == 0 else self.right(current)
        return current, ancestors

    def rebuild(self, ancestors: list[tuple[int, int]], replacement: int) -> int:
        result = replacement
        for parent, direction in reversed(ancestors):
            if direction == 0:
                result = self.node(
                    result,
                    self.right(parent),
                    self.output(parent),
                    self.multiplicity(parent),
                )
            else:
                result = self.node(
                    self.left(parent),
                    result,
                    self.output(parent),
                    self.multiplicity(parent),
                )
        return result

    def cache_stats(self) -> dict[str, Any]:
        return {
            "node_count": len(self._kind),
            "peak_node_count": self._peak_node_count,
            "leaf_count": len(self._leaf_ids),
            "node_hits": self._node_hits,
            "node_misses": self._node_misses,
            "compactions": self._compactions,
            "compact_threshold": self.compact_threshold,
        }

    def maybe_compact(self, vector: dict[Any, complex]) -> dict[Any, complex]:
        if len(self._kind) < self.compact_threshold:
            return vector
        old_kind = self._kind
        old_strand = self._strand
        old_left = self._left
        old_right = self._right
        old_output = self._output
        old_multiplicity = self._multiplicity
        old_hits = self._node_hits
        old_misses = self._node_misses
        old_compactions = self._compactions
        old_peak = self._peak_node_count
        replacement = CompactStateArena(
            compact_threshold=self.compact_threshold
        )
        remap: dict[int, int] = {}

        def copy_state(state_id: int) -> int:
            copied = remap.get(state_id)
            if copied is not None:
                return copied
            if old_kind[state_id] == 0:
                strand = old_strand[state_id]
                if strand is None:
                    raise ValueError("compact leaf lost its strand")
                copied = replacement.leaf(strand)
            else:
                copied = replacement.node(
                    copy_state(old_left[state_id]),
                    copy_state(old_right[state_id]),
                    old_output[state_id],
                    old_multiplicity[state_id],
                )
            remap[state_id] = copied
            return copied

        compacted = {
            (None if state is None else copy_state(state)): amplitude
            for state, amplitude in vector.items()
        }
        self._kind = replacement._kind
        self._strand = replacement._strand
        self._left = replacement._left
        self._right = replacement._right
        self._output = replacement._output
        self._multiplicity = replacement._multiplicity
        self._leaf_ids = replacement._leaf_ids
        self._node_ids = replacement._node_ids
        self._node_hits = old_hits + replacement._node_hits
        self._node_misses = old_misses + replacement._node_misses
        self._compactions = old_compactions + 1
        self._peak_node_count = max(old_peak, replacement._peak_node_count)
        return compacted


OBJECT_STATE_BACKEND = ObjectStateBackend()


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


def find_leaf_path(tree: Tree, strand: str, path: tuple[int, ...] = ()) -> tuple[int, ...]:
    if isinstance(tree, Leaf):
        if tree.strand == strand:
            return path
        raise ValueError(f"leaf {strand!r} is absent")
    if strand in {leaf.strand for leaf in leaves(tree.left)}:
        return find_leaf_path(tree.left, strand, path + (0,))
    return find_leaf_path(tree.right, strand, path + (1,))


def matrix_entry(matrix: Any, row: int, column: int) -> complex:
    try:
        return complex(matrix[row, column])
    except (TypeError, IndexError):
        return complex(matrix[row][column])


def _state_zipper(
    state: State, path: tuple[int, ...]
) -> tuple[State, list[tuple[NodeState, int]]]:
    ancestors = []
    current = state
    for direction in path:
        if not isinstance(current, NodeState):
            raise ValueError("state path descends through a leaf")
        ancestors.append((current, direction))
        current = current.left if direction == 0 else current.right
    return current, ancestors


def _state_at(state: State, path: tuple[int, ...]) -> State:
    return _state_zipper(state, path)[0]


def _rebuild_state(
    ancestors: list[tuple[NodeState, int]], replacement: State
) -> State:
    result = replacement
    for parent, direction in reversed(ancestors):
        if direction == 0:
            result = _rebuilt_node_state(
                result,
                parent.right,
                parent.output,
                parent.multiplicity,
            )
        else:
            result = _rebuilt_node_state(
                parent.left,
                result,
                parent.output,
                parent.multiplicity,
            )
    return result


def _replace_state(state: State, path: tuple[int, ...], replacement: State) -> State:
    _local, ancestors = _state_zipper(state, path)
    return _rebuild_state(ancestors, replacement)


def _prune(vector: dict[Any, complex], tolerance: float = TOLERANCE) -> dict[Any, complex]:
    return {state: value for state, value in vector.items() if abs(value) > tolerance}


def _state_for_backend(tree: Tree, state: State, state_backend: Any) -> Any:
    if isinstance(tree, Leaf):
        if not isinstance(state, LeafState):
            raise ValueError("leaf/tree state mismatch")
        return state_backend.leaf(state.strand)
    if not isinstance(state, NodeState):
        raise ValueError("node/tree state mismatch")
    return state_backend.node(
        _state_for_backend(tree.left, state.left, state_backend),
        _state_for_backend(tree.right, state.right, state_backend),
        state.output,
        state.multiplicity,
    )


def rotate_vector(
    category: Any,
    tree: Tree,
    vector: dict[Any, complex],
    path: tuple[int, ...],
    direction: str,
    *,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    local_tree = subtree_at(tree, path)
    output: dict[Any, complex] = defaultdict(complex)
    zipper = state_backend.zipper
    rebuild = state_backend.rebuild
    node = state_backend.node
    for state, amplitude in vector.items():
        local_state, ancestors = zipper(state, path)
        if direction == "left-to-right":
            if not isinstance(local_tree, Node) or not isinstance(local_tree.left, Node):
                raise ValueError("bad left-to-right local tree")
            if not state_backend.is_node(local_state):
                raise ValueError("bad left-to-right local state")
            a_tree, b_tree, c_tree = local_tree.left.left, local_tree.left.right, local_tree.right
            ab_state, c_state = state_backend.left(local_state), state_backend.right(local_state)
            if not state_backend.is_node(ab_state):
                raise ValueError("bad left-to-right local state")
            a_state, b_state = state_backend.left(ab_state), state_backend.right(ab_state)
            a = root_label(a_tree, a_state, state_backend)
            b = root_label(b_tree, b_state, state_backend)
            c = root_label(c_tree, c_state, state_backend)
            d = state_backend.output(local_state)
            block = category.f_block(a, b, c, d)
            left_key = (
                state_backend.output(ab_state),
                state_backend.multiplicity(ab_state),
                state_backend.multiplicity(local_state),
            )
            left_index = block["left_index"][left_key]
            inverse = block["left_to_right"]
            for right_index, right_key in enumerate(block["right_basis"]):
                coefficient = matrix_entry(inverse, right_index, left_index)
                if abs(coefficient) <= TOLERANCE:
                    continue
                y, bc_mult, ay_mult = right_key
                bc_state = node(b_state, c_state, y, bc_mult)
                replacement = node(a_state, bc_state, d, ay_mult)
                output[rebuild(ancestors, replacement)] += coefficient * amplitude
        elif direction == "right-to-left":
            if not isinstance(local_tree, Node) or not isinstance(local_tree.right, Node):
                raise ValueError("bad right-to-left local tree")
            if not state_backend.is_node(local_state):
                raise ValueError("bad right-to-left local state")
            a_tree, b_tree, c_tree = local_tree.left, local_tree.right.left, local_tree.right.right
            a_state, bc_state = state_backend.left(local_state), state_backend.right(local_state)
            if not state_backend.is_node(bc_state):
                raise ValueError("bad right-to-left local state")
            b_state, c_state = state_backend.left(bc_state), state_backend.right(bc_state)
            a = root_label(a_tree, a_state, state_backend)
            b = root_label(b_tree, b_state, state_backend)
            c = root_label(c_tree, c_state, state_backend)
            d = state_backend.output(local_state)
            block = category.f_block(a, b, c, d)
            right_key = (
                state_backend.output(bc_state),
                state_backend.multiplicity(bc_state),
                state_backend.multiplicity(local_state),
            )
            right_index = block["right_index"][right_key]
            matrix = block["right_to_left"]
            for left_index, left_key in enumerate(block["left_basis"]):
                coefficient = matrix_entry(matrix, left_index, right_index)
                if abs(coefficient) <= TOLERANCE:
                    continue
                x, ab_mult, xc_mult = left_key
                ab_state = node(a_state, b_state, x, ab_mult)
                replacement = node(ab_state, c_state, d, xc_mult)
                output[rebuild(ancestors, replacement)] += coefficient * amplitude
        else:
            raise ValueError(f"unknown rotation direction: {direction!r}")
    return rotate_shape(tree, path, direction), _prune(dict(output))


def apply_rotation_plan(
    category: Any, tree: Tree, vector: dict[Any, complex], plan, *, state_backend=OBJECT_STATE_BACKEND
):
    for path, direction in plan:
        tree, vector = rotate_vector(
            category, tree, vector, path, direction, state_backend=state_backend
        )
        vector = state_backend.maybe_compact(vector)
    return tree, vector


def project_vacuum_interval(
    category: Any,
    tree: Tree,
    vector: dict[Any, complex],
    start: int,
    stop: int,
    *,
    path_range: tuple[int, int] | None = None,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    """Apply the idempotent unit-channel projector to a leaf interval.

    The projector is diagonal only after the requested leaves have been
    grouped as a subtree.  Every fusion path whose subtree root is the tensor
    unit is retained, including distinct multiplicity copies.  No global
    dimension or handle normalization is inserted here.
    """

    require_pivotal_capabilities(category, {"vacuum_projector"})
    if not (0 <= start < stop <= leaf_count(tree)):
        raise ValueError("vacuum projector needs a nonempty in-range leaf interval")
    source = tree
    target, path = grouped_target(tree, start, stop)
    forward = rotation_plan(tree, target)
    tree, vector = apply_rotation_plan(
        category, tree, vector, forward, state_backend=state_backend
    )
    local_tree = subtree_at(tree, path)
    basis_rank = None
    selected_basis = None
    if path_range is not None:
        basis_tree, basis = right_comb_fusion_path_basis(
            category,
            ((leaf.strand, leaf.label) for leaf in leaves(local_tree)),
            target=category.unit,
        )
        if basis_tree != local_tree:
            raise AssertionError("vacuum projector target is not the canonical right comb")
        basis_rank = len(basis)
        range_start, range_stop = map(int, path_range)
        if not (0 <= range_start <= range_stop <= basis_rank):
            raise ValueError(
                "vacuum projector path range is outside its canonical basis: "
                f"{path_range!r} for rank {basis_rank}"
            )
        selected_basis = frozenset(
            _state_for_backend(basis_tree, basis_state, state_backend)
            for basis_state in basis[range_start:range_stop]
        )

    retained = {}
    selected_global_state_count = 0
    for state, amplitude in vector.items():
        local_state = state_backend.zipper(state, path)[0]
        if root_label(local_tree, local_state, state_backend) != category.unit:
            continue
        if selected_basis is not None and local_state not in selected_basis:
            continue
        retained[state] = amplitude
        selected_global_state_count += 1
    backward = rotation_plan(tree, source)
    tree, retained = apply_rotation_plan(
        category, tree, retained, backward, state_backend=state_backend
    )
    if tree != source:
        raise AssertionError("vacuum projection failed to restore the source tree")
    return tree, _prune(retained), {
        "forward_f_rotations": len(forward),
        "backward_f_rotations": len(backward),
        "support_before": len(vector),
        "support_after": len(retained),
        "subtree_path": list(path),
        "canonical_path_basis_rank": basis_rank,
        "selected_path_range": list(path_range) if path_range is not None else None,
        "selected_global_state_count": selected_global_state_count,
    }


def fuse_active_pair(
    category: Any,
    tree: Tree,
    vector: dict[Any, complex],
    path: tuple[int, ...],
    *,
    output_strand: str,
    output_label: Any,
    multiplicity: int,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    """Apply one orthonormal trivalent projection to a sibling pair."""

    local_tree = subtree_at(tree, path)
    if not isinstance(local_tree, Node):
        raise ValueError("fusion input is not a sibling pair")
    if not isinstance(local_tree.left, Leaf) or not isinstance(local_tree.right, Leaf):
        raise ValueError("fusion inputs must be active physical wires")
    available = category.fusion_multiplicity(
        local_tree.left.label, local_tree.right.label, output_label
    )
    if not (0 <= multiplicity < available):
        raise ValueError(
            "fusion multiplicity index is out of range: "
            f"{multiplicity} not in [0, {available})"
        )
    output: dict[Any, complex] = defaultdict(complex)
    for state, amplitude in vector.items():
        local_state, ancestors = state_backend.zipper(state, path)
        if not state_backend.is_node(local_state):
            raise ValueError("fusion input state is not a sibling pair")
        if state_backend.output(local_state) != output_label:
            continue
        if _is_ribbon_category_v2(category):
            pairing = category.fusion_pairing(
                local_tree.left.label, local_tree.right.label, output_label
            )
            coefficient = complex(
                pairing[multiplicity][state_backend.multiplicity(local_state)]
            )
        else:
            coefficient = complex(
                state_backend.multiplicity(local_state) == multiplicity
            )
        if abs(coefficient) > TOLERANCE:
            replacement = state_backend.leaf(output_strand)
            output[state_backend.rebuild(ancestors, replacement)] += coefficient * amplitude
    replacement_tree = Leaf(output_strand, output_label)
    return replace_subtree(tree, path, replacement_tree), _prune(dict(output))


def split_active_wire(
    category: Any,
    tree: Tree,
    vector: dict[Any, complex],
    path: tuple[int, ...],
    *,
    left_strand: str,
    left_label: Any,
    right_strand: str,
    right_label: Any,
    multiplicity: int,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    """Apply the adjoint inclusion of one orthonormal trivalent basis map."""

    local_tree = subtree_at(tree, path)
    if not isinstance(local_tree, Leaf):
        raise ValueError("split input must be one active physical wire")
    available = category.fusion_multiplicity(
        left_label, right_label, local_tree.label
    )
    if not (0 <= multiplicity < available):
        raise ValueError(
            "split multiplicity index is out of range: "
            f"{multiplicity} not in [0, {available})"
        )
    output: dict[Any, complex] = defaultdict(complex)
    for state, amplitude in vector.items():
        local_state, ancestors = state_backend.zipper(state, path)
        if not state_backend.is_leaf(local_state):
            raise ValueError("split input state must be one active physical wire")
        replacement = state_backend.node(
            state_backend.leaf(left_strand),
            state_backend.leaf(right_strand),
            local_tree.label,
            multiplicity,
        )
        output[state_backend.rebuild(ancestors, replacement)] += amplitude
    replacement_tree = Node(
        Leaf(left_strand, left_label), Leaf(right_strand, right_label)
    )
    return replace_subtree(tree, path, replacement_tree), _prune(dict(output))


def braid_siblings(
    category: Any,
    tree: Tree,
    vector: dict[Any, complex],
    path: tuple[int, ...],
    positive: bool,
    *,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    local_tree = subtree_at(tree, path)
    if not isinstance(local_tree, Node):
        raise ValueError("braid needs a node")
    output: dict[Any, complex] = defaultdict(complex)
    for state, amplitude in vector.items():
        local_state, ancestors = state_backend.zipper(state, path)
        if not state_backend.is_node(local_state):
            raise ValueError("braid needs a node state")
        left_state = state_backend.left(local_state)
        right_state = state_backend.right(local_state)
        output_label = state_backend.output(local_state)
        a = root_label(local_tree.left, left_state, state_backend)
        b = root_label(local_tree.right, right_state, state_backend)
        matrix = category.r_matrix(a, b, output_label, positive)
        for target_mult in range(category.fusion_multiplicity(b, a, output_label)):
            coefficient = matrix_entry(
                matrix, target_mult, state_backend.multiplicity(local_state)
            )
            if abs(coefficient) <= TOLERANCE:
                continue
            replacement = state_backend.node(
                right_state,
                left_state,
                output_label,
                target_mult,
            )
            output[state_backend.rebuild(ancestors, replacement)] += coefficient * amplitude
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
        elif kind == "vacuum-projector":
            strands = [
                strand
                for strand in form.get("strands", ())
                if topology.component_by_strand[strand] in retained_components
            ]
            if strands:
                positions = [kept_order.index(strand) for strand in strands]
                start = min(positions)
                if kept_order[start : start + len(strands)] != strands:
                    raise ValueError(
                        "unit pruning made vacuum-projector strands noncontiguous"
                    )
                projected = dict(form)
                projected["strands"] = strands
                output.append(projected)
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


def insert_pair(
    category: Any,
    tree: Tree | None,
    state: Any | None,
    gap: int,
    pair_tree: Node,
    pair_state: Any,
    *,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    if tree is None:
        if gap != 0 or state is not None:
            raise ValueError("bad empty cup insertion")
        return pair_tree, pair_state
    if state is None:
        raise ValueError("nonempty tree needs state")
    count = leaf_count(tree)
    if not (0 <= gap <= count):
        raise ValueError("cup gap is outside active order")
    current_root = root_label(tree, state, state_backend)
    if gap == 0:
        mult = fusion_index(category, category.unit, current_root, current_root)
        return Node(pair_tree, tree), state_backend.node(
            pair_state, state, current_root, mult
        )
    if gap == count:
        mult = fusion_index(category, current_root, category.unit, current_root)
        return Node(tree, pair_tree), state_backend.node(
            state, pair_state, current_root, mult
        )
    if not isinstance(tree, Node) or not state_backend.is_node(state):
        raise ValueError("interior insertion requires a node")
    left_count = leaf_count(tree.left)
    if gap <= left_count:
        new_left, new_left_state = insert_pair(
            category,
            tree.left,
            state_backend.left(state),
            gap,
            pair_tree,
            pair_state,
            state_backend=state_backend,
        )
        return Node(new_left, tree.right), state_backend.node(
            new_left_state,
            state_backend.right(state),
            state_backend.output(state),
            state_backend.multiplicity(state),
        )
    new_right, new_right_state = insert_pair(
        category,
        tree.right,
        state_backend.right(state),
        gap - left_count,
        pair_tree,
        pair_state,
        state_backend=state_backend,
    )
    return Node(tree.left, new_right), state_backend.node(
        state_backend.left(state),
        new_right_state,
        state_backend.output(state),
        state_backend.multiplicity(state),
    )


_REMOVED = object()
_REJECTED = object()


def remove_pair(
    category: Any,
    tree: Tree,
    state: Any,
    path: tuple[int, ...],
    *,
    state_backend: Any = OBJECT_STATE_BACKEND,
):
    if not path:
        if not isinstance(tree, Node) or not state_backend.is_node(state):
            raise ValueError("cap target is not a pair node")
        if (
            state_backend.output(state) != category.unit
            or state_backend.multiplicity(state) != 0
        ):
            return _REJECTED, _REJECTED
        return _REMOVED, _REMOVED
    if not isinstance(tree, Node) or not state_backend.is_node(state):
        raise ValueError("cap path descends through a leaf")
    direction, rest = path[0], path[1:]
    if direction == 0:
        new_tree, new_state = remove_pair(
            category,
            tree.left,
            state_backend.left(state),
            rest,
            state_backend=state_backend,
        )
        if new_tree is _REJECTED:
            return _REJECTED, _REJECTED
        if new_tree is _REMOVED:
            right_state = state_backend.right(state)
            sibling_label = root_label(tree.right, right_state, state_backend)
            if (
                state_backend.output(state) != sibling_label
                or state_backend.multiplicity(state)
                != fusion_index(category, category.unit, sibling_label, sibling_label)
            ):
                return _REJECTED, _REJECTED
            return tree.right, right_state
        return Node(new_tree, tree.right), state_backend.node(
            new_state,
            state_backend.right(state),
            state_backend.output(state),
            state_backend.multiplicity(state),
        )
    new_tree, new_state = remove_pair(
        category,
        tree.right,
        state_backend.right(state),
        rest,
        state_backend=state_backend,
    )
    if new_tree is _REJECTED:
        return _REJECTED, _REJECTED
    if new_tree is _REMOVED:
        left_state = state_backend.left(state)
        sibling_label = root_label(tree.left, left_state, state_backend)
        if (
            state_backend.output(state) != sibling_label
            or state_backend.multiplicity(state)
            != fusion_index(category, sibling_label, category.unit, sibling_label)
        ):
            return _REJECTED, _REJECTED
        return tree.left, left_state
    return Node(tree.left, new_tree), state_backend.node(
        state_backend.left(state),
        new_state,
        state_backend.output(state),
        state_backend.multiplicity(state),
    )


@dataclass
class EvaluationStats:
    f_rotations: int = 0
    leaf_r: int = 0
    block_r: int = 0
    cups: int = 0
    caps: int = 0
    kinks: int = 0
    vacuum_projectors: int = 0
    fusions: int = 0
    splits: int = 0
    coevaluations: int = 0
    evaluations: int = 0
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
        state_backend: str = "object",
        compact_state_threshold: int = 750_000,
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
        if state_backend not in {"object", "compact"}:
            raise ValueError("state_backend must be 'object' or 'compact'")
        self.state_backend_mode = state_backend
        self.compact_state_threshold = int(compact_state_threshold)
        if self.compact_state_threshold < 1:
            raise ValueError("compact_state_threshold must be positive")
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

    def _stats_payload(
        self,
        topology: MorseTopology,
        stats: EvaluationStats,
        *,
        state_backend: Any = OBJECT_STATE_BACKEND,
        **extra,
    ):
        rebuild_cache = _rebuilt_node_state.cache_info()
        local_cache = _local_node_state.cache_info()
        return {
            "component_order": list(topology.component_order),
            "f_rotations": stats.f_rotations,
            "leaf_r": stats.leaf_r,
            "block_r": stats.block_r,
            "cups": stats.cups,
            "caps": stats.caps,
            "kinks": stats.kinks,
            "vacuum_projectors": stats.vacuum_projectors,
            "fusions": stats.fusions,
            "splits": stats.splits,
            "coevaluations": stats.coevaluations,
            "evaluations": stats.evaluations,
            "max_active_strands": stats.max_active_strands,
            "max_state_support": stats.max_state_support,
            "state_rebuild_cache": {
                "hits": rebuild_cache.hits,
                "misses": rebuild_cache.misses,
                "maxsize": rebuild_cache.maxsize,
                "currsize": rebuild_cache.currsize,
            },
            "state_local_cache": {
                "hits": local_cache.hits,
                "misses": local_cache.misses,
                "maxsize": local_cache.maxsize,
                "currsize": local_cache.currsize,
            },
            "state_backend": state_backend.name,
            "state_backend_stats": state_backend.cache_stats(),
            "planner_weights": {"f": self.f_weight, "r": self.r_weight},
            "planner_mode": self.planner_mode,
            "reversed_orientation_components": sorted(
                self.reversed_orientation_components
            ),
            "plans": stats.plans,
            **extra,
        }

    def _coevaluation_coefficient(self, label: Any, reverse: bool) -> complex:
        if _is_ribbon_category_v2(self.category):
            method = (
                self.category.right_coevaluation
                if reverse
                else self.category.left_coevaluation
            )
            return complex(method(label))
        coefficient = math.sqrt(float(self.category.dimension(label)))
        if reverse:
            coefficient *= complex(self.category.reverse_bend(label))
        return coefficient

    def _evaluation_coefficient(self, label: Any, reverse: bool) -> complex:
        if _is_ribbon_category_v2(self.category):
            method = (
                self.category.right_evaluation
                if reverse
                else self.category.left_evaluation
            )
            return complex(method(label))
        coefficient = math.sqrt(float(self.category.dimension(label)))
        if reverse:
            coefficient /= complex(self.category.reverse_bend(label))
        return coefficient

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

    def _rotate(self, tree, vector, target, stats, state_backend):
        plan = rotation_plan(tree, target)
        tree, vector = apply_rotation_plan(
            self.category,
            tree,
            vector,
            plan,
            state_backend=state_backend,
        )
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

    def fixed_label_value(
        self,
        forms: Iterable[dict[str, Any]],
        component_labels: dict[str, Any],
        *,
        projector_path_ranges: Mapping[str, tuple[int, int]] | None = None,
        _unit_pruned=False,
    ):
        forms = forms if isinstance(forms, tuple) else tuple(forms)
        projector_path_ranges = dict(projector_path_ranges or {})
        projector_ids = {
            form.get("projector_id")
            for form in forms
            if form.get("kind") == "vacuum-projector"
        }
        unknown_projectors = set(projector_path_ranges) - projector_ids
        if unknown_projectors:
            raise ValueError(
                "projector path ranges reference absent projector ids: "
                f"{sorted(unknown_projectors)!r}"
            )
        required_pivotal = required_capabilities_for_forms(forms)
        if required_pivotal and not _is_ribbon_category_v2(self.category):
            require_pivotal_capabilities(self.category, required_pivotal)
        topology = self._topology(
            forms, allow_missing_reversed=_unit_pruned
        )
        missing = set(topology.component_order) - set(component_labels)
        if missing:
            raise ValueError(f"missing component labels: {sorted(missing)!r}")
        has_explicit_morphisms = any(
            form["kind"] in {"fuse", "split", "coevaluation", "evaluation"}
            for form in forms
        )
        if not _unit_pruned and not has_explicit_morphisms:
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
                    projector_path_ranges=projector_path_ranges,
                    _unit_pruned=True,
                )
                stats = dict(stats)
                stats["unit_pruned_components"] = sorted(set(topology.component_order) - retained)
                stats["original_component_order"] = list(topology.component_order)
                return value, stats
        state_backend = (
            CompactStateArena(
                compact_threshold=self.compact_state_threshold
            )
            if self.state_backend_mode == "compact"
            else OBJECT_STATE_BACKEND
        )
        state_backend.clear()
        order: list[str] = []
        tree: Tree | None = None
        vector: dict[Any | None, complex] = {None: 1.0 + 0.0j}
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
                pair_state = state_backend.node(
                    state_backend.leaf(left_strand),
                    state_backend.leaf(right_strand),
                    self.category.unit,
                    fusion_index(self.category, left_label, right_label, self.category.unit),
                )
                coefficient = self._coevaluation_coefficient(
                    label, topology.strand_orientation(left_strand) < 0
                )
                new_vector: dict[State, complex] = {}
                new_tree = None
                for state, amplitude in vector.items():
                    inserted_tree, inserted_state = insert_pair(
                        self.category,
                        tree,
                        state,
                        gap,
                        pair_tree,
                        pair_state,
                        state_backend=state_backend,
                    )
                    new_tree = inserted_tree
                    new_vector[inserted_state] = new_vector.get(inserted_state, 0.0 + 0.0j) + coefficient * amplitude
                tree = new_tree
                vector = _prune(new_vector)
                order[gap:gap] = [left_strand, right_strand]
                stats.cups += 1
                index += 1
            elif kind == "coevaluation":
                gap = self._cup_gap(order, form)
                strands = list(form["strands"])
                labels = list(form["labels"])
                if len(strands) != 2 or len(set(strands)) != 2:
                    raise ValueError(
                        "coevaluation needs two distinct output wires"
                    )
                if len(labels) != 2:
                    raise ValueError("coevaluation needs two output labels")
                if any(strand in order for strand in strands):
                    raise ValueError("coevaluation output wire is already active")
                pair_tree = Node(
                    Leaf(strands[0], labels[0]), Leaf(strands[1], labels[1])
                )
                pair_state = state_backend.node(
                    state_backend.leaf(strands[0]),
                    state_backend.leaf(strands[1]),
                    self.category.unit,
                    fusion_index(
                        self.category, labels[0], labels[1], self.category.unit
                    ),
                )
                dimension_label = form.get("dimension_label", labels[0])
                coefficient = self._coevaluation_coefficient(
                    dimension_label, bool(form.get("reverse_bend", False))
                )
                new_vector: dict[State, complex] = defaultdict(complex)
                new_tree = None
                for state, amplitude in vector.items():
                    inserted_tree, inserted_state = insert_pair(
                        self.category,
                        tree,
                        state,
                        gap,
                        pair_tree,
                        pair_state,
                        state_backend=state_backend,
                    )
                    new_tree = inserted_tree
                    new_vector[inserted_state] += coefficient * amplitude
                tree = new_tree
                vector = _prune(dict(new_vector))
                order[gap:gap] = strands
                stats.coevaluations += 1
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
                    tree, vector, plan = self._rotate(
                        tree, vector, target, stats, state_backend
                    )
                label = component_labels[topology.component_by_strand[left]]
                geometric_left = order[lo]
                reverse = topology.strand_orientation(geometric_left) < 0
                coefficient = self._evaluation_coefficient(label, reverse)
                new_vector: dict[State | None, complex] = defaultdict(complex)
                new_tree = None
                for state, amplitude in vector.items():
                    removed_tree, removed_state = remove_pair(
                        self.category,
                        tree,
                        state,
                        path,
                        state_backend=state_backend,
                    )
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
            elif kind == "evaluation":
                if tree is None:
                    raise ValueError("evaluation on an empty diagram")
                strands = list(form["strands"])
                if len(strands) != 2 or len(set(strands)) != 2:
                    raise ValueError("evaluation needs two distinct input wires")
                positions = [order.index(strand) for strand in strands]
                if abs(positions[0] - positions[1]) != 1:
                    raise ValueError("evaluation input wires are not adjacent")
                lo = min(positions)
                try:
                    path = find_subtree_path(tree, frozenset(strands))
                    plan = ()
                except ValueError:
                    target, path = grouped_target(
                        tree, lo, lo + 2, split=lo + 1
                    )
                    tree, vector, plan = self._rotate(
                        tree, vector, target, stats, state_backend
                    )
                dimension_label = form.get(
                    "dimension_label", subtree_at(tree, path).left.label
                )
                coefficient = self._evaluation_coefficient(
                    dimension_label, bool(form.get("reverse_bend", False))
                )
                new_vector: dict[State | None, complex] = defaultdict(complex)
                new_tree = None
                for state, amplitude in vector.items():
                    removed_tree, removed_state = remove_pair(
                        self.category,
                        tree,
                        state,
                        path,
                        state_backend=state_backend,
                    )
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
                order = [
                    strand for strand in order if strand not in set(strands)
                ]
                stats.evaluations += 1
                stats.plans.append(
                    {
                        "kind": "evaluation",
                        "form_index": index,
                        "f_rotations": len(plan),
                    }
                )
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
                    tree, vector, plan = self._rotate(
                        tree, vector, target, stats, state_backend
                    )
                    chosen_f += len(plan)
                    tree, vector = braid_siblings(
                        self.category,
                        tree,
                        vector,
                        path,
                        direction == "right",
                        state_backend=state_backend,
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
            elif kind == "vacuum-projector":
                strands = list(form.get("strands", ()))
                if not strands:
                    stats.plans.append(
                        {
                            "kind": "vacuum-projector",
                            "form_index": index,
                            "projector_id": form.get("projector_id"),
                            "empty_tensor_identity": True,
                        }
                    )
                    stats.vacuum_projectors += 1
                    index += 1
                    continue
                if tree is None:
                    raise ValueError("nonempty vacuum projector on an empty diagram")
                if len(set(strands)) != len(strands):
                    raise ValueError("vacuum projector repeats an active strand")
                if any(strand not in order for strand in strands):
                    raise ValueError("vacuum projector references an inactive strand")
                start = order.index(strands[0])
                stop = start + len(strands)
                if order[start:stop] != strands:
                    raise ValueError(
                        "vacuum projector strands must be one contiguous ordered interval"
                    )
                tree, vector, projector_stats = project_vacuum_interval(
                    self.category,
                    tree,
                    vector,
                    start,
                    stop,
                    path_range=projector_path_ranges.get(form.get("projector_id")),
                    state_backend=state_backend,
                )
                stats.f_rotations += (
                    projector_stats["forward_f_rotations"]
                    + projector_stats["backward_f_rotations"]
                )
                stats.vacuum_projectors += 1
                stats.plans.append(
                    {
                        "kind": "vacuum-projector",
                        "form_index": index,
                        "projector_id": form.get("projector_id"),
                        "strands": strands,
                        **projector_stats,
                    }
                )
                index += 1
            elif kind == "fuse":
                if tree is None:
                    raise ValueError("fusion on an empty diagram")
                inputs = list(form["inputs"])
                if len(inputs) != 2 or len(set(inputs)) != 2:
                    raise ValueError("fusion needs two distinct input wires")
                positions = [order.index(strand) for strand in inputs]
                if positions[1] != positions[0] + 1:
                    raise ValueError(
                        "fusion inputs must be adjacent and left-to-right ordered"
                    )
                target, path = grouped_target(
                    tree, positions[0], positions[1] + 1, split=positions[1]
                )
                tree, vector, plan = self._rotate(
                    tree, vector, target, stats, state_backend
                )
                output_strand = form["output"]
                if output_strand in order:
                    raise ValueError("fusion output wire is already active")
                tree, vector = fuse_active_pair(
                    self.category,
                    tree,
                    vector,
                    path,
                    output_strand=output_strand,
                    output_label=form["output_label"],
                    multiplicity=int(form.get("multiplicity", 0)),
                    state_backend=state_backend,
                )
                order[positions[0] : positions[1] + 1] = [output_strand]
                stats.fusions += 1
                stats.plans.append(
                    {
                        "kind": "fuse",
                        "form_index": index,
                        "inputs": inputs,
                        "output": output_strand,
                        "output_label": form["output_label"],
                        "multiplicity": int(form.get("multiplicity", 0)),
                        "f_rotations": len(plan),
                    }
                )
                index += 1
            elif kind == "split":
                if tree is None:
                    raise ValueError("split on an empty diagram")
                input_strand = form["input"]
                input_position = order.index(input_strand)
                output_strands = list(form["outputs"])
                output_labels = list(form["output_labels"])
                if len(output_strands) != 2 or len(set(output_strands)) != 2:
                    raise ValueError("split needs two distinct output wires")
                if len(output_labels) != 2:
                    raise ValueError("split needs two output labels")
                if any(strand in order for strand in output_strands):
                    raise ValueError("split output wire is already active")
                path = find_leaf_path(tree, input_strand)
                tree, vector = split_active_wire(
                    self.category,
                    tree,
                    vector,
                    path,
                    left_strand=output_strands[0],
                    left_label=output_labels[0],
                    right_strand=output_strands[1],
                    right_label=output_labels[1],
                    multiplicity=int(form.get("multiplicity", 0)),
                    state_backend=state_backend,
                )
                order[input_position : input_position + 1] = output_strands
                stats.splits += 1
                stats.plans.append(
                    {
                        "kind": "split",
                        "form_index": index,
                        "input": input_strand,
                        "outputs": output_strands,
                        "output_labels": output_labels,
                        "multiplicity": int(form.get("multiplicity", 0)),
                    }
                )
                index += 1
            else:
                raise ValueError(f"unsupported Morse form: {form!r}")

            vector = state_backend.maybe_compact(vector)
            stats.max_active_strands = max(stats.max_active_strands, len(order))
            stats.max_state_support = max(stats.max_state_support, len(vector))

            if not vector:
                return 0.0 + 0.0j, self._stats_payload(
                    topology,
                    stats,
                    state_backend=state_backend,
                    vanished_at_form=index,
                    vanishing_reason="empty support after fusion-channel projection",
                )

        if order or tree is not None:
            raise ValueError(f"Morse diagram did not close: {order!r}")
        value = complex(vector.get(None, 0.0 + 0.0j))
        return value, self._stats_payload(
            topology, stats, state_backend=state_backend
        )

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
