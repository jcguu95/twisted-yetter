"""Generic pairing-aware contraction support for RibbonGraphIRV2.

This module deliberately starts from the first-class graph.  It never uses a
Kirby-colored killing loop and never asks whether a category is pointed or
modular.  Vacuum coupons are expanded with the inverse of the actual fusion-
path Gram matrix.  Subsequent lowering and contraction therefore receive an
ordinary weighted ribbon graph whose vertices are category morphisms.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
from itertools import product
import math
from typing import Any, Iterable, Iterator

import networkx as nx
import numpy as np

from experiments.sage.morse_fusion_evaluator import (
    Leaf,
    LeafState,
    Node,
    NodeState,
    State,
    Tree,
    compile_right_comb_projector_term,
    root_label,
    vacuum_coupon_path_basis,
)
from experiments.sage.ribbon_category_v2 import (
    RibbonFusionCategoryV2,
    validate_ribbon_category_v2,
)
from experiments.scripts.special_dotted_morphism import (
    RIBBON_GRAPH_IR_V2_SCHEMA,
    stable_json_hash,
    validate_ribbon_graph_ir_v2,
)


class RibbonGraphContractionError(ValueError):
    """Raised when a certified ribbon graph cannot be contracted."""


@dataclass(frozen=True)
class ProjectorTermSpec:
    coupon_node_id: str
    inclusion_basis_index: int
    projection_basis_index: int
    coefficient: complex
    basis_rank: int
    gram_residual: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "coupon_node_id": self.coupon_node_id,
            "inclusion_basis_index": self.inclusion_basis_index,
            "projection_basis_index": self.projection_basis_index,
            "coefficient": [self.coefficient.real, self.coefficient.imag],
            "basis_rank": self.basis_rank,
            "gram_residual": self.gram_residual,
        }


@dataclass(frozen=True)
class WeightedRibbonGraphTerm:
    graph: dict[str, Any]
    coefficient: complex
    projector_terms: tuple[ProjectorTermSpec, ...]


def _port_vertex(node_id: str, port: str) -> str:
    return f"port:{node_id}:{port}"


def _add_rotation(embedding: nx.PlanarEmbedding, node: str, neighbors: list[str]) -> None:
    if not neighbors:
        embedding.add_node(node)
        return
    embedding.add_half_edge_first(node, neighbors[0])
    previous = neighbors[0]
    for neighbor in neighbors[1:]:
        embedding.add_half_edge_cw(node, neighbor, previous)
        previous = neighbor


def _embedding_faces(embedding: nx.PlanarEmbedding) -> list[list[str]]:
    visited = set()
    faces = []
    for left, right in embedding.edges():
        if (left, right) in visited:
            continue
        face = embedding.traverse_face(left, right, visited)
        faces.append(face)
    return faces


def _orientation(a, b, c) -> float:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def _proper_segment_intersection(a, b, c, d, tolerance=1e-10) -> bool:
    values = (
        _orientation(a, b, c),
        _orientation(a, b, d),
        _orientation(c, d, a),
        _orientation(c, d, b),
    )
    if any(abs(value) <= tolerance for value in values):
        return False
    return (values[0] > 0) != (values[1] > 0) and (values[2] > 0) != (values[3] > 0)


def ribbon_embedding_certificate(graph: dict[str, Any]) -> dict[str, Any]:
    """Realize the recorded rotation system without inventing crossings."""

    validate_ribbon_graph_ir_v2(graph)
    node_by_id = {node["node_id"]: node for node in graph["nodes"]}
    incident: dict[tuple[str, str], str] = {}
    port_partner: dict[str, str] = {}
    simple = nx.Graph()
    for node in graph["nodes"]:
        node_vertex = f"node:{node['node_id']}"
        simple.add_node(node_vertex)
        for port in node["ports"]:
            port_vertex = _port_vertex(node["node_id"], port)
            simple.add_edge(node_vertex, port_vertex)
    for edge in graph["edges"]:
        source_key = (edge["from"]["node_id"], edge["from"]["port"])
        target_key = (edge["to"]["node_id"], edge["to"]["port"])
        if source_key in incident or target_key in incident:
            raise RibbonGraphContractionError("graph port is incident to multiple edges")
        incident[source_key] = edge["edge_id"]
        incident[target_key] = edge["edge_id"]
        source = _port_vertex(*source_key)
        target = _port_vertex(*target_key)
        simple.add_edge(source, target)
        port_partner[source] = target
        port_partner[target] = source

    positions = {}
    component_reports = []
    offset_x = 0.0
    for component_index, vertices in enumerate(
        sorted(nx.connected_components(simple), key=lambda values: min(values))
    ):
        subgraph = simple.subgraph(vertices).copy()
        embedding = nx.PlanarEmbedding()
        for vertex in sorted(vertices):
            if vertex.startswith("node:"):
                node_id = vertex.removeprefix("node:")
                neighbors = [
                    _port_vertex(node_id, port)
                    for port in node_by_id[node_id]["cyclic_order"]
                ]
            else:
                node_neighbor = next(
                    neighbor for neighbor in subgraph.neighbors(vertex) if neighbor.startswith("node:")
                )
                other = [neighbor for neighbor in subgraph.neighbors(vertex) if neighbor != node_neighbor]
                neighbors = [node_neighbor, *sorted(other)]
            _add_rotation(embedding, vertex, neighbors)
        try:
            embedding.check_structure()
        except nx.NetworkXException as exc:
            raise RibbonGraphContractionError(
                "recorded ribbon rotation system is not a planar embedding"
            ) from exc
        faces = _embedding_faces(embedding)
        euler = subgraph.number_of_nodes() - subgraph.number_of_edges() + len(faces)
        if euler != 2:
            raise RibbonGraphContractionError(
                f"ribbon component has Euler characteristic {euler}, expected 2"
            )
        if subgraph.number_of_nodes() == 1:
            local_positions = {next(iter(vertices)): (0.0, 0.0)}
        else:
            raw_positions = nx.combinatorial_embedding_to_pos(embedding)
            local_positions = {
                vertex: (float(position[0]), float(position[1]))
                for vertex, position in raw_positions.items()
            }
        min_x = min(position[0] for position in local_positions.values())
        max_x = max(position[0] for position in local_positions.values())
        for vertex, (x, y) in local_positions.items():
            positions[vertex] = (x - min_x + offset_x, y)
        offset_x += max(max_x - min_x + 4.0, 4.0)
        component_reports.append(
            {
                "component_index": component_index,
                "vertex_count": subgraph.number_of_nodes(),
                "edge_count": subgraph.number_of_edges(),
                "face_count": len(faces),
                "euler_characteristic": euler,
            }
        )

    segments = []
    for left, right in simple.edges():
        segments.append((left, right, positions[left], positions[right]))
    unexpected = []
    for index, (a_name, b_name, a, b) in enumerate(segments):
        for c_name, d_name, c, d in segments[index + 1 :]:
            if {a_name, b_name} & {c_name, d_name}:
                continue
            if _proper_segment_intersection(a, b, c, d):
                unexpected.append([[a_name, b_name], [c_name, d_name]])
    if unexpected:
        raise RibbonGraphContractionError(
            f"planar embedding introduced {len(unexpected)} unexpected crossings"
        )
    payload = {
        "schema": "twisted-yetter.ribbon-embedding-certificate.v1",
        "status": "PASS_GENUS_ZERO_ROTATION_SYSTEM_NO_ADDED_CROSSINGS",
        "source_graph_hash": graph["graph_hash"],
        "connected_component_count": len(component_reports),
        "components": component_reports,
        "positions": {
            vertex: [position[0], position[1]]
            for vertex, position in sorted(positions.items())
        },
        "segment_count": len(segments),
        "unexpected_crossing_count": 0,
        "layout_backend": f"networkx-{nx.__version__}:combinatorial_embedding_to_pos",
    }
    payload["certificate_hash"] = stable_json_hash(payload)
    return payload


def _path_pairing(
    category: RibbonFusionCategoryV2,
    tree: Tree | None,
    left: State | None,
    right: State | None,
) -> complex:
    if tree is None:
        return 1.0 + 0.0j if left is right is None else 0.0 + 0.0j
    if isinstance(tree, Leaf):
        if not isinstance(left, LeafState) or not isinstance(right, LeafState):
            return 0.0 + 0.0j
        return complex(left.strand == right.strand == tree.strand)
    if not isinstance(left, NodeState) or not isinstance(right, NodeState):
        return 0.0 + 0.0j
    if left.output != right.output:
        return 0.0 + 0.0j
    left_a = root_label(tree.left, left.left)
    right_a = root_label(tree.left, right.left)
    left_b = root_label(tree.right, left.right)
    right_b = root_label(tree.right, right.right)
    if left_a != right_a or left_b != right_b:
        return 0.0 + 0.0j
    pairing = np.asarray(
        category.fusion_pairing(left_a, left_b, left.output),
        dtype=np.complex128,
    )
    local = complex(pairing[left.multiplicity, right.multiplicity])
    return (
        local
        * _path_pairing(category, tree.left, left.left, right.left)
        * _path_pairing(category, tree.right, left.right, right.right)
    )


def vacuum_path_gram_matrix(
    category: RibbonFusionCategoryV2,
    tree: Tree | None,
    basis: tuple[State | None, ...],
) -> tuple[np.ndarray, np.ndarray, float]:
    """Return the path pairing, its inverse, and inverse residual."""

    gram = np.asarray(
        [
            [_path_pairing(category, tree, left, right) for right in basis]
            for left in basis
        ],
        dtype=np.complex128,
    )
    if gram.shape == (0, 0):
        return gram, gram, 0.0
    try:
        inverse = np.linalg.inv(gram)
    except np.linalg.LinAlgError as exc:
        raise RibbonGraphContractionError(
            "vacuum fusion-path pairing is singular"
        ) from exc
    residual = float(np.max(np.abs(gram @ inverse - np.eye(len(basis)))))
    if residual > category.numeric_tolerance:
        raise RibbonGraphContractionError(
            f"vacuum path Gram inverse residual {residual} exceeds tolerance"
        )
    return gram, inverse, residual


def projector_term_specs(
    category: RibbonFusionCategoryV2,
    coupon_node: dict[str, Any],
    component_labels: dict[str, Any],
) -> tuple[Tree | None, tuple[State | None, ...], tuple[ProjectorTermSpec, ...]]:
    """Instantiate ``sum |mu> G^-1[mu,nu] <nu|`` without shortcuts."""

    tree, basis, _ = vacuum_coupon_path_basis(
        category, coupon_node, component_labels
    )
    if not basis:
        return tree, basis, ()
    _, inverse, residual = vacuum_path_gram_matrix(category, tree, basis)
    specs = []
    tolerance = category.numeric_tolerance
    for inclusion, projection in product(range(len(basis)), repeat=2):
        coefficient = complex(inverse[inclusion, projection])
        if abs(coefficient) <= tolerance:
            continue
        specs.append(
            ProjectorTermSpec(
                coupon_node_id=coupon_node["node_id"],
                inclusion_basis_index=inclusion,
                projection_basis_index=projection,
                coefficient=coefficient,
                basis_rank=len(basis),
                gram_residual=residual,
            )
        )
    return tree, basis, tuple(specs)


def _node_port_metadata(kind: str) -> tuple[list[str], list[str], dict[str, str]]:
    if kind == "fusion-coupon":
        ports = ["left-in", "right-in", "out"]
        return ports, ports, {
            "left-in": "input", "right-in": "input", "out": "output"
        }
    if kind == "split-coupon":
        ports = ["in", "left-out", "right-out"]
        return ports, ["in", "right-out", "left-out"], {
            "in": "input", "left-out": "output", "right-out": "output"
        }
    if kind == "unit-channel-identity":
        ports = ["in", "out"]
        return ports, ports, {"in": "input", "out": "output"}
    raise ValueError(f"unknown expanded node kind {kind!r}")


def _expand_one_coupon(
    category: RibbonFusionCategoryV2,
    graph: dict[str, Any],
    component_labels: dict[str, Any],
    coupon_node_id: str,
    tree: Tree | None,
    basis: tuple[State | None, ...],
    spec: ProjectorTermSpec,
) -> dict[str, Any]:
    coupon = next(
        (node for node in graph["nodes"] if node["node_id"] == coupon_node_id),
        None,
    )
    if coupon is None or coupon["kind"] != "vacuum-projector-coupon":
        raise RibbonGraphContractionError(f"missing coupon {coupon_node_id!r}")
    factors = list(coupon["factor_order"])
    factor_count = len(factors)
    projection_forms = [
        form
        for form in compile_right_comb_projector_term(
            tree,
            basis[spec.projection_basis_index],
            unit=category.unit,
            namespace=f"{coupon_node_id}.projection",
        )
        if form["kind"] == "fuse"
    ]
    inclusion_forms = [
        form
        for form in compile_right_comb_projector_term(
            tree,
            basis[spec.inclusion_basis_index],
            unit=category.unit,
            namespace=f"{coupon_node_id}.inclusion",
        )
        if form["kind"] == "split"
    ]
    nodes = [
        copy.deepcopy(node) for node in graph["nodes"] if node["node_id"] != coupon_node_id
    ]
    input_targets: dict[str, dict[str, str]] = {}
    output_sources: dict[str, dict[str, str]] = {}
    internal_edges = []
    projection_nodes = {}
    inclusion_nodes = {}

    if factor_count == 0:
        if graph["edges"] and any(
            endpoint["node_id"] == coupon_node_id
            for edge in graph["edges"]
            for endpoint in (edge["from"], edge["to"])
        ):
            raise RibbonGraphContractionError("zero-factor coupon unexpectedly has edges")
    elif factor_count == 1:
        cut_id = factors[0]["cut_id"]
        node_id = (
            f"trivalent:{coupon_node_id}:mu{spec.inclusion_basis_index}:"
            f"nu{spec.projection_basis_index}:unit"
        )
        ports, cyclic, variance = _node_port_metadata("unit-channel-identity")
        nodes.append(
            {
                "node_id": node_id,
                "kind": "unit-channel-identity",
                "label": category.unit,
                "ports": ports,
                "cyclic_order": cyclic,
                "port_variance": variance,
                "provenance": {"coupon_node_id": coupon_node_id},
            }
        )
        input_targets[cut_id] = {"node_id": node_id, "port": "in"}
        output_sources[cut_id] = {"node_id": node_id, "port": "out"}
    else:
        if len(projection_forms) != factor_count - 1 or len(inclusion_forms) != factor_count - 1:
            raise RibbonGraphContractionError("projector term has an incomplete trivalent tree")
        projection_by_index = {
            form["right_comb_vertex_index"]: form for form in projection_forms
        }
        inclusion_by_index = {
            form["right_comb_vertex_index"]: form for form in inclusion_forms
        }
        for index in range(factor_count - 1):
            projection = projection_by_index[index]
            inclusion = inclusion_by_index[index]
            p_id = (
                f"trivalent:{coupon_node_id}:mu{spec.inclusion_basis_index}:"
                f"nu{spec.projection_basis_index}:p{index}"
            )
            i_id = (
                f"trivalent:{coupon_node_id}:mu{spec.inclusion_basis_index}:"
                f"nu{spec.projection_basis_index}:i{index}"
            )
            p_ports, p_cyclic, p_variance = _node_port_metadata("fusion-coupon")
            i_ports, i_cyclic, i_variance = _node_port_metadata("split-coupon")
            projection_nodes[index] = {
                "node_id": p_id,
                "kind": "fusion-coupon",
                "left_label": inclusion["output_labels"][0],
                "right_label": inclusion["output_labels"][1],
                "output_label": projection["output_label"],
                "multiplicity": projection["multiplicity"],
                "ports": p_ports,
                "cyclic_order": p_cyclic,
                "port_variance": p_variance,
                "provenance": {"coupon_node_id": coupon_node_id},
            }
            inclusion_nodes[index] = {
                "node_id": i_id,
                "kind": "split-coupon",
                "input_label": projection["output_label"],
                "left_label": inclusion["output_labels"][0],
                "right_label": inclusion["output_labels"][1],
                "multiplicity": inclusion["multiplicity"],
                "ports": i_ports,
                "cyclic_order": i_cyclic,
                "port_variance": i_variance,
                "provenance": {"coupon_node_id": coupon_node_id},
            }
        nodes.extend(projection_nodes.values())
        nodes.extend(inclusion_nodes.values())
        for index, factor in enumerate(factors):
            cut_id = factor["cut_id"]
            if index < factor_count - 1:
                input_targets[cut_id] = {
                    "node_id": projection_nodes[index]["node_id"], "port": "left-in"
                }
                output_sources[cut_id] = {
                    "node_id": inclusion_nodes[index]["node_id"], "port": "left-out"
                }
            else:
                input_targets[cut_id] = {
                    "node_id": projection_nodes[index - 1]["node_id"], "port": "right-in"
                }
                output_sources[cut_id] = {
                    "node_id": inclusion_nodes[index - 1]["node_id"], "port": "right-out"
                }

        internal_index = 0
        for index in range(factor_count - 2):
            label = projection_nodes[index + 1]["output_label"]
            internal_edges.append(
                {
                    "edge_id": f"edge:{coupon_node_id}:projection:{internal_index}",
                    "component": "__vacuum_projector__",
                    "label": label,
                    "from": {"node_id": projection_nodes[index + 1]["node_id"], "port": "out"},
                    "to": {"node_id": projection_nodes[index]["node_id"], "port": "right-in"},
                    "orientation": "from-to", "framing": 0,
                    "provenance": {"coupon_node_id": coupon_node_id},
                }
            )
            internal_index += 1
        internal_edges.append(
            {
                "edge_id": f"edge:{coupon_node_id}:root",
                "component": "__vacuum_projector__",
                "label": category.unit,
                "from": {"node_id": projection_nodes[0]["node_id"], "port": "out"},
                "to": {"node_id": inclusion_nodes[0]["node_id"], "port": "in"},
                "orientation": "from-to", "framing": 0,
                "provenance": {"coupon_node_id": coupon_node_id},
            }
        )
        for index in range(factor_count - 2):
            label = inclusion_nodes[index]["right_label"]
            internal_edges.append(
                {
                    "edge_id": f"edge:{coupon_node_id}:inclusion:{internal_index}",
                    "component": "__vacuum_projector__",
                    "label": label,
                    "from": {"node_id": inclusion_nodes[index]["node_id"], "port": "right-out"},
                    "to": {"node_id": inclusion_nodes[index + 1]["node_id"], "port": "in"},
                    "orientation": "from-to", "framing": 0,
                    "provenance": {"coupon_node_id": coupon_node_id},
                }
            )
            internal_index += 1

    edges = []
    for raw_edge in graph["edges"]:
        edge = copy.deepcopy(raw_edge)
        if edge["to"]["node_id"] == coupon_node_id:
            cut_id = edge["to"]["port"].removeprefix("input:")
            edge["to"] = input_targets[cut_id]
        if edge["from"]["node_id"] == coupon_node_id:
            cut_id = edge["from"]["port"].removeprefix("output:")
            edge["from"] = output_sources[cut_id]
        if edge.get("component") in component_labels:
            edge["label"] = component_labels[edge["component"]]
        edges.append(edge)
    edges.extend(internal_edges)
    result = {
        **{
            key: copy.deepcopy(value)
            for key, value in graph.items()
            if key not in {"nodes", "edges", "node_count", "edge_count", "graph_hash"}
        },
        "schema": RIBBON_GRAPH_IR_V2_SCHEMA,
        "status": "PASS_WEIGHTED_TRIVALENT_RIBBON_GRAPH_TERM",
        "nodes": nodes,
        "edges": edges,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "evaluation_status": "NOT_CONTRACTED",
    }
    result["coupon_node_ids"] = {
        special: node_id
        for special, node_id in result.get("coupon_node_ids", {}).items()
        if node_id != coupon_node_id
    }
    result["graph_hash"] = stable_json_hash(result)
    validate_ribbon_graph_ir_v2(result)
    return result


def iter_weighted_projector_terms(
    category: RibbonFusionCategoryV2,
    graph: dict[str, Any],
    component_labels: dict[str, Any],
    *,
    require_full_coherence: bool = True,
) -> Iterator[WeightedRibbonGraphTerm]:
    """Lazily expand every coupon, preserving all inverse-pairing terms."""

    validate_ribbon_category_v2(
        category, require_full_coherence=require_full_coherence
    )
    validate_ribbon_graph_ir_v2(graph)
    ordinary = set(graph["ordinary_components"])
    if set(component_labels) != ordinary:
        raise RibbonGraphContractionError(
            "component labels do not exactly match ordinary graph components"
        )

    def recurse(
        current: dict[str, Any],
        coupon_ids: tuple[str, ...],
        coefficient: complex,
        specs: tuple[ProjectorTermSpec, ...],
    ) -> Iterator[WeightedRibbonGraphTerm]:
        if not coupon_ids:
            yield WeightedRibbonGraphTerm(current, coefficient, specs)
            return
        coupon_id, *remaining = coupon_ids
        coupon = next(node for node in current["nodes"] if node["node_id"] == coupon_id)
        tree, basis, term_specs = projector_term_specs(
            category, coupon, component_labels
        )
        for spec in term_specs:
            expanded = _expand_one_coupon(
                category, current, component_labels, coupon_id, tree, basis, spec
            )
            yield from recurse(
                expanded,
                tuple(remaining),
                coefficient * spec.coefficient,
                specs + (spec,),
            )

    coupon_ids = tuple(
        graph["coupon_node_ids"][special] for special in graph["special_components"]
    )
    yield from recurse(copy.deepcopy(graph), coupon_ids, 1.0 + 0.0j, ())
