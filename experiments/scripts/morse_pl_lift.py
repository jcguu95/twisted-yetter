"""Canonical piecewise-linear lifts of Morse link diagrams into R^3.

The input Morse forms specify an exact planar event history.  This module
realizes that history by polygonal arcs, then assigns deterministic heights
which recover every declared over/under crossing under XY projection.

Special components are kept in the plane z=0.  Consequently their exact XZ
projection is intentionally edge-on and singular.  The projection analyzer
distinguishes that forced collapse from unexplained singularities and also
checks a deterministic near-XZ projection.
"""

from __future__ import annotations

from collections import defaultdict
from copy import deepcopy
import hashlib
import math
from typing import Any, Callable, Iterable

import networkx as nx

from experiments.scripts.morse_dsl import MorseBuilder
from experiments.scripts.special_dotted_morphism import replay_forms, stable_json_hash


MORSE_PL_LIFT_SCHEMA = "twisted-yetter.morse-pl-lift.v1"
PROJECTION_CERTIFICATE_SCHEMA = "twisted-yetter.pl-projection-certificate.v1"


def _piece_of(strand: str) -> str:
    return strand.rsplit(".", 1)[0]


def _jitter(key: str, scale: float) -> float:
    digest = hashlib.sha256(key.encode("utf-8")).digest()
    unit = int.from_bytes(digest[:8], "big") / float(2**64 - 1)
    return scale * (2.0 * unit - 1.0)


def _component_for(strand: str, component_by_piece: dict[str, str]) -> str:
    try:
        return component_by_piece[_piece_of(strand)]
    except KeyError as exc:
        raise ValueError(f"missing component for strand {strand!r}") from exc


class _LiftBuilder:
    def __init__(
        self,
        *,
        component_by_piece: dict[str, str],
        special_components: set[str],
        lane_spacing: float,
        event_spacing: float,
    ) -> None:
        self.component_by_piece = component_by_piece
        self.special_components = special_components
        self.lane_spacing = lane_spacing
        self.event_spacing = event_spacing
        self.vertices: list[dict[str, Any]] = []
        self.edges: list[dict[str, Any]] = []
        self.current: dict[str, str] = {}
        self.intended_crossings: list[dict[str, Any]] = []

    def _x(self, index: int) -> float:
        return self.lane_spacing * index

    def _lane_x(self, index: int, key: str) -> float:
        # A small generic perturbation preserves left-to-right order while
        # preventing long carrier arcs from collapsing in the XZ projection.
        return self._x(index) + _jitter(key, 0.11 * self.lane_spacing)

    def _ordinary_height(self, key: str) -> float:
        return 0.35 + _jitter(key, 0.045)

    def _height(self, component: str, key: str) -> float:
        if component in self.special_components:
            return 0.0
        return self._ordinary_height(key)

    def vertex(
        self,
        *,
        x: float,
        y: float,
        z: float,
        component: str,
        strands: Iterable[str],
        event_index: int,
        role: str,
    ) -> str:
        vertex_id = f"v{len(self.vertices):05d}"
        self.vertices.append(
            {
                "vertex_id": vertex_id,
                "position": [float(x), float(y), float(z)],
                "component": component,
                "strands": sorted(set(strands)),
                "event_index": event_index,
                "role": role,
            }
        )
        return vertex_id

    def edge(
        self,
        start: str,
        end: str,
        *,
        component: str,
        strand: str | None,
        event_index: int,
        role: str,
        crossing_id: str | None = None,
        passage: str | None = None,
    ) -> str:
        edge_id = f"e{len(self.edges):05d}"
        record: dict[str, Any] = {
            "edge_id": edge_id,
            "from": start,
            "to": end,
            "component": component,
            "strand": strand,
            "event_index": event_index,
            "role": role,
        }
        if crossing_id is not None:
            record["crossing_id"] = crossing_id
        if passage is not None:
            record["passage"] = passage
        self.edges.append(record)
        return edge_id

    def _boundary_vertex(
        self, strand: str, *, event_index: int, x: float, y: float, role: str
    ) -> str:
        component = _component_for(strand, self.component_by_piece)
        return self.vertex(
            x=x,
            y=y,
            z=self._height(component, f"{strand}|{event_index}|{role}"),
            component=component,
            strands=[strand],
            event_index=event_index,
            role=role,
        )

    def add_event(self, entry: dict[str, Any]) -> None:
        event_index = int(entry["form_index"])
        form = entry["form"]
        before = entry["before_order"]
        after = entry["after_order"]
        if set(before) != set(self.current):
            raise ValueError(
                f"event {event_index}: active lift state disagrees with Morse replay"
            )
        y0 = self.event_spacing * event_index
        y3 = self.event_spacing * (event_index + 1)
        y1 = y0 + 0.36 * self.event_spacing
        y2 = y0 + 0.64 * self.event_spacing
        after_vertices = {
            strand: self._boundary_vertex(
                strand,
                event_index=event_index,
                x=self._lane_x(position, f"{strand}|{event_index}|output-x"),
                y=y3,
                role="event-output",
            )
            for position, strand in enumerate(after)
        }
        kind = form["kind"]

        if kind == "cup":
            new_strands = [f"{form['piece']}.left", f"{form['piece']}.right"]
            survivors = [strand for strand in before if strand in after_vertices]
            for strand in survivors:
                component = _component_for(strand, self.component_by_piece)
                shift = self.vertex(
                    x=self._lane_x(
                        after.index(strand), f"{strand}|{event_index}|output-x"
                    ),
                    y=y1,
                    z=self._height(component, f"{strand}|{event_index}|cup-shift"),
                    component=component,
                    strands=[strand],
                    event_index=event_index,
                    role="cup-background-shift",
                )
                self.edge(
                    self.current[strand],
                    shift,
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="cup-background-shift",
                )
                self.edge(
                    shift,
                    after_vertices[strand],
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="cup-background-carrier",
                )
            left, right = new_strands
            component = _component_for(left, self.component_by_piece)
            if component != _component_for(right, self.component_by_piece):
                raise ValueError(f"event {event_index}: cup joins different components")
            apex = self.vertex(
                x=(
                    self._lane_x(
                        after.index(left), f"{left}|{event_index}|output-x"
                    )
                    + self._lane_x(
                        after.index(right), f"{right}|{event_index}|output-x"
                    )
                )
                / 2,
                y=y2,
                z=self._height(component, f"{form['piece']}|{event_index}|cup-apex"),
                component=component,
                strands=new_strands,
                event_index=event_index,
                role="cup-apex",
            )
            for strand in new_strands:
                self.edge(
                    apex,
                    after_vertices[strand],
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="cup-branch",
                )

        elif kind == "cap":
            cap_strands = list(form["strands"])
            survivors = [strand for strand in before if strand in after_vertices]
            left, right = cap_strands
            component = _component_for(left, self.component_by_piece)
            if component != _component_for(right, self.component_by_piece):
                raise ValueError(f"event {event_index}: cap joins different components")
            apex = self.vertex(
                x=(
                    self.vertices[int(self.current[left][1:])]["position"][0]
                    + self.vertices[int(self.current[right][1:])]["position"][0]
                )
                / 2,
                y=y1,
                z=self._height(component, f"cap|{event_index}|apex"),
                component=component,
                strands=cap_strands,
                event_index=event_index,
                role="cap-apex",
            )
            for strand in cap_strands:
                self.edge(
                    self.current[strand],
                    apex,
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="cap-branch",
                )
            for strand in survivors:
                survivor_component = _component_for(strand, self.component_by_piece)
                hold = self.vertex(
                    x=self.vertices[int(self.current[strand][1:])]["position"][0],
                    y=y2,
                    z=self._height(
                        survivor_component, f"{strand}|{event_index}|cap-hold"
                    ),
                    component=survivor_component,
                    strands=[strand],
                    event_index=event_index,
                    role="cap-background-hold",
                )
                self.edge(
                    self.current[strand],
                    hold,
                    component=survivor_component,
                    strand=strand,
                    event_index=event_index,
                    role="cap-background-carrier",
                )
                self.edge(
                    hold,
                    after_vertices[strand],
                    component=survivor_component,
                    strand=strand,
                    event_index=event_index,
                    role="cap-background-shift",
                )

        elif kind == "cross":
            over, under = form["over"], form["under"]
            crossing_id = f"x{event_index + 1:03d}"
            center_x = (
                self.vertices[int(self.current[over][1:])]["position"][0]
                + self.vertices[int(self.current[under][1:])]["position"][0]
            ) / 2
            centers: dict[str, str] = {}
            center_heights: dict[str, float] = {}
            for passage, strand in (("over", over), ("under", under)):
                component = _component_for(strand, self.component_by_piece)
                if component in self.special_components:
                    height = 0.0
                elif passage == "over":
                    height = 1.0 + _jitter(f"{crossing_id}|over", 0.035)
                else:
                    height = -1.0 + _jitter(f"{crossing_id}|under", 0.035)
                center_heights[passage] = height
                centers[passage] = self.vertex(
                    x=center_x,
                    y=(y0 + y3) / 2,
                    z=height,
                    component=component,
                    strands=[strand],
                    event_index=event_index,
                    role=f"crossing-{passage}-center",
                )
                self.edge(
                    self.current[strand],
                    centers[passage],
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="crossing-approach",
                    crossing_id=crossing_id,
                    passage=passage,
                )
                self.edge(
                    centers[passage],
                    after_vertices[strand],
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="crossing-departure",
                    crossing_id=crossing_id,
                    passage=passage,
                )
            if center_heights["over"] <= center_heights["under"]:
                raise ValueError(f"event {event_index}: lift reverses over/under height")
            for strand in before:
                if strand in {over, under}:
                    continue
                component = _component_for(strand, self.component_by_piece)
                self.edge(
                    self.current[strand],
                    after_vertices[strand],
                    component=component,
                    strand=strand,
                    event_index=event_index,
                    role="crossing-background-carrier",
                )
            self.intended_crossings.append(
                {
                    "crossing_id": crossing_id,
                    "event_index": event_index,
                    "xy": [center_x, (y0 + y3) / 2],
                    "over": over,
                    "under": under,
                    "over_component": _component_for(over, self.component_by_piece),
                    "under_component": _component_for(under, self.component_by_piece),
                    "over_z": center_heights["over"],
                    "under_z": center_heights["under"],
                    "declared_sign": form.get("sign"),
                }
            )

        elif kind == "kink":
            raise ValueError(
                "canonical PL lift does not yet lower compact kink forms; expand them first"
            )
        else:
            raise ValueError(f"event {event_index}: unsupported form kind {kind!r}")
        self.current = after_vertices


def _graph_integrity(lift: dict[str, Any]) -> dict[str, Any]:
    vertices = {vertex["vertex_id"]: vertex for vertex in lift["vertices"]}
    adjacency: dict[str, list[str]] = defaultdict(list)
    edge_components: dict[str, set[str]] = defaultdict(set)
    for edge in lift["edges"]:
        start, end = edge["from"], edge["to"]
        if start not in vertices or end not in vertices:
            raise ValueError(f"edge {edge['edge_id']} has missing endpoint")
        if vertices[start]["component"] != edge["component"]:
            raise ValueError(f"edge {edge['edge_id']} start component mismatch")
        if vertices[end]["component"] != edge["component"]:
            raise ValueError(f"edge {edge['edge_id']} end component mismatch")
        adjacency[start].append(end)
        adjacency[end].append(start)
        edge_components[edge["component"]].update((start, end))
    wrong_degree = {
        vertex_id: len(neighbors)
        for vertex_id, neighbors in adjacency.items()
        if len(neighbors) != 2
    }
    if wrong_degree:
        raise ValueError(f"PL link is not a union of degree-two cycles: {wrong_degree}")
    cycle_counts: dict[str, int] = {}
    for component, component_vertices in edge_components.items():
        remaining = set(component_vertices)
        count = 0
        while remaining:
            count += 1
            seed = next(iter(remaining))
            stack = [seed]
            seen = set()
            while stack:
                current = stack.pop()
                if current in seen:
                    continue
                seen.add(current)
                stack.extend(adjacency[current])
            remaining -= seen
        cycle_counts[component] = count
    if any(count != 1 for count in cycle_counts.values()):
        raise ValueError(f"component does not form one PL cycle: {cycle_counts}")
    return {
        "vertex_count": len(vertices),
        "edge_count": len(lift["edges"]),
        "component_cycle_counts": dict(sorted(cycle_counts.items())),
        "all_vertices_degree_two": True,
    }


def build_morse_pl_lift(
    forms: Iterable[dict[str, Any]],
    *,
    component_by_piece: dict[str, str],
    special_components: Iterable[str] = (),
    lane_spacing: float = 2.0,
    event_spacing: float = 4.0,
) -> dict[str, Any]:
    """Build a deterministic PL link whose XY projection is the Morse input."""

    frozen_forms = tuple(dict(form) for form in forms)
    trace = replay_forms(frozen_forms)
    specials = set(special_components)
    declared_components = set(component_by_piece.values())
    missing_specials = specials - declared_components
    if missing_specials:
        raise ValueError(f"unknown special components: {sorted(missing_specials)!r}")
    builder = _LiftBuilder(
        component_by_piece=component_by_piece,
        special_components=specials,
        lane_spacing=lane_spacing,
        event_spacing=event_spacing,
    )
    for entry in trace:
        builder.add_event(entry)
    if builder.current:
        raise ValueError(f"PL lift ended with active strands: {sorted(builder.current)!r}")
    lift = {
        "schema": MORSE_PL_LIFT_SCHEMA,
        "status": "CANONICAL_PL_LIFT_CONSTRUCTED_NOT_YET_PROJECTION_CERTIFIED",
        "input_hash": stable_json_hash(
            {
                "forms": frozen_forms,
                "component_by_piece": component_by_piece,
                "special_components": sorted(specials),
            }
        ),
        "coordinate_convention": {
            "xy": "original Morse projection; y increases with event time",
            "z": "projection depth; greater z is over",
            "special_components": "fixed pointwise in z=0",
            "ordinary_baseline": "deterministic positive height with local crossing excursions",
            "metric_status": "canonical combinatorial realization, not recovered source geometry",
        },
        "special_components": sorted(specials),
        "component_by_piece": dict(sorted(component_by_piece.items())),
        "forms_count": len(frozen_forms),
        "vertices": builder.vertices,
        "edges": builder.edges,
        "intended_crossings": builder.intended_crossings,
    }
    lift["integrity"] = _graph_integrity(lift)
    lift["lift_hash"] = stable_json_hash(
        {key: value for key, value in lift.items() if key != "lift_hash"}
    )
    return lift


def _projection_map(name: str, tilt: float) -> tuple[
    Callable[[list[float]], tuple[float, float]], Callable[[list[float]], float]
]:
    if name == "xy":
        return lambda p: (p[0], p[1]), lambda p: p[2]
    if name == "xz":
        return lambda p: (p[0], p[2]), lambda p: p[1]
    if name == "near-xz":
        return (
            lambda p: (p[0], p[2] + tilt * p[1]),
            lambda p: p[1] - tilt * p[2],
        )
    raise ValueError(f"unknown projection {name!r}")


def _cross2(a: tuple[float, float], b: tuple[float, float]) -> float:
    return a[0] * b[1] - a[1] * b[0]


def _segment_intersection(
    p: tuple[float, float],
    p2: tuple[float, float],
    q: tuple[float, float],
    q2: tuple[float, float],
    *,
    tolerance: float,
) -> dict[str, Any] | None:
    r = (p2[0] - p[0], p2[1] - p[1])
    s = (q2[0] - q[0], q2[1] - q[1])
    rxs = _cross2(r, s)
    qmp = (q[0] - p[0], q[1] - p[1])
    qmpxr = _cross2(qmp, r)
    if abs(rxs) <= tolerance:
        if abs(qmpxr) > tolerance:
            return None
        rr = r[0] * r[0] + r[1] * r[1]
        ss = s[0] * s[0] + s[1] * s[1]
        if rr <= tolerance or ss <= tolerance:
            return {"kind": "degenerate-segment"}
        t0 = (qmp[0] * r[0] + qmp[1] * r[1]) / rr
        t1 = t0 + (s[0] * r[0] + s[1] * r[1]) / rr
        lo, hi = max(0.0, min(t0, t1)), min(1.0, max(t0, t1))
        if hi - lo <= tolerance:
            return None
        return {
            "kind": "collinear-overlap",
            "parameter_interval_a": [lo, hi],
        }
    t = _cross2(qmp, s) / rxs
    u = _cross2(qmp, r) / rxs
    if -tolerance <= t <= 1.0 + tolerance and -tolerance <= u <= 1.0 + tolerance:
        t = min(1.0, max(0.0, t))
        u = min(1.0, max(0.0, u))
        return {
            "kind": "point",
            "point": [p[0] + t * r[0], p[1] + t * r[1]],
            "parameter_a": t,
            "parameter_b": u,
            "transverse": abs(rxs) > tolerance,
            "interior_a": tolerance < t < 1.0 - tolerance,
            "interior_b": tolerance < u < 1.0 - tolerance,
        }
    return None


def analyze_projection(
    lift: dict[str, Any],
    projection: str,
    *,
    tilt: float = 0.0137,
    tolerance: float = 1e-9,
    max_examples: int = 50,
) -> dict[str, Any]:
    """Classify regular crossings and projection singularities."""

    project, depth = _projection_map(projection, tilt)
    vertices = {vertex["vertex_id"]: vertex for vertex in lift["vertices"]}
    edges = lift["edges"]
    geometry = {}
    for edge in edges:
        p3 = vertices[edge["from"]]["position"]
        q3 = vertices[edge["to"]]["position"]
        geometry[edge["edge_id"]] = {
            "p": project(p3),
            "q": project(q3),
            "depth_p": depth(p3),
            "depth_q": depth(q3),
        }
    counts: dict[str, int] = defaultdict(int)
    examples: dict[str, list[dict[str, Any]]] = defaultdict(list)
    crossing_ids_seen: set[str] = set()
    point_incidence: dict[tuple[float, float], dict[str, Any]] = defaultdict(
        lambda: {"passages": set(), "edges": set(), "components": set()}
    )

    def record(kind: str, payload: dict[str, Any]) -> None:
        counts[kind] += 1
        if len(examples[kind]) < max_examples:
            examples[kind].append(payload)

    for left_index, left_edge in enumerate(edges):
        left_geometry = geometry[left_edge["edge_id"]]
        lminx, lmaxx = sorted((left_geometry["p"][0], left_geometry["q"][0]))
        lminy, lmaxy = sorted((left_geometry["p"][1], left_geometry["q"][1]))
        for right_edge in edges[left_index + 1 :]:
            if {left_edge["from"], left_edge["to"]} & {
                right_edge["from"],
                right_edge["to"],
            }:
                continue
            right_geometry = geometry[right_edge["edge_id"]]
            rminx, rmaxx = sorted((right_geometry["p"][0], right_geometry["q"][0]))
            rminy, rmaxy = sorted((right_geometry["p"][1], right_geometry["q"][1]))
            if lmaxx < rminx - tolerance or rmaxx < lminx - tolerance:
                continue
            if lmaxy < rminy - tolerance or rmaxy < lminy - tolerance:
                continue
            intersection = _segment_intersection(
                left_geometry["p"],
                left_geometry["q"],
                right_geometry["p"],
                right_geometry["q"],
                tolerance=tolerance,
            )
            if intersection is None:
                continue
            payload = {
                "left_edge": left_edge["edge_id"],
                "right_edge": right_edge["edge_id"],
                "left_component": left_edge["component"],
                "right_component": right_edge["component"],
                **intersection,
            }
            if intersection["kind"] == "collinear-overlap":
                both_special = (
                    left_edge["component"] in lift["special_components"]
                    and right_edge["component"] in lift["special_components"]
                )
                if projection == "xz" and both_special:
                    record("expected_special_edge_on_overlap", payload)
                else:
                    record("unexplained_collinear_overlap", payload)
                continue
            if intersection["kind"] == "degenerate-segment":
                left_length2 = sum(
                    (left_geometry["q"][axis] - left_geometry["p"][axis]) ** 2
                    for axis in (0, 1)
                )
                right_length2 = sum(
                    (right_geometry["q"][axis] - right_geometry["p"][axis]) ** 2
                    for axis in (0, 1)
                )
                special_edge_collapsed = (
                    left_edge["component"] in lift["special_components"]
                    and left_length2 <= tolerance
                ) or (
                    right_edge["component"] in lift["special_components"]
                    and right_length2 <= tolerance
                )
                if projection == "xz" and special_edge_collapsed:
                    record("expected_special_edge_on_degenerate_segment", payload)
                else:
                    record("unexplained_degenerate_segment", payload)
                continue
            t, u = intersection["parameter_a"], intersection["parameter_b"]
            point_key = tuple(round(value, 8) for value in intersection["point"])

            def passage_key(edge: dict[str, Any]) -> str:
                if edge.get("crossing_id") and edge.get("passage"):
                    return f"{edge['crossing_id']}:{edge['passage']}"
                return edge["edge_id"]

            incidence = point_incidence[point_key]
            incidence["passages"].update(
                (passage_key(left_edge), passage_key(right_edge))
            )
            incidence["edges"].update(
                (left_edge["edge_id"], right_edge["edge_id"])
            )
            incidence["components"].update(
                (left_edge["component"], right_edge["component"])
            )
            left_depth = left_geometry["depth_p"] + t * (
                left_geometry["depth_q"] - left_geometry["depth_p"]
            )
            right_depth = right_geometry["depth_p"] + u * (
                right_geometry["depth_q"] - right_geometry["depth_p"]
            )
            payload["depth_difference"] = left_depth - right_depth
            same_declared_crossing = (
                projection == "xy"
                and left_edge.get("crossing_id") is not None
                and left_edge.get("crossing_id") == right_edge.get("crossing_id")
                and left_edge.get("passage") != right_edge.get("passage")
            )
            if same_declared_crossing:
                crossing_ids_seen.add(left_edge["crossing_id"])
                record("declared_xy_crossing_pair", payload)
            elif projection == "xz" and (
                left_edge["component"] in lift["special_components"]
                or right_edge["component"] in lift["special_components"]
            ):
                record("expected_special_edge_on_point", payload)
            elif not intersection["transverse"]:
                record("unexplained_tangency", payload)
            elif not intersection["interior_a"] or not intersection["interior_b"]:
                record("unexplained_projected_vertex_contact", payload)
            elif abs(left_depth - right_depth) <= tolerance:
                record("unexplained_equal_depth_double_point", payload)
            else:
                record("regular_double_point", payload)

    for point, incidence in point_incidence.items():
        if len(incidence["passages"]) < 3:
            continue
        payload = {
            "point": list(point),
            "passages": sorted(incidence["passages"]),
            "edges": sorted(incidence["edges"]),
            "components": sorted(incidence["components"]),
        }
        if projection == "xz" and (
            set(incidence["components"]) & set(lift["special_components"])
        ):
            record("expected_special_edge_on_multi_point", payload)
        else:
            record("unexplained_multi_point", payload)

    expected_crossing_ids = {
        crossing["crossing_id"] for crossing in lift["intended_crossings"]
    }
    missing_crossings = sorted(expected_crossing_ids - crossing_ids_seen)
    unexplained_keys = [key for key in counts if key.startswith("unexplained_")]
    unexplained_count = sum(counts[key] for key in unexplained_keys)
    if projection == "xy":
        status = (
            "PASS_XY_COMBINATORIAL_ROUND_TRIP"
            if not missing_crossings and unexplained_count == 0
            else "FAIL_XY_PROJECTION_MISMATCH"
        )
    elif projection == "xz":
        if unexplained_count:
            status = "FAIL_XZ_HAS_UNEXPLAINED_SINGULARITY"
        elif lift["special_components"]:
            status = "PASS_XZ_ONLY_EXPECTED_SPECIAL_EDGE_ON_SINGULARITY"
        else:
            status = "PASS_XZ_GENERIC_PROJECTION"
    else:
        status = (
            "PASS_NEAR_XZ_GENERIC_PROJECTION"
            if unexplained_count == 0
            else "FAIL_NEAR_XZ_HAS_UNEXPLAINED_SINGULARITY"
        )
    return {
        "schema": PROJECTION_CERTIFICATE_SCHEMA,
        "status": status,
        "projection": projection,
        "tilt": tilt if projection == "near-xz" else 0.0,
        "lift_hash": lift["lift_hash"],
        "counts": dict(sorted(counts.items())),
        "unexplained_singularity_count": unexplained_count,
        "missing_declared_crossings": missing_crossings,
        "declared_crossing_count": len(expected_crossing_ids),
        "declared_crossings_recovered": len(crossing_ids_seen),
        "examples": dict(sorted(examples.items())),
    }


def _component_cycle_vertices(lift: dict[str, Any], component: str) -> list[str]:
    adjacency: dict[str, list[str]] = defaultdict(list)
    for edge in lift["edges"]:
        if edge["component"] != component:
            continue
        adjacency[edge["from"]].append(edge["to"])
        adjacency[edge["to"]].append(edge["from"])
    if not adjacency or any(len(neighbors) != 2 for neighbors in adjacency.values()):
        raise ValueError(f"component {component!r} is not one polygonal cycle")
    start = min(adjacency)
    previous: str | None = None
    current = start
    cycle = []
    while True:
        cycle.append(current)
        choices = [neighbor for neighbor in adjacency[current] if neighbor != previous]
        if not choices:
            raise ValueError(f"component {component!r} traversal stopped early")
        following = min(choices) if previous is None else choices[0]
        previous, current = current, following
        if current == start:
            break
        if len(cycle) > len(adjacency):
            raise ValueError(f"component {component!r} traversal did not close")
    if len(cycle) != len(adjacency):
        raise ValueError(f"component {component!r} has more than one cycle")
    return cycle


def _point_in_polygon(point: tuple[float, float], polygon: list[tuple[float, float]]) -> bool:
    x, y = point
    inside = False
    for left, right in zip(polygon, polygon[1:] + polygon[:1], strict=True):
        x1, y1 = left
        x2, y2 = right
        if (y1 > y) == (y2 > y):
            continue
        crossing_x = x1 + (y - y1) * (x2 - x1) / (y2 - y1)
        if crossing_x > x:
            inside = not inside
    return inside


def concrete_special_disk_intersections(
    lift: dict[str, Any], special_component: str, *, tolerance: float = 1e-9
) -> dict[str, Any]:
    """Intersect ordinary PL edges with the planar disk bounded by SPECIAL."""

    if special_component not in lift["special_components"]:
        raise ValueError(f"{special_component!r} is not declared special")
    vertices = {vertex["vertex_id"]: vertex for vertex in lift["vertices"]}
    cycle = _component_cycle_vertices(lift, special_component)
    polygon = [tuple(vertices[vertex]["position"][:2]) for vertex in cycle]
    intersections = []
    boundary_tangencies = []
    for edge in lift["edges"]:
        if edge["component"] == special_component:
            continue
        start = vertices[edge["from"]]["position"]
        end = vertices[edge["to"]]["position"]
        if abs(start[2]) <= tolerance or abs(end[2]) <= tolerance:
            boundary_tangencies.append(edge["edge_id"])
            continue
        if start[2] * end[2] >= 0:
            continue
        parameter = start[2] / (start[2] - end[2])
        point = (
            start[0] + parameter * (end[0] - start[0]),
            start[1] + parameter * (end[1] - start[1]),
        )
        if _point_in_polygon(point, polygon):
            intersections.append(
                {
                    "puncture_id": f"p{len(intersections) + 1:03d}",
                    "edge_id": edge["edge_id"],
                    "component": edge["component"],
                    "strand": edge["strand"],
                    "event_index": edge["event_index"],
                    "xy": list(point),
                    "edge_parameter": parameter,
                    "z_direction": 1 if end[2] > start[2] else -1,
                }
            )
    return {
        "status": (
            "PASS_TRANSVERSE_CONCRETE_SPECIAL_DISK_INTERSECTIONS"
            if not boundary_tangencies
            else "FAIL_ORDINARY_VERTEX_LIES_IN_SPECIAL_DISK_PLANE"
        ),
        "special_component": special_component,
        "special_cycle_vertex_count": len(cycle),
        "puncture_count": len(intersections),
        "punctures": intersections,
        "ordinary_zero_height_endpoint_edges": boundary_tangencies,
        "model_scope": (
            "intersections of the canonical PL realization with its planar z=0 disk; "
            "not claimed minimal"
        ),
    }


def optimize_special_disk_sides(
    lift: dict[str, Any], special_component: str
) -> dict[str, Any]:
    """Minimize geometric disk punctures subject to crossing-height order.

    Source-side min-cut vertices mean z>0 and sink-side vertices mean z<0.
    An ordinary edge wholly inside the special disk pays one unit exactly
    when its endpoint signs differ.  Crossing inequalities are hard directed
    implications and special/ordinary crossings fix the ordinary sign.
    """

    if special_component not in lift["special_components"]:
        raise ValueError(f"{special_component!r} is not declared special")
    vertices = {vertex["vertex_id"]: vertex for vertex in lift["vertices"]}
    cycle = _component_cycle_vertices(lift, special_component)
    polygon = [tuple(vertices[vertex]["position"][:2]) for vertex in cycle]
    ordinary_vertex_ids = {
        vertex_id
        for vertex_id, vertex in vertices.items()
        if vertex["component"] != special_component
    }
    inside_edges = []
    for edge in lift["edges"]:
        if edge["component"] == special_component:
            continue
        start = vertices[edge["from"]]["position"]
        end = vertices[edge["to"]]["position"]
        midpoint = ((start[0] + end[0]) / 2, (start[1] + end[1]) / 2)
        if _point_in_polygon(midpoint, polygon):
            inside_edges.append(edge)

    ordinary_edges = [
        edge
        for edge in lift["edges"]
        if edge["component"] != special_component
    ]
    inside_edge_ids = {edge["edge_id"] for edge in inside_edges}
    outside_edges = [
        edge for edge in ordinary_edges if edge["edge_id"] not in inside_edge_ids
    ]
    # Lexicographic objective: first minimize disk punctures, then minimize
    # all remaining side changes outside the disk.  One inside transition is
    # more expensive than every outside transition combined.
    inside_priority = float(len(outside_edges) + 1)
    maximum_soft_cost = (
        inside_priority * len(inside_edges) + len(outside_edges)
    )
    hard_capacity = float(maximum_soft_cost + 1)
    source = "__positive_side__"
    sink = "__negative_side__"
    flow = nx.DiGraph()
    flow.add_nodes_from([source, sink, *sorted(ordinary_vertex_ids)])

    def add_capacity(left: str, right: str, amount: float) -> None:
        previous = flow.get_edge_data(left, right, {}).get("capacity", 0.0)
        flow.add_edge(left, right, capacity=previous + amount)

    for edge in ordinary_edges:
        left, right = edge["from"], edge["to"]
        weight = inside_priority if edge["edge_id"] in inside_edge_ids else 1.0
        add_capacity(left, right, weight)
        add_capacity(right, left, weight)

    centers: dict[tuple[int, str], str] = {}
    for vertex in lift["vertices"]:
        role = vertex["role"]
        if role == "crossing-over-center":
            centers[(vertex["event_index"], "over")] = vertex["vertex_id"]
        elif role == "crossing-under-center":
            centers[(vertex["event_index"], "under")] = vertex["vertex_id"]

    fixed: dict[str, int] = {}
    implications = []
    for crossing in lift["intended_crossings"]:
        event_index = crossing["event_index"]
        over_vertex = centers[(event_index, "over")]
        under_vertex = centers[(event_index, "under")]
        over_special = crossing["over_component"] == special_component
        under_special = crossing["under_component"] == special_component
        if over_special and under_special:
            raise ValueError("special component has a self-crossing")
        if under_special:
            fixed[over_vertex] = 1
        elif over_special:
            fixed[under_vertex] = -1
        else:
            # Forbid under>0 together with over<0.
            add_capacity(under_vertex, over_vertex, hard_capacity)
            implications.append(
                {
                    "event_index": event_index,
                    "under_vertex": under_vertex,
                    "over_vertex": over_vertex,
                }
            )

    for vertex_id, sign in fixed.items():
        if sign > 0:
            add_capacity(source, vertex_id, hard_capacity)
        else:
            add_capacity(vertex_id, sink, hard_capacity)

    cut_value, partition = nx.minimum_cut(flow, source, sink, capacity="capacity")
    positive, negative = partition
    assignment = {
        vertex_id: (1 if vertex_id in positive else -1)
        for vertex_id in sorted(ordinary_vertex_ids)
    }
    fixed_violations = [
        vertex_id
        for vertex_id, sign in fixed.items()
        if assignment[vertex_id] != sign
    ]
    implication_violations = [
        item
        for item in implications
        if assignment[item["under_vertex"]] > 0
        and assignment[item["over_vertex"]] < 0
    ]
    puncture_edges = [
        edge
        for edge in inside_edges
        if assignment[edge["from"]] != assignment[edge["to"]]
    ]
    outside_sign_change_edges = [
        edge
        for edge in outside_edges
        if assignment[edge["from"]] != assignment[edge["to"]]
    ]
    if fixed_violations or implication_violations:
        raise ValueError(
            "minimum cut violated hard crossing constraints: "
            f"fixed={fixed_violations!r}, implications={implication_violations!r}"
        )
    expected_cut_value = (
        inside_priority * len(puncture_edges) + len(outside_sign_change_edges)
    )
    if abs(cut_value - expected_cut_value) > 1e-9:
        raise ValueError(
            f"min-cut value {cut_value} disagrees with expected {expected_cut_value}"
        )
    return {
        "schema": "twisted-yetter.special-disk-side-optimization.v1",
        "status": "PASS_EXACT_MINIMUM_CUT_SIDE_ASSIGNMENT",
        "lift_hash": lift["lift_hash"],
        "special_component": special_component,
        "objective": "minimize sign-changing ordinary PL edges inside planar special disk",
        "solver": "networkx.minimum_cut",
        "inside_edge_count": len(inside_edges),
        "outside_edge_count": len(outside_edges),
        "inside_priority": inside_priority,
        "fixed_sign_count": len(fixed),
        "ordinary_crossing_implication_count": len(implications),
        "minimum_puncture_count": len(puncture_edges),
        "puncture_edge_ids": [edge["edge_id"] for edge in puncture_edges],
        "outside_sign_change_count": len(outside_sign_change_edges),
        "outside_sign_change_edge_ids": [
            edge["edge_id"] for edge in outside_sign_change_edges
        ],
        "positive_vertex_count": sum(sign > 0 for sign in assignment.values()),
        "negative_vertex_count": sum(sign < 0 for sign in assignment.values()),
        "assignment": assignment,
        "assignment_hash": stable_json_hash(assignment),
        "hard_capacity": hard_capacity,
        "fixed_constraints_satisfied": True,
        "crossing_implications_satisfied": True,
    }


def build_blockwise_flat_side_lift(
    lift: dict[str, Any],
    optimization: dict[str, Any],
    *,
    bump_fraction: float = 0.12,
    crossing_height_mode: str = "fixed-extremes",
    crossing_margin: float = 1e-3,
    block_order_strategy: str = "stable",
    block_order_angle_degrees: float = 70.0,
) -> dict[str, Any]:
    """Realize an optimized sign assignment with flat arc blocks.

    Ordinary arcs stay at one z-level between sign-changing edges.  Crossing
    height adjustments are confined to BUMP_FRACTION of each crossing arm.
    The XY polygonal diagram is unchanged.
    """

    if not 0.0 < bump_fraction < 0.5:
        raise ValueError("bump_fraction must lie strictly between 0 and 1/2")
    if crossing_height_mode not in {"fixed-extremes", "minimal-local"}:
        raise ValueError(f"unknown crossing height mode {crossing_height_mode!r}")
    if crossing_margin <= 0:
        raise ValueError("crossing_margin must be positive")
    block_order_strategies = {
        "stable",
        "stable-reverse",
        "projected-mean-ascending",
        "projected-mean-descending",
        "projected-median-ascending",
        "projected-median-descending",
    }
    if block_order_strategy not in block_order_strategies:
        raise ValueError(f"unknown block order strategy {block_order_strategy!r}")
    if optimization["lift_hash"] != lift["lift_hash"]:
        raise ValueError("side assignment belongs to a different PL lift")
    special_component = optimization["special_component"]
    assignment = optimization["assignment"]
    flattened = deepcopy(lift)
    vertices = {vertex["vertex_id"]: vertex for vertex in flattened["vertices"]}

    adjacency: dict[str, list[str]] = defaultdict(list)
    for edge in flattened["edges"]:
        if edge["component"] == special_component:
            continue
        left, right = edge["from"], edge["to"]
        if assignment[left] != assignment[right]:
            continue
        adjacency[left].append(right)
        adjacency[right].append(left)
    remaining = set(assignment)
    blocks: list[list[str]] = []
    while remaining:
        seed = min(remaining)
        stack = [seed]
        block = set()
        while stack:
            current = stack.pop()
            if current in block:
                continue
            block.add(current)
            stack.extend(adjacency[current])
        remaining -= block
        blocks.append(sorted(block))
    blocks.sort(key=lambda block: block[0])
    block_by_vertex = {
        vertex_id: block_index
        for block_index, block in enumerate(blocks)
        for vertex_id in block
    }
    by_sign = {
        sign: [
            index
            for index, block in enumerate(blocks)
            if assignment[block[0]] == sign
        ]
        for sign in (-1, 1)
    }
    order_radians = math.radians(block_order_angle_degrees)
    order_cosine = math.cos(order_radians)
    order_sine = math.sin(order_radians)

    def projected_coordinate(vertex_id: str) -> float:
        x, y, _ = vertices[vertex_id]["position"]
        return order_cosine * x + order_sine * y

    def order_key(block_index: int) -> tuple[float | str, str]:
        block = blocks[block_index]
        coordinates = sorted(projected_coordinate(vertex_id) for vertex_id in block)
        if block_order_strategy.startswith("projected-mean"):
            statistic = sum(coordinates) / len(coordinates)
        elif block_order_strategy.startswith("projected-median"):
            middle = len(coordinates) // 2
            statistic = (
                coordinates[middle]
                if len(coordinates) % 2
                else (coordinates[middle - 1] + coordinates[middle]) / 2
            )
        else:
            return (block[0], block[0])
        return (statistic, block[0])

    reverse_order = block_order_strategy in {
        "stable-reverse",
        "projected-mean-descending",
        "projected-median-descending",
    }
    for sign in (-1, 1):
        by_sign[sign] = sorted(
            by_sign[sign], key=order_key, reverse=reverse_order
        )
    baseline_by_block: dict[int, float] = {}
    amplitude_by_sign: dict[int, float] = {}
    for sign, indices in by_sign.items():
        count = len(indices)
        spacing = 0.70 / max(1, count - 1)
        amplitude_by_sign[sign] = min(0.008, 0.18 * spacing)
        for rank_index, block_index in enumerate(indices):
            offset = 0.0 if count <= 1 else 0.70 * rank_index / (count - 1)
            baseline_by_block[block_index] = sign * (0.65 + offset)

    smooth_height_by_vertex: dict[str, float] = {}
    for block_index, block in enumerate(blocks):
        sign = assignment[block[0]]
        baseline = baseline_by_block[block_index]
        amplitude = amplitude_by_sign[sign]
        block_set = set(block)
        local_adjacency = {
            vertex_id: [
                neighbor
                for neighbor in adjacency[vertex_id]
                if neighbor in block_set
            ]
            for vertex_id in block
        }
        endpoints = sorted(
            vertex_id
            for vertex_id, neighbors in local_adjacency.items()
            if len(neighbors) == 1
        )
        start = endpoints[0] if endpoints else min(block)
        ordered = []
        previous = None
        current = start
        while current not in ordered:
            ordered.append(current)
            choices = [
                neighbor
                for neighbor in local_adjacency[current]
                if neighbor != previous
            ]
            if not choices:
                break
            following = min(choices) if previous is None else choices[0]
            previous, current = current, following
        if set(ordered) != block_set:
            raise ValueError(f"flat block {block_index} is not a path or cycle")
        phase = _jitter(f"block|{block_index}|phase", math.pi)
        for position, vertex_id in enumerate(ordered):
            if len(ordered) <= 1:
                smooth = 0.0
            elif endpoints:
                smooth = amplitude * (2.0 * position / (len(ordered) - 1) - 1.0)
            else:
                angle = 2.0 * math.pi * position / len(ordered)
                smooth = amplitude * (
                    math.sin(angle + phase)
                    + 0.31 * math.sin(2.0 * angle + 0.7 * phase)
                )
            smooth_height_by_vertex[vertex_id] = baseline + smooth

    for vertex in flattened["vertices"]:
        if vertex["component"] == special_component:
            vertex["position"][2] = 0.0
            continue
        vertex["position"][2] = float(
            smooth_height_by_vertex[vertex["vertex_id"]]
        )

    original_centers = {
        (vertex["event_index"], vertex["role"]): vertex
        for vertex in flattened["vertices"]
        if vertex["role"] in {
            "crossing-over-center",
            "crossing-under-center",
        }
    }
    adjusted_crossing_count = 0
    if crossing_height_mode == "fixed-extremes":
        for (event_index, role), center in original_centers.items():
            if center["component"] == special_component:
                continue
            sign = assignment[center["vertex_id"]]
            if role == "crossing-over-center":
                center["position"][2] = 1.80 if sign > 0 else -0.30
            else:
                center["position"][2] = 0.30 if sign > 0 else -1.80
            adjusted_crossing_count += 1
    else:
        for crossing in flattened["intended_crossings"]:
            event_index = crossing["event_index"]
            over = original_centers[(event_index, "crossing-over-center")]
            under = original_centers[(event_index, "crossing-under-center")]
            over_height = over["position"][2]
            under_height = under["position"][2]
            if over_height <= under_height + crossing_margin:
                midpoint = (over_height + under_height) / 2
                over["position"][2] = midpoint + crossing_margin / 2
                under["position"][2] = midpoint - crossing_margin / 2
                adjusted_crossing_count += 1

    next_vertex_index = len(flattened["vertices"])
    rebuilt_edges = []
    localized_crossing_arm_count = 0
    for edge in flattened["edges"]:
        if edge["component"] == special_component or edge["role"] not in {
            "crossing-approach",
            "crossing-departure",
        }:
            rebuilt_edges.append(dict(edge))
            continue
        start = vertices[edge["from"]]
        end = vertices[edge["to"]]
        if edge["role"] == "crossing-approach":
            outer, center = start, end
            parameter = 1.0 - bump_fraction
        else:
            center, outer = start, end
            parameter = bump_fraction
        shoulder_position = [
            start["position"][axis]
            + parameter * (end["position"][axis] - start["position"][axis])
            for axis in range(3)
        ]
        height_delta = center["position"][2] - outer["position"][2]
        if abs(height_delta) <= 1e-12:
            height_delta = 1e-6 * assignment[outer["vertex_id"]]
        shoulder_position[2] = outer["position"][2] + 1e-4 * height_delta
        shoulder_id = f"v{next_vertex_index:05d}"
        next_vertex_index += 1
        shoulder = {
            "vertex_id": shoulder_id,
            "position": shoulder_position,
            "component": edge["component"],
            "strands": sorted(set(start["strands"] + end["strands"])),
            "event_index": edge["event_index"],
            "role": "crossing-bump-shoulder",
        }
        flattened["vertices"].append(shoulder)
        if edge["role"] == "crossing-approach":
            outer_edge = {
                **edge,
                "to": shoulder_id,
                "role": "crossing-flat-carrier",
            }
            local_edge = {**edge, "from": shoulder_id}
        else:
            local_edge = {**edge, "to": shoulder_id}
            outer_edge = {
                **edge,
                "from": shoulder_id,
                "role": "crossing-flat-carrier",
            }
        for carrier in (outer_edge, local_edge):
            if carrier["role"] == "crossing-flat-carrier":
                carrier.pop("crossing_id", None)
                carrier.pop("passage", None)
        rebuilt_edges.extend((outer_edge, local_edge))
        localized_crossing_arm_count += 1

    for index, edge in enumerate(rebuilt_edges):
        edge["edge_id"] = f"e{index:05d}"
    flattened["edges"] = rebuilt_edges
    centers = {
        (vertex["event_index"], vertex["role"]): vertex
        for vertex in flattened["vertices"]
        if vertex["role"] in {
            "crossing-over-center",
            "crossing-under-center",
        }
    }
    for crossing in flattened["intended_crossings"]:
        over = centers[(crossing["event_index"], "crossing-over-center")]
        under = centers[(crossing["event_index"], "crossing-under-center")]
        if over["position"][2] <= under["position"][2]:
            raise ValueError(
                f"blockwise heights reverse crossing at event {crossing['event_index']}"
            )
        crossing["over_z"] = over["position"][2]
        crossing["under_z"] = under["position"][2]
    flattened["status"] = "CANONICAL_PL_LIFT_WITH_BLOCKWISE_FLAT_Z"
    flattened["blockwise_flattening"] = {
        "block_count": len(blocks),
        "positive_block_count": len(by_sign[1]),
        "negative_block_count": len(by_sign[-1]),
        "localized_crossing_arm_count": localized_crossing_arm_count,
        "bump_fraction": bump_fraction,
        "crossing_height_mode": crossing_height_mode,
        "crossing_margin": crossing_margin,
        "crossings_requiring_height_adjustment": adjusted_crossing_count,
        "block_order_strategy": block_order_strategy,
        "block_order_angle_degrees": block_order_angle_degrees,
        "block_order_by_sign": {
            str(sign): [f"block{index:03d}" for index in by_sign[sign]]
            for sign in (-1, 1)
        },
        "blocks": {
            f"block{index:03d}": {
                "sign": assignment[block[0]],
                "vertex_ids": block,
            }
            for index, block in enumerate(blocks)
        },
        "within_block_height_model": (
            "open paths have tiny monotone slopes; closed cycles have tiny smooth waves"
        ),
        "maximum_within_block_amplitude": max(amplitude_by_sign.values()),
        "assignment_hash": optimization["assignment_hash"],
    }
    flattened.pop("lift_hash", None)
    flattened["lift_hash"] = stable_json_hash(
        {key: value for key, value in flattened.items() if key != "lift_hash"}
    )
    flattened["integrity"] = _graph_integrity(flattened)
    return flattened


def make_exact_side_projection_lift(
    lift: dict[str, Any], special_component: str, angle_degrees: float
) -> dict[str, Any]:
    """Rotate within the special disk, then remove its boundary component."""

    disk_intersections = concrete_special_disk_intersections(
        lift, special_component
    )
    if disk_intersections["status"] != (
        "PASS_TRANSVERSE_CONCRETE_SPECIAL_DISK_INTERSECTIONS"
    ):
        raise ValueError("cannot remove a special boundary with uncertified punctures")
    side = deepcopy(lift)
    radians = math.radians(angle_degrees)
    cosine, sine = math.cos(radians), math.sin(radians)
    special_cycle = _component_cycle_vertices(lift, special_component)
    source_vertices = {
        vertex["vertex_id"]: vertex for vertex in lift["vertices"]
    }
    special_disk_polygon = []
    for vertex_id in special_cycle:
        x, y, _z = source_vertices[vertex_id]["position"]
        special_disk_polygon.append(
            [cosine * x + sine * y, sine * x - cosine * y]
        )
    for vertex in side["vertices"]:
        x, y, z = vertex["position"]
        vertex["position"] = [
            cosine * x + sine * y,
            sine * x - cosine * y,
            z,
        ]
    side["edges"] = [
        edge for edge in side["edges"] if edge["component"] != special_component
    ]
    kept_vertices = {
        endpoint
        for edge in side["edges"]
        for endpoint in (edge["from"], edge["to"])
    }
    side["vertices"] = [
        vertex
        for vertex in side["vertices"]
        if vertex["vertex_id"] in kept_vertices
    ]
    side["special_components"] = []
    side["intended_crossings"] = [
        crossing
        for crossing in side["intended_crossings"]
        if crossing["over_component"] != special_component
        and crossing["under_component"] != special_component
    ]
    side["side_projection_source"] = {
        "source_lift_hash": lift["lift_hash"],
        "removed_special_component": special_component,
        "angle_degrees": angle_degrees,
        "event_coordinate": "z",
        "horizontal_coordinate": "cos(theta)*x + sin(theta)*y",
        "depth_coordinate": "sin(theta)*x - cos(theta)*y",
        "oriented_frame": "(horizontal, event, depth)",
        "oriented_frame_determinant": 1.0,
        "special_disk_polygon": special_disk_polygon,
        "special_disk_intersections": disk_intersections,
    }
    side.pop("lift_hash", None)
    side["lift_hash"] = stable_json_hash(
        {key: value for key, value in side.items() if key != "lift_hash"}
    )
    side["integrity"] = _graph_integrity(side)
    return side


def make_generic_view_projection_lift(
    lift: dict[str, Any],
    *,
    in_plane_angle_degrees: float,
    tilt_degrees: float,
) -> dict[str, Any]:
    """Rigidly rotate a complete PL link into a generic side-view frame.

    The returned coordinates are ``(horizontal, depth, event_time)``.  Unlike
    :func:`make_exact_side_projection_lift`, no component is removed and no
    projector is inserted.  A nonzero tilt prevents the planar special circle
    from collapsing to one event level.
    """

    angle = math.radians(in_plane_angle_degrees)
    tilt = math.radians(tilt_degrees)
    cosine, sine = math.cos(angle), math.sin(angle)
    tilt_cosine, tilt_sine = math.cos(tilt), math.sin(tilt)
    projected = deepcopy(lift)
    for vertex in projected["vertices"]:
        x, y, z = vertex["position"]
        horizontal = cosine * x + sine * y
        side_depth = sine * x - cosine * y
        vertex["position"] = [
            horizontal,
            tilt_cosine * side_depth - tilt_sine * z,
            tilt_sine * side_depth + tilt_cosine * z,
        ]
    projected["generic_view_source"] = {
        "source_lift_hash": lift["lift_hash"],
        "in_plane_angle_degrees": in_plane_angle_degrees,
        "tilt_degrees": tilt_degrees,
        "transform": (
            "rotate xy by in-plane angle, then rotate side-depth/z by tilt"
        ),
        "oriented_frame": "(horizontal, event, depth)",
        "oriented_frame_determinant": 1.0,
        "source_special_components": list(lift.get("special_components", ())),
        "component_removal": "none",
    }
    # This view treats every circle as an ordinary framed link component.
    projected["special_components"] = []
    projected.pop("lift_hash", None)
    projected["lift_hash"] = stable_json_hash(
        {key: value for key, value in projected.items() if key != "lift_hash"}
    )
    projected["integrity"] = _graph_integrity(projected)
    return projected


def restrict_pl_lift_components(
    lift: dict[str, Any], components: Iterable[str]
) -> dict[str, Any]:
    """Return the exact PL sublink carried by COMPONENTS."""

    retained = frozenset(components)
    available = {edge["component"] for edge in lift["edges"]}
    unknown = retained - available
    if unknown:
        raise ValueError(f"unknown PL-link components: {sorted(unknown)!r}")
    if not retained:
        raise ValueError("a PL sublink must retain at least one component")
    sublink = deepcopy(lift)
    sublink["edges"] = [
        edge for edge in sublink["edges"] if edge["component"] in retained
    ]
    kept_vertices = {
        endpoint
        for edge in sublink["edges"]
        for endpoint in (edge["from"], edge["to"])
    }
    sublink["vertices"] = [
        vertex
        for vertex in sublink["vertices"]
        if vertex["vertex_id"] in kept_vertices
    ]
    sublink["intended_crossings"] = [
        crossing
        for crossing in sublink["intended_crossings"]
        if crossing["over_component"] in retained
        and crossing["under_component"] in retained
    ]
    sublink["special_components"] = [
        component
        for component in sublink.get("special_components", ())
        if component in retained
    ]
    sublink["sublink_source"] = {
        "source_lift_hash": lift["lift_hash"],
        "retained_components": sorted(retained),
    }
    sublink.pop("lift_hash", None)
    sublink["lift_hash"] = stable_json_hash(
        {key: value for key, value in sublink.items() if key != "lift_hash"}
    )
    sublink["integrity"] = _graph_integrity(sublink)
    return sublink


def analyze_projector_gather_cost(
    side_lift: dict[str, Any], *, projector_height: float = 0.0, tolerance: float = 1e-9
) -> dict[str, Any]:
    """Find the least stable-partition braid making disk punctures contiguous."""

    vertices = {vertex["vertex_id"]: vertex for vertex in side_lift["vertices"]}
    puncture_edge_ids = {
        puncture["edge_id"]
        for puncture in side_lift["side_projection_source"][
            "special_disk_intersections"
        ]["punctures"]
    }
    active = []
    for edge in side_lift["edges"]:
        start = vertices[edge["from"]]["position"]
        end = vertices[edge["to"]]["position"]
        if abs(start[2] - projector_height) <= tolerance or abs(
            end[2] - projector_height
        ) <= tolerance:
            raise ValueError("projector slice passes through a PL vertex")
        if (start[2] - projector_height) * (end[2] - projector_height) >= 0:
            continue
        parameter = (projector_height - start[2]) / (end[2] - start[2])
        horizontal = start[0] + parameter * (end[0] - start[0])
        active.append((horizontal, edge["edge_id"]))
    active.sort()
    active_edges = [edge_id for _horizontal, edge_id in active]
    selected = [edge_id for edge_id in active_edges if edge_id in puncture_edge_ids]
    outside = [edge_id for edge_id in active_edges if edge_id not in puncture_edge_ids]
    if set(selected) != puncture_edge_ids:
        raise ValueError("not every certified disk puncture is active at the projector slice")

    def adjacent_swap_distance(target: list[str]) -> int:
        position = {edge_id: index for index, edge_id in enumerate(target)}
        permutation = [position[edge_id] for edge_id in active_edges]
        return sum(
            permutation[left] > permutation[right]
            for left in range(len(permutation))
            for right in range(left + 1, len(permutation))
        )

    candidates = []
    for outside_before in range(len(outside) + 1):
        target = outside[:outside_before] + selected + outside[outside_before:]
        candidates.append(
            {
                "outside_before": outside_before,
                "adjacent_swap_count": adjacent_swap_distance(target),
                "target_edge_order": target,
            }
        )
    best = min(
        candidates,
        key=lambda row: (row["adjacent_swap_count"], row["outside_before"]),
    )
    selected_positions = [active_edges.index(edge_id) for edge_id in selected]
    return {
        "status": "PASS_MINIMUM_STABLE_PROJECTOR_GATHER_PLAN",
        "projector_height": projector_height,
        "active_strand_count": len(active_edges),
        "puncture_strand_count": len(selected),
        "outside_strand_count": len(outside),
        "punctures_already_contiguous": selected_positions
        == list(range(min(selected_positions), max(selected_positions) + 1)),
        "minimum_adjacent_swap_count": best["adjacent_swap_count"],
        "outside_before": best["outside_before"],
        "active_edge_order": active_edges,
        "puncture_edge_order": selected,
        "target_edge_order": best["target_edge_order"],
        "candidate_costs": [
            {
                "outside_before": row["outside_before"],
                "adjacent_swap_count": row["adjacent_swap_count"],
            }
            for row in candidates
        ],
    }


def _point_segment_distance(
    point: tuple[float, float],
    left: tuple[float, float],
    right: tuple[float, float],
) -> float:
    dx, dy = right[0] - left[0], right[1] - left[1]
    length_squared = dx * dx + dy * dy
    if length_squared == 0:
        return math.hypot(point[0] - left[0], point[1] - left[1])
    parameter = max(
        0.0,
        min(
            1.0,
            ((point[0] - left[0]) * dx + (point[1] - left[1]) * dy)
            / length_squared,
        ),
    )
    closest = (left[0] + parameter * dx, left[1] + parameter * dy)
    return math.hypot(point[0] - closest[0], point[1] - closest[1])


def _polygon_boundary_distance(
    point: tuple[float, float], polygon: list[tuple[float, float]]
) -> float:
    return min(
        _point_segment_distance(point, left, right)
        for left, right in zip(polygon, polygon[1:] + polygon[:1], strict=True)
    )


def _clean_polygon(
    polygon: Iterable[Iterable[float]], *, tolerance: float
) -> list[tuple[float, float]]:
    cleaned: list[tuple[float, float]] = []
    for raw in polygon:
        point = (float(raw[0]), float(raw[1]))
        if cleaned and math.dist(point, cleaned[-1]) <= tolerance:
            continue
        cleaned.append(point)
    if len(cleaned) > 1 and math.dist(cleaned[0], cleaned[-1]) <= tolerance:
        cleaned.pop()
    if len(cleaned) < 3:
        raise ValueError("special disk polygon has fewer than three vertices")
    return cleaned


def _segment_strictly_inside_polygon(
    left: tuple[float, float],
    right: tuple[float, float],
    polygon: list[tuple[float, float]],
    *,
    tolerance: float,
) -> bool:
    for step in range(1, 4):
        parameter = step / 4
        sample = (
            left[0] + parameter * (right[0] - left[0]),
            left[1] + parameter * (right[1] - left[1]),
        )
        if not _point_in_polygon(sample, polygon):
            return False
    for boundary_left, boundary_right in zip(
        polygon, polygon[1:] + polygon[:1], strict=True
    ):
        intersection = _segment_intersection(
            left,
            right,
            boundary_left,
            boundary_right,
            tolerance=tolerance,
        )
        if intersection is None:
            continue
        if intersection["kind"] != "point":
            return False
        if intersection["interior_a"] and intersection["interior_b"]:
            return False
    return True


def _strict_disk_waypoints(
    polygon: list[tuple[float, float]], *, tolerance: float
) -> list[tuple[float, float]]:
    xs = [point[0] for point in polygon]
    ys = [point[1] for point in polygon]
    span = max(max(xs) - min(xs), max(ys) - min(ys), 1.0)
    radius = 0.001 * span
    minimum_clearance = max(10 * tolerance, 0.00002 * span)
    signed_area = sum(
        left[0] * right[1] - right[0] * left[1]
        for left, right in zip(polygon, polygon[1:] + polygon[:1], strict=True)
    ) / 2
    candidates = []
    for vertex_index, vertex in enumerate(polygon):
        previous = polygon[vertex_index - 1]
        following = polygon[(vertex_index + 1) % len(polygon)]
        turn = (
            (vertex[0] - previous[0]) * (following[1] - vertex[1])
            - (vertex[1] - previous[1]) * (following[0] - vertex[0])
        )
        if turn * signed_area >= 0:
            continue
        local = []
        for angle_index in range(24):
            angle = 2 * math.pi * angle_index / 24
            point = (
                vertex[0] + radius * math.cos(angle),
                vertex[1] + radius * math.sin(angle),
            )
            if not _point_in_polygon(point, polygon):
                continue
            if _polygon_boundary_distance(point, polygon) <= minimum_clearance:
                continue
            local.append(point)
        if not local:
            raise ValueError(f"cannot push reflex disk vertex {vertex_index} inward")
        candidates.append(
            max(local, key=lambda point: _polygon_boundary_distance(point, polygon))
        )
    return candidates


def _static_disk_visibility_graph(
    polygon: list[tuple[float, float]],
    waypoints: list[tuple[float, float]],
    *,
    tolerance: float,
) -> nx.Graph:
    graph = nx.Graph()
    for index, point in enumerate(waypoints):
        graph.add_node(index, point=point)
    for left_index, left in enumerate(waypoints):
        for right_index in range(left_index + 1, len(waypoints)):
            right = waypoints[right_index]
            if _segment_strictly_inside_polygon(
                left, right, polygon, tolerance=tolerance
            ):
                graph.add_edge(
                    left_index, right_index, weight=math.dist(left, right)
                )
    return graph


def _visibility_path_inside_disk(
    start: tuple[float, float],
    target: tuple[float, float],
    polygon: list[tuple[float, float]],
    waypoints: list[tuple[float, float]],
    static_graph: nx.Graph,
    *,
    tolerance: float,
) -> list[tuple[float, float]]:
    graph = static_graph.copy()
    start_node = len(waypoints)
    target_node = start_node + 1
    graph.add_node(start_node, point=start)
    graph.add_node(target_node, point=target)
    if _segment_strictly_inside_polygon(
        start, target, polygon, tolerance=tolerance
    ):
        graph.add_edge(start_node, target_node, weight=math.dist(start, target))
    for index, waypoint in enumerate(waypoints):
        for node, point in ((start_node, start), (target_node, target)):
            if _segment_strictly_inside_polygon(
                point, waypoint, polygon, tolerance=tolerance
            ):
                graph.add_edge(node, index, weight=math.dist(point, waypoint))
    try:
        path = nx.shortest_path(graph, start_node, target_node, weight="weight")
    except nx.NetworkXNoPath as exc:
        raise ValueError("cannot route a projector puncture inside its disk") from exc
    return [graph.nodes[index]["point"] for index in path]


def _geometric_projector_routing_plan(
    side_lift: dict[str, Any],
    edge_to_token: dict[str, str],
    *,
    projector_height: float,
    tolerance: float,
) -> dict[str, Any]:
    """Move disk punctures to one interval by an explicit in-disk isotopy."""

    vertices = {vertex["vertex_id"]: vertex for vertex in side_lift["vertices"]}
    polygon = _clean_polygon(
        side_lift["side_projection_source"]["special_disk_polygon"],
        tolerance=tolerance,
    )
    puncture_edge_ids = {
        puncture["edge_id"]
        for puncture in side_lift["side_projection_source"][
            "special_disk_intersections"
        ]["punctures"]
    }
    positions: dict[str, tuple[float, float]] = {}
    edge_by_token: dict[str, str] = {}
    for edge in side_lift["edges"]:
        start = vertices[edge["from"]]["position"]
        end = vertices[edge["to"]]["position"]
        if (start[2] - projector_height) * (end[2] - projector_height) >= 0:
            continue
        parameter = (projector_height - start[2]) / (end[2] - start[2])
        token = edge_to_token[edge["edge_id"]]
        if token in positions:
            raise ValueError(f"token {token!r} crosses the projector slice twice")
        positions[token] = (
            start[0] + parameter * (end[0] - start[0]),
            start[1] + parameter * (end[1] - start[1]),
        )
        edge_by_token[token] = edge["edge_id"]
    selected = sorted(
        (
            token
            for token, edge_id in edge_by_token.items()
            if edge_id in puncture_edge_ids
        ),
        key=lambda token: (positions[token][0], token),
    )
    outside = [token for token in positions if token not in set(selected)]
    if len(selected) != len(puncture_edge_ids):
        raise ValueError("geometric routing omitted a certified disk puncture")

    xs = [point[0] for point in polygon]
    ys = [point[1] for point in polygon]
    span = max(max(xs) - min(xs), max(ys) - min(ys), 1.0)
    outside_xs = sorted(positions[token][0] for token in outside)
    best_center: tuple[float, float] | None = None
    best_radius = -1.0
    for x_index in range(1, 80):
        x = min(xs) + x_index * (max(xs) - min(xs)) / 80
        horizontal_gap = min((abs(x - value) for value in outside_xs), default=span)
        for y_index in range(1, 80):
            y = min(ys) + y_index * (max(ys) - min(ys)) / 80
            point = (x, y)
            if not _point_in_polygon(point, polygon):
                continue
            radius = min(_polygon_boundary_distance(point, polygon), horizontal_gap)
            if radius > best_radius:
                best_center, best_radius = point, radius
    if best_center is None or best_radius <= 100 * tolerance:
        raise ValueError("special disk has no certified projector corridor")
    half_width = 0.35 * best_radius
    target_points = [
        (
            best_center[0]
            + half_width * (2 * index - len(selected) + 1) / len(selected),
            best_center[1],
        )
        for index in range(len(selected))
    ]
    if any(
        not _point_in_polygon(point, polygon)
        or _polygon_boundary_distance(point, polygon) <= 10 * tolerance
        for point in target_points
    ):
        raise ValueError("projector target interval is not strictly inside the disk")

    waypoints = _strict_disk_waypoints(polygon, tolerance=tolerance)
    static_visibility = _static_disk_visibility_graph(
        polygon, waypoints, tolerance=tolerance
    )
    routes = []
    minimum_boundary_clearance = math.inf
    minimum_point_clearance = math.inf
    routing_crossings = []
    current_positions = dict(positions)
    current_order = sorted(current_positions, key=lambda token: current_positions[token][0])
    for token, target in zip(selected, target_points, strict=True):
        path = _visibility_path_inside_disk(
            current_positions[token],
            target,
            polygon,
            waypoints,
            static_visibility,
            tolerance=tolerance,
        )
        route_crossings = []
        for segment_index, (left, right) in enumerate(
            zip(path, path[1:])
        ):
            minimum_boundary_clearance = min(
                minimum_boundary_clearance,
                *(
                    _polygon_boundary_distance(
                        (
                            left[0] + sample / 20 * (right[0] - left[0]),
                            left[1] + sample / 20 * (right[1] - left[1]),
                        ),
                        polygon,
                    )
                    for sample in range(21)
                ),
            )
            events = []
            dx = right[0] - left[0]
            if abs(dx) > tolerance:
                for stationary, stationary_point in current_positions.items():
                    if stationary == token:
                        continue
                    parameter = (stationary_point[0] - left[0]) / dx
                    if not tolerance < parameter < 1.0 - tolerance:
                        continue
                    moving_y = left[1] + parameter * (right[1] - left[1])
                    clearance = abs(moving_y - stationary_point[1])
                    minimum_point_clearance = min(minimum_point_clearance, clearance)
                    if clearance <= tolerance:
                        raise ValueError("projector routing collides with an active strand")
                    events.append((parameter, stationary, moving_y, stationary_point[1]))
            for parameter, stationary, moving_y, stationary_y in sorted(events):
                token_index = current_order.index(token)
                stationary_index = current_order.index(stationary)
                if abs(token_index - stationary_index) != 1:
                    raise ValueError(
                        "geometric projector crossing is not adjacent in active order"
                    )
                over, under = (
                    (token, stationary)
                    if moving_y > stationary_y
                    else (stationary, token)
                )
                crossing = {
                    "moving": token,
                    "neighbor": stationary,
                    "over": over,
                    "under": under,
                    "route_segment_index": segment_index,
                    "route_parameter": parameter,
                }
                route_crossings.append(crossing)
                routing_crossings.append(crossing)
                current_order[token_index], current_order[stationary_index] = (
                    current_order[stationary_index],
                    current_order[token_index],
                )
        current_positions[token] = target
        expected_order = sorted(
            current_positions, key=lambda item: (current_positions[item][0], item)
        )
        if current_order != expected_order:
            raise ValueError("projector routing braid disagrees with endpoint order")
        routes.append(
            {
                "token": token,
                "start": list(path[0]),
                "target": list(target),
                "path": [list(point) for point in path],
                "crossings": route_crossings,
            }
        )
    selected_final = [token for token in current_order if token in set(selected)]
    selected_positions = [current_order.index(token) for token in selected_final]
    if selected_positions != list(
        range(min(selected_positions), max(selected_positions) + 1)
    ):
        raise ValueError("geometric projector routing did not make punctures contiguous")
    return {
        "status": "PASS_EXPLICIT_IN_DISK_PROJECTOR_ISOTOPY",
        "projector_height": projector_height,
        "active_strand_count": len(positions),
        "puncture_strand_count": len(selected),
        "outside_strand_count": len(outside),
        "initial_order": sorted(positions, key=lambda token: (positions[token][0], token)),
        "target_order": current_order,
        "projector_order": selected_final,
        "projector_start": min(selected_positions),
        "routing_crossings": routing_crossings,
        "routing_crossing_count": len(routing_crossings),
        "routes": routes,
        "target_center": list(best_center),
        "target_half_width": half_width,
        "waypoint_count": len(waypoints),
        "minimum_boundary_clearance": minimum_boundary_clearance,
        "minimum_active_point_clearance": minimum_point_clearance,
    }


def lower_exact_side_projection_to_morse(
    side_lift: dict[str, Any],
    *,
    projector_height: float | None = 0.0,
    tolerance: float = 1e-9,
) -> dict[str, Any]:
    """Sweep a generic exact side projection into fundamental Morse forms.

    The side lift has coordinates ``(horizontal, depth, event_time)``.  Its
    special boundary has already been removed.  Every remaining component is
    split at local extrema into strictly event-monotone arc tokens.  Regular
    projected double points become crossings, and the complete active slice
    at PROJECTOR_HEIGHT becomes one collective vacuum projector.
    """

    regularity = analyze_exact_side_morse_regularity(
        side_lift, tolerance=tolerance
    )
    if regularity["status"] != "PASS_EXACT_SIDE_PL_EVENT_COORDINATE":
        raise ValueError("cannot lower a side projection with horizontal edges")
    if projector_height is not None and side_lift.get("special_components"):
        raise ValueError("exact side lowering expects the special boundary removed")
    vertices = {vertex["vertex_id"]: vertex for vertex in side_lift["vertices"]}
    edges = {edge["edge_id"]: edge for edge in side_lift["edges"]}
    adjacency: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for edge in edges.values():
        adjacency[edge["from"]].append((edge["to"], edge["edge_id"]))
        adjacency[edge["to"]].append((edge["from"], edge["edge_id"]))
    if any(len(neighbors) != 2 for neighbors in adjacency.values()):
        malformed = {
            vertex_id: len(neighbors)
            for vertex_id, neighbors in adjacency.items()
            if len(neighbors) != 2
        }
        raise ValueError(f"side link is not a union of polygonal cycles: {malformed!r}")

    extrema: dict[str, str] = {}
    for vertex_id, neighbors in adjacency.items():
        height = vertices[vertex_id]["position"][2]
        deltas = [vertices[neighbor]["position"][2] - height for neighbor, _ in neighbors]
        if any(abs(delta) <= tolerance for delta in deltas):
            raise ValueError(f"vertex {vertex_id!r} has a horizontal incident edge")
        if all(delta > 0 for delta in deltas):
            extrema[vertex_id] = "minimum"
        elif all(delta < 0 for delta in deltas):
            extrema[vertex_id] = "maximum"
        elif deltas[0] * deltas[1] > 0:
            raise ValueError(f"vertex {vertex_id!r} has an unclassified extremum")

    minima = sorted(
        (vertex_id for vertex_id, kind in extrema.items() if kind == "minimum"),
        key=lambda vertex_id: (
            vertices[vertex_id]["position"][2],
            vertices[vertex_id]["position"][0],
            vertex_id,
        ),
    )
    maxima = {vertex_id for vertex_id, kind in extrema.items() if kind == "maximum"}
    if len(minima) != len(maxima):
        raise ValueError("side projection has unequal numbers of minima and maxima")

    edge_to_token: dict[str, str] = {}
    token_edges: dict[str, list[str]] = {}
    token_endpoint_at_maximum: dict[str, tuple[str, str]] = {}
    component_by_piece: dict[str, str] = {}
    semantic_component_by_token: dict[str, str] = {}
    minimum_records = []
    for minimum_index, minimum in enumerate(minima):
        piece = f"sidecup{minimum_index:04d}"
        component = vertices[minimum]["component"]
        component_by_piece[piece] = component
        branches = []
        minimum_x, _, minimum_z = vertices[minimum]["position"]
        for neighbor, first_edge in adjacency[minimum]:
            neighbor_x, _, neighbor_z = vertices[neighbor]["position"]
            slope = (neighbor_x - minimum_x) / (neighbor_z - minimum_z)
            branches.append((slope, neighbor, first_edge))
        branches.sort(key=lambda item: (item[0], item[1], item[2]))
        branch_records = []
        for side, (_slope, neighbor, first_edge) in zip(
            ("left", "right"), branches, strict=True
        ):
            token = f"{piece}.{side}"
            semantic_component_by_token[token] = component
            previous = minimum
            current = neighbor
            current_edge = first_edge
            traversed = []
            while True:
                if current_edge in edge_to_token:
                    raise ValueError(f"edge {current_edge!r} belongs to two monotone arcs")
                edge_to_token[current_edge] = token
                traversed.append(current_edge)
                if current in maxima:
                    token_endpoint_at_maximum[token] = (current, previous)
                    break
                if current in extrema:
                    raise ValueError(
                        f"upward arc from {minimum!r} reached non-maximum {current!r}"
                    )
                candidates = [
                    (next_vertex, edge_id)
                    for next_vertex, edge_id in adjacency[current]
                    if next_vertex != previous
                ]
                if len(candidates) != 1:
                    raise ValueError(f"regular vertex {current!r} has ambiguous continuation")
                following, following_edge = candidates[0]
                if (
                    vertices[following]["position"][2]
                    <= vertices[current]["position"][2] + tolerance
                ):
                    raise ValueError(f"arc {token!r} is not strictly increasing in event time")
                previous, current, current_edge = current, following, following_edge
            token_edges[token] = traversed
            branch_records.append(
                {
                    "token": token,
                    "initial_edge_id": first_edge,
                    "terminal_maximum_vertex_id": current,
                    "edge_ids": traversed,
                }
            )
        minimum_records.append(
            {
                "minimum_vertex_id": minimum,
                "piece": piece,
                "component": component,
                "height": minimum_z,
                "horizontal": minimum_x,
                "branches": branch_records,
            }
        )
    if set(edge_to_token) != set(edges):
        missing = sorted(set(edges) - set(edge_to_token))
        raise ValueError(f"monotone arc decomposition missed edges: {missing[:20]!r}")

    maximum_tokens: dict[str, list[str]] = defaultdict(list)
    for token, (maximum, _previous) in token_endpoint_at_maximum.items():
        maximum_tokens[maximum].append(token)
    if any(len(tokens) != 2 for tokens in maximum_tokens.values()):
        malformed = {
            maximum: tokens
            for maximum, tokens in maximum_tokens.items()
            if len(tokens) != 2
        }
        raise ValueError(f"maximum is not incident to exactly two arc tokens: {malformed!r}")

    def token_horizontal_at(token: str, height: float) -> float:
        candidates = []
        for edge_id in token_edges[token]:
            edge = edges[edge_id]
            start = vertices[edge["from"]]["position"]
            end = vertices[edge["to"]]["position"]
            low, high = sorted((start[2], end[2]))
            if low - tolerance <= height <= high + tolerance:
                parameter = (height - start[2]) / (end[2] - start[2])
                candidates.append(start[0] + parameter * (end[0] - start[0]))
        if not candidates:
            raise ValueError(f"token {token!r} is not active at height {height}")
        return sum(candidates) / len(candidates)

    crossing_events = []
    edge_list = list(edges.values())
    for left_index, left_edge in enumerate(edge_list):
        left_start = vertices[left_edge["from"]]["position"]
        left_end = vertices[left_edge["to"]]["position"]
        left_projected = (left_start[0], left_start[2]), (left_end[0], left_end[2])
        for right_edge in edge_list[left_index + 1 :]:
            if {left_edge["from"], left_edge["to"]} & {
                right_edge["from"], right_edge["to"]
            }:
                continue
            right_start = vertices[right_edge["from"]]["position"]
            right_end = vertices[right_edge["to"]]["position"]
            intersection = _segment_intersection(
                *left_projected,
                (right_start[0], right_start[2]),
                (right_end[0], right_end[2]),
                tolerance=tolerance,
            )
            if intersection is None:
                continue
            if (
                intersection["kind"] != "point"
                or not intersection["transverse"]
                or not intersection["interior_a"]
                or not intersection["interior_b"]
            ):
                raise ValueError(
                    "side projection contains a non-regular intersection during lowering"
                )
            left_depth = left_start[1] + intersection["parameter_a"] * (
                left_end[1] - left_start[1]
            )
            right_depth = right_start[1] + intersection["parameter_b"] * (
                right_end[1] - right_start[1]
            )
            if abs(left_depth - right_depth) <= tolerance:
                raise ValueError("side crossing has equal projection depth")
            left_token = edge_to_token[left_edge["edge_id"]]
            right_token = edge_to_token[right_edge["edge_id"]]
            if left_token == right_token:
                raise ValueError("one event-monotone arc crosses itself")
            over, under = (
                (left_token, right_token)
                if left_depth > right_depth
                else (right_token, left_token)
            )
            crossing_events.append(
                {
                    "kind": "cross",
                    "height": intersection["point"][1],
                    "horizontal": intersection["point"][0],
                    "over": over,
                    "under": under,
                    "edge_ids": [left_edge["edge_id"], right_edge["edge_id"]],
                    "depth_difference": left_depth - right_depth,
                }
            )

    events = []
    for record in minimum_records:
        events.append(
            {
                "kind": "cup",
                "height": record["height"],
                "horizontal": record["horizontal"],
                "piece": record["piece"],
                "minimum_vertex_id": record["minimum_vertex_id"],
            }
        )
    for maximum, tokens in maximum_tokens.items():
        maximum_x, _, maximum_z = vertices[maximum]["position"]
        events.append(
            {
                "kind": "cap",
                "height": maximum_z,
                "horizontal": maximum_x,
                "tokens": sorted(tokens),
                "maximum_vertex_id": maximum,
            }
        )
    events.extend(crossing_events)
    if projector_height is not None:
        events.append(
            {
                "kind": "vacuum-projector",
                "height": projector_height,
                "horizontal": 0.0,
            }
        )
    events.sort(key=lambda event: (event["height"], event["horizontal"], event["kind"]))
    for left, right in zip(events, events[1:]):
        if abs(left["height"] - right["height"]) <= tolerance:
            raise ValueError(
                "side projection has simultaneous Morse events: "
                f"{left!r} and {right!r}"
            )

    builder = MorseBuilder()
    event_trace = []
    projector_order: list[str] | None = None
    projector_active_order: list[str] | None = None
    puncture_edge_ids = set()
    puncture_tokens = set()
    gather_plan = None
    if projector_height is not None:
        puncture_edge_ids = {
            puncture["edge_id"]
            for puncture in side_lift["side_projection_source"][
                "special_disk_intersections"
            ]["punctures"]
        }
        puncture_tokens = {
            edge_to_token[edge_id] for edge_id in puncture_edge_ids
        }
        gather_plan = _geometric_projector_routing_plan(
            side_lift,
            edge_to_token,
            projector_height=projector_height,
            tolerance=tolerance,
        )
    for event_index, event in enumerate(events):
        kind = event["kind"]
        active_before = list(builder.order)
        if kind == "cup":
            gap = sum(
                token_horizontal_at(token, event["height"]) < event["horizontal"]
                for token in builder.order
            )
            if gap == 0:
                builder.cup(event["piece"], at="far-left")
            elif gap == len(builder.order):
                builder.cup(event["piece"], at="far-right")
            else:
                builder.cup(
                    event["piece"],
                    between=(builder.order[gap - 1], builder.order[gap]),
                )
        elif kind == "cross":
            builder.cross(over=event["over"], under=event["under"])
        elif kind == "cap":
            tokens = list(event["tokens"])
            tokens.sort(key=builder.order.index)
            builder.cap(strands=(tokens[0], tokens[1]))
        elif kind == "vacuum-projector":
            assert projector_height is not None
            assert gather_plan is not None
            geometric_order = sorted(
                builder.order,
                key=lambda token: token_horizontal_at(token, projector_height),
            )
            if geometric_order != builder.order:
                raise ValueError("active order disagrees with geometry at projector slice")
            if gather_plan["initial_order"] != builder.order:
                raise ValueError("geometric projector plan starts in a different active order")
            projector_active_order = list(builder.order)
            routing_crossings = gather_plan["routing_crossings"]
            for crossing in routing_crossings:
                builder.cross(over=crossing["over"], under=crossing["under"])
            if builder.order != gather_plan["target_order"]:
                raise ValueError("lowered routing disagrees with geometric target order")
            projector_order = list(gather_plan["projector_order"])
            projector_start = gather_plan["projector_start"]
            contiguous_projector_order = builder.order[
                projector_start : projector_start + len(projector_order)
            ]
            if contiguous_projector_order != projector_order:
                raise ValueError("stable gather did not produce the intended projector interval")
            builder.vacuum_projector(
                projector_order, projector_id="special-disk:red"
            )
            for crossing in reversed(routing_crossings):
                builder.cross(
                    over=crossing["over"], under=crossing["under"]
                )
            if builder.order != projector_active_order:
                raise ValueError("inverse projector routing did not restore active order")
            event["routing_crossings"] = routing_crossings
        else:
            raise ValueError(f"unsupported lowering event {kind!r}")
        event_trace.append(
            {
                "event_id": f"side-event-{event_index:04d}",
                **event,
                "active_before": active_before,
                "active_after": list(builder.order),
            }
        )
    if builder.order:
        raise ValueError(f"side Morse lowering did not close: {builder.order!r}")
    if projector_height is not None and projector_order is None:
        raise ValueError("side Morse lowering omitted the vacuum projector")
    if projector_height is not None:
        expected_projector_factors = len(
            side_lift["side_projection_source"]["special_disk_intersections"][
                "punctures"
            ]
        )
        if len(projector_order or ()) != expected_projector_factors:
            raise ValueError(
                "projector slice has "
                f"{len(projector_order or ())} strands, "
                f"expected {expected_projector_factors}"
            )
    payload = {
        "schema": "twisted-yetter.exact-side-projection-morse-lowering.v1",
        "status": (
            "PASS_EXACT_SIDE_PROJECTION_MORSE_LOWERING_CONTROLS"
            if projector_height is not None
            else "PASS_GENERIC_PL_PROJECTION_MORSE_LOWERING_CONTROLS"
        ),
        "source_side_lift_hash": side_lift["lift_hash"],
        "event_coordinate": "z",
        "horizontal_coordinate": "x",
        "depth_coordinate": "y",
        "projector_height": projector_height,
        "forms": builder.forms,
        "component_by_piece": component_by_piece,
        "semantic_component_by_token": semantic_component_by_token,
        "edge_to_token": dict(sorted(edge_to_token.items())),
        "token_edges": {
            token: list(edge_ids)
            for token, edge_ids in sorted(token_edges.items())
        },
        "puncture_edge_to_token": {
            edge_id: edge_to_token[edge_id]
            for edge_id in sorted(puncture_edge_ids)
        },
        "projector_order": projector_order,
        "projector_active_order": projector_active_order,
        "projector_slice_active_count": len(projector_active_order or ()),
        "projector_gather_plan": gather_plan,
        "projector_routing_crossing_count_each_way": (
            gather_plan["routing_crossing_count"] if gather_plan is not None else 0
        ),
        "total_routing_crossing_count": (
            2 * gather_plan["routing_crossing_count"]
            if gather_plan is not None
            else 0
        ),
        "minimum_count": len(minima),
        "maximum_count": len(maxima),
        "crossing_count": len(crossing_events),
        "projector_factor_count": len(projector_order or ()),
        "monotone_arc_count": len(token_edges),
        "minimum_records": minimum_records,
        "event_trace": event_trace,
        "regularity": regularity,
    }
    payload["lowering_hash"] = stable_json_hash(payload)
    return payload


def lower_generic_projection_to_morse(
    projected_lift: dict[str, Any], *, tolerance: float = 1e-9
) -> dict[str, Any]:
    """Lower a complete generic PL projection without inserting a coupon."""

    return lower_exact_side_projection_to_morse(
        projected_lift,
        projector_height=None,
        tolerance=tolerance,
    )


def analyze_exact_side_morse_regularity(
    side_lift: dict[str, Any], *, tolerance: float = 1e-10
) -> dict[str, Any]:
    """Check that z is a valid PL event coordinate on every side-view edge."""

    vertices = {vertex["vertex_id"]: vertex for vertex in side_lift["vertices"]}
    horizontal_edges = []
    for edge in side_lift["edges"]:
        start_z = vertices[edge["from"]]["position"][2]
        end_z = vertices[edge["to"]]["position"][2]
        if abs(start_z - end_z) <= tolerance:
            horizontal_edges.append(edge["edge_id"])
    return {
        "status": (
            "PASS_EXACT_SIDE_PL_EVENT_COORDINATE"
            if not horizontal_edges
            else "FAIL_EXACT_SIDE_HAS_HORIZONTAL_EDGES"
        ),
        "event_coordinate": "z",
        "edge_count": len(side_lift["edges"]),
        "horizontal_edge_count": len(horizontal_edges),
        "horizontal_edge_ids": horizontal_edges[:100],
        "horizontal_edge_ids_truncated": len(horizontal_edges) > 100,
        "tolerance": tolerance,
    }


def certify_exact_side_projection_round_trip(
    source_lift: dict[str, Any],
    side_lift: dict[str, Any],
    special_component: str,
    *,
    tolerance: float = 1e-9,
) -> dict[str, Any]:
    """Certify that SIDE is the declared rigid rotation of SOURCE.

    The special boundary is intentionally removed from SIDE.  Every ordinary
    vertex and edge must otherwise survive unchanged, and the rotation must be
    invertible pointwise.  Certified disk punctures are checked on their exact
    source edge parameters before and after the rotation.
    """

    metadata = side_lift.get("side_projection_source", {})
    angle_degrees = metadata.get("angle_degrees")
    if not isinstance(angle_degrees, (int, float)):
        raise ValueError("side lift does not record a numeric rotation angle")
    radians = math.radians(float(angle_degrees))
    cosine, sine = math.cos(radians), math.sin(radians)

    source_all_vertices = {
        vertex["vertex_id"]: vertex for vertex in source_lift["vertices"]
    }
    source_vertices = {
        vertex["vertex_id"]: vertex
        for vertex in source_lift["vertices"]
        if vertex["component"] != special_component
    }
    side_vertices = {
        vertex["vertex_id"]: vertex for vertex in side_lift["vertices"]
    }
    vertex_ids_match = set(source_vertices) == set(side_vertices)
    vertex_metadata_match = vertex_ids_match and all(
        {
            key: value
            for key, value in source_vertices[vertex_id].items()
            if key != "position"
        }
        == {
            key: value
            for key, value in side_vertices[vertex_id].items()
            if key != "position"
        }
        for vertex_id in source_vertices
    )

    maximum_forward_residual = 0.0
    maximum_inverse_residual = 0.0
    first_vertex_mismatch = None
    if vertex_ids_match:
        for vertex_id in sorted(source_vertices):
            x, y, z = source_vertices[vertex_id]["position"]
            h, depth, event = side_vertices[vertex_id]["position"]
            expected_side = (
                cosine * x + sine * y,
                sine * x - cosine * y,
                z,
            )
            recovered_source = (
                cosine * h + sine * depth,
                sine * h - cosine * depth,
                event,
            )
            forward_residual = max(
                abs(actual - expected)
                for actual, expected in zip(
                    (h, depth, event), expected_side, strict=True
                )
            )
            inverse_residual = max(
                abs(actual - expected)
                for actual, expected in zip(
                    recovered_source, (x, y, z), strict=True
                )
            )
            maximum_forward_residual = max(
                maximum_forward_residual, forward_residual
            )
            maximum_inverse_residual = max(
                maximum_inverse_residual, inverse_residual
            )
            if (
                first_vertex_mismatch is None
                and max(forward_residual, inverse_residual) > tolerance
            ):
                first_vertex_mismatch = {
                    "vertex_id": vertex_id,
                    "source_position": [x, y, z],
                    "side_position": [h, depth, event],
                    "expected_side_position": list(expected_side),
                    "recovered_source_position": list(recovered_source),
                    "forward_residual": forward_residual,
                    "inverse_residual": inverse_residual,
                }

    source_edges = [
        edge
        for edge in source_lift["edges"]
        if edge["component"] != special_component
    ]
    side_edges = side_lift["edges"]
    edges_match_exactly = source_edges == side_edges
    source_crossings = [
        crossing
        for crossing in source_lift["intended_crossings"]
        if crossing["over_component"] != special_component
        and crossing["under_component"] != special_component
    ]
    crossings_match_exactly = source_crossings == side_lift["intended_crossings"]

    recomputed_intersections = concrete_special_disk_intersections(
        source_lift, special_component, tolerance=tolerance
    )
    stored_intersections = metadata.get("special_disk_intersections")
    puncture_set_matches = recomputed_intersections == stored_intersections
    source_edges_by_id = {edge["edge_id"]: edge for edge in source_edges}
    side_edges_by_id = {edge["edge_id"]: edge for edge in side_edges}
    puncture_records = []
    maximum_puncture_residual = 0.0
    first_puncture_mismatch = None
    for puncture in recomputed_intersections["punctures"]:
        edge_id = puncture["edge_id"]
        if edge_id not in source_edges_by_id or edge_id not in side_edges_by_id:
            record = {
                "puncture_id": puncture["puncture_id"],
                "edge_id": edge_id,
                "status": "FAIL_PUNCTURE_EDGE_MISSING_AFTER_ROTATION",
            }
            puncture_records.append(record)
            if first_puncture_mismatch is None:
                first_puncture_mismatch = record
            continue
        parameter = puncture["edge_parameter"]
        source_edge = source_edges_by_id[edge_id]
        side_edge = side_edges_by_id[edge_id]
        source_start = source_all_vertices[source_edge["from"]]["position"]
        source_end = source_all_vertices[source_edge["to"]]["position"]
        side_start = side_vertices[side_edge["from"]]["position"]
        side_end = side_vertices[side_edge["to"]]["position"]

        def interpolate(start: list[float], end: list[float]) -> list[float]:
            return [
                left + parameter * (right - left)
                for left, right in zip(start, end, strict=True)
            ]

        source_point = interpolate(source_start, source_end)
        side_point = interpolate(side_start, side_end)
        expected_side_point = [
            cosine * source_point[0] + sine * source_point[1],
            sine * source_point[0] - cosine * source_point[1],
            source_point[2],
        ]
        recovered_source_point = [
            cosine * side_point[0] + sine * side_point[1],
            sine * side_point[0] - cosine * side_point[1],
            side_point[2],
        ]
        residual = max(
            abs(source_point[0] - puncture["xy"][0]),
            abs(source_point[1] - puncture["xy"][1]),
            abs(source_point[2]),
            *(abs(actual - expected) for actual, expected in zip(
                side_point, expected_side_point, strict=True
            )),
            *(abs(actual - expected) for actual, expected in zip(
                recovered_source_point, source_point, strict=True
            )),
        )
        maximum_puncture_residual = max(maximum_puncture_residual, residual)
        record = {
            "puncture_id": puncture["puncture_id"],
            "edge_id": edge_id,
            "component": puncture["component"],
            "edge_parameter": parameter,
            "source_point": source_point,
            "side_point": side_point,
            "residual": residual,
            "status": (
                "PASS_PUNCTURE_POINT_ROUND_TRIP"
                if residual <= tolerance
                else "FAIL_PUNCTURE_POINT_ROUND_TRIP"
            ),
        }
        puncture_records.append(record)
        if first_puncture_mismatch is None and residual > tolerance:
            first_puncture_mismatch = record

    source_xy = analyze_projection(source_lift, "xy", max_examples=5)
    side_xz = analyze_projection(side_lift, "xz", max_examples=5)
    regularity = analyze_exact_side_morse_regularity(
        side_lift, tolerance=tolerance
    )
    checks = {
        "source_hash_matches": metadata.get("source_lift_hash")
        == source_lift.get("lift_hash"),
        "oriented_frame_is_preserving": abs(
            float(metadata.get("oriented_frame_determinant", 0.0)) - 1.0
        )
        <= tolerance,
        "removed_special_component_matches": metadata.get(
            "removed_special_component"
        )
        == special_component,
        "source_xy_recovers_input": source_xy["status"]
        == "PASS_XY_COMBINATORIAL_ROUND_TRIP",
        "ordinary_vertex_ids_match": vertex_ids_match,
        "ordinary_vertex_metadata_match": vertex_metadata_match,
        "ordinary_edges_match_exactly": edges_match_exactly,
        "ordinary_declared_crossings_match_exactly": crossings_match_exactly,
        "puncture_set_matches_recomputation": puncture_set_matches,
        "side_xz_is_generic": side_xz["status"] == "PASS_XZ_GENERIC_PROJECTION",
        "side_event_coordinate_is_regular": regularity["status"]
        == "PASS_EXACT_SIDE_PL_EVENT_COORDINATE",
        "forward_rotation_within_tolerance": maximum_forward_residual <= tolerance,
        "inverse_rotation_within_tolerance": maximum_inverse_residual <= tolerance,
        "puncture_round_trip_within_tolerance": (
            first_puncture_mismatch is None
            and maximum_puncture_residual <= tolerance
        ),
    }
    payload = {
        "schema": "twisted-yetter.exact-side-projection-round-trip-certificate.v1",
        "status": (
            "PASS_EXACT_SIDE_PROJECTION_ROUND_TRIP"
            if all(checks.values())
            else "FAIL_EXACT_SIDE_PROJECTION_ROUND_TRIP"
        ),
        "source_lift_hash": source_lift.get("lift_hash"),
        "side_lift_hash": side_lift.get("lift_hash"),
        "special_component": special_component,
        "angle_degrees": angle_degrees,
        "tolerance": tolerance,
        "checks": checks,
        "ordinary_vertex_count": len(source_vertices),
        "ordinary_edge_count": len(source_edges),
        "puncture_count": len(puncture_records),
        "maximum_forward_residual": maximum_forward_residual,
        "maximum_inverse_residual": maximum_inverse_residual,
        "maximum_puncture_residual": maximum_puncture_residual,
        "first_vertex_mismatch": first_vertex_mismatch,
        "first_puncture_mismatch": first_puncture_mismatch,
        "source_xy_projection": source_xy,
        "side_xz_projection": side_xz,
        "side_event_regularity": regularity,
        "punctures": puncture_records,
    }
    payload["certificate_hash"] = stable_json_hash(payload)
    return payload


def certify_puncture_projector_mapping(
    side_lift: dict[str, Any],
    lowered: dict[str, Any],
) -> dict[str, Any]:
    """Certify the edge-by-edge map from disk punctures to projector factors."""

    punctures = side_lift["side_projection_source"][
        "special_disk_intersections"
    ]["punctures"]
    edge_to_token = lowered.get("puncture_edge_to_token", {})
    token_edges = lowered.get("token_edges", {})
    semantic_components = lowered.get("semantic_component_by_token", {})
    projector_order = lowered.get("projector_order", [])
    expected_edge_ids = [puncture["edge_id"] for puncture in punctures]
    expected_edge_set = set(expected_edge_ids)
    mapped_edge_set = set(edge_to_token)
    records = []
    first_mismatch = None
    mapped_tokens = []
    for puncture in punctures:
        edge_id = puncture["edge_id"]
        token = edge_to_token.get(edge_id)
        checks = {
            "edge_is_mapped": token is not None,
            "edge_belongs_to_token": token is not None
            and edge_id in token_edges.get(token, []),
            "component_is_preserved": token is not None
            and semantic_components.get(token) == puncture["component"],
            "token_occurs_once_in_projector": token is not None
            and projector_order.count(token) == 1,
        }
        if token is not None:
            mapped_tokens.append(token)
        record = {
            "puncture_id": puncture["puncture_id"],
            "edge_id": edge_id,
            "edge_parameter": puncture["edge_parameter"],
            "component": puncture["component"],
            "token": token,
            "projector_index": (
                projector_order.index(token)
                if token is not None and token in projector_order
                else None
            ),
            "checks": checks,
            "status": (
                "PASS_PUNCTURE_TO_PROJECTOR_FACTOR"
                if all(checks.values())
                else "FAIL_PUNCTURE_TO_PROJECTOR_FACTOR"
            ),
        }
        records.append(record)
        if first_mismatch is None and not all(checks.values()):
            first_mismatch = record

    global_checks = {
        "lowering_source_hash_matches": lowered.get("source_side_lift_hash")
        == side_lift.get("lift_hash"),
        "puncture_edge_sets_match": expected_edge_set == mapped_edge_set,
        "puncture_edges_are_unique": len(expected_edge_ids) == len(expected_edge_set),
        "puncture_tokens_are_unique": len(mapped_tokens) == len(set(mapped_tokens)),
        "projector_has_exactly_all_puncture_tokens": set(projector_order)
        == set(mapped_tokens)
        and len(projector_order) == len(mapped_tokens),
        "every_puncture_record_passes": first_mismatch is None,
    }
    payload = {
        "schema": "twisted-yetter.puncture-projector-mapping-certificate.v1",
        "status": (
            "PASS_PUNCTURE_PROJECTOR_MAPPING"
            if all(global_checks.values())
            else "FAIL_PUNCTURE_PROJECTOR_MAPPING"
        ),
        "side_lift_hash": side_lift.get("lift_hash"),
        "lowering_hash": lowered.get("lowering_hash"),
        "puncture_count": len(punctures),
        "projector_factor_count": len(projector_order),
        "checks": global_checks,
        "first_mismatch": first_mismatch,
        "records": records,
    }
    payload["certificate_hash"] = stable_json_hash(payload)
    return payload


def apply_special_disk_side_assignment(
    lift: dict[str, Any], optimization: dict[str, Any]
) -> dict[str, Any]:
    """Return a copy of LIFT whose ordinary z-heights realize OPTIMIZATION."""

    if optimization["lift_hash"] != lift["lift_hash"]:
        raise ValueError("side assignment belongs to a different PL lift")
    special_component = optimization["special_component"]
    assignment = optimization["assignment"]
    optimized = deepcopy(lift)
    for vertex in optimized["vertices"]:
        component = vertex["component"]
        if component == special_component:
            vertex["position"][2] = 0.0
            continue
        sign = assignment[vertex["vertex_id"]]
        role = vertex["role"]
        if role == "crossing-over-center":
            magnitude = 1.20 if sign > 0 else 0.60
        elif role == "crossing-under-center":
            magnitude = 0.60 if sign > 0 else 1.20
        else:
            magnitude = 0.38 + _jitter(
                f"{vertex['vertex_id']}|optimized-height", 0.055
            )
        vertex["position"][2] = float(sign * magnitude)

    centers = {
        (vertex["event_index"], vertex["role"]): vertex
        for vertex in optimized["vertices"]
        if vertex["role"] in {
            "crossing-over-center",
            "crossing-under-center",
        }
    }
    for crossing in optimized["intended_crossings"]:
        over = centers[(crossing["event_index"], "crossing-over-center")]
        under = centers[(crossing["event_index"], "crossing-under-center")]
        if over["position"][2] <= under["position"][2]:
            raise ValueError(
                f"optimized heights reverse crossing at event {crossing['event_index']}"
            )
        crossing["over_z"] = over["position"][2]
        crossing["under_z"] = under["position"][2]
    optimized["status"] = "CANONICAL_PL_LIFT_WITH_EXACT_MINIMUM_DISK_SIDES"
    optimized["side_optimization"] = {
        key: value for key, value in optimization.items() if key != "assignment"
    }
    optimized.pop("lift_hash", None)
    optimized["lift_hash"] = stable_json_hash(
        {key: value for key, value in optimized.items() if key != "lift_hash"}
    )
    optimized["integrity"] = _graph_integrity(optimized)
    return optimized


DEFAULT_COLORS = {
    "red": "#e45756",
    "purple": "#8f6bd8",
    "mint": "#5abf90",
    "pink1": "#f59ab2",
    "pink2": "#e66c9c",
    "pink3": "#c84e89",
    "pink4": "#a83c78",
    "orange": "#f39c34",
    "blue": "#2d9cdb",
    "beige": "#c9a66b",
    "green": "#4e9f50",
    "black": "#222222",
}


def render_projection_svg(
    lift: dict[str, Any],
    projection: str,
    *,
    tilt: float = 0.0137,
    width: int = 1800,
    margin: float = 40.0,
) -> str:
    project, _ = _projection_map(projection, tilt)
    vertices = {vertex["vertex_id"]: vertex for vertex in lift["vertices"]}
    points = [project(vertex["position"]) for vertex in lift["vertices"]]
    min_x = min(point[0] for point in points)
    max_x = max(point[0] for point in points)
    min_y = min(point[1] for point in points)
    max_y = max(point[1] for point in points)
    span_x = max(1e-9, max_x - min_x)
    span_y = max(1e-9, max_y - min_y)
    drawable_width = width - 2 * margin
    scale = drawable_width / span_x
    height = max(180, int(2 * margin + scale * span_y))

    def screen(point: tuple[float, float]) -> tuple[float, float]:
        return (
            margin + scale * (point[0] - min_x),
            height - margin - scale * (point[1] - min_y),
        )

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        f'<text x="16" y="24" font-family="monospace" font-size="15">canonical PL {projection} projection</text>',
    ]
    for edge in lift["edges"]:
        start = screen(project(vertices[edge["from"]]["position"]))
        end = screen(project(vertices[edge["to"]]["position"]))
        color = DEFAULT_COLORS.get(edge["component"], "#666666")
        lines.append(
            f'<line x1="{start[0]:.4f}" y1="{start[1]:.4f}" '
            f'x2="{end[0]:.4f}" y2="{end[1]:.4f}" '
            f'stroke="{color}" stroke-width="1.6" stroke-linecap="round"/>'
        )
    lines.append("</svg>\n")
    return "\n".join(lines)


def build_projection_bundle(
    lift: dict[str, Any], *, tilt: float = 0.0137
) -> dict[str, Any]:
    projections = {
        name: analyze_projection(lift, name, tilt=tilt)
        for name in ("xy", "xz", "near-xz")
    }
    disk_intersections = {
        special: concrete_special_disk_intersections(lift, special)
        for special in lift["special_components"]
    }
    passed = (
        projections["xy"]["status"] == "PASS_XY_COMBINATORIAL_ROUND_TRIP"
        and projections["near-xz"]["status"] == "PASS_NEAR_XZ_GENERIC_PROJECTION"
        and all(
            report["status"] == "PASS_TRANSVERSE_CONCRETE_SPECIAL_DISK_INTERSECTIONS"
            for report in disk_intersections.values()
        )
    )
    return {
        "schema": "twisted-yetter.morse-pl-projection-bundle.v1",
        "status": "PASS_PL_LIFT_PROJECTION_CONTROLS" if passed else "NEEDS_REVIEW",
        "lift_hash": lift["lift_hash"],
        "near_xz_tilt": tilt,
        "projections": projections,
        "special_disk_intersections": disk_intersections,
        "bundle_hash": stable_json_hash(
            {
                "lift_hash": lift["lift_hash"],
                "tilt": tilt,
                "projections": projections,
                "special_disk_intersections": disk_intersections,
            }
        ),
    }
