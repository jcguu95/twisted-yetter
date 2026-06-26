"""Machine-readable framed link diagrams for Kirby-input experiments.

This module is intentionally an input-schema layer.  It validates small
oriented framed link diagrams and can derive a linking matrix for sanity
checks, but it does not evaluate any RT, Kirby-color, or twisted Yetter
invariant.
"""

from __future__ import annotations

from dataclasses import dataclass
from numbers import Integral
from typing import Any, Literal, Sequence

from twisted_yetter.linking_matrix import KirbyMatrixPresentation

LINK_DIAGRAM_SCHEMA = "twisted-yetter.link-diagram.v1"

Orientation = Literal["+", "-"]
CrossingSign = Literal[-1, 1]
JsonObject = dict[str, Any]


def _as_int(value: object, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError(f"{field} must be an integer")
    return int(value)


def _as_str(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{field} must be a non-empty string")
    return value


def _as_bool(value: object, field: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{field} must be a boolean")
    return value


def _as_orientation(value: object, field: str) -> Orientation:
    if value not in {"+", "-"}:
        raise ValueError(f"{field} must be '+' or '-'")
    return value  # type: ignore[return-value]


def _as_crossing_sign(value: object, field: str) -> CrossingSign:
    sign = _as_int(value, field)
    if sign not in {-1, 1}:
        raise ValueError(f"{field} must be -1 or 1")
    return sign  # type: ignore[return-value]


@dataclass(frozen=True)
class Component:
    """A framed oriented link component.

    ``dotted`` records Kirby 1-handle metadata for later nodes.  The current
    matrix sanity check still requires an integer ``framing`` for every
    component; dotted-component semantics are not interpreted here.
    """

    component_id: str
    framing: int
    dotted: bool = False
    orientation: Orientation = "+"

    @classmethod
    def from_json(cls, payload: JsonObject) -> "Component":
        _require_keys(payload, {"id", "framing", "dotted", "orientation"}, "component")
        return cls(
            component_id=_as_str(payload["id"], "component.id"),
            framing=_as_int(payload["framing"], "component.framing"),
            dotted=_as_bool(payload["dotted"], "component.dotted"),
            orientation=_as_orientation(payload["orientation"], "component.orientation"),
        )

    def to_json(self) -> JsonObject:
        return {
            "id": self.component_id,
            "framing": self.framing,
            "dotted": self.dotted,
            "orientation": self.orientation,
        }


@dataclass(frozen=True)
class StrandRef:
    """A reference to a local strand at a crossing."""

    component_id: str
    arc_id: str

    @classmethod
    def from_json(cls, payload: JsonObject, field: str) -> "StrandRef":
        _require_keys(payload, {"component_id", "arc_id"}, field)
        return cls(
            component_id=_as_str(payload["component_id"], f"{field}.component_id"),
            arc_id=_as_str(payload["arc_id"], f"{field}.arc_id"),
        )

    def to_json(self) -> JsonObject:
        return {"component_id": self.component_id, "arc_id": self.arc_id}


@dataclass(frozen=True)
class Crossing:
    """A signed over/under crossing record.

    This is PD-code-like but deliberately minimal: later evaluator nodes may
    add full planar adjacency data without changing component/framing records.
    """

    crossing_id: str
    sign: CrossingSign
    over: StrandRef
    under: StrandRef

    @classmethod
    def from_json(cls, payload: JsonObject) -> "Crossing":
        _require_keys(payload, {"id", "sign", "over", "under"}, "crossing")
        if not isinstance(payload["over"], dict):
            raise TypeError("crossing.over must be an object")
        if not isinstance(payload["under"], dict):
            raise TypeError("crossing.under must be an object")
        return cls(
            crossing_id=_as_str(payload["id"], "crossing.id"),
            sign=_as_crossing_sign(payload["sign"], "crossing.sign"),
            over=StrandRef.from_json(payload["over"], "crossing.over"),
            under=StrandRef.from_json(payload["under"], "crossing.under"),
        )

    def to_json(self) -> JsonObject:
        return {
            "id": self.crossing_id,
            "sign": self.sign,
            "over": self.over.to_json(),
            "under": self.under.to_json(),
        }


@dataclass(frozen=True)
class LinkDiagram:
    """A validated framed oriented link diagram payload."""

    diagram_id: str
    components: tuple[Component, ...]
    crossings: tuple[Crossing, ...] = ()
    description: str | None = None

    def __init__(
        self,
        diagram_id: str,
        components: Sequence[Component],
        crossings: Sequence[Crossing] = (),
        description: str | None = None,
    ) -> None:
        object.__setattr__(self, "diagram_id", _as_str(diagram_id, "diagram_id"))
        object.__setattr__(self, "components", tuple(components))
        object.__setattr__(self, "crossings", tuple(crossings))
        object.__setattr__(self, "description", description)
        self.validate()

    @classmethod
    def from_json(cls, payload: JsonObject) -> "LinkDiagram":
        _require_keys(payload, {"schema", "diagram_id", "components", "crossings"}, "diagram")
        if payload["schema"] != LINK_DIAGRAM_SCHEMA:
            raise ValueError(f"unsupported link diagram schema: {payload['schema']!r}")
        if not isinstance(payload["components"], list):
            raise TypeError("components must be a list")
        if not isinstance(payload["crossings"], list):
            raise TypeError("crossings must be a list")
        description = payload.get("description")
        if description is not None and not isinstance(description, str):
            raise TypeError("description must be a string when present")
        return cls(
            diagram_id=_as_str(payload["diagram_id"], "diagram_id"),
            components=tuple(Component.from_json(item) for item in payload["components"]),
            crossings=tuple(Crossing.from_json(item) for item in payload["crossings"]),
            description=description,
        )

    def to_json(self) -> JsonObject:
        payload: JsonObject = {
            "schema": LINK_DIAGRAM_SCHEMA,
            "diagram_id": self.diagram_id,
            "components": [component.to_json() for component in self.components],
            "crossings": [crossing.to_json() for crossing in self.crossings],
        }
        if self.description is not None:
            payload["description"] = self.description
        return payload

    @property
    def component_ids(self) -> tuple[str, ...]:
        return tuple(component.component_id for component in self.components)

    @property
    def framings(self) -> tuple[int, ...]:
        return tuple(component.framing for component in self.components)

    def validate(self) -> None:
        component_ids = self.component_ids
        if len(set(component_ids)) != len(component_ids):
            raise ValueError("component ids must be unique")
        component_set = set(component_ids)

        crossing_ids = [crossing.crossing_id for crossing in self.crossings]
        if len(set(crossing_ids)) != len(crossing_ids):
            raise ValueError("crossing ids must be unique")

        for crossing in self.crossings:
            for role, strand in (("over", crossing.over), ("under", crossing.under)):
                if strand.component_id not in component_set:
                    raise ValueError(
                        f"crossing {crossing.crossing_id} {role} references unknown component"
                    )

    def linking_matrix(self) -> tuple[tuple[int, ...], ...]:
        """Return the signed linking/framing matrix as a schema sanity check."""

        size = len(self.components)
        matrix = [[0 for _ in range(size)] for _ in range(size)]
        for index, component in enumerate(self.components):
            matrix[index][index] = component.framing

        index_by_component = {
            component.component_id: index for index, component in enumerate(self.components)
        }
        crossing_sums: dict[tuple[int, int], int] = {}
        for crossing in self.crossings:
            left = index_by_component[crossing.over.component_id]
            right = index_by_component[crossing.under.component_id]
            if left == right:
                continue
            key = (left, right) if left < right else (right, left)
            crossing_sums[key] = crossing_sums.get(key, 0) + crossing.sign

        for (left, right), signed_sum in crossing_sums.items():
            if signed_sum % 2 != 0:
                raise ValueError("inter-component crossing signs must sum to an even number")
            linking = signed_sum // 2
            matrix[left][right] = linking
            matrix[right][left] = linking

        return tuple(tuple(row) for row in matrix)

    def to_matrix_presentation(self) -> KirbyMatrixPresentation:
        """Convert to the existing matrix model for sanity checks only."""

        return KirbyMatrixPresentation(
            self.linking_matrix(),
            component_ids=self.component_ids,
            orientation_labels=tuple(component.orientation for component in self.components),
        )


def _require_keys(payload: JsonObject, required: set[str], label: str) -> None:
    if not isinstance(payload, dict):
        raise TypeError(f"{label} must be an object")
    missing = sorted(required.difference(payload))
    if missing:
        raise ValueError(f"{label} missing required fields: {', '.join(missing)}")
    unknown = sorted(set(payload).difference(required.union({"description"})))
    if unknown:
        raise ValueError(f"{label} has unknown fields: {', '.join(unknown)}")


def unknot(component_id: str = "u", framing: int = 0) -> LinkDiagram:
    return LinkDiagram(
        diagram_id=f"unknot-{component_id}-{framing}",
        components=(Component(component_id, framing),),
        description="One oriented framed unknot with no crossings.",
    )


def unlink(component_ids: Sequence[str], framings: Sequence[int] | None = None) -> LinkDiagram:
    frames = tuple(framings) if framings is not None else tuple(0 for _ in component_ids)
    if len(frames) != len(component_ids):
        raise ValueError("framings length must match component_ids")
    return LinkDiagram(
        diagram_id=f"unlink-{len(component_ids)}",
        components=tuple(Component(component_id, frame) for component_id, frame in zip(component_ids, frames)),
        description="Unlink with no crossings.",
    )


def hopf_link(
    component_ids: tuple[str, str] = ("h1", "h2"),
    framings: tuple[int, int] = (0, 0),
    linking: int = 1,
) -> LinkDiagram:
    sign = 1 if linking >= 0 else -1
    crossings = tuple(
        Crossing(
            crossing_id=f"x{i + 1}",
            sign=sign,
            over=StrandRef(component_ids[0], f"{component_ids[0]}_arc_{i + 1}"),
            under=StrandRef(component_ids[1], f"{component_ids[1]}_arc_{i + 1}"),
        )
        for i in range(abs(linking) * 2)
    )
    return LinkDiagram(
        diagram_id=f"hopf-linking-{linking}",
        components=(
            Component(component_ids[0], framings[0]),
            Component(component_ids[1], framings[1]),
        ),
        crossings=crossings,
        description="Minimal Hopf-style record with signed crossings for linking sanity checks.",
    )


def s4_diagram() -> LinkDiagram:
    return LinkDiagram("s4-empty-kirby-diagram", components=(), description="Empty Kirby diagram.")


def cp2_diagram() -> LinkDiagram:
    return LinkDiagram(
        "cp2-plus-one-framed-unknot",
        components=(Component("cp2_h", 1),),
        description="Toy CP2 Kirby input: one +1-framed unknot.",
    )


def s2x_s2_diagram() -> LinkDiagram:
    return hopf_link(component_ids=("s2_a", "s2_b"), framings=(0, 0), linking=1)


__all__ = [
    "LINK_DIAGRAM_SCHEMA",
    "Component",
    "Crossing",
    "LinkDiagram",
    "StrandRef",
    "cp2_diagram",
    "hopf_link",
    "s2x_s2_diagram",
    "s4_diagram",
    "unlink",
    "unknot",
]
