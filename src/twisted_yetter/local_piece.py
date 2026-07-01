"""Local-piece link evaluator input model.

This is the first executable "B track" schema layer: it records a link as a
composition of local braid-crossing pieces, then closes the braid.  It is not a
general planar tensor graph yet; cups, caps, trivalent vertices, and arbitrary
F/R recoupling data are deliberately outside this v1 slice.
"""

from __future__ import annotations

from dataclasses import dataclass
from numbers import Integral
from typing import Any, Literal, Sequence


LOCAL_PIECE_PROGRAM_SCHEMA = "twisted-yetter.local-piece-program.v1"

JsonObject = dict[str, Any]
PieceKind = Literal["braid_crossing"]
ClosureKind = Literal["braid_closure"]


def _as_int(value: object, field: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral):
        raise TypeError(f"{field} must be an integer")
    return int(value)


def _as_str(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise TypeError(f"{field} must be a non-empty string")
    return value


def _optional_int_tuple(value: object, field: str) -> tuple[int, ...] | None:
    if value is None:
        return None
    return _int_tuple(value, field)


def _int_tuple(value: object, field: str) -> tuple[int, ...]:
    if not isinstance(value, list | tuple):
        raise TypeError(f"{field} must be a list")
    return tuple(_as_int(item, f"{field}[{index}]") for index, item in enumerate(value))


def _require_keys(
    payload: JsonObject,
    required: set[str],
    label: str,
    optional: set[str] | None = None,
) -> None:
    if not isinstance(payload, dict):
        raise TypeError(f"{label} must be an object")
    missing = sorted(required.difference(payload))
    if missing:
        raise ValueError(f"{label} missing required fields: {', '.join(missing)}")
    unknown = sorted(set(payload).difference(required.union(optional or set()).union({"description"})))
    if unknown:
        raise ValueError(f"{label} has unknown fields: {', '.join(unknown)}")


@dataclass(frozen=True)
class BraidCrossingPiece:
    """A local R or R^{-1} piece in a braid word."""

    piece_id: str
    left_index: int
    sign: Literal[-1, 1]

    @classmethod
    def from_json(cls, payload: JsonObject, strand_count: int) -> "BraidCrossingPiece":
        _require_keys(payload, {"kind", "id", "left_index", "sign"}, "piece")
        if payload["kind"] != "braid_crossing":
            raise ValueError(f"unsupported local piece kind: {payload['kind']!r}")
        left_index = _as_int(payload["left_index"], "piece.left_index")
        sign = _as_int(payload["sign"], "piece.sign")
        if sign not in {-1, 1}:
            raise ValueError("piece.sign must be -1 or 1")
        return cls(
            piece_id=_as_str(payload["id"], "piece.id"),
            left_index=left_index,
            sign=sign,  # type: ignore[arg-type]
        ).validated(strand_count)

    def validated(self, strand_count: int) -> "BraidCrossingPiece":
        if self.left_index < 1 or self.left_index >= strand_count:
            raise ValueError("piece.left_index must be between 1 and strand_count - 1")
        return self

    def generator(self) -> int:
        return self.sign * self.left_index

    def to_json(self) -> JsonObject:
        return {
            "kind": "braid_crossing",
            "id": self.piece_id,
            "left_index": self.left_index,
            "sign": self.sign,
        }


@dataclass(frozen=True)
class BraidClosure:
    """Closure/evaluation data for the local braid program."""

    framings: tuple[int, ...]
    omega_labels: tuple[int, ...]
    fixed_labels: tuple[int, ...] | None = None

    @classmethod
    def from_json(cls, payload: JsonObject) -> "BraidClosure":
        _require_keys(
            payload,
            {"kind", "framings", "omega_labels"},
            "closure",
            optional={"fixed_labels"},
        )
        if payload["kind"] != "braid_closure":
            raise ValueError(f"unsupported closure kind: {payload['kind']!r}")
        return cls(
            framings=_int_tuple(payload["framings"], "closure.framings"),
            omega_labels=_int_tuple(payload["omega_labels"], "closure.omega_labels"),
            fixed_labels=_optional_int_tuple(payload.get("fixed_labels"), "closure.fixed_labels"),
        )

    def validated(self, component_count: int) -> "BraidClosure":
        if len(self.framings) != component_count:
            raise ValueError("closure.framings count must match braid-closure component count")
        if len(self.omega_labels) != component_count:
            raise ValueError("closure.omega_labels count must match braid-closure component count")
        if self.fixed_labels is not None and len(self.fixed_labels) != component_count:
            raise ValueError("closure.fixed_labels count must match braid-closure component count")
        return self

    def to_json(self) -> JsonObject:
        payload: JsonObject = {
            "kind": "braid_closure",
            "framings": list(self.framings),
            "omega_labels": list(self.omega_labels),
        }
        if self.fixed_labels is not None:
            payload["fixed_labels"] = list(self.fixed_labels)
        return payload


@dataclass(frozen=True)
class BraidClosureData:
    """Component data for the closure of a braid-local-piece program."""

    components: tuple[tuple[int, ...], ...]
    strand_to_component: tuple[int, ...]

    def to_json(self) -> JsonObject:
        return {
            "components_0_based_strands": [list(component) for component in self.components],
            "strand_to_component": list(self.strand_to_component),
            "component_count": len(self.components),
        }


@dataclass(frozen=True)
class LocalPieceProgram:
    """A composable local-piece program with braid closure."""

    program_id: str
    category_id: str
    strand_count: int
    pieces: tuple[BraidCrossingPiece, ...]
    closure: BraidClosure
    description: str | None = None

    def __init__(
        self,
        program_id: str,
        category_id: str,
        strand_count: int,
        pieces: Sequence[BraidCrossingPiece],
        closure: BraidClosure,
        description: str | None = None,
    ) -> None:
        object.__setattr__(self, "program_id", _as_str(program_id, "program_id"))
        object.__setattr__(self, "category_id", _as_str(category_id, "category_id"))
        object.__setattr__(self, "strand_count", _as_int(strand_count, "strand_count"))
        object.__setattr__(self, "pieces", tuple(pieces))
        object.__setattr__(self, "closure", closure)
        object.__setattr__(self, "description", description)
        self.validate()

    @classmethod
    def from_json(cls, payload: JsonObject) -> "LocalPieceProgram":
        _require_keys(
            payload,
            {"schema", "program_id", "category_id", "strand_count", "pieces", "closure"},
            "local piece program",
        )
        if payload["schema"] != LOCAL_PIECE_PROGRAM_SCHEMA:
            raise ValueError(f"unsupported local-piece schema: {payload['schema']!r}")
        strand_count = _as_int(payload["strand_count"], "strand_count")
        if not isinstance(payload["pieces"], list):
            raise TypeError("pieces must be a list")
        if not isinstance(payload["closure"], dict):
            raise TypeError("closure must be an object")
        description = payload.get("description")
        if description is not None and not isinstance(description, str):
            raise TypeError("description must be a string when present")
        return cls(
            program_id=_as_str(payload["program_id"], "program_id"),
            category_id=_as_str(payload["category_id"], "category_id"),
            strand_count=strand_count,
            pieces=tuple(BraidCrossingPiece.from_json(item, strand_count) for item in payload["pieces"]),
            closure=BraidClosure.from_json(payload["closure"]),
            description=description,
        )

    def validate(self) -> None:
        if self.strand_count < 1:
            raise ValueError("strand_count must be positive")
        piece_ids = [piece.piece_id for piece in self.pieces]
        if len(set(piece_ids)) != len(piece_ids):
            raise ValueError("piece ids must be unique")
        for piece in self.pieces:
            piece.validated(self.strand_count)
        self.closure.validated(len(self.closure_data().components))

    def braid_word(self) -> tuple[int, ...]:
        return tuple(piece.generator() for piece in self.pieces)

    def closure_data(self) -> BraidClosureData:
        return braid_closure_data(self.strand_count, self.braid_word())

    def linking_matrix(self) -> tuple[tuple[int, ...], ...]:
        return braid_closure_linking_matrix(self.strand_count, self.braid_word())

    def to_oracle_payload(self) -> JsonObject:
        payload: JsonObject = {
            "n_strands": self.strand_count,
            "braid_word": list(self.braid_word()),
            "framings": list(self.closure.framings),
            "omega_labels": list(self.closure.omega_labels),
        }
        if self.closure.fixed_labels is not None:
            payload["fixed_labels"] = list(self.closure.fixed_labels)
        return payload

    def to_json(self) -> JsonObject:
        payload: JsonObject = {
            "schema": LOCAL_PIECE_PROGRAM_SCHEMA,
            "program_id": self.program_id,
            "category_id": self.category_id,
            "strand_count": self.strand_count,
            "pieces": [piece.to_json() for piece in self.pieces],
            "closure": self.closure.to_json(),
        }
        if self.description is not None:
            payload["description"] = self.description
        return payload

    def diagnostics(self) -> JsonObject:
        return {
            "program_id": self.program_id,
            "category_id": self.category_id,
            "strand_count": self.strand_count,
            "piece_count": len(self.pieces),
            "braid_word": list(self.braid_word()),
            "closure": self.closure.to_json(),
            "closure_data": self.closure_data().to_json(),
            "linking_matrix": [list(row) for row in self.linking_matrix()],
            "supported_piece_kinds": ["braid_crossing"],
            "unsupported_piece_kinds_v1": ["cup", "cap", "trivalent_split", "trivalent_merge"],
        }


def braid_closure_data(n_strands: int, braid_word: Sequence[int]) -> BraidClosureData:
    n = _as_int(n_strands, "n_strands")
    if n < 1:
        raise ValueError("n_strands must be positive")
    _validate_braid_word(n, braid_word)

    positions = list(range(n))
    for generator in braid_word:
        index = abs(generator) - 1
        positions[index], positions[index + 1] = positions[index + 1], positions[index]

    next_strand = [0 for _ in range(n)]
    for top_position, original_strand in enumerate(positions):
        next_strand[original_strand] = top_position

    seen: set[int] = set()
    cycles: list[tuple[int, ...]] = []
    for start in range(n):
        if start in seen:
            continue
        cycle: list[int] = []
        strand = start
        while strand not in seen:
            seen.add(strand)
            cycle.append(strand)
            strand = next_strand[strand]
        cycles.append(tuple(sorted(cycle)))

    ordered = tuple(sorted(cycles, key=lambda component: component[0]))
    strand_to_component = [0 for _ in range(n)]
    for component_index, component in enumerate(ordered):
        for strand in component:
            strand_to_component[strand] = component_index
    return BraidClosureData(ordered, tuple(strand_to_component))


def braid_closure_linking_matrix(
    n_strands: int,
    braid_word: Sequence[int],
) -> tuple[tuple[int, ...], ...]:
    data = braid_closure_data(n_strands, braid_word)
    component_count = len(data.components)
    crossing_sums = [[0 for _ in range(component_count)] for _ in range(component_count)]
    positions = list(range(n_strands))

    for generator in braid_word:
        sign = 1 if generator > 0 else -1
        index = abs(generator) - 1
        left = positions[index]
        right = positions[index + 1]
        left_component = data.strand_to_component[left]
        right_component = data.strand_to_component[right]
        if left_component != right_component:
            crossing_sums[left_component][right_component] += sign
            crossing_sums[right_component][left_component] += sign
        positions[index], positions[index + 1] = positions[index + 1], positions[index]

    matrix = [[0 for _ in range(component_count)] for _ in range(component_count)]
    for left in range(component_count):
        for right in range(left + 1, component_count):
            total = crossing_sums[left][right]
            if total % 2 != 0:
                raise ValueError("inter-component crossing signs must sum to an even number")
            matrix[left][right] = total // 2
            matrix[right][left] = total // 2
    return tuple(tuple(row) for row in matrix)


def _validate_braid_word(n_strands: int, braid_word: Sequence[int]) -> None:
    for index, generator in enumerate(braid_word):
        value = _as_int(generator, f"braid_word[{index}]")
        if value == 0:
            raise ValueError("braid generators must be nonzero")
        if abs(value) >= n_strands:
            raise ValueError("braid generator index exceeds strand count")


def braid_program(
    *,
    program_id: str,
    category_id: str,
    strand_count: int,
    braid_word: Sequence[int],
    framings: Sequence[int],
    omega_labels: Sequence[int],
    fixed_labels: Sequence[int] | None = None,
    description: str | None = None,
) -> LocalPieceProgram:
    """Convenience constructor from a braid word."""

    pieces = tuple(
        BraidCrossingPiece(
            piece_id=f"r{index + 1}",
            left_index=abs(_as_int(generator, f"braid_word[{index}]")),
            sign=1 if generator > 0 else -1,
        )
        for index, generator in enumerate(braid_word)
    )
    return LocalPieceProgram(
        program_id=program_id,
        category_id=category_id,
        strand_count=strand_count,
        pieces=pieces,
        closure=BraidClosure(
            framings=tuple(int(item) for item in framings),
            omega_labels=tuple(int(item) for item in omega_labels),
            fixed_labels=None if fixed_labels is None else tuple(int(item) for item in fixed_labels),
        ),
        description=description,
    )


__all__ = [
    "BraidClosure",
    "BraidClosureData",
    "BraidCrossingPiece",
    "LOCAL_PIECE_PROGRAM_SCHEMA",
    "LocalPieceProgram",
    "braid_closure_data",
    "braid_closure_linking_matrix",
    "braid_program",
]
