"""Small stateful builder for hand-written Morse/tangle diagrams.

The builder provides convenient Python functions that expand into local
fundamental forms while checking the active left-to-right strand order.
This is an input/sanity tool only; it does not evaluate category morphisms.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Iterable, Literal


Direction = Literal["left", "right"]
TwistSign = Literal["+", "-"]


def left(piece: str) -> str:
    return f"{piece}.left"


def right(piece: str) -> str:
    return f"{piece}.right"


@dataclass
class MorseBuilder:
    order: list[str] = field(default_factory=list)
    forms: list[dict[str, Any]] = field(default_factory=list)
    trace: list[dict[str, Any]] = field(default_factory=list)

    def _index(self, strand: str) -> int:
        try:
            return self.order.index(strand)
        except ValueError as exc:
            raise ValueError(f"strand is not active: {strand!r} in {self.order!r}") from exc

    def _require_adjacent(self, a: str, b: str) -> None:
        ia = self._index(a)
        ib = self._index(b)
        if abs(ia - ib) != 1:
            raise ValueError(f"strands are not adjacent: {a!r}, {b!r} in {self.order!r}")

    def _record(self, form: dict[str, Any]) -> dict[str, Any]:
        self.forms.append(form)
        self.trace.append({"form": form.copy(), "order": list(self.order)})
        return form

    def cup(
        self,
        piece: str,
        *,
        at: Literal["far-left", "far-right"] | None = None,
        between: tuple[str, str] | None = None,
        after: str | None = None,
    ) -> dict[str, Any]:
        """Create the two strands of a cup."""
        new_left = left(piece)
        new_right = right(piece)
        if new_left in self.order or new_right in self.order:
            raise ValueError(f"cup would duplicate active strands for {piece!r}")

        if at == "far-left":
            index = 0
        elif at == "far-right":
            index = len(self.order)
        elif between is not None:
            a, b = between
            if self._index(b) != self._index(a) + 1:
                raise ValueError(f"cup endpoints are not adjacent left-to-right: {between!r}")
            index = self._index(a) + 1
        elif after is not None:
            index = self._index(after) + 1
        else:
            raise ValueError("cup needs at='far-left'/'far-right', between=(a,b), or after=a")

        self.order[index:index] = [new_left, new_right]
        form: dict[str, Any] = {"kind": "cup", "piece": piece}
        if at is not None:
            form["at"] = at
        if between is not None:
            form["between"] = list(between)
        if after is not None:
            form["after"] = after
        return self._record(form)

    def cap(
        self,
        piece: str | None = None,
        *,
        strands: tuple[str, str] | None = None,
    ) -> dict[str, Any]:
        """Remove the two adjacent strands of a cap."""
        if strands is None:
            if piece is None:
                raise ValueError("cap needs piece or strands=(a,b)")
            strands = (left(piece), right(piece))
        a, b = strands
        self._require_adjacent(a, b)
        self.order = [x for x in self.order if x not in {a, b}]
        form: dict[str, Any] = {"kind": "cap", "strands": [a, b]}
        if piece is not None:
            form["piece"] = piece
        return self._record(form)

    def cross(self, *, over: str, under: str, sign: str | None = None) -> dict[str, Any]:
        """Add a local crossing and swap the adjacent strands."""
        self._require_adjacent(over, under)
        io = self._index(over)
        iu = self._index(under)
        self.order[io], self.order[iu] = self.order[iu], self.order[io]
        form: dict[str, Any] = {"kind": "cross", "over": over, "under": under}
        if sign is not None:
            form["sign"] = sign
        return self._record(form)

    def kink(self, strand: str, *, sign: str, times: int = 1) -> dict[str, Any]:
        """Record a one-sided local kink/self-curl.

        This changes self-framing data but does not change active order.
        """
        if strand not in self.order:
            raise ValueError(f"kink strand is not active: {strand!r}")
        if times <= 0:
            raise ValueError("kink times must be positive")
        return self._record({"kind": "kink", "strand": strand, "sign": sign, "times": times})

    def vacuum_projector(
        self, strands: Iterable[str] | None = None, *, projector_id: str
    ) -> dict[str, Any]:
        """Insert a collective unit-channel projector on a contiguous interval."""

        selected = list(self.order if strands is None else strands)
        if len(set(selected)) != len(selected):
            raise ValueError("vacuum projector repeats an active strand")
        if any(strand not in self.order for strand in selected):
            raise ValueError("vacuum projector references an inactive strand")
        if selected:
            start = self.order.index(selected[0])
            if self.order[start : start + len(selected)] != selected:
                raise ValueError("vacuum projector strands are not contiguous")
        return self._record(
            {
                "kind": "vacuum-projector",
                "projector_id": projector_id,
                "strands": selected,
            }
        )

    def _infer_target(self, strand: str, direction: Direction) -> str:
        index = self._index(strand)
        if direction == "left":
            if index == 0:
                raise ValueError(f"{strand!r} cannot move further left in {self.order!r}")
            return self.order[index - 1]
        if index == len(self.order) - 1:
            raise ValueError(f"{strand!r} cannot move further right in {self.order!r}")
        return self.order[index + 1]

    def over(
        self,
        strand: str,
        direction: Direction,
        *,
        under: Iterable[str] | None = None,
        times: int | None = None,
        sign: str | None = None,
    ) -> list[dict[str, Any]]:
        """Move STRAND over a list of strands or infer targets by TIMES."""
        if under is not None and times is not None:
            raise ValueError("use under=... or times=..., not both")
        if under is None:
            if times is None:
                raise ValueError("over needs under=... or times=...")
            if times < 0:
                raise ValueError("times must be nonnegative")
            targets = []
            for _ in range(times):
                targets.append(self._infer_target(strand, direction))
                self.cross(over=strand, under=targets[-1], sign=sign)
            return self.forms[-times:] if times else []

        made = []
        for target in under:
            made.append(self.cross(over=strand, under=target, sign=sign))
        return made

    def over_left(
        self,
        strand: str,
        *,
        under: Iterable[str] | None = None,
        times: int | None = None,
        sign: str | None = None,
    ) -> list[dict[str, Any]]:
        return self.over(strand, "left", under=under, times=times, sign=sign)

    def over_right(
        self,
        strand: str,
        *,
        under: Iterable[str] | None = None,
        times: int | None = None,
        sign: str | None = None,
    ) -> list[dict[str, Any]]:
        return self.over(strand, "right", under=under, times=times, sign=sign)

    def under(
        self,
        strand: str,
        direction: Direction,
        *,
        over: Iterable[str] | None = None,
        times: int | None = None,
        sign: str | None = None,
    ) -> list[dict[str, Any]]:
        """Move STRAND under a list of strands or infer targets by TIMES."""
        if over is not None and times is not None:
            raise ValueError("use over=... or times=..., not both")
        if over is None:
            if times is None:
                raise ValueError("under needs over=... or times=...")
            if times < 0:
                raise ValueError("times must be nonnegative")
            made = []
            for _ in range(times):
                target = self._infer_target(strand, direction)
                made.append(self.cross(over=target, under=strand, sign=sign))
            return made

        made = []
        for target in over:
            made.append(self.cross(over=target, under=strand, sign=sign))
        return made

    def under_left(
        self,
        strand: str,
        *,
        over: Iterable[str] | None = None,
        times: int | None = None,
        sign: str | None = None,
    ) -> list[dict[str, Any]]:
        return self.under(strand, "left", over=over, times=times, sign=sign)

    def under_right(
        self,
        strand: str,
        *,
        over: Iterable[str] | None = None,
        times: int | None = None,
        sign: str | None = None,
    ) -> list[dict[str, Any]]:
        return self.under(strand, "right", over=over, times=times, sign=sign)

    def nested_cups(
        self,
        components: Iterable[str],
        *,
        between: tuple[str, str],
        order: Literal["increasing", "decreasing"] = "increasing",
    ) -> list[dict[str, Any]]:
        """Create nested cups between two active adjacent boundary strands."""
        comps = list(components)
        if order == "decreasing":
            comps.reverse()
        made = []
        prev: str | None = None
        left_bound, right_bound = between
        for component in comps:
            made.append(
                self.cup(
                    component,
                    between=(left(prev) if prev else left_bound, right(prev) if prev else right_bound),
                )
            )
            prev = component
        return made

    def kink_each(self, strands: Iterable[str], *, sign: str, times: int = 1) -> list[dict[str, Any]]:
        return [self.kink(strand, sign=sign, times=times) for strand in strands]

    def interval(self, start: str, end: str) -> list[str]:
        i = self._index(start)
        j = self._index(end)
        lo = min(i, j)
        hi = max(i, j)
        return self.order[lo : hi + 1]

    def full_twist(
        self,
        *,
        start: str,
        end: str,
        direction: Direction = "left",
        sign: TwistSign,
    ) -> list[dict[str, Any]]:
        """Expand a handed full twist over the current strand interval.

        ``sign`` is geometric handedness, not an oriented crossing-sign
        annotation.  With a leftward sweep, a negative twist moves each
        strand over its neighbors and a positive twist moves it under them.
        The over/under choice reverses for a rightward sweep so handedness is
        independent of the expansion direction.
        """
        if sign not in {"+", "-"}:
            raise ValueError("full-twist sign must be '+' or '-'")
        strands = self.interval(start, end)
        count = len(strands) - 1
        movers = list(reversed(strands)) if direction == "left" else list(strands)
        made = []
        mover_is_over = (direction == "left") == (sign == "-")
        for strand in movers:
            if mover_is_over:
                made.extend(self.over(strand, direction, times=count))
            else:
                made.extend(self.under(strand, direction, times=count))
        return made

    def snapshot(self) -> dict[str, Any]:
        return {"forms": self.forms, "trace": self.trace, "final_order": self.order}
