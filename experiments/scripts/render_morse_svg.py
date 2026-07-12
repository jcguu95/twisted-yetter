"""Render expanded Morse fundamental forms to a large inspection SVG.

This is a draft visual-inspection tool for hand transcriptions.  It is not a
link evaluator and does not certify agreement with the source Kirby diagram.
"""

from __future__ import annotations

import argparse
import html
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


RAINBOW10 = [
    "#d62728",  # red
    "#ff7f0e",  # orange
    "#f1c40f",  # yellow
    "#2ca02c",  # green
    "#1f77b4",  # blue
    "#4b3fbd",  # indigo
    "#9467bd",  # violet
    "#17becf",  # cyan
    "#8c564b",  # brown
    "#e377c2",  # magenta
]

FALLBACK_PALETTE = [
    "#7f7f7f",
    "#bcbd22",
    "#393b79",
    "#637939",
    "#8c6d31",
]


@dataclass(frozen=True)
class Segment:
    x1: float
    y1: float
    x2: float
    y2: float
    strand: str
    role: str
    event: str
    layer: int
    allowed_crossing: str | None = None

    def as_json(self) -> dict[str, Any]:
        return {
            "from": [round(self.x1, 3), round(self.y1, 3)],
            "to": [round(self.x2, 3), round(self.y2, 3)],
            "strand": self.strand,
            "role": self.role,
            "event": self.event,
            "layer": self.layer,
            "allowed_crossing": self.allowed_crossing,
        }


def component_of(strand: str) -> str:
    piece = strand.split(".", 1)[0]
    if piece.startswith("A"):
        return "A"
    return piece


def color_map(forms: list[dict[str, Any]]) -> dict[str, str]:
    components: list[str] = []
    for form in forms:
        for key in ("over", "under", "strand"):
            strand = form.get(key)
            if isinstance(strand, str):
                comp = component_of(strand)
                if comp not in components:
                    components.append(comp)
        for strand in form.get("strands", []):
            comp = component_of(strand)
            if comp not in components:
                components.append(comp)
        if form.get("kind") == "cup":
            comp = component_of(form["piece"])
            if comp not in components:
                components.append(comp)
    components.sort(key=lambda c: (c[0], int(c[1:]) if c[1:].isdigit() else -1, c))
    colors: dict[str, str] = {}
    fallback_i = 0
    for component in components:
        if component == "A":
            colors[component] = "#000000"
        elif component == "B":
            colors[component] = "#d62728"
        elif component.startswith(("L", "R")) and component[1:].isdigit():
            colors[component] = RAINBOW10[(int(component[1:]) - 1) % len(RAINBOW10)]
        else:
            colors[component] = FALLBACK_PALETTE[fallback_i % len(FALLBACK_PALETTE)]
            fallback_i += 1
    return colors


def svg_line(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    color: str,
    width: float = 2.4,
    *,
    stroke_scale: float = 1.0,
) -> str:
    return (
        f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
        f'stroke="{color}" stroke-width="{width * stroke_scale:.1f}" '
        'stroke-linecap="round" fill="none" />'
    )


def svg_step_path(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    color: str,
    width: float = 2.4,
    *,
    stroke_scale: float = 1.0,
    elbow: float | None = None,
) -> str:
    if abs(x1 - x2) < 1e-9:
        return svg_line(x1, y1, x2, y2, color, width, stroke_scale=stroke_scale)
    ym = (y1 + y2) / 2 if elbow is None else elbow
    return (
        f'<path d="M {x1:.1f} {y1:.1f} L {x1:.1f} {ym:.1f} '
        f'L {x2:.1f} {ym:.1f} L {x2:.1f} {y2:.1f}" '
        f'stroke="{color}" stroke-width="{width * stroke_scale:.1f}" '
        'stroke-linecap="round" stroke-linejoin="round" fill="none" />'
    )


def step_segments(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    *,
    strand: str,
    role: str,
    event: str,
    layer: int,
    elbow: float | None = None,
    allowed_crossing: str | None = None,
) -> list[Segment]:
    if abs(x1 - x2) < 1e-9:
        return [Segment(x1, y1, x2, y2, strand, role, event, layer, allowed_crossing)]
    ym = (y1 + y2) / 2 if elbow is None else elbow
    return [
        Segment(x1, y1, x1, ym, strand, role, event, layer, allowed_crossing),
        Segment(x1, ym, x2, ym, strand, role, event, layer, allowed_crossing),
        Segment(x2, ym, x2, y2, strand, role, event, layer, allowed_crossing),
    ]


def svg_crossing_path_45(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    color: str,
    width: float = 2.4,
    *,
    stroke_scale: float = 1.0,
    center_y: float | None = None,
) -> str:
    if abs(x1 - x2) < 1e-9:
        return svg_line(x1, y1, x2, y2, color, width, stroke_scale=stroke_scale)
    cy = (y1 + y2) / 2 if center_y is None else center_y
    dx = x2 - x1
    half_run = abs(dx) / 2
    available = max(2.0, min(abs(cy - y1), abs(cy - y2)) - 1.0)
    half_rise = min(half_run, available)
    ya = cy + half_rise if y1 > y2 else cy - half_rise
    yb = cy - half_rise if y1 > y2 else cy + half_rise
    return (
        f'<path d="M {x1:.1f} {y1:.1f} L {x1:.1f} {ya:.1f} '
        f'L {x2:.1f} {yb:.1f} L {x2:.1f} {y2:.1f}" '
        f'stroke="{color}" stroke-width="{width * stroke_scale:.1f}" '
        'stroke-linecap="round" stroke-linejoin="round" fill="none" />'
    )


def crossing_segments_45(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    *,
    strand: str,
    role: str,
    event: str,
    layer: int,
    center_y: float | None = None,
    allowed_crossing: str | None = None,
) -> list[Segment]:
    if abs(x1 - x2) < 1e-9:
        return [Segment(x1, y1, x2, y2, strand, role, event, layer, allowed_crossing)]
    cy = (y1 + y2) / 2 if center_y is None else center_y
    dx = x2 - x1
    half_run = abs(dx) / 2
    available = max(2.0, min(abs(cy - y1), abs(cy - y2)) - 1.0)
    half_rise = min(half_run, available)
    ya = cy + half_rise if y1 > y2 else cy - half_rise
    yb = cy - half_rise if y1 > y2 else cy + half_rise
    return [
        Segment(x1, y1, x1, ya, strand, role, event, layer, allowed_crossing),
        Segment(x1, ya, x2, yb, strand, role, event, layer, allowed_crossing),
        Segment(x2, yb, x2, y2, strand, role, event, layer, allowed_crossing),
    ]


def strand_segments(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    *,
    strand: str,
    role: str,
    event: str,
    layer: int,
    draw_style: str,
    elbow: float | None = None,
    allowed_crossing: str | None = None,
) -> list[Segment]:
    if draw_style == "straight":
        return [Segment(x1, y1, x2, y2, strand, role, event, layer, allowed_crossing)]
    if draw_style in {"rectilinear", "rectilinear45"}:
        return step_segments(
            x1,
            y1,
            x2,
            y2,
            strand=strand,
            role=role,
            event=event,
            layer=layer,
            elbow=elbow,
            allowed_crossing=allowed_crossing,
        )
    raise ValueError(f"unknown draw style: {draw_style}")


def svg_strand_path(
    x1: float,
    y1: float,
    x2: float,
    y2: float,
    color: str,
    width: float = 2.4,
    *,
    stroke_scale: float = 1.0,
    draw_style: str = "straight",
    elbow: float | None = None,
) -> str:
    if draw_style == "straight":
        return svg_line(x1, y1, x2, y2, color, width, stroke_scale=stroke_scale)
    if draw_style == "rectilinear":
        return svg_step_path(x1, y1, x2, y2, color, width, stroke_scale=stroke_scale, elbow=elbow)
    if draw_style == "rectilinear45":
        return svg_step_path(x1, y1, x2, y2, color, width, stroke_scale=stroke_scale, elbow=elbow)
    raise ValueError(f"unknown draw style: {draw_style}")


def carrier_draw_style(draw_style: str) -> str:
    if draw_style in {"rectilinear", "rectilinear45"}:
        return "straight"
    return draw_style


def quadratic_segments(
    x0: float,
    y0: float,
    cx: float,
    cy: float,
    x1: float,
    y1: float,
    *,
    strand: str,
    role: str,
    event: str,
    layer: int,
    pieces: int = 12,
) -> list[Segment]:
    points: list[tuple[float, float]] = []
    for i in range(pieces + 1):
        t = i / pieces
        mt = 1.0 - t
        x = mt * mt * x0 + 2 * mt * t * cx + t * t * x1
        y = mt * mt * y0 + 2 * mt * t * cy + t * t * y1
        points.append((x, y))
    return [
        Segment(ax, ay, bx, by, strand, role, event, layer)
        for (ax, ay), (bx, by) in zip(points, points[1:])
    ]


def shallow_control_y(endpoint_y: float, full_control_y: float) -> float:
    return endpoint_y + (full_control_y - endpoint_y) / 2


def svg_text(x: float, y: float, text: str, size: int = 10, color: str = "#444") -> str:
    return (
        f'<text x="{x:.1f}" y="{y:.1f}" font-family="Menlo, monospace" '
        f'font-size="{size}" fill="{color}">{html.escape(text)}</text>'
    )


def load_crossing_sign_labels(path: Path | None) -> dict[int, str]:
    if path is None:
        return {}
    payload = json.loads(path.read_text())
    labels: dict[int, str] = {}
    for record in payload.get("crossing_records", []):
        form_index = record.get("form_index")
        used_sign = record.get("used_sign")
        if isinstance(form_index, int) and used_sign in {-1, 1}:
            labels[form_index] = "+" if used_sign == 1 else "-"
    return labels


def load_piece_orientations(path: Path | None) -> dict[str, int]:
    if path is None:
        return {}
    payload = json.loads(path.read_text())
    solution = payload.get("piece_orientation_solution", {})
    orientations: dict[str, int] = {}
    for piece, sign in solution.items():
        if sign == "+":
            orientations[piece] = 1
        elif sign == "-":
            orientations[piece] = -1
    return orientations


def strand_orientation_arrow(strand: str, piece_orientations: dict[str, int]) -> str | None:
    if "." not in strand:
        return None
    piece, side = strand.rsplit(".", 1)
    if piece not in piece_orientations:
        return None
    side_sign = 1 if side == "left" else -1 if side == "right" else 0
    if side_sign == 0:
        return None
    return "↑" if piece_orientations[piece] * side_sign == 1 else "↓"


def svg_orientation_arrow(x: float, y: float, strand: str, piece_orientations: dict[str, int]) -> str:
    arrow = strand_orientation_arrow(strand, piece_orientations)
    if arrow is None:
        return ""
    return svg_text(x + 4, y + 3, arrow, 9, "#111")


class StableLayout:
    """Stateful layout with cup-local lookahead and no global reflow."""

    def __init__(
        self,
        trace: list[dict[str, Any]],
        *,
        margin: float,
        step: float,
        layout_mode: str = "optimized",
    ) -> None:
        self.margin = margin
        self.step = step
        self.layout_mode = layout_mode
        if layout_mode == "optimized":
            self.cup_widths = self._solve_cup_widths(trace)
        elif layout_mode == "unoptimized":
            self.cup_widths = self._unoptimized_cup_widths(trace)
        else:
            raise ValueError(f"unknown layout mode: {layout_mode}")
        self.rows = self._rows(trace, self.cup_widths)
        self.max_x = max(
            (max(row["before_x"].values(), default=margin) for row in self.rows),
            default=margin,
        )
        self.max_x = max(
            self.max_x,
            max((max(row["after_x"].values(), default=margin) for row in self.rows), default=margin),
        )

    def _states(self, trace: list[dict[str, Any]]) -> list[list[str]]:
        states: list[list[str]] = [[]]
        states.extend(list(row["order"]) for row in trace)
        return states

    def _unoptimized_cup_widths(self, trace: list[dict[str, Any]]) -> dict[str, float]:
        return {
            row["form"]["piece"]: self.step
            for row in trace
            if row["form"]["kind"] == "cup"
        }

    def _base_cup_width_units(self, trace: list[dict[str, Any]]) -> dict[str, int]:
        widths: dict[str, int] = {}
        for i, row in enumerate(trace):
            form = row["form"]
            if form["kind"] != "cup":
                continue
            piece = form["piece"]
            left = f"{piece}.left"
            right = f"{piece}.right"
            max_span = 1
            for later in trace[i:]:
                order = later["order"]
                if left not in order or right not in order:
                    break
                max_span = max(max_span, abs(order.index(right) - order.index(left)))
            widths[piece] = max_span
        return widths

    def _solve_cup_widths(self, trace: list[dict[str, Any]]) -> dict[str, float]:
        states = self._states(trace)
        width_units = self._base_cup_width_units(trace)

        def adjacent(order: list[str], a: str, b: str) -> bool:
            return a in order and b in order and abs(order.index(a) - order.index(b)) == 1

        def cup_inserted_between(form: dict[str, Any], a: str, b: str) -> str | None:
            if form["kind"] != "cup":
                return None
            between = form.get("between")
            if between is None:
                return None
            if set(between) == {a, b}:
                return form["piece"]
            return None

        def endpoint_cup(a: str, b: str, widths: dict[str, int]) -> str | None:
            for piece in widths:
                if {a, b} == {f"{piece}.left", f"{piece}.right"}:
                    return piece
            return None

        def future_gap_units(state_index: int, a: str, b: str, widths: dict[str, int]) -> int:
            endpoint_piece = endpoint_cup(a, b, widths)
            endpoint_width = widths[endpoint_piece] if endpoint_piece is not None else 1
            for event_index in range(state_index + 1, len(states)):
                before = states[event_index - 1]
                if not adjacent(before, a, b):
                    return endpoint_width
                piece = cup_inserted_between(trace[event_index - 1]["form"], a, b)
                if piece is not None:
                    return max(endpoint_width, 1 + widths[piece] + 1)
            return endpoint_width

        def interval_width_units(state_index: int, interval: list[str], widths: dict[str, int]) -> int:
            if len(interval) < 2:
                return 0
            total = 0
            for a, b in zip(interval, interval[1:]):
                total += future_gap_units(state_index, a, b, widths)
            return max(1, total)

        for _ in range(32):
            updated = dict(width_units)
            for piece in width_units:
                left = f"{piece}.left"
                right = f"{piece}.right"
                for state_index, order in enumerate(states):
                    if left not in order or right not in order:
                        continue
                    i = order.index(left)
                    j = order.index(right)
                    lo, hi = sorted((i, j))
                    updated[piece] = max(
                        updated[piece],
                        interval_width_units(state_index, order[lo : hi + 1], width_units),
                    )
            if updated == width_units:
                break
            width_units = updated

        return {piece: units * self.step for piece, units in width_units.items()}

    def _rows(self, trace: list[dict[str, Any]], cup_widths: dict[str, float]) -> list[dict[str, Any]]:
        order: list[str] = []
        xs: dict[str, float] = {}
        rows = []
        for row in trace:
            form = row["form"]
            after = row["order"]
            before = list(order)
            before_x = dict(xs)
            xs = self._apply(form, before, after, xs, cup_widths)
            rows.append(
                {
                    "form": form,
                    "before": before,
                    "after": list(after),
                    "before_x": before_x,
                    "after_x": dict(xs),
                }
            )
            order = list(after)
        return rows

    def _shift_right_side(
        self,
        xs: dict[str, float],
        after: list[str],
        first_right_index: int,
        amount: float,
    ) -> None:
        if amount <= 0:
            return
        for strand in after[first_right_index:]:
            if strand in xs:
                xs[strand] += amount

    def _apply(
        self,
        form: dict[str, Any],
        before: list[str],
        after: list[str],
        xs: dict[str, float],
        cup_widths: dict[str, float],
    ) -> dict[str, float]:
        kind = form["kind"]
        new_xs = dict(xs)
        if kind == "cross":
            over = form["over"]
            under = form["under"]
            new_xs[over], new_xs[under] = xs[under], xs[over]
            return new_xs
        if kind == "kink":
            return new_xs
        if kind == "cap":
            for strand in form["strands"]:
                new_xs.pop(strand, None)
            return new_xs
        if kind != "cup":
            raise ValueError(f"unknown form kind: {kind}")

        piece = form["piece"]
        left = f"{piece}.left"
        right = f"{piece}.right"
        left_index = after.index(left)
        right_index = after.index(right)
        width = max(self.step, cup_widths.get(piece, self.step))

        left_neighbor = after[left_index - 1] if left_index > 0 else None
        right_neighbor = after[right_index + 1] if right_index + 1 < len(after) else None
        if left_neighbor is not None and right_neighbor is not None:
            available_left = new_xs[left_neighbor]
            available_right = new_xs[right_neighbor]
            available_width = available_right - available_left
            required_width = width + 2 * self.step
            if available_width >= required_width:
                x_left = available_left + (available_width - width) / 2
                x_right = x_left + width
            else:
                x_left = available_left + self.step
                x_right = x_left + width
                needed = x_right + self.step - available_right
                self._shift_right_side(new_xs, after, right_index + 1, max(needed, 0.0))
        elif left_neighbor is None:
            x_left = self.margin
            x_right = x_left + width
            if right_neighbor is not None:
                needed = x_right + self.step - new_xs[right_neighbor]
                self._shift_right_side(new_xs, after, right_index + 1, max(needed, 0.0))
        else:
            x_left = new_xs[left_neighbor] + self.step
            x_right = x_left + width

        new_xs[left] = x_left
        new_xs[right] = x_right
        return new_xs


def draw_cross(
    parts: list[str],
    form: dict[str, Any],
    before: list[str],
    after: list[str],
    y0: float,
    y1: float,
    xs0: dict[str, float],
    xs1: dict[str, float],
    colors: dict[str, str],
    stroke_scale: float,
    *,
    draw_stationary: bool = True,
    draw_style: str = "straight",
    elbow: float | None = None,
    sign_label: str | None = None,
) -> None:
    over = form["over"]
    under = form["under"]
    moving = {over, under}
    if draw_stationary:
        for strand in before:
            if strand in after and strand not in moving:
                parts.append(
                    svg_strand_path(
                        xs0[strand],
                        y0,
                        xs1[strand],
                        y1,
                        colors[component_of(strand)],
                        2.4,
                        stroke_scale=stroke_scale,
                        draw_style=carrier_draw_style(draw_style),
                    )
                )

    ux0, ux1 = xs0[under], xs1[under]
    ox0, ox1 = xs0[over], xs1[over]
    under_color = colors[component_of(under)]
    over_color = colors[component_of(over)]
    if draw_stationary or draw_style in {"rectilinear", "rectilinear45"}:
        under_path = svg_crossing_path_45(
            ux0,
            y0,
            ux1,
            y1,
            under_color,
            2.4,
            stroke_scale=stroke_scale,
            center_y=elbow,
        ) if draw_style == "rectilinear45" else svg_strand_path(
            ux0,
            y0,
            ux1,
            y1,
            under_color,
            2.4,
            stroke_scale=stroke_scale,
            draw_style=draw_style,
            elbow=elbow,
        )
        parts.append(
            under_path
        )
    cx = (ox0 + ox1 + ux0 + ux1) / 4
    cy = (y0 + y1) / 2 if elbow is None else elbow
    parts.append(
        f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{3.8 * stroke_scale:.1f}" '
        'fill="white" stroke="none" />'
    )
    over_path = svg_crossing_path_45(
        ox0,
        y0,
        ox1,
        y1,
        over_color,
        2.4,
        stroke_scale=stroke_scale,
        center_y=elbow,
    ) if draw_style == "rectilinear45" else svg_strand_path(
            ox0,
            y0,
            ox1,
            y1,
            over_color,
            2.4,
            stroke_scale=stroke_scale,
            draw_style=draw_style,
            elbow=elbow,
    )
    parts.append(over_path)
    label = sign_label if sign_label is not None else form.get("sign", "")
    if label:
        parts.append(
            f'<circle cx="{cx + 10:.1f}" cy="{cy - 7:.1f}" r="7.5" '
            'fill="white" stroke="#222" stroke-width="0.8" />'
        )
        parts.append(svg_text(cx + 5.5, cy - 3.5, label, 11, "#111"))


def draw_cup(
    parts: list[str],
    form: dict[str, Any],
    before: list[str],
    after: list[str],
    y0: float,
    y1: float,
    xs0: dict[str, float],
    xs1: dict[str, float],
    colors: dict[str, str],
    stroke_scale: float,
    *,
    draw_stationary: bool = True,
    draw_style: str = "straight",
) -> None:
    piece = form["piece"]
    new = {f"{piece}.left", f"{piece}.right"}
    for strand in before:
        if draw_stationary and strand in after:
            parts.append(
                svg_strand_path(
                    xs0[strand],
                    y0,
                    xs1[strand],
                    y1,
                    colors[component_of(strand)],
                    2.4,
                    stroke_scale=stroke_scale,
                    draw_style=carrier_draw_style(draw_style),
                )
            )
    left = f"{piece}.left"
    right = f"{piece}.right"
    color = colors[component_of(left)]
    x_left, x_right = xs1[left], xs1[right]
    x_mid = (x_left + x_right) / 2
    control_y = shallow_control_y(y1, y0)
    path = (
        f'<path d="M {x_left:.1f} {y1:.1f} Q {x_mid:.1f} {control_y:.1f} {x_right:.1f} {y1:.1f}" '
        f'stroke="{color}" stroke-width="{2.4 * stroke_scale:.1f}" '
        'fill="none" stroke-linecap="round" />'
    )
    parts.append(
        f'<path d="M {x_left:.1f} {y1:.1f} Q {x_mid:.1f} {control_y:.1f} {x_right:.1f} {y1:.1f}" '
        f'stroke="white" stroke-width="{6.0 * stroke_scale:.1f}" '
        'fill="none" stroke-linecap="round" />'
    )
    parts.append(path)
    parts.append(svg_text(x_mid + 3, (y0 + y1) / 2, f"cup {piece}", 9, color))


def draw_cap(
    parts: list[str],
    form: dict[str, Any],
    before: list[str],
    after: list[str],
    y0: float,
    y1: float,
    xs0: dict[str, float],
    xs1: dict[str, float],
    colors: dict[str, str],
    stroke_scale: float,
    *,
    draw_stationary: bool = True,
    draw_style: str = "straight",
) -> None:
    gone = set(form["strands"])
    for strand in before:
        if draw_stationary and strand in after:
            parts.append(
                svg_strand_path(
                    xs0[strand],
                    y0,
                    xs1[strand],
                    y1,
                    colors[component_of(strand)],
                    2.4,
                    stroke_scale=stroke_scale,
                    draw_style=carrier_draw_style(draw_style),
                )
            )
    a, b = form["strands"]
    color = colors[component_of(a)]
    xa, xb = xs0[a], xs0[b]
    x_mid = (xa + xb) / 2
    control_y = shallow_control_y(y0, y1)
    path = (
        f'<path d="M {xa:.1f} {y0:.1f} Q {x_mid:.1f} {control_y:.1f} {xb:.1f} {y0:.1f}" '
        f'stroke="{color}" stroke-width="{2.4 * stroke_scale:.1f}" '
        'fill="none" stroke-linecap="round" />'
    )
    parts.append(
        f'<path d="M {xa:.1f} {y0:.1f} Q {x_mid:.1f} {control_y:.1f} {xb:.1f} {y0:.1f}" '
        f'stroke="white" stroke-width="{6.0 * stroke_scale:.1f}" '
        'fill="none" stroke-linecap="round" />'
    )
    parts.append(path)
    parts.append(svg_text(x_mid + 3, (y0 + y1) / 2, f"cap {component_of(a)}", 9, color))


def draw_kink(
    parts: list[str],
    form: dict[str, Any],
    before: list[str],
    after: list[str],
    y0: float,
    y1: float,
    xs0: dict[str, float],
    xs1: dict[str, float],
    colors: dict[str, str],
    stroke_scale: float,
    *,
    draw_stationary: bool = True,
    draw_style: str = "straight",
) -> None:
    strand = form["strand"]
    for active in before:
        if draw_stationary and active in after:
            parts.append(
                svg_strand_path(
                    xs0[active],
                    y0,
                    xs1[active],
                    y1,
                    colors[component_of(active)],
                    2.4,
                    stroke_scale=stroke_scale,
                    draw_style=carrier_draw_style(draw_style),
                )
            )
    x = xs0[strand]
    y = (y0 + y1) / 2
    color = colors[component_of(strand)]
    r = 7
    parts.append(
        f'<circle cx="{x + 10:.1f}" cy="{y:.1f}" r="{r}" stroke="{color}" '
        f'stroke-width="{2.4 * stroke_scale:.1f}" fill="none" />'
    )
    label = f'{form["sign"]}{form["times"]}'
    parts.append(svg_text(x + 20, y + 4, f"kink {component_of(strand)} {label}", 10, color))


def row_height(form: dict[str, Any], vertical_mode: str, base_y_step: float) -> float:
    if vertical_mode == "full":
        return base_y_step
    if vertical_mode not in {"compressed", "scheduled"}:
        raise ValueError(f"unknown vertical mode: {vertical_mode}")
    kind = form["kind"]
    if kind == "cross":
        return 10.0
    if kind == "kink":
        return 12.0
    return 18.0


def touched_strands(form: dict[str, Any]) -> set[str]:
    kind = form["kind"]
    if kind == "cross":
        return {form["over"], form["under"]}
    if kind == "kink":
        return {form["strand"]}
    if kind == "cup":
        piece = form["piece"]
        touched = {f"{piece}.left", f"{piece}.right"}
        if "between" in form:
            touched |= set(form["between"])
        if "after" in form:
            touched.add(form["after"])
        return touched
    if kind == "cap":
        return set(form["strands"])
    raise ValueError(f"unknown form kind: {kind}")


def piece_endpoints(piece: str) -> set[str]:
    return {f"{piece}.left", f"{piece}.right"}


def cup_piece(form: dict[str, Any]) -> str | None:
    return form["piece"] if form["kind"] == "cup" else None


def cap_piece(form: dict[str, Any]) -> str | None:
    if form["kind"] != "cap":
        return None
    if "piece" in form:
        return form["piece"]
    strands = set(form["strands"])
    for strand in strands:
        if "." not in strand:
            continue
        piece = strand.split(".", 1)[0]
        if strands == piece_endpoints(piece):
            return piece
    return None


def nested_cup_parent(form: dict[str, Any]) -> str | None:
    if form["kind"] != "cup" or "between" not in form:
        return None
    anchors = set(form["between"])
    for strand in anchors:
        if "." not in strand:
            continue
        piece = strand.split(".", 1)[0]
        if anchors == piece_endpoints(piece):
            return piece
    return None


def event_dependencies(rows: list[dict[str, Any]]) -> list[set[int]]:
    deps: list[set[int]] = [set() for _ in rows]
    last_toucher: dict[str, int] = {}
    cup_by_piece: dict[str, int] = {}
    cap_by_piece: dict[str, int] = {}
    children: dict[str, set[str]] = {}
    children_by_anchor_pair: dict[frozenset[str], set[str]] = {}
    previous_consecutive_cup: int | None = None

    for i, row in enumerate(rows):
        form = row["form"]
        if form["kind"] == "cup":
            if previous_consecutive_cup is not None and form.get("at") in {"far-left", "far-right"}:
                deps[i].add(previous_consecutive_cup)
            previous_consecutive_cup = i
        else:
            previous_consecutive_cup = None

        for strand in touched_strands(form):
            if strand in last_toucher:
                deps[i].add(last_toucher[strand])
        for strand in touched_strands(form):
            last_toucher[strand] = i

        piece = cup_piece(form)
        if piece is not None:
            cup_by_piece[piece] = i
            parent = nested_cup_parent(form)
            if parent is not None:
                children.setdefault(parent, set()).add(piece)
                if parent in cup_by_piece:
                    deps[i].add(cup_by_piece[parent])
            if "between" in form:
                children_by_anchor_pair.setdefault(frozenset(form["between"]), set()).add(piece)

        piece = cap_piece(form)
        if piece is not None:
            cap_by_piece[piece] = i
        if form["kind"] == "cap":
            for child in children_by_anchor_pair.get(frozenset(form["strands"]), set()):
                child_cap = cap_by_piece.get(child)
                if child_cap is not None:
                    deps[i].add(child_cap)

    for parent, child_pieces in children.items():
        parent_cap = cap_by_piece.get(parent)
        if parent_cap is None:
            continue
        for child in child_pieces:
            child_cap = cap_by_piece.get(child)
            if child_cap is not None:
                deps[parent_cap].add(child_cap)
    return deps


def indexed_parallel_piece(piece: str) -> tuple[str, int] | None:
    match = re.fullmatch(r"([LR])(\d+)", piece)
    if match is None:
        return None
    return match.group(1), int(match.group(2))


def compute_layer_indices(deps: list[set[int]], constraints: dict[int, int] | None = None) -> list[int]:
    constraints = constraints or {}
    layer_index: list[int] = []
    for i, row_deps in enumerate(deps):
        lower_bound = constraints.get(i, 0)
        if row_deps:
            lower_bound = max(lower_bound, max(layer_index[j] for j in row_deps) + 1)
        layer_index.append(lower_bound)
    return layer_index


def parallel_alignment_constraints(rows: list[dict[str, Any]], deps: list[set[int]]) -> dict[int, int]:
    """Delay parallel L_i/R_i birth/death chains so matching depths align."""
    base_layers = compute_layer_indices(deps)
    constraints: dict[int, int] = {}
    for kind, piece_getter in (("cup", cup_piece), ("cap", cap_piece)):
        by_index: dict[int, list[int]] = {}
        for i, row in enumerate(rows):
            form = row["form"]
            if form["kind"] != kind:
                continue
            piece = piece_getter(form)
            if piece is None:
                continue
            indexed = indexed_parallel_piece(piece)
            if indexed is None:
                continue
            _, index = indexed
            by_index.setdefault(index, []).append(i)
        for indices in by_index.values():
            if len(indices) < 2:
                continue
            target = max(base_layers[i] for i in indices)
            for i in indices:
                constraints[i] = max(constraints.get(i, 0), target)
    return constraints


def dependency_layers(rows: list[dict[str, Any]]) -> list[list[dict[str, Any]]]:
    """Schedule independent events onto shared horizontal layers.

    This is intentionally conservative.  It preserves the order of events on
    each touched strand, preserves nesting for cup/cap pairs, and then delays
    parallel L_i/R_i chains so matching depths align visually.
    """
    deps = event_dependencies(rows)
    constraints = parallel_alignment_constraints(rows, deps)

    previous: list[int] | None = None
    layer_index = compute_layer_indices(deps, constraints)
    while previous != layer_index:
        previous = layer_index
        layer_index = compute_layer_indices(deps, constraints)

    layers: list[list[dict[str, Any]]] = [[] for _ in range(max(layer_index, default=-1) + 1)]
    for row, layer in zip(rows, layer_index, strict=True):
        layers[layer].append(row)
    return [layer for layer in layers if layer]


def make_layers(rows: list[dict[str, Any]], vertical_mode: str) -> list[list[dict[str, Any]]]:
    if vertical_mode == "full":
        return [[row] for row in rows]
    if vertical_mode == "scheduled":
        return dependency_layers(rows)
    if vertical_mode != "compressed":
        raise ValueError(f"unknown vertical mode: {vertical_mode}")

    layers: list[list[dict[str, Any]]] = []
    current: list[dict[str, Any]] = []
    current_touched: set[str] = set()
    current_kind: str | None = None
    for row in rows:
        kind = row["form"]["kind"]
        touched = touched_strands(row["form"])
        can_batch = (
            current
            and kind in {"cross", "kink"}
            and current_kind in {"cross", "kink"}
            and not (current_touched & touched)
        )
        if can_batch:
            current.append(row)
            current_touched |= touched
            continue
        if current:
            layers.append(current)
        current = [row]
        current_touched = set(touched)
        current_kind = kind
    if current:
        layers.append(current)
    return layers


def draw_layer_background(
    parts: list[str],
    layer: list[dict[str, Any]],
    y0: float,
    y1: float,
    colors: dict[str, str],
    stroke_scale: float,
    draw_style: str,
    skip_touched: bool = False,
    elbows_by_strand: dict[str, float] | None = None,
) -> None:
    elbows_by_strand = elbows_by_strand or {}
    before = layer[0]["before"]
    after = layer[-1]["after"]
    xs0 = layer[0]["before_x"]
    xs1 = layer[-1]["after_x"]
    touched: set[str] = set()
    if skip_touched:
        for row in layer:
            touched |= touched_strands(row["form"])
    for strand in before:
        if strand in after and strand not in touched:
            elbow = elbows_by_strand.get(strand)
            parts.append(
                svg_strand_path(
                    xs0[strand],
                    y0,
                    xs1[strand],
                    y1,
                    colors[component_of(strand)],
                    2.4,
                    stroke_scale=stroke_scale,
                    draw_style="rectilinear" if elbow is not None else carrier_draw_style(draw_style),
                    elbow=elbow,
                )
            )


def layer_background_strands(
    layer: list[dict[str, Any]],
    *,
    skip_touched: bool,
    moved_only: bool = False,
) -> list[str]:
    before = layer[0]["before"]
    after = layer[-1]["after"]
    xs0 = layer[0]["before_x"]
    xs1 = layer[-1]["after_x"]
    touched: set[str] = set()
    if skip_touched:
        for row in layer:
            touched |= touched_strands(row["form"])
    strands: list[str] = []
    for strand in before:
        if strand not in after or strand in touched:
            continue
        if moved_only and abs(xs0[strand] - xs1[strand]) < 1e-9:
            continue
        strands.append(strand)
    return strands


def background_route_count(layer: list[dict[str, Any]], *, skip_touched: bool) -> int:
    return len(layer_background_strands(layer, skip_touched=skip_touched, moved_only=True))


def background_elbows_by_strand(
    layer: list[dict[str, Any]],
    y0: float,
    y1: float,
    *,
    skip_touched: bool,
) -> dict[str, float]:
    moving = layer_background_strands(layer, skip_touched=skip_touched, moved_only=True)
    if len(moving) <= 1:
        return {}
    padding = max(2.0, min(4.0, abs(y0 - y1) / 6))
    usable = max(1.0, abs(y0 - y1) - 2 * padding)
    return {
        strand: y0 - padding - usable * (i + 0.5) / len(moving)
        for i, strand in enumerate(moving)
    }


def cup_anchor_elbows_by_strand(
    layer: list[dict[str, Any]],
    y0: float,
    y1: float,
) -> dict[str, float]:
    before = layer[0]["before"]
    after = layer[-1]["after"]
    xs0 = layer[0]["before_x"]
    xs1 = layer[-1]["after_x"]
    anchors: list[str] = []
    for row in layer:
        form = row["form"]
        if form["kind"] != "cup" or "between" not in form:
            continue
        for strand in form["between"]:
            if strand in before and strand in after and abs(xs0[strand] - xs1[strand]) > 1e-9:
                anchors.append(strand)
    deduped = list(dict.fromkeys(anchors))
    if not deduped:
        return {}
    padding = max(2.0, min(4.0, abs(y0 - y1) / 6))
    spacing = min(3.0, max(1.0, (abs(y0 - y1) - 2 * padding) / max(1, len(deduped))))
    return {strand: y0 - padding - i * spacing for i, strand in enumerate(deduped)}


def collect_layer_background_segments(
    layer: list[dict[str, Any]],
    y0: float,
    y1: float,
    draw_style: str,
    *,
    layer_index: int,
    skip_touched: bool = False,
    elbows_by_strand: dict[str, float] | None = None,
) -> list[Segment]:
    elbows_by_strand = elbows_by_strand or {}
    before = layer[0]["before"]
    after = layer[-1]["after"]
    xs0 = layer[0]["before_x"]
    xs1 = layer[-1]["after_x"]
    touched: set[str] = set()
    if skip_touched:
        for row in layer:
            touched |= touched_strands(row["form"])
    segments: list[Segment] = []
    for strand in before:
        if strand in after and strand not in touched:
            elbow = elbows_by_strand.get(strand)
            segments.extend(
                strand_segments(
                    xs0[strand],
                    y0,
                    xs1[strand],
                    y1,
                    strand=strand,
                    role="layer-background",
                    event="layer-background",
                    layer=layer_index,
                    draw_style="rectilinear" if elbow is not None else carrier_draw_style(draw_style),
                    elbow=elbow,
                )
            )
    return segments


def collect_row_segments(
    row: dict[str, Any],
    y0: float,
    y1: float,
    draw_style: str,
    *,
    layer_index: int,
    draw_stationary: bool,
    elbow: float | None = None,
) -> list[Segment]:
    form = row["form"]
    before = row["before"]
    after = row["after"]
    xs0 = row["before_x"]
    xs1 = row["after_x"]
    original_index = row.get("original_index")
    event = f"event-{original_index + 1:03d}" if isinstance(original_index, int) else "event"
    segments: list[Segment] = []

    if form["kind"] == "cross":
        over = form["over"]
        under = form["under"]
        moving = {over, under}
        if draw_stationary:
            for strand in before:
                if strand in after and strand not in moving:
                    segments.extend(
                        strand_segments(
                            xs0[strand],
                            y0,
                            xs1[strand],
                            y1,
                            strand=strand,
                            role="stationary",
                            event=event,
                            layer=layer_index,
                            draw_style=carrier_draw_style(draw_style),
                        )
                    )
        allowed = f"{event}:cross"
        if draw_stationary or draw_style in {"rectilinear", "rectilinear45"}:
            if draw_style == "rectilinear45":
                segments.extend(
                    crossing_segments_45(
                        xs0[under],
                        y0,
                        xs1[under],
                        y1,
                        strand=under,
                        role="crossing-under",
                        event=event,
                        layer=layer_index,
                        center_y=elbow,
                        allowed_crossing=allowed,
                    )
                )
            else:
                segments.extend(
                    strand_segments(
                        xs0[under],
                        y0,
                        xs1[under],
                        y1,
                        strand=under,
                        role="crossing-under",
                        event=event,
                        layer=layer_index,
                        draw_style=draw_style,
                        elbow=elbow,
                        allowed_crossing=allowed,
                    )
                )
        if draw_style == "rectilinear45":
            segments.extend(
                crossing_segments_45(
                    xs0[over],
                    y0,
                    xs1[over],
                    y1,
                    strand=over,
                    role="crossing-over",
                    event=event,
                    layer=layer_index,
                    center_y=elbow,
                    allowed_crossing=allowed,
                )
            )
        else:
            segments.extend(
                strand_segments(
                    xs0[over],
                    y0,
                    xs1[over],
                    y1,
                    strand=over,
                    role="crossing-over",
                    event=event,
                    layer=layer_index,
                    draw_style=draw_style,
                    elbow=elbow,
                    allowed_crossing=allowed,
                )
            )
        return segments

    if form["kind"] == "cup":
        if draw_stationary:
            for strand in before:
                if strand in after:
                    segments.extend(
                        strand_segments(
                            xs0[strand],
                            y0,
                            xs1[strand],
                            y1,
                            strand=strand,
                            role="stationary",
                            event=event,
                            layer=layer_index,
                            draw_style=carrier_draw_style(draw_style),
                        )
                    )
        piece = form["piece"]
        left = f"{piece}.left"
        right = f"{piece}.right"
        x_left, x_right = xs1[left], xs1[right]
        x_mid = (x_left + x_right) / 2
        segments.extend(
            quadratic_segments(
                x_left,
                y1,
                x_mid,
                shallow_control_y(y1, y0),
                x_right,
                y1,
                strand=piece,
                role="cup",
                event=event,
                layer=layer_index,
            )
        )
        return segments

    if form["kind"] == "cap":
        if draw_stationary:
            for strand in before:
                if strand in after:
                    segments.extend(
                        strand_segments(
                            xs0[strand],
                            y0,
                            xs1[strand],
                            y1,
                            strand=strand,
                            role="stationary",
                            event=event,
                            layer=layer_index,
                            draw_style=carrier_draw_style(draw_style),
                        )
                    )
        a, b = form["strands"]
        xa, xb = xs0[a], xs0[b]
        x_mid = (xa + xb) / 2
        segments.extend(
            quadratic_segments(
                xa,
                y0,
                x_mid,
                shallow_control_y(y0, y1),
                xb,
                y0,
                strand=component_of(a),
                role="cap",
                event=event,
                layer=layer_index,
            )
        )
        return segments

    if form["kind"] == "kink":
        if draw_stationary:
            for strand in before:
                if strand in after:
                    segments.extend(
                        strand_segments(
                            xs0[strand],
                            y0,
                            xs1[strand],
                            y1,
                            strand=strand,
                            role="stationary",
                            event=event,
                            layer=layer_index,
                            draw_style=carrier_draw_style(draw_style),
                        )
                    )
        return segments

    raise ValueError(f"unknown form kind: {form['kind']}")


def _bbox_disjoint(a: Segment, b: Segment, eps: float) -> bool:
    return (
        max(a.x1, a.x2) < min(b.x1, b.x2) - eps
        or max(b.x1, b.x2) < min(a.x1, a.x2) - eps
        or max(a.y1, a.y2) < min(b.y1, b.y2) - eps
        or max(b.y1, b.y2) < min(a.y1, a.y2) - eps
    )


def _orient(ax: float, ay: float, bx: float, by: float, cx: float, cy: float) -> float:
    return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)


def _between(a: float, b: float, c: float, eps: float) -> bool:
    return min(a, b) - eps <= c <= max(a, b) + eps


def _point_on_segment(x: float, y: float, segment: Segment, eps: float) -> bool:
    return (
        abs(_orient(segment.x1, segment.y1, segment.x2, segment.y2, x, y)) <= eps
        and _between(segment.x1, segment.x2, x, eps)
        and _between(segment.y1, segment.y2, y, eps)
    )


def _is_endpoint(x: float, y: float, segment: Segment, eps: float) -> bool:
    return (
        abs(x - segment.x1) <= eps and abs(y - segment.y1) <= eps
    ) or (
        abs(x - segment.x2) <= eps and abs(y - segment.y2) <= eps
    )


def _line_intersection_point(a: Segment, b: Segment, eps: float) -> tuple[float, float] | None:
    x1, y1, x2, y2 = a.x1, a.y1, a.x2, a.y2
    x3, y3, x4, y4 = b.x1, b.y1, b.x2, b.y2
    denom = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4)
    if abs(denom) <= eps:
        return None
    px = (
        (x1 * y2 - y1 * x2) * (x3 - x4)
        - (x1 - x2) * (x3 * y4 - y3 * x4)
    ) / denom
    py = (
        (x1 * y2 - y1 * x2) * (y3 - y4)
        - (y1 - y2) * (x3 * y4 - y3 * x4)
    ) / denom
    if _point_on_segment(px, py, a, eps) and _point_on_segment(px, py, b, eps):
        return px, py
    return None


def _colinear_overlap(a: Segment, b: Segment, eps: float) -> dict[str, Any] | None:
    if abs(_orient(a.x1, a.y1, a.x2, a.y2, b.x1, b.y1)) > eps:
        return None
    if abs(_orient(a.x1, a.y1, a.x2, a.y2, b.x2, b.y2)) > eps:
        return None
    if abs(a.x1 - a.x2) >= abs(a.y1 - a.y2):
        start = max(min(a.x1, a.x2), min(b.x1, b.x2))
        end = min(max(a.x1, a.x2), max(b.x1, b.x2))
    else:
        start = max(min(a.y1, a.y2), min(b.y1, b.y2))
        end = min(max(a.y1, a.y2), max(b.y1, b.y2))
    if end - start <= eps:
        return None
    return {"type": "overlap", "overlap_span": [round(start, 3), round(end, 3)]}


def _segments_allowed_to_meet(a: Segment, b: Segment) -> bool:
    if a.strand == b.strand:
        return True
    if a.allowed_crossing is not None and a.allowed_crossing == b.allowed_crossing:
        return True
    return False


def collision_report(
    segments: list[Segment],
    *,
    source: str,
    max_collisions: int = 200,
    eps: float = 1e-6,
) -> dict[str, Any]:
    collisions: list[dict[str, Any]] = []
    considered = 0
    for i, left in enumerate(segments):
        for j in range(i + 1, len(segments)):
            right = segments[j]
            if _segments_allowed_to_meet(left, right) or _bbox_disjoint(left, right, eps):
                continue
            considered += 1
            overlap = _colinear_overlap(left, right, eps)
            if overlap is not None:
                collisions.append(
                    {
                        **overlap,
                        "left": left.as_json(),
                        "right": right.as_json(),
                    }
                )
            else:
                point = _line_intersection_point(left, right, eps)
                if point is None:
                    continue
                px, py = point
                if _is_endpoint(px, py, left, eps) or _is_endpoint(px, py, right, eps):
                    continue
                collisions.append(
                    {
                        "type": "point",
                        "point": [round(px, 3), round(py, 3)],
                        "left": left.as_json(),
                        "right": right.as_json(),
                    }
                )
            if len(collisions) >= max_collisions:
                return {
                    "schema": "twisted-yetter.morse-render-collision-report.v1",
                    "source": source,
                    "segment_count": len(segments),
                    "considered_candidate_pairs": considered,
                    "collision_count": len(collisions),
                    "truncated": True,
                    "collisions": collisions,
                }
    return {
        "schema": "twisted-yetter.morse-render-collision-report.v1",
        "source": source,
        "segment_count": len(segments),
        "considered_candidate_pairs": considered,
        "collision_count": len(collisions),
        "truncated": False,
        "collisions": collisions,
    }


def _require_active(order: list[str], strand: str, context: str) -> int:
    try:
        return order.index(strand)
    except ValueError as exc:
        raise ValueError(f"{context}: strand is not active: {strand!r} in {order!r}") from exc


def _require_adjacent(order: list[str], a: str, b: str, context: str) -> tuple[int, int]:
    ia = _require_active(order, a, context)
    ib = _require_active(order, b, context)
    if abs(ia - ib) != 1:
        raise ValueError(f"{context}: strands are not adjacent: {a!r}, {b!r} in {order!r}")
    return ia, ib


def _shift_right_side(xs: dict[str, float], order: list[str], first_index: int, amount: float) -> None:
    if amount <= 0:
        return
    for strand in order[first_index:]:
        if strand in xs:
            xs[strand] += amount


def _cup_insert_index(form: dict[str, Any], order: list[str], context: str) -> int:
    if form.get("at") == "far-left":
        return 0
    if form.get("at") == "far-right":
        return len(order)
    if "between" in form:
        a, b = form["between"]
        ia, ib = _require_adjacent(order, a, b, context)
        if ib != ia + 1:
            raise ValueError(
                f"{context}: cup anchors are adjacent but not left-to-right: {a!r}, {b!r} in {order!r}"
            )
        return ia + 1
    if "after" in form:
        return _require_active(order, form["after"], context) + 1
    raise ValueError(f"{context}: cup has no insertion site: {form!r}")


def _apply_from_state(
    form: dict[str, Any],
    order: list[str],
    xs: dict[str, float],
    cup_widths: dict[str, float],
    *,
    margin: float,
    step: float,
    context: str,
) -> tuple[list[str], dict[str, float]]:
    kind = form["kind"]
    new_order = list(order)
    new_xs = dict(xs)

    if kind == "cross":
        over = form["over"]
        under = form["under"]
        io, iu = _require_adjacent(new_order, over, under, context)
        new_order[io], new_order[iu] = new_order[iu], new_order[io]
        new_xs[over], new_xs[under] = new_xs[under], new_xs[over]
        return new_order, new_xs

    if kind == "kink":
        _require_active(new_order, form["strand"], context)
        return new_order, new_xs

    if kind == "cap":
        a, b = form["strands"]
        _require_adjacent(new_order, a, b, context)
        gone = {a, b}
        new_order = [strand for strand in new_order if strand not in gone]
        for strand in gone:
            new_xs.pop(strand, None)
        return new_order, new_xs

    if kind != "cup":
        raise ValueError(f"{context}: unknown form kind: {kind}")

    piece = form["piece"]
    left = f"{piece}.left"
    right = f"{piece}.right"
    if left in new_order or right in new_order:
        raise ValueError(f"{context}: cup would duplicate active strands for {piece!r}")

    insert_at = _cup_insert_index(form, new_order, context)
    after = new_order[:insert_at] + [left, right] + new_order[insert_at:]
    left_index = insert_at
    right_index = insert_at + 1
    width = max(step, cup_widths.get(piece, step))

    left_neighbor = after[left_index - 1] if left_index > 0 else None
    right_neighbor = after[right_index + 1] if right_index + 1 < len(after) else None
    if left_neighbor is not None and right_neighbor is not None:
        available_left = new_xs[left_neighbor]
        available_right = new_xs[right_neighbor]
        available_width = available_right - available_left
        required_width = width + 2 * step
        if available_width >= required_width:
            x_left = available_left + (available_width - width) / 2
            x_right = x_left + width
        else:
            x_left = available_left + step
            x_right = x_left + width
            needed = x_right + step - available_right
            _shift_right_side(new_xs, after, right_index + 1, max(needed, 0.0))
    elif left_neighbor is None:
        x_left = margin
        x_right = x_left + width
        if right_neighbor is not None:
            needed = x_right + step - new_xs[right_neighbor]
            _shift_right_side(new_xs, after, right_index + 1, max(needed, 0.0))
    else:
        x_left = new_xs[left_neighbor] + step
        x_right = x_left + width

    new_xs[left] = x_left
    new_xs[right] = x_right
    return after, new_xs


def _can_apply_from_order(form: dict[str, Any], order: list[str]) -> bool:
    try:
        kind = form["kind"]
        if kind == "cross":
            _require_adjacent(order, form["over"], form["under"], "schedule")
            return True
        if kind == "kink":
            _require_active(order, form["strand"], "schedule")
            return True
        if kind == "cap":
            a, b = form["strands"]
            _require_adjacent(order, a, b, "schedule")
            return True
        if kind == "cup":
            piece = form["piece"]
            if f"{piece}.left" in order or f"{piece}.right" in order:
                return False
            _cup_insert_index(form, order, "schedule")
            return True
    except ValueError:
        return False
    raise ValueError(f"unknown form kind: {form['kind']}")


def _scheduling_touched(form: dict[str, Any]) -> set[str]:
    """Local sites that make two forms unsafe to draw as one Morse layer."""
    touched = touched_strands(form)
    if form["kind"] == "cup":
        if form.get("at") == "far-left":
            touched.add("__far_left__")
        elif form.get("at") == "far-right":
            touched.add("__far_right__")
    return touched


def _split_into_simultaneous_sublayers(
    layer: list[dict[str, Any]],
    order: list[str],
) -> list[list[dict[str, Any]]]:
    """Refine a dependency layer into genuine same-height local moves."""
    pending = list(layer)
    sublayers: list[list[dict[str, Any]]] = []
    scratch_order = list(order)
    scratch_xs = {strand: float(i) for i, strand in enumerate(scratch_order)}

    while pending:
        selected: list[dict[str, Any]] = []
        blocked: list[dict[str, Any]] = []
        occupied: set[str] = set()
        target_kind: str | None = None
        candidate_order = list(scratch_order)
        candidate_xs = dict(scratch_xs)
        for row in pending:
            kind = row["form"]["kind"]
            if target_kind is not None and kind != target_kind:
                blocked.append(row)
                continue
            sites = _scheduling_touched(row["form"])
            allow_shared_sites = kind == "cup"
            if _can_apply_from_order(row["form"], candidate_order) and (
                allow_shared_sites or not (occupied & sites)
            ):
                selected.append(row)
                occupied |= sites
                target_kind = kind
                if kind == "cup":
                    candidate_order, candidate_xs = _apply_from_state(
                        row["form"],
                        candidate_order,
                        candidate_xs,
                        {},
                        margin=0.0,
                        step=1.0,
                        context="schedule cup selection",
                    )
            else:
                blocked.append(row)

        if not selected:
            form = pending[0]["form"]
            raise ValueError(
                f"dependency layer cannot be refined into legal simultaneous moves; "
                f"first blocked form is {form!r} in order {scratch_order!r}"
            )

        for row in selected:
            scratch_order, scratch_xs = _apply_from_state(
                row["form"],
                scratch_order,
                scratch_xs,
                {},
                margin=0.0,
                step=1.0,
                context="schedule refinement",
            )
        sublayers.append(selected)
        pending = blocked

    return sublayers


def _can_merge_small_cup_layers(left_layer: list[dict[str, Any]], right_layer: list[dict[str, Any]]) -> bool:
    if len(left_layer) != 1 or len(right_layer) != 1:
        return False
    left = left_layer[0]["form"]
    right = right_layer[0]["form"]
    if left["kind"] != "cup" or right["kind"] != "cup":
        return False
    if "between" not in left or "between" not in right:
        return False
    left_piece = left["piece"]
    left_endpoints = {f"{left_piece}.left", f"{left_piece}.right"}
    return bool(left_endpoints & set(right["between"]))


def _merge_small_adjacent_cup_layers(layers: list[list[dict[str, Any]]]) -> list[list[dict[str, Any]]]:
    merged: list[list[dict[str, Any]]] = []
    i = 0
    while i < len(layers):
        layer = list(layers[i])
        while i + 1 < len(layers) and _can_merge_small_cup_layers(layer, layers[i + 1]):
            i += 1
            layer.extend(layers[i])
        merged.append(layer)
        i += 1
    return merged


def scheduled_replay_layers(
    rows: list[dict[str, Any]],
    *,
    cup_widths: dict[str, float],
    margin: float,
    step: float,
) -> tuple[list[list[dict[str, Any]]], float]:
    """Replay dependency-scheduled rows and recompute states for that order."""
    row_indices = {id(row): i for i, row in enumerate(rows)}
    layers = _merge_small_adjacent_cup_layers(dependency_layers(rows))
    order: list[str] = []
    xs: dict[str, float] = {}
    replayed_layers: list[list[dict[str, Any]]] = []
    max_x = margin

    for layer_i, layer in enumerate(layers):
        for sublayer_i, sublayer in enumerate(_split_into_simultaneous_sublayers(layer, order)):
            layer_before = list(order)
            layer_before_x = dict(xs)
            replayed_layer = []
            applied: list[dict[str, Any]] = []
            for row in sublayer:
                original_i = row_indices[id(row)]
                try:
                    order, xs = _apply_from_state(
                        row["form"],
                        order,
                        xs,
                        cup_widths,
                        margin=margin,
                        step=step,
                        context=(
                            f"scheduled layer {layer_i + 1}.{sublayer_i + 1}, "
                            f"event {original_i + 1}"
                        ),
                    )
                except ValueError as exc:
                    raise ValueError(f"cannot scheduled-replay form {row['form']!r}: {exc}") from exc
                applied.append(row)

            layer_after = list(order)
            layer_after_x = dict(xs)
            max_x = max(
                max_x,
                max(layer_before_x.values(), default=margin),
                max(layer_after_x.values(), default=margin),
            )
            for row in applied:
                original_i = row_indices[id(row)]
                replayed_layer.append(
                    {
                        "form": row["form"],
                        "before": layer_before,
                        "after": layer_after,
                        "before_x": layer_before_x,
                        "after_x": layer_after_x,
                        "original_index": original_i,
                    }
                )
            replayed_layers.append(replayed_layer)
    return replayed_layers, max_x


def render(
    data: dict[str, Any],
    out: Path,
    *,
    layout_mode: str = "optimized",
    vertical_mode: str = "full",
    stroke_scale: float = 1.0,
    draw_style: str = "straight",
    vertical_scale: float = 1.0,
    collision_report_path: Path | None = None,
    sign_labels: dict[int, str] | None = None,
    piece_orientations: dict[str, int] | None = None,
) -> Path:
    trace = data["trace"]
    forms = data["forms"]
    colors = color_map(forms)
    title = data.get("source", "Morse rendering")
    margin = 90.0
    x_step = 24.0
    y_step = 24.0
    layout = StableLayout(trace, margin=margin, step=x_step, layout_mode=layout_mode)
    for original_index, row in enumerate(layout.rows):
        row["original_index"] = original_index
    sign_labels = sign_labels or {}
    piece_orientations = piece_orientations or {}
    if vertical_mode == "scheduled":
        layers, max_x = scheduled_replay_layers(
            layout.rows,
            cup_widths=layout.cup_widths,
            margin=margin,
            step=x_step,
        )
    else:
        layers = make_layers(layout.rows, vertical_mode)
        max_x = layout.max_x
    layer_heights = []
    for layer in layers:
        height_i = max(row_height(row["form"], vertical_mode, y_step) for row in layer)
        crossing_rows = [row for row in layer if row["form"]["kind"] == "cross"]
        if draw_style in {"rectilinear", "rectilinear45"} and len(crossing_rows) == len(layer):
            height_i = max(height_i, 7.0 * len(layer) + 8.0)
            if draw_style == "rectilinear45":
                max_shift = max(
                    (
                        abs(row["after_x"][strand] - row["before_x"][strand])
                        for row in layer
                        for strand in (row["form"]["over"], row["form"]["under"])
                    ),
                    default=0.0,
                )
                height_i = max(height_i, max_shift + 16.0)
        layer_heights.append(height_i * vertical_scale)
    width = margin * 2 + (max_x - margin) + 360
    height = 130 + sum(layer_heights) + 2 * y_step
    parts: list[str] = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width:.0f}" height="{height:.0f}" viewBox="0 0 {width:.0f} {height:.0f}">',
        '<rect width="100%" height="100%" fill="white" />',
        svg_text(20, 28, title, 16, "#111"),
        svg_text(
            20,
            48,
            (
                f"forms={len(forms)} layers={len(layers)} bottom-to-top, "
                f"layout={layout_mode}, vertical={vertical_mode}, "
                f"draw={draw_style}, stroke-scale={stroke_scale:g}, "
                f"vertical-scale={vertical_scale:g}"
            ),
            11,
            "#555",
        ),
    ]

    legend_x = width - 330
    legend_y = 24
    for i, (component, color) in enumerate(colors.items()):
        y = legend_y + i * 15
        parts.append(svg_line(legend_x, y - 4, legend_x + 24, y - 4, color, 4, stroke_scale=stroke_scale))
        parts.append(svg_text(legend_x + 32, y, component, 10, "#222"))

    y_top = 90.0
    current_y = y_top + sum(layer_heights)
    row_index = 0
    all_segments: list[Segment] = []
    for layer_i, (layer, height_i) in enumerate(zip(layers, layer_heights, strict=True), start=1):
        y0 = current_y
        y1 = y0 - height_i
        current_y = y1
        if vertical_mode == "scheduled":
            original_indices = sorted(row.get("original_index", row_index) + 1 for row in layer)
            label = ",".join(f"{index:03d}" for index in original_indices[:3])
            if len(original_indices) > 3:
                label += ",..."
        else:
            first = row_index + 1
            last = row_index + len(layer)
            label = f"{first:03d}" if first == last else f"{first:03d}-{last:03d}"
        if vertical_mode in {"full", "scheduled"} or row_index % 5 == 0:
            parts.append(svg_text(8, (y0 + y1) / 2 + 3, label, 8, "#999"))
        is_batched = len(layer) > 1
        crossing_rows = [row for row in layer if row["form"]["kind"] == "cross"]
        crossing_elbows: dict[int, float] = {}
        skip_touched_background = (
            draw_style in {"rectilinear", "rectilinear45"}
            and len(crossing_rows) == len(layer)
        )
        background_elbows: dict[str, float] = {}
        if draw_style in {"rectilinear", "rectilinear45"} and len(crossing_rows) > 1:
            padding = max(2.0, min(4.0, height_i / 6))
            usable = max(1.0, height_i - 2 * padding)
            for cross_i, row in enumerate(crossing_rows):
                crossing_elbows[id(row)] = y0 - padding - usable * (cross_i + 0.5) / len(crossing_rows)
        if is_batched:
            draw_layer_background(
                parts,
                layer,
                y0,
                y1,
                colors,
                stroke_scale,
                draw_style,
                skip_touched=skip_touched_background,
                elbows_by_strand=background_elbows,
            )
            all_segments.extend(
                collect_layer_background_segments(
                    layer,
                    y0,
                    y1,
                    draw_style,
                    layer_index=layer_i,
                    skip_touched=skip_touched_background,
                    elbows_by_strand=background_elbows,
                )
            )
        if piece_orientations:
            xs0_layer = layer[0]["before_x"]
            xs1_layer = layer[-1]["after_x"]
            after_layer = set(layer[-1]["after"])
            for strand in layer[0]["before"]:
                if strand in after_layer and abs(xs0_layer[strand] - xs1_layer[strand]) < 1e-9:
                    parts.append(
                        svg_orientation_arrow(
                            xs0_layer[strand],
                            (y0 + y1) / 2,
                            strand,
                            piece_orientations,
                        )
                    )
        for row in layer:
            form = row["form"]
            before = row["before"]
            after = row["after"]
            xs0 = row["before_x"]
            xs1 = row["after_x"]
            kind = form["kind"]
            all_segments.extend(
                collect_row_segments(
                    row,
                    y0,
                    y1,
                    draw_style,
                    layer_index=layer_i,
                    draw_stationary=not is_batched,
                    elbow=crossing_elbows.get(id(row)),
                )
            )
            if kind == "cross":
                draw_cross(
                    parts,
                    form,
                    before,
                    after,
                    y0,
                    y1,
                    xs0,
                    xs1,
                    colors,
                    stroke_scale,
                    draw_stationary=not is_batched,
                    draw_style=draw_style,
                    elbow=crossing_elbows.get(id(row)),
                    sign_label=sign_labels.get(row.get("original_index")),
                )
            elif kind == "cup":
                draw_cup(
                    parts,
                    form,
                    before,
                    after,
                    y0,
                    y1,
                    xs0,
                    xs1,
                    colors,
                    stroke_scale,
                    draw_stationary=not is_batched,
                    draw_style=draw_style,
                )
            elif kind == "cap":
                draw_cap(
                    parts,
                    form,
                    before,
                    after,
                    y0,
                    y1,
                    xs0,
                    xs1,
                    colors,
                    stroke_scale,
                    draw_stationary=not is_batched,
                    draw_style=draw_style,
                )
            elif kind == "kink":
                draw_kink(
                    parts,
                    form,
                    before,
                    after,
                    y0,
                    y1,
                    xs0,
                    xs1,
                    colors,
                    stroke_scale,
                    draw_stationary=not is_batched,
                    draw_style=draw_style,
                )
            else:
                raise ValueError(f"unknown form kind: {kind}")
        row_index += len(layer)

    parts.append("</svg>\n")
    out.write_text("\n".join(parts))
    if collision_report_path is not None:
        report = collision_report(
            all_segments,
            source=str(out),
            max_collisions=500,
        )
        report.update(
            {
                "input_source": data.get("source"),
                "layout_mode": layout_mode,
                "vertical_mode": vertical_mode,
                "draw_style": draw_style,
                "stroke_scale": stroke_scale,
                "vertical_scale": vertical_scale,
                "layers": len(layers),
                "forms": len(forms),
            }
        )
        collision_report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--out", type=Path, default=Path("/tmp/k3-figure815-morse-expanded-v1.svg"))
    parser.add_argument("--layout-mode", choices=["optimized", "unoptimized"], default="optimized")
    parser.add_argument("--vertical-mode", choices=["full", "compressed", "scheduled"], default="full")
    parser.add_argument(
        "--draw-style",
        choices=["straight", "rectilinear", "rectilinear45"],
        default="straight",
    )
    parser.add_argument("--stroke-scale", type=float, default=1.0)
    parser.add_argument("--vertical-scale", type=float, default=1.0)
    parser.add_argument("--collision-report", type=Path)
    parser.add_argument(
        "--sign-labels-from-sanity",
        type=Path,
        help="Optional link sanity JSON whose crossing_records provide used_sign labels.",
    )
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    sign_labels = load_crossing_sign_labels(args.sign_labels_from_sanity)
    piece_orientations = load_piece_orientations(args.sign_labels_from_sanity)
    print(
        render(
            data,
            args.out,
            layout_mode=args.layout_mode,
            vertical_mode=args.vertical_mode,
            draw_style=args.draw_style,
            stroke_scale=args.stroke_scale,
            vertical_scale=args.vertical_scale,
            collision_report_path=args.collision_report,
            sign_labels=sign_labels,
            piece_orientations=piece_orientations,
        ).resolve()
    )


if __name__ == "__main__":
    main()
