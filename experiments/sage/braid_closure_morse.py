"""Mechanical braid-closure to Morse fundamental-form bridge.

This module exists for calibration and reuse.  It presents the quantum trace
of an n-strand braid as n nested cups, the braid crossings on the upward
branches, framing-correction kinks, and n middle-out caps.
"""

from __future__ import annotations

from experiments.scripts.morse_dsl import MorseBuilder
from experiments.sage.morse_fusion_evaluator import analyze_topology


def braid_component_data(n_strands, braid_word):
    positions = list(range(n_strands))
    crossing_records = []
    for generator in braid_word:
        index = abs(int(generator)) - 1
        crossing_records.append(
            (positions[index], positions[index + 1], 1 if generator > 0 else -1)
        )
        positions[index], positions[index + 1] = positions[index + 1], positions[index]
    successor = [None] * n_strands
    for top_position, original in enumerate(positions):
        successor[original] = top_position
    cycles = []
    seen = set()
    for start in range(n_strands):
        if start in seen:
            continue
        cycle = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = successor[current]
        cycles.append(tuple(sorted(cycle)))
    cycles = tuple(sorted(cycles, key=lambda cycle: cycle[0]))
    strand_to_component = {}
    for component, cycle in enumerate(cycles):
        for strand in cycle:
            strand_to_component[strand] = component
    writhe = [0] * len(cycles)
    for left, right, sign in crossing_records:
        if strand_to_component[left] == strand_to_component[right]:
            writhe[strand_to_component[left]] += sign
    return cycles, strand_to_component, tuple(writhe)


def braid_closure_morse_forms(n_strands, braid_word, framings):
    forms = []
    order = []
    original_strand_count = int(n_strands)
    for strand in range(original_strand_count):
        piece = f"S{strand}"
        if strand == 0:
            form = {"kind": "cup", "piece": piece, "at": "far-left"}
            gap = 0
        else:
            previous = f"S{strand - 1}"
            form = {
                "kind": "cup",
                "piece": piece,
                "between": [f"{previous}.left", f"{previous}.right"],
            }
            gap = order.index(f"{previous}.left") + 1
        forms.append(form)
        order[gap:gap] = [f"{piece}.left", f"{piece}.right"]

    cycles, strand_to_component, writhe = braid_component_data(
        original_strand_count, braid_word
    )
    if len(framings) != len(cycles):
        raise ValueError("framing count does not match braid-closure component count")
    for generator in braid_word:
        index = abs(int(generator)) - 1
        left, right = order[index], order[index + 1]
        over, under = (left, right) if generator > 0 else (right, left)
        forms.append({"kind": "cross", "over": over, "under": under})
        order[index], order[index + 1] = order[index + 1], order[index]

    for component, (framing, blackboard) in enumerate(
        zip(framings, writhe, strict=True)
    ):
        correction = int(framing) - int(blackboard)
        if correction:
            strand = next(
                active
                for active in order[:original_strand_count]
                if strand_to_component[int(active[1:].split(".", 1)[0])]
                == component
            )
            forms.append(
                {
                    "kind": "kink",
                    "strand": strand,
                    "sign": "+" if correction > 0 else "-",
                    "times": abs(correction),
                }
            )

    remaining = original_strand_count
    while order:
        left, right = order[remaining - 1], order[remaining]
        forms.append({"kind": "cap", "strands": [left, right]})
        order = [strand for strand in order if strand not in {left, right}]
        remaining -= 1

    topology = analyze_topology(forms)
    component_index_by_name = {}
    for name in topology.component_order:
        source_strand = int(name.split("+")[0][1:])
        component_index_by_name[name] = strand_to_component[source_strand]
    return tuple(forms), component_index_by_name


def trace_fundamental_forms(forms):
    """Replay fundamental forms through the checked drawing-state builder."""
    builder = MorseBuilder()
    for form in forms:
        kind = form["kind"]
        if kind == "cup":
            builder.cup(
                form["piece"],
                at=form.get("at"),
                between=tuple(form["between"]) if "between" in form else None,
                after=form.get("after"),
            )
        elif kind == "cross":
            builder.cross(
                over=form["over"], under=form["under"], sign=form.get("sign")
            )
        elif kind == "kink":
            builder.kink(
                form["strand"], sign=form["sign"], times=int(form.get("times", 1))
            )
        elif kind == "cap":
            builder.cap(strands=tuple(form["strands"]))
        else:
            raise ValueError(f"unsupported fundamental form: {kind!r}")
    return builder.snapshot()
