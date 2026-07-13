"""Compile crossing-free special-dotted Morse components into projector IR.

This module is deliberately category independent.  It reconstructs the
planar ribbon data carried by fundamental Morse forms, certifies a simple
special-component disk model, and records the aggregate vacuum projector
which must eventually replace that special component.  It does not evaluate
the projector and does not insert any Crane--Yetter normalization.
"""

from __future__ import annotations

from collections import defaultdict, deque
import hashlib
import json
from typing import Any, Iterable


DISK_CERTIFICATE_SCHEMA = "twisted-yetter.special-disk-certificate.v1"
PROJECTED_MORPHISM_SCHEMA = "twisted-yetter.projected-morphism-ir.v1"


def stable_json_hash(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def piece_of(strand: str) -> str:
    return strand.rsplit(".", 1)[0]


def replay_forms(forms: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    """Replay forms and return both pre- and post-event active orders."""

    order: list[str] = []
    trace: list[dict[str, Any]] = []
    for index, raw_form in enumerate(forms):
        form = dict(raw_form)
        before = list(order)
        kind = form["kind"]
        if kind == "cup":
            pair = [f"{form['piece']}.left", f"{form['piece']}.right"]
            if any(strand in order for strand in pair):
                raise ValueError(f"form {index}: cup duplicates an active strand")
            if form.get("at") == "far-left":
                gap = 0
            elif form.get("at") == "far-right":
                gap = len(order)
            elif "between" in form:
                left, right = form["between"]
                if left not in order or right not in order:
                    raise ValueError(f"form {index}: cup boundary is not active")
                if order.index(right) != order.index(left) + 1:
                    raise ValueError(f"form {index}: cup boundary is not adjacent")
                gap = order.index(left) + 1
            elif "after" in form:
                if form["after"] not in order:
                    raise ValueError(f"form {index}: cup predecessor is not active")
                gap = order.index(form["after"]) + 1
            else:
                raise ValueError(f"form {index}: unsupported cup placement")
            order[gap:gap] = pair
        elif kind == "cap":
            left, right = form["strands"]
            if left not in order or right not in order:
                raise ValueError(f"form {index}: cap strand is not active")
            if abs(order.index(left) - order.index(right)) != 1:
                raise ValueError(f"form {index}: cap strands are not adjacent")
            order = [strand for strand in order if strand not in {left, right}]
        elif kind == "cross":
            over, under = form["over"], form["under"]
            if over not in order or under not in order:
                raise ValueError(f"form {index}: crossing strand is not active")
            io, iu = order.index(over), order.index(under)
            if abs(io - iu) != 1:
                raise ValueError(f"form {index}: crossing strands are not adjacent")
            order[io], order[iu] = order[iu], order[io]
        elif kind == "kink":
            if form["strand"] not in order:
                raise ValueError(f"form {index}: kink strand is not active")
        elif kind == "vacuum-projector":
            strands = list(form.get("strands", ()))
            if len(set(strands)) != len(strands):
                raise ValueError(f"form {index}: projector repeats a strand")
            if any(strand not in order for strand in strands):
                raise ValueError(f"form {index}: projector strand is not active")
            if strands:
                start = order.index(strands[0])
                if order[start : start + len(strands)] != strands:
                    raise ValueError(
                        f"form {index}: projector strands are not a contiguous ordered interval"
                    )
        else:
            raise ValueError(f"form {index}: unsupported Morse form {kind!r}")
        trace.append(
            {
                "form_index": index,
                "form": form,
                "before_order": before,
                "after_order": list(order),
            }
        )
    if order:
        raise ValueError(f"Morse forms do not close: {order!r}")
    return trace


def _component_data(
    forms: tuple[dict[str, Any], ...], component_by_piece: dict[str, str]
) -> tuple[dict[str, str], dict[str, list[str]], dict[str, int]]:
    graph: dict[str, list[str]] = defaultdict(list)
    pieces: set[str] = set()
    for form in forms:
        if form["kind"] == "cup":
            piece = form["piece"]
            pieces.add(piece)
            left, right = f"{piece}.left", f"{piece}.right"
            graph[left].append(right)
            graph[right].append(left)
        elif form["kind"] == "cap":
            left, right = form["strands"]
            pieces.update((piece_of(left), piece_of(right)))
            graph[left].append(right)
            graph[right].append(left)

    missing = pieces - set(component_by_piece)
    extra = set(component_by_piece) - pieces
    if missing or extra:
        raise ValueError(
            f"component_by_piece mismatch: missing={sorted(missing)!r}, extra={sorted(extra)!r}"
        )

    orientation: dict[str, int] = {}
    components: dict[str, list[str]] = defaultdict(list)
    strand_component: dict[str, str] = {}
    for strand in sorted(graph):
        component = component_by_piece[piece_of(strand)]
        strand_component[strand] = component
        components[component].append(strand)
        if strand in orientation:
            continue
        orientation[strand] = 1
        queue = deque([strand])
        while queue:
            current = queue.popleft()
            for neighbor in graph[current]:
                if component_by_piece[piece_of(neighbor)] != component:
                    raise ValueError(
                        f"cap/cup connects different declared components: {current}, {neighbor}"
                    )
                expected = -orientation[current]
                if neighbor in orientation and orientation[neighbor] != expected:
                    raise ValueError(f"orientation inconsistency at {current}, {neighbor}")
                if neighbor not in orientation:
                    orientation[neighbor] = expected
                    queue.append(neighbor)

    for component, strands in components.items():
        if any(len(graph[strand]) != 2 for strand in strands):
            raise ValueError(f"component {component!r} is not a closed strand cycle")
        seen = set()
        queue = deque([strands[0]])
        while queue:
            current = queue.popleft()
            if current in seen:
                continue
            seen.add(current)
            queue.extend(graph[current])
        if seen != set(strands):
            raise ValueError(f"declared component {component!r} has multiple cycles")

    return strand_component, dict(components), orientation


def _crossing_records(
    trace: list[dict[str, Any]],
    orientation: dict[str, int],
    strand_component: dict[str, str],
) -> list[dict[str, Any]]:
    records = []
    for entry in trace:
        form = entry["form"]
        if form["kind"] != "cross":
            continue
        over, under = form["over"], form["under"]
        before, after = entry["before_order"], entry["after_order"]
        dx_over = after.index(over) - before.index(over)
        dx_under = after.index(under) - before.index(under)
        determinant = orientation[over] * orientation[under] * (
            dx_over - dx_under
        )
        if determinant == 0:
            raise ValueError(f"degenerate crossing at form {entry['form_index']}")
        records.append(
            {
                "crossing_id": f"x{len(records) + 1:03d}",
                "form_index": entry["form_index"],
                "over": over,
                "under": under,
                "over_component": strand_component[over],
                "under_component": strand_component[under],
                "sign": 1 if determinant > 0 else -1,
                "before_order": before,
                "after_order": after,
            }
        )
    return records


def _successors(
    forms: tuple[dict[str, Any], ...], orientation: dict[str, int]
) -> dict[str, str]:
    successor: dict[str, str] = {}
    for form in forms:
        if form["kind"] == "cup":
            piece = form["piece"]
            left, right = f"{piece}.left", f"{piece}.right"
            incoming = left if orientation[left] < 0 else right
            outgoing = right if orientation[left] < 0 else left
            successor[incoming] = outgoing
        elif form["kind"] == "cap":
            left, right = form["strands"]
            incoming = left if orientation[left] > 0 else right
            outgoing = right if orientation[left] > 0 else left
            successor[incoming] = outgoing
    return successor


def _component_cycles(
    components: dict[str, list[str]], successor: dict[str, str]
) -> dict[str, list[str]]:
    cycles = {}
    for component, strands in sorted(components.items()):
        start = sorted(strands)[0]
        cycle = []
        current = start
        while current not in cycle:
            cycle.append(current)
            if current not in successor:
                raise ValueError(f"missing oriented successor for {current!r}")
            current = successor[current]
        if current != start or set(cycle) != set(strands):
            raise ValueError(f"oriented traversal failed for {component!r}: {cycle!r}")
        cycles[component] = cycle
    return cycles


def _linking_row(
    special: str, records: list[dict[str, Any]], ordinary_order: list[str]
) -> list[int]:
    signed = defaultdict(int)
    for crossing in records:
        pair = {crossing["over_component"], crossing["under_component"]}
        if special not in pair or len(pair) != 2:
            continue
        ordinary = next(iter(pair - {special}))
        signed[ordinary] += crossing["sign"]
    odd = {component: value for component, value in signed.items() if value % 2}
    if odd:
        raise ValueError(f"odd signed crossing sum in special linking row: {odd!r}")
    return [signed[component] // 2 for component in ordinary_order]


def _compile_one_disk(
    *,
    special: str,
    forms: tuple[dict[str, Any], ...],
    records: list[dict[str, Any]],
    components: dict[str, list[str]],
    orientation: dict[str, int],
    cycles: dict[str, list[str]],
    strand_component: dict[str, str],
    component_order: list[str],
) -> dict[str, Any]:
    special_pieces = sorted({piece_of(strand) for strand in components[special]})
    if len(special_pieces) != 1:
        raise ValueError(
            f"special component {special!r} must use exactly one cup/cap piece in v1"
        )
    special_piece = special_pieces[0]
    boundary = [f"{special_piece}.left", f"{special_piece}.right"]
    self_crossings = [
        record
        for record in records
        if record["over_component"] == special
        and record["under_component"] == special
    ]
    if self_crossings:
        raise ValueError(
            f"special component {special!r} has {len(self_crossings)} self-crossings"
        )

    boundary_crossings = []
    by_strand: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        pair = {record["over_component"], record["under_component"]}
        if special not in pair or len(pair) != 2:
            continue
        ordinary_is_over = record["over_component"] != special
        ordinary = record["over"] if ordinary_is_over else record["under"]
        special_strand = record["under"] if ordinary_is_over else record["over"]

        def inside(order: list[str]) -> bool:
            if any(strand not in order for strand in boundary):
                raise ValueError(
                    f"special boundary is inactive at crossing {record['crossing_id']}"
                )
            lo, hi = sorted(order.index(strand) for strand in boundary)
            return lo < order.index(ordinary) < hi

        item = {
            "crossing_id": record["crossing_id"],
            "form_index": record["form_index"],
            "ordinary_component": (
                record["over_component"]
                if ordinary_is_over
                else record["under_component"]
            ),
            "ordinary_strand": ordinary,
            "ordinary_orientation_dy": orientation[ordinary],
            "special_boundary_strand": special_strand,
            "ordinary_z_at_boundary": 1 if ordinary_is_over else -1,
            "inside_before": inside(record["before_order"]),
            "inside_after": inside(record["after_order"]),
        }
        boundary_crossings.append(item)
        by_strand[ordinary].append(item)

    invalid = [
        item
        for item in boundary_crossings
        if item["inside_before"] == item["inside_after"]
    ]
    if invalid:
        raise ValueError(
            "special-boundary crossing does not toggle planar disk interior: "
            + ", ".join(item["crossing_id"] for item in invalid)
        )

    intervals = []
    cuts = []
    for component in component_order:
        if component == special:
            continue
        sequence = []
        for strand in cycles[component]:
            ordered = sorted(
                by_strand.get(strand, ()),
                key=lambda item: item["form_index"],
                reverse=orientation[strand] < 0,
            )
            for crossing in ordered:
                item = dict(crossing)
                if orientation[strand] > 0:
                    before = crossing["inside_before"]
                    after = crossing["inside_after"]
                else:
                    before = crossing["inside_after"]
                    after = crossing["inside_before"]
                item["transition"] = "enter" if not before and after else "exit"
                sequence.append(item)
        if not sequence:
            continue
        enter_index = next(
            (index for index, item in enumerate(sequence) if item["transition"] == "enter"),
            None,
        )
        if enter_index is None or len(sequence) % 2:
            raise ValueError(f"malformed boundary sequence for {component!r}")
        sequence = sequence[enter_index:] + sequence[:enter_index]
        for index in range(0, len(sequence), 2):
            entry, exit_ = sequence[index : index + 2]
            if entry["transition"] != "enter" or exit_["transition"] != "exit":
                raise ValueError(
                    f"nonalternating disk sequence at {entry['crossing_id']}, {exit_['crossing_id']}"
                )
            forced = entry["ordinary_z_at_boundary"] != exit_["ordinary_z_at_boundary"]
            signed_intersection = (
                (exit_["ordinary_z_at_boundary"] - entry["ordinary_z_at_boundary"]) // 2
                if forced
                else 0
            )
            interval = {
                "component": component,
                "entry_crossing": entry["crossing_id"],
                "exit_crossing": exit_["crossing_id"],
                "entry_form_index": entry["form_index"],
                "exit_form_index": exit_["form_index"],
                "entry_strand": entry["ordinary_strand"],
                "exit_strand": exit_["ordinary_strand"],
                "entry_z": entry["ordinary_z_at_boundary"],
                "exit_z": exit_["ordinary_z_at_boundary"],
                "forced_disk_intersection_parity": int(forced),
                "signed_intersection": signed_intersection,
            }
            intervals.append(interval)
            if forced:
                cuts.append(
                    {
                        "cut_id": f"{special}:cut{len(cuts) + 1:03d}",
                        **interval,
                        "factor_variance": (
                            "label" if signed_intersection > 0 else "dual"
                        ),
                    }
                )

    ordinary_order = [name for name in component_order if name != special]
    d2 = _linking_row(special, records, ordinary_order)
    signed_by_component = {
        component: sum(
            interval["signed_intersection"]
            for interval in intervals
            if interval["component"] == component
        )
        for component in ordinary_order
    }
    disk_vector = [signed_by_component[component] for component in ordinary_order]
    if disk_vector == d2:
        disk_to_linking_sign = 1
    elif disk_vector == [-value for value in d2]:
        disk_to_linking_sign = -1
    else:
        raise ValueError(
            f"disk intersection vector {disk_vector!r} is not +/- linking row {d2!r}"
        )

    return {
        "schema": DISK_CERTIFICATE_SCHEMA,
        "status": "PASS_SPECIAL_DISK_TOPOLOGY_CONTROLS",
        "special_component": special,
        "special_piece": special_piece,
        "disk_model": {
            "kind": "active-lane-interval",
            "boundary_strands": boundary,
            "description": (
                "At each regular Morse level, the projected disk interior is the "
                "open active-order interval between the two special strands."
            ),
        },
        "red_projection_self_crossings": len(self_crossings),
        "boundary_crossing_count": len(boundary_crossings),
        "boundary_crossings": boundary_crossings,
        "inside_arc_interval_count": len(intervals),
        "inside_arc_intervals": intervals,
        "forced_cut_count": len(cuts),
        "forced_cuts": cuts,
        "puncture_order_convention": "component-order-then-oriented-traversal-v1",
        "ordinary_component_order": ordinary_order,
        "d2_linking_row": d2,
        "signed_disk_intersections": disk_vector,
        "disk_to_linking_orientation_sign": disk_to_linking_sign,
    }


def erase_components(
    forms: Iterable[dict[str, Any]],
    strand_component: dict[str, str],
    erased_components: Iterable[str],
) -> list[dict[str, Any]]:
    """Erase selected closed components while preserving surviving order."""

    erased = frozenset(erased_components)
    full_order: list[str] = []
    kept_order: list[str] = []
    output: list[dict[str, Any]] = []

    for source_form_index, raw_form in enumerate(forms):
        form = dict(raw_form)
        kind = form["kind"]
        if kind == "cup":
            if form.get("at") == "far-left":
                full_gap = 0
            elif form.get("at") == "far-right":
                full_gap = len(full_order)
            elif "between" in form:
                full_gap = full_order.index(form["between"][0]) + 1
            elif "after" in form:
                full_gap = full_order.index(form["after"]) + 1
            else:
                raise ValueError(f"unsupported cup placement: {form!r}")
            pair = [f"{form['piece']}.left", f"{form['piece']}.right"]
            if strand_component[pair[0]] not in erased:
                kept_gap = sum(
                    strand in kept_order for strand in full_order[:full_gap]
                )
                new_form = {"kind": "cup", "piece": form["piece"]}
                if kept_gap == 0:
                    new_form["at"] = "far-left"
                elif kept_gap == len(kept_order):
                    new_form["at"] = "far-right"
                else:
                    new_form["between"] = [
                        kept_order[kept_gap - 1],
                        kept_order[kept_gap],
                    ]
                new_form["source_form_index"] = source_form_index
                output.append(new_form)
                kept_order[kept_gap:kept_gap] = pair
            full_order[full_gap:full_gap] = pair
        elif kind == "cross":
            over, under = form["over"], form["under"]
            io, iu = full_order.index(over), full_order.index(under)
            if over in kept_order and under in kept_order:
                ko, ku = kept_order.index(over), kept_order.index(under)
                if abs(ko - ku) != 1:
                    raise ValueError("component erasure made a crossing nonlocal")
                form["source_form_index"] = source_form_index
                output.append(form)
                kept_order[ko], kept_order[ku] = kept_order[ku], kept_order[ko]
            full_order[io], full_order[iu] = full_order[iu], full_order[io]
        elif kind == "cap":
            left, right = form["strands"]
            if left in kept_order or right in kept_order:
                if left not in kept_order or right not in kept_order:
                    raise ValueError("component erasure split a cap across components")
                if abs(kept_order.index(left) - kept_order.index(right)) != 1:
                    raise ValueError("component erasure made a cap nonlocal")
                form["source_form_index"] = source_form_index
                output.append(form)
                kept_order = [
                    strand for strand in kept_order if strand not in {left, right}
                ]
            full_order = [
                strand for strand in full_order if strand not in {left, right}
            ]
        elif kind == "kink":
            if strand_component[form["strand"]] not in erased:
                form["source_form_index"] = source_form_index
                output.append(form)
        elif kind == "vacuum-projector":
            retained = [
                strand
                for strand in form.get("strands", ())
                if strand_component[strand] not in erased
            ]
            if retained:
                new_form = dict(form)
                new_form["strands"] = retained
                new_form["source_form_index"] = source_form_index
                output.append(new_form)
        else:
            raise ValueError(f"unsupported form during component erasure: {form!r}")
    if full_order or kept_order:
        raise ValueError("component erasure replay did not close")
    replay_forms(output)
    return output


def insert_horizontal_projector(
    forms: Iterable[dict[str, Any]],
    *,
    before_form_index: int,
    strands: Iterable[str],
    projector_id: str,
    identity_projector: bool = False,
) -> dict[str, Any]:
    """Insert an explicit gather/project/inverse-gather corridor.

    This function is intentionally limited to strands which are already
    simultaneous at one Morse slice.  Selected strands are stably gathered
    into one contiguous interval by adjacent over-crossings.  Replaying the
    swaps in reverse while keeping the same physical overstrand gives the
    inverse braid and a Reidemeister-II identity when the projector is absent.
    """

    forms = [dict(form) for form in forms]
    if not (0 <= before_form_index <= len(forms)):
        raise ValueError("horizontal projector insertion index is out of range")
    trace = replay_forms(forms)
    active = (
        trace[before_form_index]["before_order"]
        if before_form_index < len(trace)
        else []
    )
    requested = list(strands)
    if not requested:
        raise ValueError("horizontal corridor needs at least one projector strand")
    if len(set(requested)) != len(requested):
        raise ValueError("horizontal corridor cannot represent two cuts on one strand")
    if any(strand not in active for strand in requested):
        raise ValueError("horizontal corridor strand is not active at the gate slice")

    selected = [strand for strand in active if strand in set(requested)]
    current = list(active)
    anchor = min(current.index(strand) for strand in selected)
    gather = []
    for offset, strand in enumerate(selected):
        target = anchor + offset
        while current.index(strand) > target:
            index = current.index(strand)
            spectator = current[index - 1]
            crossing = {
                "kind": "cross",
                "over": strand,
                "under": spectator,
                "corridor_role": "gather",
                "corridor_step": len(gather),
                "projector_id": projector_id,
            }
            gather.append(crossing)
            current[index - 1], current[index] = current[index], current[index - 1]
    if current[anchor : anchor + len(selected)] != selected:
        raise AssertionError("stable projector gather failed")

    inverse = []
    for crossing in reversed(gather):
        over, under = crossing["over"], crossing["under"]
        io, iu = current.index(over), current.index(under)
        if abs(io - iu) != 1:
            raise AssertionError("inverse gather strands are not adjacent")
        inverse_crossing = {
            "kind": "cross",
            "over": over,
            "under": under,
            "corridor_role": "inverse-gather",
            "inverse_of_step": crossing["corridor_step"],
            "projector_id": projector_id,
        }
        inverse.append(inverse_crossing)
        current[io], current[iu] = current[iu], current[io]
    if current != active:
        raise AssertionError("inverse gather did not restore active order")

    projector = {
        "kind": "vacuum-projector",
        "projector_id": projector_id,
        "strands": selected,
        "normalization": "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR",
        "corridor_role": "projector",
    }
    inserted = [*gather]
    if not identity_projector:
        inserted.append(projector)
    inserted.extend(inverse)
    compiled = [*forms[:before_form_index], *inserted, *forms[before_form_index:]]
    replay_forms(compiled)
    return {
        "status": "PASS_HORIZONTAL_GATHER_PROJECTOR_INVERSE_GATHER",
        "projector_id": projector_id,
        "identity_projector": identity_projector,
        "before_form_index": before_form_index,
        "active_order_before": active,
        "requested_strands": requested,
        "projector_strands": selected,
        "gather": gather,
        "inverse_gather": inverse,
        "inserted_forms": inserted,
        "compiled_forms": compiled,
    }


def preflight_horizontal_disk_corridor(
    source_forms: Iterable[dict[str, Any]],
    projected_ir: dict[str, Any],
) -> dict[str, Any]:
    """Find a common horizontal representative for every disk puncture.

    The v1 preflight only accepts a cut whose entry and exit lie on the same
    monotone Morse strand.  This is a deliberate fail-closed boundary: cuts
    that pass a cup or cap require a graph-level, non-horizontal coupon and
    must not be silently flattened.
    """

    source_forms = tuple(dict(form) for form in source_forms)
    if projected_ir["special_component_count"] != 1:
        return {
            "status": "UNSUPPORTED_MULTIPLE_SPECIAL_COMPONENTS_FAIL_CLOSED",
            "reason": "numeric v1 accepts exactly one special component",
        }
    certificate = projected_ir["special_disk_certificates"][0]
    cuts = certificate["forced_cuts"]
    nonmonotone = [
        cut for cut in cuts if cut["entry_strand"] != cut["exit_strand"]
    ]
    duplicate_strands = sorted(
        strand
        for strand, count in _counts(cut["entry_strand"] for cut in cuts).items()
        if count > 1
    )
    if nonmonotone or duplicate_strands:
        return {
            "status": "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR",
            "reason": (
                "some disk arcs cross a cup/cap or require multiple punctures "
                "on one active Morse strand"
            ),
            "nonmonotone_cut_ids": [cut["cut_id"] for cut in nonmonotone],
            "duplicate_active_strands": duplicate_strands,
            "forced_cut_count": len(cuts),
        }

    candidate_sets = []
    for cut in cuts:
        lower = min(cut["entry_form_index"], cut["exit_form_index"])
        upper = max(cut["entry_form_index"], cut["exit_form_index"])
        candidate_sets.append(set(range(lower + 1, upper + 1)))
    common = set.intersection(*candidate_sets) if candidate_sets else set()
    trace = replay_forms(source_forms)
    valid = []
    for before_index in sorted(common):
        active = (
            trace[before_index]["before_order"]
            if before_index < len(trace)
            else []
        )
        if all(cut["entry_strand"] in active for cut in cuts):
            valid.append(before_index)
    if not valid:
        return {
            "status": "UNSUPPORTED_NONHORIZONTAL_PROJECTOR_CORRIDOR",
            "reason": "disk punctures have no common active Morse slice",
            "forced_cut_count": len(cuts),
            "candidate_slice_count": len(common),
        }

    source_index = valid[0]
    ordinary_forms = projected_ir["ordinary_forms"]
    ordinary_index = sum(
        int(form.get("source_form_index", -1) < source_index)
        for form in ordinary_forms
    )
    source_active = trace[source_index]["before_order"]
    cut_by_strand = {cut["entry_strand"]: cut for cut in cuts}
    strands = [strand for strand in source_active if strand in cut_by_strand]
    return {
        "status": "PASS_COMMON_HORIZONTAL_PROJECTOR_SLICE",
        "source_before_form_index": source_index,
        "ordinary_before_form_index": ordinary_index,
        "projector_strands": strands,
        "cut_order_at_slice": [cut_by_strand[strand]["cut_id"] for strand in strands],
    }


def linearize_horizontal_disk_projector(
    source_forms: Iterable[dict[str, Any]],
    projected_ir: dict[str, Any],
    *,
    identity_projector: bool = False,
) -> dict[str, Any]:
    """Linearize one disk projector when preflight proves a common slice."""

    preflight = preflight_horizontal_disk_corridor(source_forms, projected_ir)
    if preflight["status"] != "PASS_COMMON_HORIZONTAL_PROJECTOR_SLICE":
        return {
            "status": preflight["status"],
            "preflight": preflight,
            "compiled_forms": None,
        }
    projector = projected_ir["vacuum_projectors"][0]
    corridor = insert_horizontal_projector(
        projected_ir["ordinary_forms"],
        before_form_index=preflight["ordinary_before_form_index"],
        strands=preflight["projector_strands"],
        projector_id=projector["projector_id"],
        identity_projector=identity_projector,
    )
    return {
        "status": "PASS_HORIZONTAL_DISK_PROJECTOR_LINEARIZATION",
        "preflight": preflight,
        "corridor": corridor,
        "compiled_forms": corridor["compiled_forms"],
    }


def _counts(values: Iterable[str]) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for value in values:
        counts[value] += 1
    return dict(counts)


def compile_projected_morphism(
    forms: Iterable[dict[str, Any]],
    *,
    component_by_piece: dict[str, str],
    special_components: Iterable[str],
) -> dict[str, Any]:
    """Return topology-only projector IR for crossing-free special components."""

    forms = tuple(dict(form) for form in forms)
    specials = tuple(special_components)
    if not specials:
        raise ValueError("at least one special component is required")
    if len(set(specials)) != len(specials):
        raise ValueError("special component names must be unique")
    trace = replay_forms(forms)
    strand_component, components, orientation = _component_data(
        forms, component_by_piece
    )
    missing = set(specials) - set(components)
    if missing:
        raise ValueError(f"unknown special components: {sorted(missing)!r}")
    component_order = list(dict.fromkeys(component_by_piece.values()))
    records = _crossing_records(trace, orientation, strand_component)
    cycles = _component_cycles(
        components, _successors(forms, orientation)
    )
    certificates = [
        _compile_one_disk(
            special=special,
            forms=forms,
            records=records,
            components=components,
            orientation=orientation,
            cycles=cycles,
            strand_component=strand_component,
            component_order=component_order,
        )
        for special in specials
    ]
    ordinary_forms = erase_components(forms, strand_component, specials)
    input_payload = {
        "forms": forms,
        "component_by_piece": component_by_piece,
        "special_components": specials,
    }
    input_hash = stable_json_hash(input_payload)
    for certificate in certificates:
        certificate["input_hash"] = input_hash
        certificate["certificate_hash"] = stable_json_hash(certificate)
    return {
        "schema": PROJECTED_MORPHISM_SCHEMA,
        "status": "PROJECTED_MORPHISM_IR_TOPOLOGY_ONLY_NOT_EVALUATED",
        "input_hash": input_hash,
        "special_component_count": len(specials),
        "numeric_support": (
            "SUPPORTED_ONE_SPECIAL_COMPONENT"
            if len(specials) == 1
            else "UNSUPPORTED_MULTIPLE_SPECIAL_COMPONENTS_FAIL_CLOSED"
        ),
        "component_order": component_order,
        "component_by_piece": dict(component_by_piece),
        "strand_orientation_dy": orientation,
        "crossing_count": len(records),
        "crossings": records,
        "special_disk_certificates": certificates,
        "ordinary_forms": ordinary_forms,
        "vacuum_projectors": [
            {
                "projector_id": f"vacuum:{certificate['special_component']}",
                "special_component": certificate["special_component"],
                "normalization": "IDEMPOTENT_UNIT_CHANNEL_NO_GLOBAL_DIMENSION_FACTOR",
                "aggregate_factor_word": [
                    {
                        "cut_id": cut["cut_id"],
                        "component": cut["component"],
                        "variance": cut["factor_variance"],
                    }
                    for cut in certificate["forced_cuts"]
                ],
                "corridor_status": "NOT_LINEARIZED",
            }
            for certificate in certificates
        ],
    }
