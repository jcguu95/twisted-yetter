"""Fail-closed schema for content-addressed framed-link presentations."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from typing import Any


SCHEMA = "twisted-yetter.kirby-presentation.v1"
SHA256_PREFIX = "sha256:"
ROLES = {"ordinary", "dotted", "specially_dotted"}
ORIENTATIONS = {"positive", "negative"}
SIGNS = {-1, 1}

TOP_LEVEL_KEYS = {
    "schema",
    "presentation_id",
    "source_snapshot_hash",
    "source_ref",
    "source_locator",
    "components",
    "events",
    "declared_slices",
    "content_hash",
}
COMPONENT_KEYS = {
    "component_id",
    "role",
    "orientation",
    "integer_framing",
    "blackboard_writhe",
    "framing_correction",
    "kirby_label",
}
SLICE_KEYS = {"index", "active_strands"}
STRAND_KEYS = {"strand_id", "component_id", "orientation"}
EVENT_KEYS = {
    "birth": {
        "event_id",
        "kind",
        "component_id",
        "positive_strand",
        "negative_strand",
        "insert_at",
    },
    "death": {
        "event_id",
        "kind",
        "component_id",
        "first_strand",
        "second_strand",
    },
    "crossing": {
        "event_id",
        "kind",
        "over_strand",
        "under_strand",
        "sign",
    },
    "coupon": {
        "event_id",
        "kind",
        "coupon_id",
        "label",
        "strands",
    },
    "framing_twist": {
        "event_id",
        "kind",
        "strand_id",
        "sign",
    },
    "planar_isotopy": {
        "event_id",
        "kind",
        "active_order",
    },
}


class PresentationValidationError(ValueError):
    """Raised when a formal presentation violates any admission boundary."""


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode()


def stable_content_hash(payload: dict[str, Any]) -> str:
    body = deepcopy(payload)
    body.pop("content_hash", None)
    return SHA256_PREFIX + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def add_content_hash(payload: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(payload)
    result.pop("content_hash", None)
    result["content_hash"] = stable_content_hash(result)
    return result


def serialize_presentation(payload: dict[str, Any]) -> bytes:
    validate_presentation(payload)
    return canonical_json_bytes(payload) + b"\n"


def deserialize_presentation(data: bytes) -> dict[str, Any]:
    payload = json.loads(data)
    if not isinstance(payload, dict):
        raise PresentationValidationError("presentation JSON must be an object")
    validate_presentation(payload)
    return payload


def _require_exact_keys(
    value: dict[str, Any],
    expected: set[str],
    where: str,
) -> None:
    observed = set(value)
    if observed != expected:
        missing = sorted(expected - observed)
        extra = sorted(observed - expected)
        raise PresentationValidationError(
            f"{where} keys mismatch; missing={missing}, extra={extra}"
        )


def _require_nonempty_string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise PresentationValidationError(f"{where} must be a nonempty string")
    return value


def _require_sha256(value: Any, where: str) -> str:
    text = _require_nonempty_string(value, where)
    if len(text) != 71 or not text.startswith(SHA256_PREFIX):
        raise PresentationValidationError(f"{where} is not a sha256 content hash")
    digest = text[len(SHA256_PREFIX) :]
    if any(character not in "0123456789abcdef" for character in digest):
        raise PresentationValidationError(
            f"{where} is not lowercase hexadecimal"
        )
    return text


def _require_unique(values: list[str], where: str) -> None:
    if len(values) != len(set(values)):
        raise PresentationValidationError(f"{where} contains duplicate IDs")


def _active_snapshot(
    index: int,
    order: list[str],
    active: dict[str, dict[str, str]],
) -> dict[str, Any]:
    return {
        "index": index,
        "active_strands": [deepcopy(active[strand_id]) for strand_id in order],
    }


def _positions(order: list[str], ids: list[str], where: str) -> list[int]:
    try:
        return [order.index(strand_id) for strand_id in ids]
    except ValueError as exc:
        raise PresentationValidationError(
            f"{where} references an inactive strand"
        ) from exc


def _require_adjacent(order: list[str], ids: list[str], where: str) -> None:
    positions = sorted(_positions(order, ids, where))
    if positions != list(range(positions[0], positions[0] + len(positions))):
        raise PresentationValidationError(
            f"{where} strands are not adjacent in the Morse slice"
        )


def _simulate(
    payload: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, int], set[str], set[str]]:
    components = {
        component["component_id"]: component
        for component in payload["components"]
    }
    active: dict[str, dict[str, str]] = {}
    order: list[str] = []
    slices = [_active_snapshot(0, order, active)]
    writhe = {component_id: 0 for component_id in components}
    born: set[str] = set()
    closed: set[str] = set()

    for index, event in enumerate(payload["events"], start=1):
        kind = event["kind"]
        _require_exact_keys(event, EVENT_KEYS[kind], f"event {index}")

        if kind == "birth":
            component_id = event["component_id"]
            if component_id not in components:
                raise PresentationValidationError(
                    f"birth references unknown component {component_id}"
                )
            strand_ids = [
                event["positive_strand"],
                event["negative_strand"],
            ]
            for strand_id in strand_ids:
                _require_nonempty_string(strand_id, "birth strand ID")
                if strand_id in active:
                    raise PresentationValidationError(
                        f"birth reuses active strand {strand_id}"
                    )
            _require_unique(strand_ids, "birth")
            insert_at = event["insert_at"]
            if (
                not isinstance(insert_at, int)
                or isinstance(insert_at, bool)
                or not 0 <= insert_at <= len(order)
            ):
                raise PresentationValidationError(
                    "birth insert_at is outside the active boundary"
                )
            active[strand_ids[0]] = {
                "strand_id": strand_ids[0],
                "component_id": component_id,
                "orientation": "positive",
            }
            active[strand_ids[1]] = {
                "strand_id": strand_ids[1],
                "component_id": component_id,
                "orientation": "negative",
            }
            order[insert_at:insert_at] = strand_ids
            born.add(component_id)

        elif kind == "death":
            component_id = event["component_id"]
            strand_ids = [event["first_strand"], event["second_strand"]]
            _require_unique(strand_ids, "death")
            _require_adjacent(order, strand_ids, "death")
            if any(
                active[strand_id]["component_id"] != component_id
                for strand_id in strand_ids
            ):
                raise PresentationValidationError(
                    "death crosses component lineage"
                )
            if {
                active[strand_id]["orientation"]
                for strand_id in strand_ids
            } != ORIENTATIONS:
                raise PresentationValidationError(
                    "death requires opposite strand orientations"
                )
            for strand_id in strand_ids:
                del active[strand_id]
                order.remove(strand_id)
            closed.add(component_id)

        elif kind == "crossing":
            strand_ids = [event["over_strand"], event["under_strand"]]
            _require_unique(strand_ids, "crossing")
            _require_adjacent(order, strand_ids, "crossing")
            sign = event["sign"]
            if (
                not isinstance(sign, int)
                or isinstance(sign, bool)
                or sign not in SIGNS
            ):
                raise PresentationValidationError(
                    "crossing sign must be exactly -1 or 1"
                )
            first_position, second_position = _positions(
                order, strand_ids, "crossing"
            )
            order[first_position], order[second_position] = (
                order[second_position],
                order[first_position],
            )
            owners = {active[strand_id]["component_id"] for strand_id in strand_ids}
            if len(owners) == 1:
                owner = next(iter(owners))
                writhe[owner] += sign

        elif kind == "coupon":
            _require_nonempty_string(event["coupon_id"], "coupon ID")
            _require_nonempty_string(event["label"], "coupon label")
            strands = event["strands"]
            if not isinstance(strands, list) or not strands:
                raise PresentationValidationError(
                    "coupon strands must be a nonempty list"
                )
            if not all(isinstance(item, str) and item for item in strands):
                raise PresentationValidationError(
                    "coupon strand IDs must be nonempty strings"
                )
            _require_unique(strands, "coupon")
            _require_adjacent(order, strands, "coupon")

        elif kind == "framing_twist":
            strand_id = event["strand_id"]
            if strand_id not in active:
                raise PresentationValidationError(
                    "framing twist references an inactive strand"
                )
            sign = event["sign"]
            if (
                not isinstance(sign, int)
                or isinstance(sign, bool)
                or sign not in SIGNS
            ):
                raise PresentationValidationError(
                    "framing twist sign must be exactly -1 or 1"
                )
            writhe[active[strand_id]["component_id"]] += sign

        elif kind == "planar_isotopy":
            requested = event["active_order"]
            if requested != order:
                raise PresentationValidationError(
                    "planar isotopy cannot reorder the active boundary"
                )

        else:
            raise PresentationValidationError(f"unsupported event kind {kind}")

        slices.append(_active_snapshot(index, order, active))

    if order or active:
        raise PresentationValidationError(
            "presentation has a nonempty terminal boundary"
        )
    return slices, writhe, born, closed


def materialize_declared_slices(
    payload_without_slices: dict[str, Any],
) -> list[dict[str, Any]]:
    probe = deepcopy(payload_without_slices)
    probe["declared_slices"] = []
    slices, _, _, _ = _simulate(probe)
    return slices


def validate_presentation(payload: dict[str, Any]) -> None:
    _require_exact_keys(payload, TOP_LEVEL_KEYS, "presentation")
    if payload["schema"] != SCHEMA:
        raise PresentationValidationError("unsupported presentation schema")
    _require_nonempty_string(payload["presentation_id"], "presentation ID")
    _require_sha256(payload["source_snapshot_hash"], "source snapshot")
    _require_nonempty_string(payload["source_ref"], "source reference")
    _require_nonempty_string(payload["source_locator"], "source locator")

    components = payload["components"]
    events = payload["events"]
    declared_slices = payload["declared_slices"]
    if not isinstance(components, list) or not components:
        raise PresentationValidationError("component registry must be nonempty")
    if not isinstance(events, list) or not events:
        raise PresentationValidationError("event list must be nonempty")
    if not isinstance(declared_slices, list):
        raise PresentationValidationError("declared slices must be a list")

    component_ids: list[str] = []
    for index, component in enumerate(components):
        if not isinstance(component, dict):
            raise PresentationValidationError(f"component {index} is not an object")
        _require_exact_keys(component, COMPONENT_KEYS, f"component {index}")
        component_id = _require_nonempty_string(
            component["component_id"], f"component {index} ID"
        )
        component_ids.append(component_id)
        if component["role"] not in ROLES:
            raise PresentationValidationError(
                f"component {component_id} has an unknown role"
            )
        if component["orientation"] not in ORIENTATIONS:
            raise PresentationValidationError(
                f"component {component_id} has an unknown orientation"
            )
        for field in (
            "integer_framing",
            "blackboard_writhe",
            "framing_correction",
        ):
            value = component[field]
            if not isinstance(value, int) or isinstance(value, bool):
                raise PresentationValidationError(
                    f"component {component_id} {field} must be an integer"
                )
        if (
            component["blackboard_writhe"]
            + component["framing_correction"]
            != component["integer_framing"]
        ):
            raise PresentationValidationError(
                f"component {component_id} violates the framing relation"
            )
        _require_nonempty_string(
            component["kirby_label"], f"component {component_id} label"
        )
    _require_unique(component_ids, "component registry")

    event_ids: list[str] = []
    for index, event in enumerate(events):
        if not isinstance(event, dict):
            raise PresentationValidationError(f"event {index} is not an object")
        kind = event.get("kind")
        if kind not in EVENT_KEYS:
            raise PresentationValidationError(
                f"event {index} has unsupported kind {kind!r}"
            )
        event_ids.append(
            _require_nonempty_string(event.get("event_id"), f"event {index} ID")
        )
    _require_unique(event_ids, "event list")

    slices, observed_writhe, born, closed = _simulate(payload)
    if born != set(component_ids):
        raise PresentationValidationError(
            "not every component has explicit birth lineage"
        )
    if closed != set(component_ids):
        raise PresentationValidationError(
            "not every component has explicit death lineage"
        )
    for component in components:
        component_id = component["component_id"]
        if observed_writhe[component_id] != component["blackboard_writhe"]:
            raise PresentationValidationError(
                f"component {component_id} blackboard writhe does not match events"
            )

    for index, declared in enumerate(declared_slices):
        if not isinstance(declared, dict):
            raise PresentationValidationError(f"slice {index} is not an object")
        _require_exact_keys(declared, SLICE_KEYS, f"slice {index}")
        if declared["index"] != index:
            raise PresentationValidationError("slice indices are not contiguous")
        strands = declared["active_strands"]
        if not isinstance(strands, list):
            raise PresentationValidationError(
                f"slice {index} active_strands is not a list"
            )
        for strand in strands:
            if not isinstance(strand, dict):
                raise PresentationValidationError(
                    f"slice {index} strand is not an object"
                )
            _require_exact_keys(strand, STRAND_KEYS, f"slice {index} strand")
    if declared_slices != slices:
        raise PresentationValidationError(
            "declared Morse slices do not match event execution"
        )

    observed_hash = _require_sha256(payload["content_hash"], "content hash")
    expected_hash = stable_content_hash(payload)
    if observed_hash != expected_hash:
        raise PresentationValidationError(
            "content hash does not match canonical presentation bytes"
        )


def build_reference_fixture() -> dict[str, Any]:
    body: dict[str, Any] = {
        "schema": SCHEMA,
        "presentation_id": "lean-kirby-r6-three-role-fixture",
        "source_snapshot_hash": (
            "sha256:"
            "bcaac3b51bcccde5acce97a5bf62c556398506ff20beabbfff339dd5039cb052"
        ),
        "source_ref": "ref:baerenz-barrett-dichromatic-2018",
        "source_locator": (
            "Definition 2.39 and Remarks 2.40, journal pages 675-676"
        ),
        "components": [
            {
                "component_id": "K0",
                "role": "ordinary",
                "orientation": "positive",
                "integer_framing": 1,
                "blackboard_writhe": 1,
                "framing_correction": 0,
                "kirby_label": "omega-C",
            },
            {
                "component_id": "D0",
                "role": "dotted",
                "orientation": "positive",
                "integer_framing": 0,
                "blackboard_writhe": 0,
                "framing_correction": 0,
                "kirby_label": "omega-D",
            },
            {
                "component_id": "S0",
                "role": "specially_dotted",
                "orientation": "negative",
                "integer_framing": -1,
                "blackboard_writhe": 0,
                "framing_correction": -1,
                "kirby_label": "special-alpha",
            },
        ],
        "events": [
            {
                "event_id": "e00",
                "kind": "birth",
                "component_id": "K0",
                "positive_strand": "K0+",
                "negative_strand": "K0-",
                "insert_at": 0,
            },
            {
                "event_id": "e01",
                "kind": "crossing",
                "over_strand": "K0+",
                "under_strand": "K0-",
                "sign": 1,
            },
            {
                "event_id": "e02",
                "kind": "coupon",
                "coupon_id": "coupon-K0",
                "label": "identity-K0",
                "strands": ["K0-", "K0+"],
            },
            {
                "event_id": "e03",
                "kind": "birth",
                "component_id": "D0",
                "positive_strand": "D0+",
                "negative_strand": "D0-",
                "insert_at": 2,
            },
            {
                "event_id": "e04",
                "kind": "crossing",
                "over_strand": "K0+",
                "under_strand": "D0+",
                "sign": -1,
            },
            {
                "event_id": "e05",
                "kind": "birth",
                "component_id": "S0",
                "positive_strand": "S0+",
                "negative_strand": "S0-",
                "insert_at": 4,
            },
            {
                "event_id": "e06",
                "kind": "coupon",
                "coupon_id": "coupon-S0",
                "label": "special-morphism",
                "strands": ["S0+", "S0-"],
            },
            {
                "event_id": "e07",
                "kind": "planar_isotopy",
                "active_order": ["K0-", "D0+", "K0+", "D0-", "S0+", "S0-"],
            },
            {
                "event_id": "e08",
                "kind": "death",
                "component_id": "S0",
                "first_strand": "S0+",
                "second_strand": "S0-",
            },
            {
                "event_id": "e09",
                "kind": "crossing",
                "over_strand": "D0+",
                "under_strand": "K0+",
                "sign": 1,
            },
            {
                "event_id": "e10",
                "kind": "death",
                "component_id": "D0",
                "first_strand": "D0+",
                "second_strand": "D0-",
            },
            {
                "event_id": "e11",
                "kind": "death",
                "component_id": "K0",
                "first_strand": "K0-",
                "second_strand": "K0+",
            },
        ],
    }
    body["declared_slices"] = materialize_declared_slices(body)
    return add_content_hash(body)
