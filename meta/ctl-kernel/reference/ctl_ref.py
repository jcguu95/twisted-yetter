#!/usr/bin/env python3
"""CTL Kernel v0.1.1 reference starter.

This is intentionally small and strict.  It is not a production CLI; it is a
protocol-review artifact that makes canonical bytes, CIDs, governance profile
validation, transition validation, and golden vectors executable.
"""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import hashlib
import json
import re
from pathlib import Path
from typing import Any


CID_RE = re.compile(r"^ctlobj-sha256:[0-9a-f]{64}$")
ID_RE = re.compile(r"^[a-z0-9][a-z0-9._:/-]*$")
TS_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$")

OBJ_DOMAIN = b"ctl-object-v1\0"
SUPPORTED_PAYLOAD_PROFILES = {
    "agent/run-receipt/1",
    "ctl-governance/policy-set/1",
    "ctl-governance/role-binding/1",
    "ctl-data/opaque-json/1",
}
SUPPORTED_EVIDENCE_BASIS = {"agent/run-receipt/1"}
ALLOWED_ACTIONS = {
    "revision.record",
    "binding.set",
    "binding.remove",
    "policy.replace",
}
RESOURCE_SELECTOR_KEYS = {
    "logical_id",
    "logical_id_prefix",
    "payload_profile",
    "revision_kind",
    "role_binding",
}

MAX_AUTHORIZATION_MATCH_WORK = 1_048_576
MAX_PREDICATE_WORK = 65_536
MAX_CANONICAL_OBJECT_BYTES = 1_048_576
MAX_JSON_DEPTH = 64
MAX_ID_BYTES = 256


class InvalidHistory(Exception):
    pass


class UnsupportedProfile(Exception):
    pass


def die_unless(cond: bool, msg: str) -> None:
    if not cond:
        raise InvalidHistory(msg)


def canonical_bytes(value: Any) -> bytes:
    _check_json_value(value)
    text = json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return text.encode("utf-8")


def canonical_text(value: Any) -> str:
    return canonical_bytes(value).decode("utf-8")


def object_cid(value: Any) -> str:
    digest = hashlib.sha256(OBJ_DOMAIN + canonical_bytes(value)).hexdigest()
    return f"ctlobj-sha256:{digest}"


def sort_scalars(values: list[str]) -> list[str]:
    return sorted(values, key=lambda x: x.encode("utf-8"))


def sort_objects(values: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return sorted(values, key=canonical_bytes)


def unique_sorted_scalars(values: list[str], label: str) -> None:
    die_unless(all(isinstance(value, str) for value in values), f"{label} entries must be strings")
    die_unless(values == sort_scalars(values), f"{label} not sorted")
    die_unless(len(values) == len(set(values)), f"{label} not unique")


def unique_sorted_objects(values: list[dict[str, Any]], label: str) -> None:
    encoded = [canonical_bytes(v) for v in values]
    die_unless(encoded == sorted(encoded), f"{label} not sorted")
    die_unless(len(encoded) == len(set(encoded)), f"{label} not unique")


def is_id(value: Any) -> bool:
    return isinstance(value, str) and len(value.encode("utf-8")) <= MAX_ID_BYTES and ID_RE.fullmatch(value) is not None


def is_cid(value: Any) -> bool:
    return isinstance(value, str) and CID_RE.fullmatch(value) is not None


def _check_json_value(value: Any, depth: int = 0, enforce_depth: bool = False) -> None:
    if enforce_depth:
        die_unless(depth <= MAX_JSON_DEPTH, "JSON nesting too deep")
    if value is None or isinstance(value, bool):
        return
    if isinstance(value, int):
        die_unless(-(2**53 - 1) <= value <= 2**53 - 1, "integer out of range")
        return
    if isinstance(value, float):
        raise InvalidHistory("floats are not canonical JSON values")
    if isinstance(value, str):
        for ch in value:
            die_unless(not (0xD800 <= ord(ch) <= 0xDFFF), "lone surrogate")
        die_unless(len(value.encode("utf-8")) <= 262144, "string too large")
        return
    if isinstance(value, list):
        die_unless(len(value) <= 16384, "array too large")
        for item in value:
            _check_json_value(item, depth + 1, enforce_depth)
        return
    if isinstance(value, dict):
        die_unless(len(value) <= 8192, "object has too many keys")
        for key, item in value.items():
            die_unless(isinstance(key, str), "object key must be string")
            for ch in key:
                die_unless(not (0xD800 <= ord(ch) <= 0xDFFF), "lone surrogate in object key")
            die_unless(len(key.encode("utf-8")) <= 262144, "object key too large")
            _check_json_value(item, depth + 1, enforce_depth)
        return
    raise InvalidHistory(f"unsupported JSON value: {type(value).__name__}")


def check_canonical_object_size(value: Any) -> None:
    die_unless(len(canonical_bytes(value)) <= MAX_CANONICAL_OBJECT_BYTES, "canonical object too large")


def check_timestamp(value: Any) -> None:
    die_unless(isinstance(value, str) and TS_RE.fullmatch(value) is not None, "bad timestamp")
    try:
        parsed = dt.datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError as exc:
        raise InvalidHistory("bad timestamp") from exc
    die_unless(parsed.strftime("%Y-%m-%dT%H:%M:%SZ") == value, "bad timestamp")


def load_json_strict(path: Path) -> Any:
    def reject_float(_: str) -> Any:
        raise InvalidHistory("floats are not allowed")

    def pairs_hook(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for key, value in pairs:
            if key in out:
                raise InvalidHistory(f"duplicate JSON key: {key}")
            out[key] = value
        return out

    return json.loads(path.read_text(), object_pairs_hook=pairs_hook, parse_float=reject_float)


def check_keys(obj: dict[str, Any], required: set[str], optional: set[str] = frozenset()) -> None:
    die_unless(isinstance(obj, dict), "expected object")
    got = set(obj.keys())
    die_unless(required <= got, f"missing keys: {sorted(required - got)}")
    die_unless(got <= required | optional, f"unknown keys: {sorted(got - required - optional)}")


class Store:
    def __init__(self) -> None:
        self.objects: dict[str, dict[str, Any]] = {}

    def add(self, obj: dict[str, Any]) -> str:
        check_canonical_object_size(obj)
        cid = object_cid(obj)
        old = self.objects.get(cid)
        if old is not None and canonical_bytes(old) != canonical_bytes(obj):
            raise InvalidHistory("CID collision with different bytes")
        self.objects[cid] = copy.deepcopy(obj)
        return cid

    def resolve(self, cid: str) -> dict[str, Any]:
        die_unless(is_cid(cid), f"bad CID: {cid}")
        if cid not in self.objects:
            raise InvalidHistory(f"missing object: {cid}")
        obj = copy.deepcopy(self.objects[cid])
        die_unless(object_cid(obj) == cid, "CID mismatch")
        return obj


def validate_revision_envelope(store: Store, cid: str | None, rev: dict[str, Any]) -> None:
    _check_json_value(rev, enforce_depth=True)
    check_canonical_object_size(rev)
    if cid is not None:
        die_unless(object_cid(rev) == cid, "revision CID mismatch")
    check_keys(
        rev,
        {
            "profile",
            "kernel_profile",
            "project_id",
            "logical_id",
            "revision_kind",
            "parents",
            "payload_profile",
            "payload",
            "created_at",
            "created_by",
        },
    )
    die_unless(rev["profile"] == "ctl/revision/1", "bad revision profile")
    die_unless(rev["kernel_profile"] == "ctl-kernel/1", "bad kernel profile")
    die_unless(is_id(rev["project_id"]), "bad project_id")
    die_unless(is_id(rev["logical_id"]), "bad logical_id")
    die_unless(not rev["logical_id"].startswith("sys:") or rev["logical_id"] == "sys:policy", "reserved sys logical_id")
    if rev["logical_id"] == "sys:policy":
        die_unless(rev["revision_kind"] == "policy-set", "sys:policy kind")
        die_unless(rev["payload_profile"] == "ctl-governance/policy-set/1", "sys:policy profile")
    die_unless(is_id(rev["revision_kind"]), "bad revision_kind")
    die_unless(isinstance(rev["parents"], list), "parents must be array")
    die_unless(all(is_cid(x) for x in rev["parents"]), "bad parent CID")
    unique_sorted_scalars(rev["parents"], "parents")
    die_unless(is_id(rev["payload_profile"]), "bad payload_profile")
    die_unless(isinstance(rev["payload"], dict), "payload must be object")
    check_timestamp(rev["created_at"])
    check_keys(rev["created_by"], {"actor_id"})
    die_unless(is_id(rev["created_by"]["actor_id"]), "bad created_by actor")

    is_role_ns = rev["logical_id"].startswith("role-binding:")
    is_role_profile = rev["payload_profile"] == "ctl-governance/role-binding/1"
    is_role_kind = rev["revision_kind"] == "role-binding"
    die_unless(is_role_ns == is_role_profile, "RoleBinding namespace/profile invariant")
    die_unless(is_role_kind == is_role_profile, "RoleBinding kind/profile invariant")


def validate_revision_payload(rev: dict[str, Any]) -> None:
    profile = rev["payload_profile"]
    if profile == "ctl-governance/policy-set/1":
        validate_policy_revision(rev)
    elif profile == "ctl-governance/role-binding/1":
        validate_role_binding_revision(rev)
    elif profile == "ctl-data/opaque-json/1":
        pass
    elif profile == "agent/run-receipt/1":
        validate_run_receipt_revision(rev)
    else:
        raise UnsupportedProfile(profile)


def validate_revision(store: Store, cid: str | None, rev: dict[str, Any]) -> None:
    validate_revision_envelope(store, cid, rev)
    validate_revision_payload(rev)


def validate_policy_revision(rev: dict[str, Any]) -> None:
    die_unless(rev["logical_id"] == "sys:policy", "policy logical_id")
    die_unless(rev["revision_kind"] == "policy-set", "policy kind")
    validate_policy_payload(rev["payload"])


def validate_policy_payload(payload: dict[str, Any]) -> None:
    check_keys(payload, {"version", "default", "rules"})
    die_unless(type(payload["version"]) is int and payload["version"] == 1, "policy version")
    die_unless(payload["default"] == "deny", "policy default")
    die_unless(isinstance(payload["rules"], list), "rules must be array")
    die_unless(len(payload["rules"]) <= 1024, "too many policy rules")
    unique_sorted_objects(payload["rules"], "policy rules")
    for rule in payload["rules"]:
        check_keys(rule, {"effect", "subject", "actions", "resources", "required_evidence_basis"})
        die_unless(rule["effect"] == "allow", "only allow rules supported")
        check_keys(rule["subject"], {"role_id"})
        die_unless(is_id(rule["subject"]["role_id"]), "bad rule role")
        die_unless(isinstance(rule["actions"], list), "actions must be array")
        die_unless(len(rule["actions"]) <= 16, "too many actions")
        unique_sorted_scalars(rule["actions"], "rule actions")
        for action in rule["actions"]:
            die_unless(action in ALLOWED_ACTIONS, "unknown action in policy")
        die_unless(isinstance(rule["resources"], list), "resources must be array")
        die_unless(len(rule["resources"]) <= 256, "too many resources")
        unique_sorted_objects(rule["resources"], "resources")
        for selector in rule["resources"]:
            die_unless(isinstance(selector, dict), "selector must be object")
            die_unless(set(selector.keys()) <= RESOURCE_SELECTOR_KEYS, "unknown selector")
            die_unless(len(selector) == 1, "selector must have exactly one field")
            key, value = next(iter(selector.items()))
            if key == "role_binding":
                check_keys(value, {"role_id"}, {"actor_id"})
                die_unless(is_id(value["role_id"]), "bad role_binding selector role_id")
                if "actor_id" in value:
                    die_unless(is_id(value["actor_id"]), "bad role_binding selector actor_id")
            else:
                die_unless(is_id(value), "selector value must be id")
        die_unless(isinstance(rule["required_evidence_basis"], list), "basis must be array")
        die_unless(len(rule["required_evidence_basis"]) <= 64, "too many basis ids")
        unique_sorted_scalars(rule["required_evidence_basis"], "basis")
        for basis in rule["required_evidence_basis"]:
            die_unless(is_id(basis), "bad basis id")


def unsupported_policy_basis(policy: dict[str, Any]) -> str | None:
    for rule in policy["payload"]["rules"]:
        for basis in rule["required_evidence_basis"]:
            if basis not in SUPPORTED_EVIDENCE_BASIS:
                return basis
    return None


def validate_role_binding_revision(rev: dict[str, Any]) -> None:
    die_unless(rev["logical_id"].startswith("role-binding:"), "role binding namespace")
    payload = rev["payload"]
    check_keys(payload, {"actor_id", "role_id", "scope"})
    die_unless(is_id(payload["actor_id"]), "bad role actor")
    die_unless(is_id(payload["role_id"]), "bad role id")
    check_keys(payload["scope"], {"project_id"})
    die_unless(is_id(payload["scope"]["project_id"]), "bad role scope")


def validate_run_receipt_revision(rev: dict[str, Any]) -> None:
    die_unless(rev["revision_kind"] == "run-receipt", "run receipt kind")
    payload = rev["payload"]
    check_keys(payload, {"status"}, {"command", "started_at", "finished_at"})
    die_unless(isinstance(payload["status"], str), "bad run receipt status")
    die_unless(payload["status"] in {"failed", "ok"}, "bad run receipt status")
    if "command" in payload:
        die_unless(isinstance(payload["command"], list), "run receipt command must be array")
        die_unless(all(isinstance(part, str) for part in payload["command"]), "bad run receipt command")
    if "started_at" in payload:
        check_timestamp(payload["started_at"])
    if "finished_at" in payload:
        check_timestamp(payload["finished_at"])


def is_role_binding_revision(rev: dict[str, Any]) -> bool:
    return rev.get("payload_profile") == "ctl-governance/role-binding/1"


def role_binding_identity(rev: dict[str, Any]) -> tuple[str, str, str]:
    payload = rev["payload"]
    return (payload["actor_id"], payload["role_id"], payload["scope"]["project_id"])


def extend_role_binding_identities(
    current: dict[str, tuple[str, str, str]],
    recorded: list[tuple[str, dict[str, Any]]],
) -> dict[str, tuple[str, str, str]]:
    out = dict(current)
    for _cid, rev in recorded:
        if not is_role_binding_revision(rev):
            continue
        logical_id = rev["logical_id"]
        identity = role_binding_identity(rev)
        old = out.get(logical_id)
        if old is None:
            out[logical_id] = identity
        else:
            die_unless(old == identity, "role binding logical identity mismatch")
    return out


def validate_batch_common(
    store: Store, batch: dict[str, Any]
) -> tuple[list[tuple[str, dict[str, Any]]], list[str], list[str]]:
    check_canonical_object_size(batch)
    check_keys(
        batch,
        {
            "profile",
            "kernel_profile",
            "project_id",
            "parent_root",
            "recorded_revisions",
            "binding_ops",
            "evidence",
            "principal_claim",
            "submitted_by",
            "admitted_at",
        },
    )
    die_unless(batch["profile"] == "ctl/admission-batch/1", "bad batch profile")
    die_unless(batch["kernel_profile"] == "ctl-kernel/1", "bad batch kernel")
    die_unless(is_id(batch["project_id"]), "bad batch project")
    die_unless(batch["parent_root"] is None or is_cid(batch["parent_root"]), "bad parent root")
    die_unless(isinstance(batch["recorded_revisions"], list), "recorded_revisions must be array")
    die_unless(isinstance(batch["binding_ops"], list), "binding_ops must be array")
    die_unless(batch["recorded_revisions"] or batch["binding_ops"], "empty batch")
    die_unless(len(batch["recorded_revisions"]) <= 4096, "too many recorded revisions")
    die_unless(all(is_cid(x) for x in batch["recorded_revisions"]), "bad recorded CID")
    unique_sorted_scalars(batch["recorded_revisions"], "recorded_revisions")

    check_keys(batch["principal_claim"], {"actor_id", "role_bindings"}, {"authentication_assurance"})
    die_unless(is_id(batch["principal_claim"]["actor_id"]), "bad principal actor")
    if "authentication_assurance" in batch["principal_claim"]:
        die_unless(is_id(batch["principal_claim"]["authentication_assurance"]), "bad authentication assurance")
    die_unless(isinstance(batch["principal_claim"]["role_bindings"], list), "principal roles array")
    die_unless(len(batch["principal_claim"]["role_bindings"]) <= 64, "too many principal role bindings")
    die_unless(all(is_cid(x) for x in batch["principal_claim"]["role_bindings"]), "bad principal role CID")
    unique_sorted_scalars(batch["principal_claim"]["role_bindings"], "principal role_bindings")
    check_keys(batch["submitted_by"], {"actor_id"})
    die_unless(is_id(batch["submitted_by"]["actor_id"]), "bad submitted_by")
    check_timestamp(batch["admitted_at"])

    die_unless(len(batch["binding_ops"]) <= 1024, "too many binding ops")
    binding_ids = set()
    binding_logical_ids: list[str] = []
    for op in batch["binding_ops"]:
        die_unless(isinstance(op, dict), "binding op must be object")
        die_unless("logical_id" in op, "missing binding logical_id")
        op_kind = op.get("op")
        die_unless(isinstance(op_kind, str), "bad op")
        die_unless(op_kind in {"set", "remove"}, "bad op")
        die_unless(is_id(op.get("logical_id")), "bad binding logical_id")
        die_unless(not op["logical_id"].startswith("sys:") or op["logical_id"] == "sys:policy", "reserved sys binding op")
        binding_ids.add(op["logical_id"])
        binding_logical_ids.append(op["logical_id"])
        check_expected(op.get("expected"))
        if op["op"] == "set":
            check_keys(op, {"op", "logical_id", "expected", "new_cid"})
            die_unless(is_cid(op["new_cid"]), "bad new_cid")
        else:
            check_keys(op, {"op", "logical_id", "expected"})
    die_unless(binding_logical_ids == sort_scalars(binding_logical_ids), "binding_ops not sorted")
    die_unless(len(set(binding_logical_ids)) == len(binding_logical_ids), "duplicate binding op logical_id")

    die_unless(isinstance(batch["evidence"], list), "evidence must be array")
    die_unless(len(batch["evidence"]) <= 4096, "too many evidence entries")
    unique_sorted_objects(batch["evidence"], "evidence")
    recorded_set = set(batch["recorded_revisions"])
    unsupported_evidence_basis: list[str] = []
    for entry in batch["evidence"]:
        check_keys(entry, {"target", "basis", "cid"})
        die_unless(is_id(entry["basis"]), "bad evidence basis")
        if entry["basis"] not in SUPPORTED_EVIDENCE_BASIS:
            unsupported_evidence_basis.append(entry["basis"])
        die_unless(is_cid(entry["cid"]), "bad evidence cid")
        target = entry["target"]
        check_keys(target, {"kind"}, {"cid", "logical_id"})
        if target["kind"] == "recorded_revision":
            check_keys(target, {"kind", "cid"})
            die_unless(target["cid"] in recorded_set, "evidence target not recorded in batch")
        elif target["kind"] == "binding_op":
            check_keys(target, {"kind", "logical_id"})
            die_unless(target["logical_id"] in binding_ids, "evidence target not binding op")
        else:
            raise InvalidHistory("bad evidence target kind")

    recorded: list[tuple[str, dict[str, Any]]] = []
    unsupported_profiles: list[str] = []
    for cid in batch["recorded_revisions"]:
        rev = store.resolve(cid)
        validate_revision_envelope(store, cid, rev)
        if rev["payload_profile"] in SUPPORTED_PAYLOAD_PROFILES:
            validate_revision_payload(rev)
        else:
            unsupported_profiles.append(rev["payload_profile"])
        die_unless(rev["project_id"] == batch["project_id"], "recorded project mismatch")
        die_unless(rev["kernel_profile"] == batch["kernel_profile"], "recorded kernel mismatch")
        recorded.append((cid, rev))

    recorded_map = dict(recorded)
    for _cid, rev in recorded:
        for parent in rev["parents"]:
            if parent in recorded_map:
                validate_parent_relation(rev, recorded_map[parent])
    assert_no_parent_cycle(recorded_map)
    extend_role_binding_identities({}, recorded)

    return recorded, unsupported_profiles, unsupported_evidence_basis


def check_expected(expected: Any) -> None:
    die_unless(isinstance(expected, dict), "expected must be object")
    if expected.get("state") == "absent":
        check_keys(expected, {"state"})
    elif expected.get("state") == "bound":
        check_keys(expected, {"state", "cid"})
        die_unless(is_cid(expected["cid"]), "bad expected cid")
    else:
        raise InvalidHistory("bad expected state")


def apply_binding_ops(bindings: dict[str, str], ops: list[dict[str, Any]]) -> dict[str, str]:
    out = dict(bindings)
    for op in sorted(ops, key=lambda x: x["logical_id"].encode("utf-8")):
        if op["op"] == "set":
            out[op["logical_id"]] = op["new_cid"]
        else:
            del out[op["logical_id"]]
    return out


def assert_no_parent_cycle(recorded: dict[str, dict[str, Any]]) -> None:
    color: dict[str, int] = {}
    for start in recorded:
        if color.get(start) == 2:
            continue
        stack: list[tuple[str, int]] = [(start, 0)]
        while stack:
            cid, index = stack[-1]
            if cid not in color:
                color[cid] = 1
            parents = [parent for parent in recorded[cid]["parents"] if parent in recorded]
            if index >= len(parents):
                color[cid] = 2
                stack.pop()
                continue
            parent = parents[index]
            stack[-1] = (cid, index + 1)
            parent_color = color.get(parent, 0)
            die_unless(parent_color != 1, "revision parent cycle")
            if parent_color == 0:
                stack.append((parent, 0))


def validate_parent_relation(child: dict[str, Any], parent: dict[str, Any]) -> None:
    die_unless(parent["project_id"] == child["project_id"], "parent project mismatch")
    die_unless(parent["kernel_profile"] == child["kernel_profile"], "parent kernel mismatch")
    die_unless(parent["logical_id"] == child["logical_id"], "parent logical mismatch")
    if child["payload_profile"] == "ctl-governance/role-binding/1":
        die_unless(parent["payload_profile"] == "ctl-governance/role-binding/1", "role parent profile mismatch")
        child_payload = child["payload"]
        parent_payload = parent["payload"]
        die_unless(child_payload["actor_id"] == parent_payload["actor_id"], "role parent actor mismatch")
        die_unless(child_payload["role_id"] == parent_payload["role_id"], "role parent role mismatch")
        die_unless(
            child_payload["scope"]["project_id"] == parent_payload["scope"]["project_id"],
            "role parent scope mismatch",
        )


def check_expected_against(bindings: dict[str, str], op: dict[str, Any]) -> None:
    expected = op["expected"]
    key = op["logical_id"]
    if expected["state"] == "absent":
        die_unless(key not in bindings, "expected absent mismatch")
    else:
        die_unless(bindings.get(key) == expected["cid"], "expected bound mismatch")
        if op["op"] == "set":
            die_unless(op["new_cid"] != expected["cid"], "set-to-same no-op")


def validate_root(root: dict[str, Any]) -> None:
    check_keys(root, {"profile", "kernel_profile", "project_id", "parent", "bindings", "transition"})
    die_unless(root["profile"] == "ctl/project-state-root/1", "bad root profile")
    die_unless(root["kernel_profile"] == "ctl-kernel/1", "bad root kernel")
    die_unless(is_id(root["project_id"]), "bad root project")
    die_unless(root["parent"] is None or is_cid(root["parent"]), "bad root parent")
    die_unless(is_cid(root["transition"]), "bad root transition")
    die_unless(isinstance(root["bindings"], dict), "bindings must be object")
    die_unless(len(root["bindings"]) <= 4096, "too many bindings")
    die_unless("sys:policy" in root["bindings"], "missing sys:policy")
    for key, value in root["bindings"].items():
        die_unless(is_id(key), "bad binding key")
        die_unless(not key.startswith("sys:") or key == "sys:policy", "reserved sys binding")
        die_unless(is_cid(value), "bad binding value")


def role_bindings_for_principal(store: Store, state: dict[str, Any], claim: dict[str, Any]) -> list[dict[str, str]]:
    roles: list[dict[str, str]] = []
    active = set(state["bindings"].values())
    for cid in claim["role_bindings"]:
        die_unless(cid in active, "principal role binding not active")
        rev = store.resolve(cid)
        validate_role_binding_revision(rev)
        payload = rev["payload"]
        die_unless(payload["actor_id"] == claim["actor_id"], "principal actor mismatch")
        die_unless(payload["scope"]["project_id"] == state["project_id"], "role scope mismatch")
        roles.append({"cid": cid, "role_id": payload["role_id"], "actor_id": payload["actor_id"]})
    return roles


def request_target(req: dict[str, Any]) -> dict[str, Any]:
    if req["action"] == "revision.record":
        return {"kind": "recorded_revision", "cid": req["new_cid"]}
    return {"kind": "binding_op", "logical_id": req["logical_id"]}


def attach_applicable_evidence(batch: dict[str, Any], req: dict[str, Any]) -> dict[str, Any]:
    target = request_target(req)
    applicable = []
    for entry in batch["evidence"]:
        if entry["target"] == target:
            applicable.append({"basis": entry["basis"], "cid": entry["cid"]})
    req = dict(req)
    req["applicable_evidence"] = sort_objects(applicable)
    dedup: list[dict[str, Any]] = []
    seen = set()
    for item in req["applicable_evidence"]:
        key = canonical_bytes(item)
        if key not in seen:
            dedup.append(item)
            seen.add(key)
    req["applicable_evidence"] = dedup
    return req


def make_requests(
    store: Store, state: dict[str, Any], batch: dict[str, Any], recorded: list[tuple[str, dict[str, Any]]]
) -> list[dict[str, Any]]:
    requests: list[dict[str, Any]] = []
    for cid, rev in recorded:
        requests.append(
            {
                "action": "revision.record",
                "logical_id": rev["logical_id"],
                "old_cid": None,
                "new_cid": cid,
                "payload_profile": rev["payload_profile"],
                "revision_kind": rev["revision_kind"],
                "resource_cid": cid,
                "resource_revision": rev,
            }
        )
    for op in batch["binding_ops"]:
        if op["op"] == "set":
            rev = store.resolve(op["new_cid"])
            requests.append(
                {
                    "action": "binding.set",
                    "logical_id": op["logical_id"],
                    "old_cid": state["bindings"].get(op["logical_id"]),
                    "new_cid": op["new_cid"],
                    "payload_profile": rev["payload_profile"],
                    "revision_kind": rev["revision_kind"],
                    "resource_cid": op["new_cid"],
                    "resource_revision": rev,
                }
            )
            if op["logical_id"] == "sys:policy" and state["bindings"].get("sys:policy") != op["new_cid"]:
                requests.append(
                    {
                        "action": "policy.replace",
                        "logical_id": "sys:policy",
                        "old_cid": state["bindings"].get("sys:policy"),
                        "new_cid": op["new_cid"],
                        "payload_profile": "ctl-governance/policy-set/1",
                        "revision_kind": "policy-set",
                        "resource_cid": op["new_cid"],
                        "resource_revision": rev,
                    }
                )
        else:
            old_cid = state["bindings"].get(op["logical_id"])
            die_unless(old_cid is not None, "remove missing binding")
            rev = store.resolve(old_cid)
            requests.append(
                {
                    "action": "binding.remove",
                    "logical_id": op["logical_id"],
                    "old_cid": old_cid,
                    "new_cid": None,
                    "payload_profile": rev["payload_profile"],
                    "revision_kind": rev["revision_kind"],
                    "resource_cid": old_cid,
                    "resource_revision": rev,
                }
            )
    return [attach_applicable_evidence(batch, req) for req in requests]


def selector_matches(store: Store, selector: dict[str, Any], req: dict[str, Any]) -> bool:
    key, value = next(iter(selector.items()))
    if key == "logical_id":
        return req["logical_id"] == value
    if key == "logical_id_prefix":
        return req["logical_id"].startswith(value)
    if key == "payload_profile":
        return req["payload_profile"] == value
    if key == "revision_kind":
        return req["revision_kind"] == value
    if key == "role_binding":
        rev = req.get("resource_revision")
        if not rev:
            return False
        if rev["payload_profile"] != "ctl-governance/role-binding/1":
            return False
        payload = rev["payload"]
        if payload["role_id"] != value["role_id"]:
            return False
        if "actor_id" in value and payload["actor_id"] != value["actor_id"]:
            return False
        return True
    raise InvalidHistory("unknown selector")


def evidence_passes(store: Store, evidence_cid: str) -> bool:
    evidence = store.resolve(evidence_cid)
    return (
        evidence.get("profile") == "ctl/revision/1"
        and evidence.get("revision_kind") == "run-receipt"
        and evidence.get("payload_profile") == "agent/run-receipt/1"
    )


def rule_subject_action_resource_matches(
    store: Store, rule: dict[str, Any], roles: list[dict[str, str]], req: dict[str, Any]
) -> bool:
    if not any(role["role_id"] == rule["subject"]["role_id"] for role in roles):
        return False
    if req["action"] not in rule["actions"]:
        return False
    return any(selector_matches(store, selector, req) for selector in rule["resources"])


def predicate_work(store: Store, policy: dict[str, Any], roles: list[dict[str, str]], requests: list[dict[str, Any]]) -> int:
    total = 0
    for req in requests:
        for rule in policy["payload"]["rules"]:
            if rule_subject_action_resource_matches(store, rule, roles, req):
                for basis in rule["required_evidence_basis"]:
                    total += sum(1 for item in req["applicable_evidence"] if item["basis"] == basis)
    return total


def authorization_match_work(policy: dict[str, Any], requests: list[dict[str, Any]]) -> int:
    total = 0
    for _req in requests:
        for rule in policy["payload"]["rules"]:
            total += 1 + len(rule["actions"]) + len(rule["resources"])
            die_unless(total <= MAX_AUTHORIZATION_MATCH_WORK, "authorization match work limit")
    return total


def liveness_match_work(policy: dict[str, Any], actor_count: int) -> int:
    per_probe = 0
    for rule in policy["payload"]["rules"]:
        per_probe += 1 + len(rule["actions"]) + len(rule["resources"])
        die_unless(per_probe <= MAX_AUTHORIZATION_MATCH_WORK, "liveness match work limit")
    total = actor_count * 3 * per_probe
    die_unless(total <= MAX_AUTHORIZATION_MATCH_WORK, "liveness match work limit")
    return total


def policy_allows(
    store: Store, policy: dict[str, Any], roles: list[dict[str, str]], req: dict[str, Any], liveness: bool = False
) -> bool:
    for rule in policy["payload"]["rules"]:
        if liveness and rule["required_evidence_basis"]:
            continue
        if not rule_subject_action_resource_matches(store, rule, roles, req):
            continue
        ok = True
        for basis in rule["required_evidence_basis"]:
            if basis not in SUPPORTED_EVIDENCE_BASIS:
                raise UnsupportedProfile(basis)
            candidates = [item for item in req["applicable_evidence"] if item["basis"] == basis]
            if not any(evidence_passes(store, item["cid"]) for item in candidates):
                ok = False
                break
        if ok:
            return True
    return False


def future_policy_update_possible(store: Store, state: dict[str, Any]) -> bool:
    policy = store.resolve(state["bindings"]["sys:policy"])
    active_roles_by_actor: dict[str, list[dict[str, str]]] = {}
    for cid in state["bindings"].values():
        rev = store.resolve(cid)
        if rev["payload_profile"] == "ctl-governance/role-binding/1":
            payload = rev["payload"]
            if payload["scope"]["project_id"] == state["project_id"]:
                active_roles_by_actor.setdefault(payload["actor_id"], []).append(
                    {"cid": cid, "role_id": payload["role_id"], "actor_id": payload["actor_id"]}
                )
    liveness_match_work(policy, len(active_roles_by_actor))
    probes = [
        {
            "action": "revision.record",
            "logical_id": "sys:policy",
            "payload_profile": "ctl-governance/policy-set/1",
            "revision_kind": "policy-set",
            "applicable_evidence": [],
        },
        {
            "action": "binding.set",
            "logical_id": "sys:policy",
            "payload_profile": "ctl-governance/policy-set/1",
            "revision_kind": "policy-set",
            "applicable_evidence": [],
        },
        {
            "action": "policy.replace",
            "logical_id": "sys:policy",
            "payload_profile": "ctl-governance/policy-set/1",
            "revision_kind": "policy-set",
            "applicable_evidence": [],
        },
    ]
    for roles in active_roles_by_actor.values():
        if all(policy_allows(store, policy, roles, probe, liveness=True) for probe in probes):
            return True
    return False


def derive_genesis(store: Store, batch_cid: str) -> dict[str, Any]:
    batch = store.resolve(batch_cid)
    recorded, unsupported_profiles, unsupported_evidence_basis = validate_batch_common(store, batch)
    die_unless(batch["parent_root"] is None, "genesis parent_root must be null")
    die_unless(batch["principal_claim"]["role_bindings"] == [], "genesis principal roles must be empty")
    die_unless(batch["evidence"] == [], "genesis evidence must be empty")
    for op in batch["binding_ops"]:
        die_unless(op["op"] == "set", "genesis only sets bindings")
        die_unless(op["expected"]["state"] == "absent", "genesis expects absent")
    recorded_map = dict(recorded)
    role_binding_identities = extend_role_binding_identities({}, recorded)
    die_unless("sys:policy" in [op["logical_id"] for op in batch["binding_ops"]], "genesis must set policy")
    for cid, rev in recorded:
        for parent in rev["parents"]:
            die_unless(parent in recorded_map, "genesis parent not in batch")
            validate_parent_relation(rev, recorded_map[parent])
    assert_no_parent_cycle(recorded_map)
    bindings = apply_binding_ops({}, batch["binding_ops"])
    for logical_id, cid in bindings.items():
        die_unless(cid in recorded_map, "genesis binding target not recorded")
        rev = recorded_map[cid]
        die_unless(rev["logical_id"] == logical_id, "genesis binding logical mismatch")
        validate_revision_envelope(store, cid, rev)
    policy = recorded_map[bindings["sys:policy"]]
    validate_policy_revision(policy)
    unsupported_basis = unsupported_policy_basis(policy)
    root = {
        "profile": "ctl/project-state-root/1",
        "kernel_profile": batch["kernel_profile"],
        "project_id": batch["project_id"],
        "parent": None,
        "bindings": bindings,
        "transition": batch_cid,
    }
    validate_root(root)
    root_cid = store.add(root)
    state = {
        "root": root,
        "root_cid": root_cid,
        "recorded": set(batch["recorded_revisions"]),
        "bindings": bindings,
        "project_id": batch["project_id"],
        "kernel_profile": batch["kernel_profile"],
        "role_binding_identities": role_binding_identities,
    }
    die_unless(future_policy_update_possible(store, state), "genesis lacks future policy path")
    if unsupported_basis is not None:
        raise UnsupportedProfile(unsupported_basis)
    if unsupported_evidence_basis:
        raise UnsupportedProfile(unsupported_evidence_basis[0])
    if unsupported_profiles:
        raise UnsupportedProfile(unsupported_profiles[0])
    return state


def validate_transition(store: Store, state: dict[str, Any], batch_cid: str) -> dict[str, Any]:
    batch = store.resolve(batch_cid)
    recorded, unsupported_profiles, unsupported_evidence_basis = validate_batch_common(store, batch)
    die_unless(batch["parent_root"] == state["root_cid"], "parent root mismatch")
    die_unless(batch["project_id"] == state["project_id"], "project mismatch")
    die_unless(batch["kernel_profile"] == state["kernel_profile"], "kernel mismatch")
    recorded_set = set(state["recorded"]) | set(batch["recorded_revisions"])
    die_unless(not (set(batch["recorded_revisions"]) & set(state["recorded"])), "already recorded")
    current_role_binding_identities = state.get("role_binding_identities")
    if current_role_binding_identities is None:
        current_role_binding_identities = {}
        for cid in state["recorded"]:
            rev = store.resolve(cid)
            current_role_binding_identities = extend_role_binding_identities(
                current_role_binding_identities, [(cid, rev)]
            )
    role_binding_identities = extend_role_binding_identities(current_role_binding_identities, recorded)
    old_policy_cid = state["bindings"]["sys:policy"]
    old_policy = store.resolve(old_policy_cid)
    validate_policy_revision(old_policy)
    for _, rev in recorded:
        for parent in rev["parents"]:
            die_unless(parent in recorded_set, "parent not recorded")
            parent_rev = store.resolve(parent)
            validate_parent_relation(rev, parent_rev)
    for op in batch["binding_ops"]:
        check_expected_against(state["bindings"], op)
        if op["op"] == "set":
            die_unless(op["new_cid"] in recorded_set, "set target not recorded")
            target = store.resolve(op["new_cid"])
            die_unless(target["logical_id"] == op["logical_id"], "set logical mismatch")
            die_unless(target["project_id"] == batch["project_id"], "set project mismatch")
            validate_revision_envelope(store, op["new_cid"], target)
            if target["payload_profile"] in SUPPORTED_PAYLOAD_PROFILES:
                validate_revision_payload(target)
            if op["logical_id"].startswith("role-binding:") and op["logical_id"] in state["bindings"]:
                die_unless(state["bindings"][op["logical_id"]] in target["parents"], "role binding fast-forward violation")
    changing_policy = any(op["op"] == "set" and op["logical_id"] == "sys:policy" for op in batch["binding_ops"])
    if changing_policy:
        new_policy_cid = next(op["new_cid"] for op in batch["binding_ops"] if op["logical_id"] == "sys:policy")
        die_unless(new_policy_cid in batch["recorded_revisions"], "policy replacement must be recorded atomically")
    for entry in batch["evidence"]:
        die_unless(entry["cid"] in recorded_set, "evidence CID not recorded")
    roles = role_bindings_for_principal(store, state, batch["principal_claim"])
    requests = make_requests(store, state, batch, recorded)
    die_unless(len(requests) <= 5121, "too many requests")
    authorization_match_work(old_policy, requests)
    die_unless(predicate_work(store, old_policy, roles, requests) <= MAX_PREDICATE_WORK, "predicate work limit")
    for req in requests:
        die_unless(policy_allows(store, old_policy, roles, req), f"policy denied {req['action']} {req['logical_id']}")
    bindings = apply_binding_ops(state["bindings"], batch["binding_ops"])
    die_unless("sys:policy" in bindings, "missing sys:policy")
    active_unsupported_profiles: list[str] = []
    for logical_id, cid in bindings.items():
        die_unless(cid in recorded_set, "active target not recorded")
        rev = store.resolve(cid)
        die_unless(rev["logical_id"] == logical_id, "active logical mismatch")
        validate_revision_envelope(store, cid, rev)
        if rev["payload_profile"] in SUPPORTED_PAYLOAD_PROFILES:
            validate_revision_payload(rev)
        else:
            active_unsupported_profiles.append(rev["payload_profile"])
    candidate_policy = store.resolve(bindings["sys:policy"])
    validate_policy_revision(candidate_policy)
    unsupported_candidate_basis = unsupported_policy_basis(candidate_policy)
    if changing_policy:
        die_unless(old_policy_cid in candidate_policy["parents"], "policy fast-forward violation")
    root = {
        "profile": "ctl/project-state-root/1",
        "kernel_profile": state["kernel_profile"],
        "project_id": state["project_id"],
        "parent": state["root_cid"],
        "bindings": bindings,
        "transition": batch_cid,
    }
    validate_root(root)
    root_cid = store.add(root)
    child = {
        "root": root,
        "root_cid": root_cid,
        "recorded": recorded_set,
        "bindings": bindings,
        "project_id": state["project_id"],
        "kernel_profile": state["kernel_profile"],
        "role_binding_identities": role_binding_identities,
    }
    die_unless(future_policy_update_possible(store, child), "future policy update impossible")
    if unsupported_candidate_basis is not None:
        raise UnsupportedProfile(unsupported_candidate_basis)
    if unsupported_evidence_basis:
        raise UnsupportedProfile(unsupported_evidence_basis[0])
    if unsupported_profiles:
        raise UnsupportedProfile(unsupported_profiles[0])
    if active_unsupported_profiles:
        raise UnsupportedProfile(active_unsupported_profiles[0])
    return child


def validate_chain(store: Store, target_root_cid: str, trust_anchor: dict[str, str]) -> dict[str, Any]:
    check_keys(trust_anchor, {"project_id", "kernel_profile", "genesis_root_cid"})
    die_unless(is_id(trust_anchor["project_id"]), "bad trust project")
    die_unless(trust_anchor["kernel_profile"] == "ctl-kernel/1", "bad trust kernel")
    die_unless(is_cid(trust_anchor["genesis_root_cid"]), "bad trust genesis")

    path: list[tuple[str, dict[str, Any]]] = []
    seen: set[str] = set()
    cursor = target_root_cid
    while True:
        die_unless(cursor not in seen, "root parent cycle")
        seen.add(cursor)
        root = store.resolve(cursor)
        validate_root(root)
        die_unless(root["project_id"] == trust_anchor["project_id"], "root project trust mismatch")
        die_unless(root["kernel_profile"] == trust_anchor["kernel_profile"], "root kernel trust mismatch")
        path.append((cursor, root))
        if cursor == trust_anchor["genesis_root_cid"]:
            break
        die_unless(root["parent"] is not None, "chain does not reach pinned genesis")
        cursor = root["parent"]

    path.reverse()
    genesis_cid, genesis_root = path[0]
    state = derive_genesis(store, genesis_root["transition"])
    die_unless(state["root_cid"] == genesis_cid, "computed genesis root CID mismatch")
    die_unless(canonical_bytes(state["root"]) == canonical_bytes(genesis_root), "computed genesis root bytes mismatch")

    for child_cid, child_root in path[1:]:
        validate_root(child_root)
        state = validate_transition(store, state, child_root["transition"])
        die_unless(state["root_cid"] == child_cid, "computed child root CID mismatch")
        die_unless(canonical_bytes(state["root"]) == canonical_bytes(child_root), "computed child root bytes mismatch")
    return state


def policy_payload(allow_owner: bool = True, required_basis: list[str] | None = None) -> dict[str, Any]:
    rules = []
    if allow_owner:
        selectors = sort_objects(
            [
                {"logical_id": "sys:policy"},
                {"logical_id_prefix": "claim:"},
                {"logical_id_prefix": "role-binding:"},
                {"payload_profile": "ctl-data/opaque-json/1"},
            ]
        )
        rules.append(
            {
                "effect": "allow",
                "subject": {"role_id": "role:owner"},
                "actions": sort_scalars(["binding.remove", "binding.set", "policy.replace", "revision.record"]),
                "resources": selectors,
                "required_evidence_basis": sort_scalars(required_basis or []),
            }
        )
    return {"version": 1, "default": "deny", "rules": sort_objects(rules)}


def restricted_role_binding_policy_payload() -> dict[str, Any]:
    owner_rule = {
        "effect": "allow",
        "subject": {"role_id": "role:owner"},
        "actions": sort_scalars(["binding.set", "policy.replace", "revision.record"]),
        "resources": [{"logical_id": "sys:policy"}],
        "required_evidence_basis": [],
    }
    lead_rule = {
        "effect": "allow",
        "subject": {"role_id": "role:lead"},
        "actions": sort_scalars(["binding.set", "revision.record"]),
        "resources": [{"role_binding": {"role_id": "role:reviewer"}}],
        "required_evidence_basis": [],
    }
    return {"version": 1, "default": "deny", "rules": sort_objects([owner_rule, lead_rule])}


def revision(logical_id: str, kind: str, profile: str, payload: dict[str, Any], parents: list[str] | None = None) -> dict[str, Any]:
    return {
        "profile": "ctl/revision/1",
        "kernel_profile": "ctl-kernel/1",
        "project_id": "project:demo",
        "logical_id": logical_id,
        "revision_kind": kind,
        "parents": sort_scalars(parents or []),
        "payload_profile": profile,
        "payload": payload,
        "created_at": "2026-06-25T23:00:00Z",
        "created_by": {"actor_id": "operator:local"},
    }


def batch(
    parent_root: str | None,
    recorded: list[str],
    ops: list[dict[str, Any]],
    roles: list[str],
    actor_id: str = "actor:jin",
    evidence: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    return {
        "profile": "ctl/admission-batch/1",
        "kernel_profile": "ctl-kernel/1",
        "project_id": "project:demo",
        "parent_root": parent_root,
        "recorded_revisions": sort_scalars(recorded),
        "binding_ops": sorted(ops, key=lambda op: op["logical_id"].encode("utf-8")),
        "evidence": sort_objects(evidence or []),
        "principal_claim": {"actor_id": actor_id, "role_bindings": sort_scalars(roles)},
        "submitted_by": {"actor_id": "operator:local"},
        "admitted_at": "2026-06-25T23:01:00Z",
    }


def set_op(logical_id: str, expected: dict[str, Any], new_cid: str) -> dict[str, Any]:
    return {"op": "set", "logical_id": logical_id, "expected": expected, "new_cid": new_cid}


def absent() -> dict[str, str]:
    return {"state": "absent"}


def bound(cid: str) -> dict[str, str]:
    return {"state": "bound", "cid": cid}


def build_case(case: str) -> tuple[Store, dict[str, Any]]:
    store = Store()
    policy = revision("sys:policy", "policy-set", "ctl-governance/policy-set/1", policy_payload())
    policy_cid = store.add(policy)
    role = revision(
        "role-binding:operator",
        "role-binding",
        "ctl-governance/role-binding/1",
        {"actor_id": "actor:jin", "role_id": "role:owner", "scope": {"project_id": "project:demo"}},
    )
    role_cid = store.add(role)
    genesis_batch = batch(
        None,
        [policy_cid, role_cid],
        [
            set_op("role-binding:operator", absent(), role_cid),
            set_op("sys:policy", absent(), policy_cid),
        ],
        [],
    )
    genesis_cid = store.add(genesis_batch)
    objects = {"policy": policy_cid, "role": role_cid, "genesis_batch": genesis_cid}
    if case == "genesis":
        return store, {"kind": "genesis", "objects": objects, "genesis_batch": genesis_cid, "expect": "valid"}

    genesis_state = derive_genesis(store, genesis_cid)
    if case == "non-genesis":
        claim = revision("claim:one", "claim", "ctl-data/opaque-json/1", {"text": "hello"})
        claim_cid = store.add(claim)
        trans = batch(
            genesis_state["root_cid"],
            [claim_cid],
            [set_op("claim:one", absent(), claim_cid)],
            [role_cid],
        )
        trans_cid = store.add(trans)
        objects.update({"genesis_root": genesis_state["root_cid"], "claim": claim_cid, "transition_batch": trans_cid})
        return store, {
            "kind": "non-genesis",
            "objects": objects,
            "genesis_batch": genesis_cid,
            "transition_batch": trans_cid,
            "expect": "valid",
        }
    if case in {
        "role-binding-selector-pass",
        "role-binding-payload-escalation",
        "role-binding-slot-hijack-no-parent",
    }:
        store = Store()
        restricted_policy = revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            restricted_role_binding_policy_payload(),
        )
        restricted_policy_cid = store.add(restricted_policy)
        owner_role = revision(
            "role-binding:operator",
            "role-binding",
            "ctl-governance/role-binding/1",
            {"actor_id": "actor:jin", "role_id": "role:owner", "scope": {"project_id": "project:demo"}},
        )
        owner_role_cid = store.add(owner_role)
        lead_role = revision(
            "role-binding:lead",
            "role-binding",
            "ctl-governance/role-binding/1",
            {"actor_id": "actor:lead", "role_id": "role:lead", "scope": {"project_id": "project:demo"}},
        )
        lead_role_cid = store.add(lead_role)
        extra_recorded: list[str] = []
        extra_ops: list[dict[str, Any]] = []
        extra_objects: dict[str, str] = {}
        if case == "role-binding-slot-hijack-no-parent":
            backup_role = revision(
                "role-binding:backup",
                "role-binding",
                "ctl-governance/role-binding/1",
                {"actor_id": "actor:bob", "role_id": "role:owner", "scope": {"project_id": "project:demo"}},
            )
            backup_role_cid = store.add(backup_role)
            extra_recorded.append(backup_role_cid)
            extra_ops.append(set_op("role-binding:backup", absent(), backup_role_cid))
            extra_objects["backup_role"] = backup_role_cid
        restricted_genesis = batch(
            None,
            [restricted_policy_cid, owner_role_cid, lead_role_cid] + extra_recorded,
            [
                set_op("role-binding:lead", absent(), lead_role_cid),
                set_op("role-binding:operator", absent(), owner_role_cid),
                set_op("sys:policy", absent(), restricted_policy_cid),
            ]
            + extra_ops,
            [],
        )
        restricted_genesis_cid = store.add(restricted_genesis)
        restricted_state = derive_genesis(store, restricted_genesis_cid)
        granted_role = "role:owner" if case == "role-binding-payload-escalation" else "role:reviewer"
        logical_id = (
            "role-binding:operator"
            if case == "role-binding-slot-hijack-no-parent"
            else "role-binding:reviewer:alice"
        )
        reviewer_binding = revision(
            logical_id,
            "role-binding",
            "ctl-governance/role-binding/1",
            {"actor_id": "actor:alice", "role_id": granted_role, "scope": {"project_id": "project:demo"}},
        )
        reviewer_binding_cid = store.add(reviewer_binding)
        expected = bound(owner_role_cid) if case == "role-binding-slot-hijack-no-parent" else absent()
        trans = batch(
            restricted_state["root_cid"],
            [reviewer_binding_cid],
            [set_op(logical_id, expected, reviewer_binding_cid)],
            [lead_role_cid],
            actor_id="actor:lead",
        )
        trans_cid = store.add(trans)
        return store, {
            "kind": case,
            "objects": {
                "policy": restricted_policy_cid,
                "owner_role": owner_role_cid,
                "lead_role": lead_role_cid,
                "genesis_batch": restricted_genesis_cid,
                "genesis_root": restricted_state["root_cid"],
                "new_role_binding": reviewer_binding_cid,
                "transition_batch": trans_cid,
            }
            | extra_objects,
            "genesis_batch": restricted_genesis_cid,
            "transition_batch": trans_cid,
            "expect": "valid" if case == "role-binding-selector-pass" else "invalid",
        }
    if case in {"policy-replace-pass", "policy-replace-liveness-fail"}:
        allow_owner = case == "policy-replace-pass"
        new_policy = revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            policy_payload(allow_owner=allow_owner),
            parents=[policy_cid],
        )
        new_policy_cid = store.add(new_policy)
        trans = batch(
            genesis_state["root_cid"],
            [new_policy_cid],
            [set_op("sys:policy", bound(policy_cid), new_policy_cid)],
            [role_cid],
        )
        trans_cid = store.add(trans)
        objects.update({"genesis_root": genesis_state["root_cid"], "new_policy": new_policy_cid, "transition_batch": trans_cid})
        return store, {
            "kind": case,
            "objects": objects,
            "genesis_batch": genesis_cid,
            "transition_batch": trans_cid,
            "expect": "valid" if allow_owner else "invalid",
        }
    if case == "unsupported-basis":
        store = Store()
        bad_policy = revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            policy_payload(required_basis=["agent/unknown-basis/1"]),
        )
        bad_policy_cid = store.add(bad_policy)
        role_cid = store.add(role)
        bad_genesis = batch(
            None,
            [bad_policy_cid, role_cid],
            [set_op("role-binding:operator", absent(), role_cid), set_op("sys:policy", absent(), bad_policy_cid)],
            [],
        )
        bad_genesis_cid = store.add(bad_genesis)
        return store, {
            "kind": "unsupported-basis",
            "objects": {"policy": bad_policy_cid, "role": role_cid, "genesis_batch": bad_genesis_cid},
            "genesis_batch": bad_genesis_cid,
            "expect": "invalid",
        }
    if case == "genesis-parent-outside":
        store = Store()
        policy_cid = store.add(policy)
        role_cid = store.add(role)
        outside_parent = revision("claim:child", "claim", "ctl-data/opaque-json/1", {"text": "outside"})
        outside_parent_cid = store.add(outside_parent)
        child = revision(
            "claim:child",
            "claim",
            "ctl-data/opaque-json/1",
            {"text": "child"},
            parents=[outside_parent_cid],
        )
        child_cid = store.add(child)
        bad_genesis = batch(
            None,
            [policy_cid, role_cid, child_cid],
            [set_op("role-binding:operator", absent(), role_cid), set_op("sys:policy", absent(), policy_cid)],
            [],
        )
        bad_genesis_cid = store.add(bad_genesis)
        return store, {
            "kind": "genesis-parent-outside",
            "objects": {
                "policy": policy_cid,
                "role": role_cid,
                "outside_parent": outside_parent_cid,
                "child": child_cid,
                "genesis_batch": bad_genesis_cid,
            },
            "genesis_batch": bad_genesis_cid,
            "expect": "invalid",
        }
    if case == "genesis-evidence-nonempty":
        evidence_entry = {
            "target": {"kind": "recorded_revision", "cid": policy_cid},
            "basis": "agent/run-receipt/1",
            "cid": role_cid,
        }
        bad_genesis = batch(
            None,
            [policy_cid, role_cid],
            [set_op("role-binding:operator", absent(), role_cid), set_op("sys:policy", absent(), policy_cid)],
            [],
            evidence=[evidence_entry],
        )
        bad_genesis_cid = store.add(bad_genesis)
        objects.update({"genesis_batch": bad_genesis_cid})
        return store, {
            "kind": "genesis-evidence-nonempty",
            "objects": objects,
            "genesis_batch": bad_genesis_cid,
            "expect": "invalid",
        }
    if case == "sys-namespace-invalid":
        sys_revision = revision("sys:evil", "claim", "ctl-data/opaque-json/1", {"text": "reserved"})
        sys_revision_cid = store.add(sys_revision)
        bad_genesis = batch(
            None,
            [policy_cid, role_cid, sys_revision_cid],
            [set_op("role-binding:operator", absent(), role_cid), set_op("sys:policy", absent(), policy_cid)],
            [],
        )
        bad_genesis_cid = store.add(bad_genesis)
        objects.update({"sys_revision": sys_revision_cid, "genesis_batch": bad_genesis_cid})
        return store, {
            "kind": "sys-namespace-invalid",
            "objects": objects,
            "genesis_batch": bad_genesis_cid,
            "expect": "invalid",
        }
    if case == "sys-policy-opaque-invalid":
        opaque_policy_slot = revision("sys:policy", "opaque", "ctl-data/opaque-json/1", {"text": "not a policy"})
        opaque_policy_slot_cid = store.add(opaque_policy_slot)
        bad_genesis = batch(
            None,
            [opaque_policy_slot_cid, role_cid],
            [set_op("role-binding:operator", absent(), role_cid), set_op("sys:policy", absent(), opaque_policy_slot_cid)],
            [],
        )
        bad_genesis_cid = store.add(bad_genesis)
        return store, {
            "kind": "sys-policy-opaque-invalid",
            "objects": {"opaque_policy_slot": opaque_policy_slot_cid, "role": role_cid, "genesis_batch": bad_genesis_cid},
            "genesis_batch": bad_genesis_cid,
            "expect": "invalid",
        }
    if case == "role-binding-lineage-change":
        changed_role = revision(
            "role-binding:operator",
            "role-binding",
            "ctl-governance/role-binding/1",
            {"actor_id": "actor:jin", "role_id": "role:reviewer", "scope": {"project_id": "project:demo"}},
            parents=[role_cid],
        )
        changed_role_cid = store.add(changed_role)
        bad_trans = batch(
            derive_genesis(store, genesis_cid)["root_cid"],
            [changed_role_cid],
            [set_op("role-binding:operator", bound(role_cid), changed_role_cid)],
            [role_cid],
        )
        bad_trans_cid = store.add(bad_trans)
        return store, {
            "kind": "role-binding-lineage-change",
            "objects": {
                "policy": policy_cid,
                "role": role_cid,
                "genesis_batch": genesis_cid,
                "changed_role": changed_role_cid,
                "transition_batch": bad_trans_cid,
            },
            "genesis_batch": genesis_cid,
            "transition_batch": bad_trans_cid,
            "expect": "invalid",
        }
    if case == "role-binding-non-fast-forward":
        successor = revision(
            "role-binding:operator",
            "role-binding",
            "ctl-governance/role-binding/1",
            {"actor_id": "actor:jin", "role_id": "role:owner", "scope": {"project_id": "project:demo"}},
        )
        successor["created_at"] = "2026-06-25T23:00:01Z"
        successor_cid = store.add(successor)
        bad_trans = batch(
            genesis_state["root_cid"],
            [successor_cid],
            [set_op("role-binding:operator", bound(role_cid), successor_cid)],
            [role_cid],
        )
        bad_trans_cid = store.add(bad_trans)
        return store, {
            "kind": "role-binding-non-fast-forward",
            "objects": {
                "policy": policy_cid,
                "role": role_cid,
                "genesis_batch": genesis_cid,
                "successor": successor_cid,
                "transition_batch": bad_trans_cid,
            },
            "genesis_batch": genesis_cid,
            "transition_batch": bad_trans_cid,
            "expect": "invalid",
        }
    if case == "invalid-plus-unsupported":
        bad_revision = revision("sys:evil", "claim", "ctl-data/opaque-json/1", {"text": "reserved"})
        bad_revision_cid = store.add(bad_revision)
        evidence_entry = {
            "target": {"kind": "recorded_revision", "cid": bad_revision_cid},
            "basis": "agent/unknown-basis/1",
            "cid": role_cid,
        }
        bad_trans = batch(
            genesis_state["root_cid"],
            [bad_revision_cid],
            [],
            [role_cid],
            evidence=[evidence_entry],
        )
        bad_trans_cid = store.add(bad_trans)
        objects.update({"bad_revision": bad_revision_cid, "transition_batch": bad_trans_cid})
        return store, {
            "kind": "invalid-plus-unsupported",
            "objects": objects,
            "genesis_batch": genesis_cid,
            "transition_batch": bad_trans_cid,
            "expect": "invalid",
        }
    if case == "genesis-evidence-plus-unsupported":
        evidence_entry = {
            "target": {"kind": "recorded_revision", "cid": policy_cid},
            "basis": "agent/unknown-basis/1",
            "cid": role_cid,
        }
        bad_genesis = batch(
            None,
            [policy_cid, role_cid],
            [set_op("role-binding:operator", absent(), role_cid), set_op("sys:policy", absent(), policy_cid)],
            [],
            evidence=[evidence_entry],
        )
        bad_genesis_cid = store.add(bad_genesis)
        return store, {
            "kind": "genesis-evidence-plus-unsupported",
            "objects": {"policy": policy_cid, "role": role_cid, "genesis_batch": bad_genesis_cid},
            "genesis_batch": bad_genesis_cid,
            "expect": "invalid",
        }
    raise ValueError(case)


def write_case(root: Path, case: str, dirname: str) -> None:
    store, manifest = build_case(case)
    out_dir = root / dirname
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest = dict(manifest)
    if manifest["expect"] == "valid":
        state = derive_genesis(store, manifest["genesis_batch"])
        if "transition_batch" in manifest:
            state = validate_transition(store, state, manifest["transition_batch"])
        manifest["expected_root_cid"] = state["root_cid"]
        manifest["expected_root_canonical_hex"] = canonical_bytes(state["root"]).hex()
    manifest["object_values"] = {cid: obj for cid, obj in sorted(store.objects.items())}
    (out_dir / "case.json").write_text(canonical_text(manifest), encoding="utf-8")


def write_vectors(root: Path) -> None:
    root.mkdir(parents=True, exist_ok=True)
    encoding_values = [
        {"name": "empty-object", "value": {}},
        {"name": "sorted-object", "value": {"b": 2, "a": 1}},
        {"name": "unicode", "value": {"text": "繁體中文"}},
    ]
    lines = []
    for item in encoding_values:
        value = item["value"]
        lines.append(
            canonical_text(
                {
                    "name": item["name"],
                    "canonical_hex": canonical_bytes(value).hex(),
                    "cid": object_cid(value),
                    "value": value,
                }
            )
        )
    (root / "encoding.jsonl").write_text("\n".join(lines) + "\n", encoding="utf-8")
    write_case(root, "genesis", "genesis")
    write_case(root, "non-genesis", "non-genesis")
    write_case(root, "role-binding-selector-pass", "role-binding-selector-pass")
    write_case(root, "role-binding-payload-escalation", "role-binding-payload-escalation")
    write_case(root, "role-binding-slot-hijack-no-parent", "role-binding-slot-hijack-no-parent")
    write_case(root, "role-binding-non-fast-forward", "role-binding-non-fast-forward")
    write_case(root, "policy-replace-pass", "policy-replace-pass")
    write_case(root, "policy-replace-liveness-fail", "policy-replace-liveness-fail")
    write_case(root, "unsupported-basis", "unsupported-basis")
    write_case(root, "invalid-plus-unsupported", "invalid-plus-unsupported")
    write_case(root, "genesis-evidence-plus-unsupported", "genesis-evidence-plus-unsupported")
    write_case(root, "genesis-parent-outside", "genesis-parent-outside")
    write_case(root, "genesis-evidence-nonempty", "genesis-evidence-nonempty")
    write_case(root, "sys-namespace-invalid", "sys-namespace-invalid")
    write_case(root, "sys-policy-opaque-invalid", "sys-policy-opaque-invalid")
    write_case(root, "role-binding-lineage-change", "role-binding-lineage-change")


def load_case(path: Path) -> tuple[Store, dict[str, Any]]:
    manifest = load_json_strict(path)
    store = Store()
    for cid, obj in manifest["object_values"].items():
        die_unless(store.add(obj) == cid, f"case object CID mismatch: {cid}")
    return store, manifest


def check_case(path: Path) -> str:
    store, manifest = load_case(path)
    expect = manifest["expect"]
    try:
        state = derive_genesis(store, manifest["genesis_batch"])
        if "transition_batch" in manifest:
            state = validate_transition(store, state, manifest["transition_batch"])
        result = "valid"
    except UnsupportedProfile:
        result = "unsupported"
    except InvalidHistory:
        result = "invalid"
    die_unless(result == expect, f"{path}: expected {expect}, got {result}")
    if result == "valid":
        die_unless(state["root_cid"] == manifest["expected_root_cid"], f"{path}: expected root CID mismatch")
        die_unless(
            canonical_bytes(state["root"]).hex() == manifest["expected_root_canonical_hex"],
            f"{path}: expected root bytes mismatch",
        )
    return result


def check_vectors(root: Path) -> None:
    with (root / "encoding.jsonl").open(encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            row = json.loads(line)
            die_unless(canonical_bytes(row["value"]).hex() == row["canonical_hex"], f"encoding mismatch {row['name']}")
            die_unless(object_cid(row["value"]) == row["cid"], f"CID mismatch {row['name']}")
    for dirname in [
        "genesis",
        "non-genesis",
        "role-binding-selector-pass",
        "role-binding-payload-escalation",
        "role-binding-slot-hijack-no-parent",
        "role-binding-non-fast-forward",
        "policy-replace-pass",
        "policy-replace-liveness-fail",
        "unsupported-basis",
        "invalid-plus-unsupported",
        "genesis-evidence-plus-unsupported",
        "genesis-parent-outside",
        "genesis-evidence-nonempty",
        "sys-namespace-invalid",
        "sys-policy-opaque-invalid",
        "role-binding-lineage-change",
    ]:
        result = check_case(root / dirname / "case.json")
        print(f"{dirname}: {result}")
    print("encoding: valid")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", nargs="?", choices=["generate-vectors", "check-vectors", "verify-vectors"])
    parser.add_argument("path", nargs="?", type=Path)
    parser.add_argument("--write-vectors", type=Path)
    parser.add_argument("--check-vectors", type=Path)
    args = parser.parse_args()
    if args.command == "generate-vectors":
        die_unless(args.path is not None, "generate-vectors requires path")
        write_vectors(args.path)
        return
    if args.command in {"check-vectors", "verify-vectors"}:
        die_unless(args.path is not None, "check-vectors requires path")
        check_vectors(args.path)
        return
    if args.write_vectors:
        write_vectors(args.write_vectors)
    if args.check_vectors:
        check_vectors(args.check_vectors)
    if not args.command and not args.write_vectors and not args.check_vectors:
        parser.print_help()


if __name__ == "__main__":
    main()
