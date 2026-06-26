#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parents[1]
KERNEL_ROOT = REPO_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))

import ctl_ref  # noqa: E402


KERNEL_PROFILE = "ctl-kernel/1"
DEFAULT_ACTOR_ID = "actor:jin"
DEFAULT_SUBMITTED_BY = "actor:codex"


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n")


def cid_path(cid: str) -> Path:
    prefix, digest = cid.split(":", 1)
    ctl_ref.die_unless(prefix == "ctlobj-sha256", "unexpected CID prefix")
    return DOGFOOD_ROOT / "objects" / "ctlobj-sha256" / f"{digest}.json"


def load_store() -> ctl_ref.Store:
    store = ctl_ref.Store()
    object_dir = DOGFOOD_ROOT / "objects" / "ctlobj-sha256"
    for path in sorted(object_dir.glob("*.json")):
        obj = load_json(path)
        cid = store.add(obj)
        expected = "ctlobj-sha256:" + path.stem
        ctl_ref.die_unless(cid == expected, f"object filename CID mismatch: {path}")
    return store


def write_object(store: ctl_ref.Store, cid: str) -> None:
    path = cid_path(cid)
    obj = store.resolve(cid)
    if path.exists():
        old = load_json(path)
        ctl_ref.die_unless(ctl_ref.canonical_bytes(old) == ctl_ref.canonical_bytes(obj), f"object mismatch: {cid}")
        return
    write_json(path, obj)


def revision(
    project_id: str,
    logical_id: str,
    payload: dict[str, Any],
    parents: list[str],
    created_at: str,
    submitted_by: str,
) -> dict[str, Any]:
    return {
        "profile": "ctl/revision/1",
        "kernel_profile": KERNEL_PROFILE,
        "project_id": project_id,
        "logical_id": logical_id,
        "revision_kind": "claim",
        "parents": ctl_ref.sort_scalars(parents),
        "payload_profile": "ctl-data/opaque-json/1",
        "payload": payload,
        "created_at": created_at,
        "created_by": {"actor_id": submitted_by},
    }


def set_op(logical_id: str, expected: dict[str, Any], new_cid: str) -> dict[str, Any]:
    return {"op": "set", "logical_id": logical_id, "expected": expected, "new_cid": new_cid}


def transition_batch(
    project_id: str,
    parent_root: str,
    recorded: list[str],
    binding_ops: list[dict[str, Any]],
    principal_roles: list[str],
    actor_id: str,
    submitted_by: str,
    admitted_at: str,
) -> dict[str, Any]:
    return {
        "profile": "ctl/admission-batch/1",
        "kernel_profile": KERNEL_PROFILE,
        "project_id": project_id,
        "parent_root": parent_root,
        "recorded_revisions": ctl_ref.sort_scalars(recorded),
        "binding_ops": sorted(binding_ops, key=lambda op: op["logical_id"].encode("utf-8")),
        "evidence": [],
        "principal_claim": {"actor_id": actor_id, "role_bindings": ctl_ref.sort_scalars(principal_roles)},
        "submitted_by": {"actor_id": submitted_by},
        "admitted_at": admitted_at,
    }


def active_role_bindings_for_actor(store: ctl_ref.Store, state: dict[str, Any], actor_id: str) -> list[str]:
    out = []
    for cid in state["bindings"].values():
        rev = store.resolve(cid)
        if rev.get("payload_profile") != "ctl-governance/role-binding/1":
            continue
        payload = rev["payload"]
        if payload["actor_id"] == actor_id and payload["scope"]["project_id"] == state["project_id"]:
            out.append(cid)
    return ctl_ref.sort_scalars(out)


def expected_for_logical_id(state: dict[str, Any], logical_id: str) -> tuple[dict[str, Any], list[str]]:
    old_cid = state["bindings"].get(logical_id)
    if old_cid is None:
        return {"state": "absent"}, []
    return {"state": "bound", "cid": old_cid}, [old_cid]


def manifest_name(logical_id: str, admitted_at: str) -> str:
    slug = re.sub(r"[^a-z0-9._-]+", "-", logical_id.replace(":", "-")).strip("-")
    date = admitted_at[:10]
    return f"admission-{date}-{slug}.json"


def main() -> int:
    parser = argparse.ArgumentParser(description="Append a shadow-mode CTL claim decision.")
    parser.add_argument("--logical-id", required=True)
    parser.add_argument("--payload-file", required=True, type=Path)
    parser.add_argument("--created-at", required=True)
    parser.add_argument("--admitted-at", required=True)
    parser.add_argument("--actor-id", default=DEFAULT_ACTOR_ID)
    parser.add_argument("--submitted-by", default=DEFAULT_SUBMITTED_BY)
    parser.add_argument("--expected-root", required=True)
    args = parser.parse_args()

    ctl_ref.die_unless(args.logical_id.startswith("claim:"), "dogfood decision logical_id must be claim:*")
    ctl_ref.check_timestamp(args.created_at)
    ctl_ref.check_timestamp(args.admitted_at)

    payload = load_json(args.payload_file)
    ctl_ref.die_unless(isinstance(payload, dict), "decision payload must be object")
    store = load_store()
    ref = load_json(DOGFOOD_ROOT / "refs" / "main.json")
    ctl_ref.die_unless(ref["root_cid"] == args.expected_root, "expected root mismatch")
    trust_anchor = {
        "project_id": ref["project_id"],
        "kernel_profile": ref["kernel_profile"],
        "genesis_root_cid": ref["genesis_root_cid"],
    }
    state = ctl_ref.validate_chain(store, ref["root_cid"], trust_anchor)
    roles = active_role_bindings_for_actor(store, state, args.actor_id)
    ctl_ref.die_unless(roles != [], "no active principal roles for actor")

    expected, parents = expected_for_logical_id(state, args.logical_id)
    claim = revision(ref["project_id"], args.logical_id, payload, parents, args.created_at, args.submitted_by)
    claim_cid = store.add(claim)
    batch = transition_batch(
        ref["project_id"],
        state["root_cid"],
        [claim_cid],
        [set_op(args.logical_id, expected, claim_cid)],
        roles,
        args.actor_id,
        args.submitted_by,
        args.admitted_at,
    )
    batch_cid = store.add(batch)
    child = ctl_ref.validate_transition(store, state, batch_cid)

    write_object(store, claim_cid)
    write_object(store, batch_cid)
    write_object(store, child["root_cid"])
    write_json(
        DOGFOOD_ROOT / "refs" / "main.json",
        {
            "schema": "ctl-dogfood/ref/1",
            "name": "refs/main",
            "project_id": ref["project_id"],
            "kernel_profile": ref["kernel_profile"],
            "root_cid": child["root_cid"],
            "genesis_root_cid": ref["genesis_root_cid"],
            "transition_cid": batch_cid,
            "updated_at": args.admitted_at,
            "updated_by": args.submitted_by,
        },
    )
    write_json(
        DOGFOOD_ROOT / "manifests" / manifest_name(args.logical_id, args.admitted_at),
        {
            "schema": "ctl-dogfood/admission-manifest/1",
            "mode": "shadow",
            "project_id": ref["project_id"],
            "kernel_profile": ref["kernel_profile"],
            "logical_id": args.logical_id,
            "payload_file": str(args.payload_file),
            "created_at": args.created_at,
            "admitted_at": args.admitted_at,
            "previous_root_cid": state["root_cid"],
            "current_root_cid": child["root_cid"],
            "claim_cid": claim_cid,
            "transition_cid": batch_cid,
            "principal_roles": roles,
            "reproduce": [
                "cd meta/ctl-dogfood",
                "uv run python scripts/verify.py",
            ],
        },
    )
    checked = ctl_ref.validate_chain(store, child["root_cid"], trust_anchor)
    ctl_ref.die_unless(checked["root_cid"] == child["root_cid"], "admission replay mismatch")
    print(json.dumps({"status": "ok", "root_cid": child["root_cid"], "claim_cid": claim_cid}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
