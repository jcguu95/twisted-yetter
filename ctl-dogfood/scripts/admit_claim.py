#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parent
CTL_META_ROOT = Path(os.environ.get("CTL_META_ROOT", REPO_ROOT.parent / "ctl-meta")).resolve()
KERNEL_ROOT = CTL_META_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))

import ctl_ref  # noqa: E402


PROJECT_ID = "project:twisted-yetter"
KERNEL_PROFILE = "ctl-kernel/1"
ACTOR_ID = "actor:jin"
SUBMITTED_BY = "actor:codex"


def run_git(root: Path, args: list[str]) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n")


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def load_store() -> ctl_ref.Store:
    store = ctl_ref.Store()
    for path in sorted((DOGFOOD_ROOT / "objects" / "ctlobj-sha256").glob("*.json")):
        obj = load_json(path)
        cid = store.add(obj)
        expected = "ctlobj-sha256:" + path.stem
        ctl_ref.die_unless(cid == expected, f"object filename CID mismatch: {path}")
    return store


def revision(
    logical_id: str,
    payload: dict[str, Any],
    created_at: str,
    parents: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "profile": "ctl/revision/1",
        "kernel_profile": KERNEL_PROFILE,
        "project_id": PROJECT_ID,
        "logical_id": logical_id,
        "revision_kind": "claim",
        "parents": ctl_ref.sort_scalars(parents or []),
        "payload_profile": "ctl-data/opaque-json/1",
        "payload": payload,
        "created_at": created_at,
        "created_by": {"actor_id": SUBMITTED_BY},
    }


def absent() -> dict[str, str]:
    return {"state": "absent"}


def bound(cid: str) -> dict[str, str]:
    return {"state": "bound", "cid": cid}


def set_op(logical_id: str, expected: dict[str, Any], new_cid: str) -> dict[str, Any]:
    return {"op": "set", "logical_id": logical_id, "expected": expected, "new_cid": new_cid}


def batch(
    parent_root: str,
    recorded: list[str],
    binding_ops: list[dict[str, Any]],
    principal_roles: list[str],
    admitted_at: str,
) -> dict[str, Any]:
    return {
        "profile": "ctl/admission-batch/1",
        "kernel_profile": KERNEL_PROFILE,
        "project_id": PROJECT_ID,
        "parent_root": parent_root,
        "recorded_revisions": ctl_ref.sort_scalars(recorded),
        "binding_ops": sorted(binding_ops, key=lambda op: op["logical_id"].encode("utf-8")),
        "evidence": [],
        "principal_claim": {"actor_id": ACTOR_ID, "role_bindings": ctl_ref.sort_scalars(principal_roles)},
        "submitted_by": {"actor_id": SUBMITTED_BY},
        "admitted_at": admitted_at,
    }


def cid_path(cid: str) -> Path:
    prefix, digest = cid.split(":", 1)
    if prefix != "ctlobj-sha256":
        raise ValueError(f"unexpected CID prefix: {cid}")
    return DOGFOOD_ROOT / "objects" / "ctlobj-sha256" / f"{digest}.json"


def find_active_owner_role(state: dict[str, Any], store: ctl_ref.Store) -> str:
    matches = []
    for cid in state["bindings"].values():
        rev = store.resolve(cid)
        if rev.get("payload_profile") != "ctl-governance/role-binding/1":
            continue
        payload = rev["payload"]
        if (
            payload["actor_id"] == ACTOR_ID
            and payload["role_id"] == "role:owner"
            and payload["scope"]["project_id"] == PROJECT_ID
        ):
            matches.append(cid)
    ctl_ref.die_unless(len(matches) == 1, "expected exactly one active owner role for actor:jin")
    return matches[0]


def main() -> int:
    parser = argparse.ArgumentParser(description="Append an opaque JSON claim to the CTL dogfood store.")
    parser.add_argument("--logical-id", required=True)
    parser.add_argument("--payload", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--created-at", required=True)
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()

    ref_path = DOGFOOD_ROOT / "refs" / "main.json"
    ref = load_json(ref_path)
    store = load_store()
    trust_anchor = {
        "project_id": ref["project_id"],
        "kernel_profile": ref["kernel_profile"],
        "genesis_root_cid": ref["genesis_root_cid"],
    }
    state = ctl_ref.validate_chain(store, ref["root_cid"], trust_anchor)
    role_cid = find_active_owner_role(state, store)

    payload_path = args.payload.resolve()
    payload = load_json(payload_path)
    old_cid = state["bindings"].get(args.logical_id)
    if old_cid is not None:
        old_rev = store.resolve(old_cid)
        if ctl_ref.canonical_bytes(old_rev["payload"]) == ctl_ref.canonical_bytes(payload):
            print(json.dumps({"status": "already_admitted", "claim_cid": old_cid, "root_cid": state["root_cid"]}, sort_keys=True))
            return 0
        if not args.update:
            raise SystemExit(f"{args.logical_id} already admitted with different payload; pass --update")

    claim = revision(args.logical_id, payload, args.created_at, parents=[old_cid] if old_cid else [])
    claim_cid = store.add(claim)
    expected = bound(old_cid) if old_cid else absent()
    transition = batch(
        state["root_cid"],
        [claim_cid],
        [set_op(args.logical_id, expected, claim_cid)],
        [role_cid],
        args.created_at,
    )
    transition_cid = store.add(transition)
    child = ctl_ref.validate_transition(store, state, transition_cid)

    write_json(cid_path(claim_cid), claim)
    write_json(cid_path(transition_cid), transition)
    write_json(cid_path(child["root_cid"]), child["root"])
    write_json(
        ref_path,
        {
            "schema": "ctl-dogfood/ref/1",
            "name": "refs/main",
            "project_id": PROJECT_ID,
            "kernel_profile": KERNEL_PROFILE,
            "root_cid": child["root_cid"],
            "genesis_root_cid": ref["genesis_root_cid"],
            "transition_cid": transition_cid,
            "updated_at": args.created_at,
            "updated_by": SUBMITTED_BY,
        },
    )
    manifest_path = args.manifest.resolve()
    write_json(
        manifest_path,
        {
            "schema": "ctl-dogfood/admission-manifest/1",
            "generated_at": args.created_at,
            "generator": "ctl-dogfood/scripts/admit_claim.py",
            "mode": "shadow",
            "project_id": PROJECT_ID,
            "kernel_profile": KERNEL_PROFILE,
            "logical_id": args.logical_id,
            "payload_file": str(payload_path.relative_to(REPO_ROOT)),
            "source_repo_commit_before_admission": run_git(REPO_ROOT, ["rev-parse", "HEAD"]),
            "ctl_meta_commit_at_admission": run_git(CTL_META_ROOT, ["rev-parse", "HEAD"]),
            "parent_root_cid": state["root_cid"],
            "genesis_root_cid": ref["genesis_root_cid"],
            "current_root_cid": child["root_cid"],
            "objects": {
                "claim": claim_cid,
                "transition": transition_cid,
                "current_root": child["root_cid"],
                "principal_role_binding": role_cid,
            },
            "reproduce": [
                "cd ctl-dogfood",
                (
                    "CTL_META_ROOT=/Users/jin/data/local/projects/ctl-meta "
                    "python scripts/admit_claim.py "
                    f"--logical-id {args.logical_id} "
                    f"--payload {payload_path.relative_to(DOGFOOD_ROOT)} "
                    f"--manifest {manifest_path.relative_to(DOGFOOD_ROOT)} "
                    f"--created-at {args.created_at} --update"
                ),
                "CTL_META_ROOT=/Users/jin/data/local/projects/ctl-meta python scripts/verify.py",
            ],
        },
    )
    checked = ctl_ref.validate_chain(store, child["root_cid"], trust_anchor)
    ctl_ref.die_unless(checked["root_cid"] == child["root_cid"], "claim admission replay mismatch")
    print(json.dumps({"status": "ok", "claim_cid": claim_cid, "transition_cid": transition_cid, "root_cid": child["root_cid"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
