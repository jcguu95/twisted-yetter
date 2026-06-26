#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import shutil
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
CREATED_AT = "2026-06-26T18:55:00Z"
ADMITTED_AT = "2026-06-26T18:56:00Z"
ACTOR_ID = "actor:jin"
SUBMITTED_BY = "actor:codex"
PLAN_LOGICAL_ID = "claim:twisted-yetter-computation-first-plan"
PLAN_FILE = DOGFOOD_ROOT / "decisions" / "twisted-yetter-computation-first-plan-2026-06-26.json"


def run_git(root: Path, args: list[str]) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n")


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def revision(
    logical_id: str,
    kind: str,
    profile: str,
    payload: dict[str, Any],
    parents: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "profile": "ctl/revision/1",
        "kernel_profile": KERNEL_PROFILE,
        "project_id": PROJECT_ID,
        "logical_id": logical_id,
        "revision_kind": kind,
        "parents": ctl_ref.sort_scalars(parents or []),
        "payload_profile": profile,
        "payload": payload,
        "created_at": CREATED_AT,
        "created_by": {"actor_id": SUBMITTED_BY},
    }


def set_op(logical_id: str, expected: dict[str, Any], new_cid: str) -> dict[str, Any]:
    return {"op": "set", "logical_id": logical_id, "expected": expected, "new_cid": new_cid}


def absent() -> dict[str, str]:
    return {"state": "absent"}


def batch(
    parent_root: str | None,
    recorded: list[str],
    binding_ops: list[dict[str, Any]],
    principal_roles: list[str],
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
        "admitted_at": ADMITTED_AT,
    }


def dogfood_policy_payload() -> dict[str, Any]:
    selectors = ctl_ref.sort_objects(
        [
            {"logical_id": "sys:policy"},
            {"logical_id_prefix": "claim:"},
            {"logical_id_prefix": "role-binding:"},
            {"payload_profile": "ctl-data/opaque-json/1"},
        ]
    )
    rule = {
        "effect": "allow",
        "subject": {"role_id": "role:owner"},
        "actions": ctl_ref.sort_scalars(["binding.remove", "binding.set", "policy.replace", "revision.record"]),
        "resources": selectors,
        "required_evidence_basis": [],
    }
    return {"version": 1, "default": "deny", "rules": ctl_ref.sort_objects([rule])}


def cid_path(cid: str) -> Path:
    prefix, digest = cid.split(":", 1)
    if prefix != "ctlobj-sha256":
        raise ValueError(f"unexpected CID prefix: {cid}")
    return DOGFOOD_ROOT / "objects" / "ctlobj-sha256" / f"{digest}.json"


def write_store(store: ctl_ref.Store, force: bool) -> None:
    object_dir = DOGFOOD_ROOT / "objects" / "ctlobj-sha256"
    if object_dir.exists() and any(object_dir.iterdir()):
        if not force:
            raise SystemExit("object store already exists; pass --force to rebuild bootstrap snapshot")
        shutil.rmtree(object_dir)
    object_dir.mkdir(parents=True, exist_ok=True)
    for cid in sorted(store.objects):
        write_json(cid_path(cid), store.objects[cid])


def provider_metadata() -> dict[str, Any]:
    return {
        "ctl_meta_root": str(CTL_META_ROOT),
        "ctl_meta_commit": run_git(CTL_META_ROOT, ["rev-parse", "HEAD"]),
        "ctl_meta_status_short": run_git(CTL_META_ROOT, ["status", "--short"]),
        "ctl_kernel_freeze_tag": "ctl-kernel-v0.1.1-experimental",
        "ctl_kernel_freeze_commit": run_git(CTL_META_ROOT, ["rev-parse", "ctl-kernel-v0.1.1-experimental^{}"]),
        "reference_import": str(KERNEL_ROOT / "reference" / "ctl_ref.py"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Bootstrap the project-local CTL dogfood store.")
    parser.add_argument("--force", action="store_true", help="overwrite current bootstrap snapshot")
    args = parser.parse_args()

    if not args.force:
        for path in [DOGFOOD_ROOT / "refs" / "main.json", DOGFOOD_ROOT / "manifests" / "bootstrap-2026-06-26.json"]:
            if path.exists():
                raise SystemExit(f"{path} already exists; pass --force to rebuild bootstrap snapshot")

    plan_payload = load_json(PLAN_FILE)
    provider = provider_metadata()
    store = ctl_ref.Store()

    policy = revision("sys:policy", "policy-set", "ctl-governance/policy-set/1", dogfood_policy_payload())
    role = revision(
        "role-binding:owner:jin",
        "role-binding",
        "ctl-governance/role-binding/1",
        {"actor_id": ACTOR_ID, "role_id": "role:owner", "scope": {"project_id": PROJECT_ID}},
    )
    policy_cid = store.add(policy)
    role_cid = store.add(role)
    genesis_batch = batch(
        None,
        [policy_cid, role_cid],
        [
            set_op("role-binding:owner:jin", absent(), role_cid),
            set_op("sys:policy", absent(), policy_cid),
        ],
        [],
    )
    genesis_batch_cid = store.add(genesis_batch)
    genesis = ctl_ref.derive_genesis(store, genesis_batch_cid)

    plan_claim = revision(PLAN_LOGICAL_ID, "claim", "ctl-data/opaque-json/1", plan_payload)
    plan_claim_cid = store.add(plan_claim)
    transition = batch(
        genesis["root_cid"],
        [plan_claim_cid],
        [set_op(PLAN_LOGICAL_ID, absent(), plan_claim_cid)],
        [role_cid],
    )
    transition_cid = store.add(transition)
    child = ctl_ref.validate_transition(store, genesis, transition_cid)

    write_store(store, args.force)
    trust_anchor = {
        "project_id": PROJECT_ID,
        "kernel_profile": KERNEL_PROFILE,
        "genesis_root_cid": genesis["root_cid"],
    }
    write_json(
        DOGFOOD_ROOT / "refs" / "main.json",
        {
            "schema": "ctl-dogfood/ref/1",
            "name": "refs/main",
            "project_id": PROJECT_ID,
            "kernel_profile": KERNEL_PROFILE,
            "root_cid": child["root_cid"],
            "genesis_root_cid": genesis["root_cid"],
            "transition_cid": transition_cid,
            "updated_at": ADMITTED_AT,
            "updated_by": SUBMITTED_BY,
        },
    )
    write_json(
        DOGFOOD_ROOT / "manifests" / "bootstrap-2026-06-26.json",
        {
            "schema": "ctl-dogfood/bootstrap-manifest/1",
            "generated_at": ADMITTED_AT,
            "generator": "ctl-dogfood/scripts/bootstrap.py",
            "mode": "shadow",
            "project_id": PROJECT_ID,
            "kernel_profile": KERNEL_PROFILE,
            "provider": provider,
            "source_repo_commit_at_decision": plan_payload["source_repo"]["commit_at_decision"],
            "trust_anchor": trust_anchor,
            "genesis_root_cid": genesis["root_cid"],
            "current_root_cid": child["root_cid"],
            "objects": {
                "policy": policy_cid,
                "role_binding_owner_jin": role_cid,
                "genesis_batch": genesis_batch_cid,
                "genesis_root": genesis["root_cid"],
                "plan_claim": plan_claim_cid,
                "plan_transition": transition_cid,
                "current_root": child["root_cid"],
            },
            "object_count": len(store.objects),
            "reproduce": [
                "cd ctl-dogfood",
                "uv run python scripts/verify.py",
                "uv run python scripts/bootstrap.py --force",
                "uv run python scripts/verify.py",
            ],
        },
    )
    checked = ctl_ref.validate_chain(store, child["root_cid"], trust_anchor)
    ctl_ref.die_unless(checked["root_cid"] == child["root_cid"], "bootstrap replay mismatch")
    print(json.dumps({"status": "ok", "root_cid": child["root_cid"], "objects": len(store.objects)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
