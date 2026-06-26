#!/usr/bin/env python3
from __future__ import annotations

import json
import argparse
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parents[1]
KERNEL_ROOT = REPO_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))

import ctl_ref  # noqa: E402


PROJECT_ID = "project:twisted-yetter-meta"
KERNEL_PROFILE = "ctl-kernel/1"
CREATED_AT = "2026-06-26T18:20:00Z"
ADMITTED_AT = "2026-06-26T18:21:00Z"
ACTOR_ID = "actor:jin"
SUBMITTED_BY = "actor:codex"
FREEZE_TAG = "ctl-kernel-v0.1.1-experimental"
FREEZE_CLAIM_ID = "claim:ctl-kernel-v0.1.1-experimental-freeze-accepted"


def run_git(args: list[str]) -> str:
    return subprocess.check_output(["git", "-C", str(REPO_ROOT), *args], text=True).strip()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n")


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
    evidence: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    return {
        "profile": "ctl/admission-batch/1",
        "kernel_profile": KERNEL_PROFILE,
        "project_id": PROJECT_ID,
        "parent_root": parent_root,
        "recorded_revisions": ctl_ref.sort_scalars(recorded),
        "binding_ops": sorted(binding_ops, key=lambda op: op["logical_id"].encode("utf-8")),
        "evidence": ctl_ref.sort_objects(evidence or []),
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


def freeze_acceptance_payload() -> dict[str, Any]:
    freeze_commit = run_git(["rev-parse", f"{FREEZE_TAG}^{{}}"])
    return {
        "schema": "ctl-dogfood/freeze-acceptance/1",
        "status": "accepted",
        "decision": "accept CTL Kernel v0.1.1 Experimental Freeze and begin shadow-mode dogfood",
        "dogfood_mode": "shadow",
        "kernel_profile": KERNEL_PROFILE,
        "freeze_tag": FREEZE_TAG,
        "freeze_commit": freeze_commit,
        "self_reference_policy": "canonical bootstrap objects intentionally avoid current HEAD",
        "accepted_scope": [
            "Revision",
            "AdmissionBatch",
            "ProjectStateRoot",
            "PolicySetRevision",
            "RoleBindingRevision",
            "fixed pure governance evaluator",
            "reference validator behavior",
            "golden vectors",
            "current P0/P1 adversarial regression corpus",
        ],
        "caveats": [
            "not a production security boundary",
            "not full Chronicle compatibility",
            "no cryptographic actor authentication",
            "no confidential compartments",
            "no agent read capability enforcement",
            "no sandbox or tool-call mediation",
            "no raw filesystem crash recovery or rollback detection",
            "agent/run-receipt/1 remains a weak structural predicate",
        ],
        "evidence_artifacts": [
            "meta/ctl-kernel/experimental-freeze-2026-06-26.org",
            "meta/ctl-kernel/reviews/round18-final-freeze-review-2026-06-26.org",
            "meta/ctl-kernel/run-reference-tests.txt",
            "meta/ctl-kernel/fuzz/round18-final-gate-fuzz-output.txt",
        ],
        "next_gate": "dogfood 5-10 low-risk meta decisions before admitting twisted-Yetter research claims",
    }


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
    object_dir.mkdir(parents=True)
    for cid in sorted(store.objects):
        write_json(cid_path(cid), store.objects[cid])


def main() -> int:
    parser = argparse.ArgumentParser(description="Bootstrap the CTL dogfood shadow store.")
    parser.add_argument(
        "--force",
        action="store_true",
        help="overwrite the existing bootstrap object store, refs, and manifest",
    )
    args = parser.parse_args()

    if not args.force:
        for path in [DOGFOOD_ROOT / "refs" / "main.json", DOGFOOD_ROOT / "manifests" / "bootstrap-2026-06-26.json"]:
            if path.exists():
                raise SystemExit(f"{path} already exists; pass --force to rebuild bootstrap snapshot")

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

    freeze_claim = revision(FREEZE_CLAIM_ID, "claim", "ctl-data/opaque-json/1", freeze_acceptance_payload())
    freeze_claim_cid = store.add(freeze_claim)
    transition_batch = batch(
        genesis["root_cid"],
        [freeze_claim_cid],
        [set_op(FREEZE_CLAIM_ID, absent(), freeze_claim_cid)],
        [role_cid],
    )
    transition_batch_cid = store.add(transition_batch)
    child = ctl_ref.validate_transition(store, genesis, transition_batch_cid)

    write_store(store, args.force)

    trust_anchor = {
        "project_id": PROJECT_ID,
        "kernel_profile": KERNEL_PROFILE,
        "genesis_root_cid": genesis["root_cid"],
    }
    ref = {
        "schema": "ctl-dogfood/ref/1",
        "name": "refs/main",
        "project_id": PROJECT_ID,
        "kernel_profile": KERNEL_PROFILE,
        "root_cid": child["root_cid"],
        "genesis_root_cid": genesis["root_cid"],
        "transition_cid": transition_batch_cid,
        "updated_at": ADMITTED_AT,
        "updated_by": SUBMITTED_BY,
    }
    manifest = {
        "schema": "ctl-dogfood/bootstrap-manifest/1",
        "generated_at": ADMITTED_AT,
        "generator": "meta/ctl-dogfood/scripts/bootstrap.py",
        "project_id": PROJECT_ID,
        "kernel_profile": KERNEL_PROFILE,
        "mode": "shadow",
        "repo_commit_note": "not pinned inside bootstrap objects to avoid self-referential CID churn",
        "freeze_tag": FREEZE_TAG,
        "freeze_commit": run_git(["rev-parse", f"{FREEZE_TAG}^{{}}"]),
        "trust_anchor": trust_anchor,
        "genesis_root_cid": genesis["root_cid"],
        "current_root_cid": child["root_cid"],
        "objects": {
            "policy": policy_cid,
            "role_binding_owner_jin": role_cid,
            "genesis_batch": genesis_batch_cid,
            "genesis_root": genesis["root_cid"],
            "freeze_acceptance_claim": freeze_claim_cid,
            "freeze_acceptance_transition": transition_batch_cid,
            "current_root": child["root_cid"],
        },
        "object_count": len(store.objects),
        "reproduce": [
            "cd meta/ctl-dogfood",
            "uv run python scripts/verify.py",
            "uv run python scripts/bootstrap.py --force  # rebuild bootstrap snapshot from scratch",
        ],
    }
    write_json(DOGFOOD_ROOT / "refs" / "main.json", ref)
    write_json(DOGFOOD_ROOT / "manifests" / "bootstrap-2026-06-26.json", manifest)

    checked = ctl_ref.validate_chain(store, child["root_cid"], trust_anchor)
    ctl_ref.die_unless(checked["root_cid"] == child["root_cid"], "bootstrap replay mismatch")
    print(json.dumps({"status": "ok", "root_cid": child["root_cid"], "objects": len(store.objects)}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
