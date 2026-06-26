#!/usr/bin/env python3
from __future__ import annotations

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


def run_git(root: Path, args: list[str]) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def load_store() -> ctl_ref.Store:
    store = ctl_ref.Store()
    object_dir = DOGFOOD_ROOT / "objects" / "ctlobj-sha256"
    for path in sorted(object_dir.glob("*.json")):
        obj = load_json(path)
        cid = store.add(obj)
        expected = "ctlobj-sha256:" + path.stem
        ctl_ref.die_unless(cid == expected, f"object filename CID mismatch: {path}")
    return store


def load_manifests() -> list[dict[str, Any]]:
    manifests = []
    for path in sorted((DOGFOOD_ROOT / "manifests").glob("*.json")):
        manifests.append(load_json(path))
    return manifests


def root_chain_cids(store: ctl_ref.Store, target_root_cid: str) -> set[str]:
    out: set[str] = set()
    cursor: str | None = target_root_cid
    while cursor is not None:
        ctl_ref.die_unless(cursor not in out, "root parent cycle in manifest reachability check")
        out.add(cursor)
        root = store.resolve(cursor)
        ctl_ref.validate_root(root)
        cursor = root["parent"]
    return out


def verify_manifest_reachability(store: ctl_ref.Store, manifests: list[dict[str, Any]], ref: dict[str, Any]) -> None:
    chain = root_chain_cids(store, ref["root_cid"])
    for manifest in manifests:
        if "genesis_root_cid" in manifest:
            ctl_ref.die_unless(manifest["genesis_root_cid"] == ref["genesis_root_cid"], "manifest genesis mismatch")
        root_cid = manifest.get("current_root_cid")
        if root_cid is not None:
            ctl_ref.die_unless(ctl_ref.is_cid(root_cid), "bad manifest current root")
            ctl_ref.die_unless(root_cid in chain, "manifest root is not reachable from refs/main")
        objects = manifest.get("objects", {})
        if objects:
            ctl_ref.die_unless(isinstance(objects, dict), "manifest objects must be object")
            for cid in objects.values():
                ctl_ref.die_unless(ctl_ref.is_cid(cid), "bad manifest object cid")
                store.resolve(cid)


def verify_admission_fast_forward(store: ctl_ref.Store, manifests: list[dict[str, Any]]) -> None:
    for manifest in manifests:
        if manifest.get("schema") != "ctl-dogfood/admission-manifest/1":
            continue
        logical_id = manifest.get("logical_id")
        objects = manifest.get("objects", {})
        new_cid = objects.get("graph_claim")
        parent_root_cid = manifest.get("parent_root_cid")
        if logical_id is None or new_cid is None or parent_root_cid is None:
            continue
        parent_root = store.resolve(parent_root_cid)
        ctl_ref.validate_root(parent_root)
        old_cid = parent_root["bindings"].get(logical_id)
        if old_cid is None:
            continue
        new_rev = store.resolve(new_cid)
        ctl_ref.validate_revision_envelope(store, new_cid, new_rev)
        ctl_ref.die_unless(old_cid in new_rev["parents"], "admission revision did not parent prior active revision")


def verify_decision_graph_payload(payload: dict[str, Any]) -> None:
    if payload.get("schema") != "twisted-yetter/decision-graph/1":
        return
    ctl_ref.die_unless(isinstance(payload.get("nodes"), list), "graph nodes must be array")
    ctl_ref.die_unless(isinstance(payload.get("edges"), list), "graph edges must be array")
    nodes = []
    for node in payload["nodes"]:
        ctl_ref.die_unless(isinstance(node, dict), "graph node must be object")
        node_id = node.get("node_id")
        ctl_ref.die_unless(ctl_ref.is_id(node_id), "bad graph node_id")
        nodes.append(node_id)
    ctl_ref.die_unless(len(nodes) == len(set(nodes)), "duplicate graph node_id")
    node_set = set(nodes)
    for node in payload["nodes"]:
        dependencies = node.get("dependencies", [])
        ctl_ref.die_unless(isinstance(dependencies, list), "graph dependencies must be array")
        for dependency in dependencies:
            ctl_ref.die_unless(dependency in node_set, "graph dependency missing node")
    edge_ids = []
    for edge in payload["edges"]:
        ctl_ref.die_unless(isinstance(edge, dict), "graph edge must be object")
        edge_id = edge.get("edge_id")
        ctl_ref.die_unless(ctl_ref.is_id(edge_id), "bad graph edge_id")
        edge_ids.append(edge_id)
        ctl_ref.die_unless(edge.get("from") in node_set, "graph edge from missing node")
        ctl_ref.die_unless(edge.get("to") in node_set, "graph edge to missing node")
    ctl_ref.die_unless(len(edge_ids) == len(set(edge_ids)), "duplicate graph edge_id")
    active = payload.get("active", {})
    ctl_ref.die_unless(isinstance(active, dict), "graph active must be object")
    for key in ["entry_node_id"]:
        ctl_ref.die_unless(active.get(key) in node_set, f"graph active {key} missing node")
    for key in ["current_node_ids", "terminal_node_ids"]:
        ids = active.get(key, [])
        ctl_ref.die_unless(isinstance(ids, list), f"graph active {key} must be array")
        for node_id in ids:
            ctl_ref.die_unless(node_id in node_set, f"graph active {key} missing node")
    speed_policy = payload.get("speed_policy", {})
    if speed_policy:
        ctl_ref.die_unless(isinstance(speed_policy, dict), "graph speed_policy must be object")
        for key in ["critical_path", "parallel_after_entry"]:
            ids = speed_policy.get(key, [])
            ctl_ref.die_unless(isinstance(ids, list), f"graph speed_policy {key} must be array")
            for node_id in ids:
                ctl_ref.die_unless(node_id in node_set, f"graph speed_policy {key} missing node")


def verify_active_decision_graphs(store: ctl_ref.Store, state: dict[str, Any]) -> None:
    for logical_id, cid in state["bindings"].items():
        if not logical_id.startswith("claim:graph:"):
            continue
        rev = store.resolve(cid)
        ctl_ref.validate_revision_envelope(store, cid, rev)
        verify_decision_graph_payload(rev["payload"])


def main() -> int:
    store = load_store()
    ref = load_json(DOGFOOD_ROOT / "refs" / "main.json")
    bootstrap = load_json(DOGFOOD_ROOT / "manifests" / "bootstrap-2026-06-26.json")
    manifests = load_manifests()
    provider = bootstrap["provider"]
    ctl_ref.die_unless(run_git(CTL_META_ROOT, ["rev-parse", "HEAD"]) == provider["ctl_meta_commit"], "ctl-meta HEAD mismatch")
    ctl_ref.die_unless(
        run_git(CTL_META_ROOT, ["rev-parse", "ctl-kernel-v0.1.1-experimental^{}"])
        == provider["ctl_kernel_freeze_commit"],
        "ctl-kernel freeze tag mismatch",
    )
    ctl_ref.die_unless(run_git(CTL_META_ROOT, ["status", "--short"]) == provider["ctl_meta_status_short"], "ctl-meta dirty status mismatch")
    ctl_ref.check_keys(
        ref,
        {
            "schema",
            "name",
            "project_id",
            "kernel_profile",
            "root_cid",
            "genesis_root_cid",
            "transition_cid",
            "updated_at",
            "updated_by",
        },
    )
    ctl_ref.die_unless(ref["schema"] == "ctl-dogfood/ref/1", "bad ref schema")
    ctl_ref.die_unless(ref["name"] == "refs/main", "bad ref name")
    trust_anchor = {
        "project_id": ref["project_id"],
        "kernel_profile": ref["kernel_profile"],
        "genesis_root_cid": ref["genesis_root_cid"],
    }
    state = ctl_ref.validate_chain(store, ref["root_cid"], trust_anchor)
    ctl_ref.die_unless(state["root_cid"] == ref["root_cid"], "ref root replay mismatch")
    verify_manifest_reachability(store, manifests, ref)
    verify_admission_fast_forward(store, manifests)
    verify_active_decision_graphs(store, state)
    ctl_ref.die_unless(bootstrap["genesis_root_cid"] == ref["genesis_root_cid"], "manifest/ref genesis mismatch")
    current_manifests = [manifest for manifest in manifests if manifest.get("current_root_cid") == ref["root_cid"]]
    ctl_ref.die_unless(current_manifests, "no manifest pins current ref root")
    print(
        json.dumps(
            {
                "status": "ok",
                "project_id": ref["project_id"],
                "root_cid": ref["root_cid"],
                "genesis_root_cid": ref["genesis_root_cid"],
                "object_count": len(store.objects),
                "current_manifest_count": len(current_manifests),
                "manifest_count": len(manifests),
                "ctl_meta_commit": bootstrap["provider"]["ctl_meta_commit"],
                "ctl_kernel_freeze_commit": bootstrap["provider"]["ctl_kernel_freeze_commit"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
