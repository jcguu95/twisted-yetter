#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parent
CTL_META_ROOT = Path(os.environ.get("CTL_META_ROOT", REPO_ROOT.parent / "ctl-meta")).resolve()
KERNEL_ROOT = CTL_META_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))

import ctl_ref  # noqa: E402


GRAPH_LOGICAL_ID = "claim:graph:computation-first-v1"


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


def current_graph() -> dict[str, Any]:
    ref = load_json(DOGFOOD_ROOT / "refs" / "main.json")
    store = load_store()
    trust_anchor = {
        "project_id": ref["project_id"],
        "kernel_profile": ref["kernel_profile"],
        "genesis_root_cid": ref["genesis_root_cid"],
    }
    state = ctl_ref.validate_chain(store, ref["root_cid"], trust_anchor)
    graph_cid = state["bindings"].get(GRAPH_LOGICAL_ID)
    ctl_ref.die_unless(graph_cid is not None, f"missing active graph binding: {GRAPH_LOGICAL_ID}")
    revision = store.resolve(graph_cid)
    payload = revision["payload"]
    return {
        "root_cid": state["root_cid"],
        "graph_cid": graph_cid,
        "graph_logical_id": GRAPH_LOGICAL_ID,
        "revision_created_at": revision["created_at"],
        "revision_parents": revision["parents"],
        "graph": payload,
    }


def compact_view(current: dict[str, Any]) -> dict[str, Any]:
    graph = current["graph"]
    nodes = {node["node_id"]: node for node in graph["nodes"]}
    active = graph.get("active", {})
    current_ids = active.get("current_node_ids", [])
    return {
        "root_cid": current["root_cid"],
        "graph_cid": current["graph_cid"],
        "graph_logical_id": current["graph_logical_id"],
        "revision_created_at": current["revision_created_at"],
        "revision_parents_hidden_by_default": len(current["revision_parents"]),
        "graph_identity": graph["graph_identity"],
        "priority_node_id": active.get("priority_node_id"),
        "current_node_ids": current_ids,
        "current_nodes": [
            {
                "node_id": node_id,
                "kind": nodes[node_id]["kind"],
                "goal": nodes[node_id]["goal"],
                "dependencies": nodes[node_id]["dependencies"],
                "expected_outputs": nodes[node_id]["expected_outputs"],
            }
            for node_id in current_ids
            if node_id in nodes
        ],
        "critical_path": graph["speed_policy"]["critical_path"],
        "invariants": graph["invariants"],
    }


def print_text(view: dict[str, Any]) -> None:
    identity = view["graph_identity"]
    print(f"Current graph: {identity['title']}")
    print(f"Version: {identity['version']}")
    print(f"Graph CID: {view['graph_cid']}")
    print(f"Root CID:  {view['root_cid']}")
    print(f"Priority node: {view.get('priority_node_id')}")
    print()
    print("Current nodes:")
    for node in view["current_nodes"]:
        print(f"- {node['node_id']} [{node['kind']}]")
        print(f"  goal: {node['goal']}")
        if node["dependencies"]:
            print(f"  deps: {', '.join(node['dependencies'])}")
        if node["expected_outputs"]:
            print(f"  outputs: {', '.join(node['expected_outputs'])}")
    print()
    print("Critical path:")
    for index, node_id in enumerate(view["critical_path"], 1):
        marker = " <= priority" if node_id == view.get("priority_node_id") else ""
        print(f"{index:02d}. {node_id}{marker}")
    print()
    print("Invariants:")
    for invariant in view["invariants"]:
        print(f"- {invariant}")
    print()
    print(
        "Older graph revisions are hidden by default. Use --json if an agent needs "
        "the exact current projection payload."
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Show the active CTL decision graph projection.")
    parser.add_argument("--json", action="store_true", help="print the compact current graph view as JSON")
    parser.add_argument("--full", action="store_true", help="print the full active graph payload as JSON")
    args = parser.parse_args()

    current = current_graph()
    if args.full:
        print(json.dumps(current, sort_keys=True, indent=2, ensure_ascii=False))
        return 0

    view = compact_view(current)
    if args.json:
        print(json.dumps(view, sort_keys=True, indent=2, ensure_ascii=False))
    else:
        print_text(view)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
