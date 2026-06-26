#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parents[1]
KERNEL_ROOT = REPO_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))

import ctl_ref  # noqa: E402


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


def main() -> int:
    store = load_store()
    ref = load_json(DOGFOOD_ROOT / "refs" / "main.json")
    manifest = load_json(DOGFOOD_ROOT / "manifests" / "bootstrap-2026-06-26.json")
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
    ctl_ref.die_unless(manifest["current_root_cid"] == ref["root_cid"], "manifest/ref root mismatch")
    ctl_ref.die_unless(manifest["genesis_root_cid"] == ref["genesis_root_cid"], "manifest/ref genesis mismatch")
    print(
        json.dumps(
            {
                "status": "ok",
                "project_id": ref["project_id"],
                "root_cid": ref["root_cid"],
                "genesis_root_cid": ref["genesis_root_cid"],
                "object_count": len(store.objects),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
