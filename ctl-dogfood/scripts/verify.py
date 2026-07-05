#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tarfile
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parent
CTL_META_ROOT = Path(os.environ.get("CTL_META_ROOT", REPO_ROOT.parent / "ctl-meta")).resolve()
KERNEL_ROOT = CTL_META_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))
sys.path.insert(0, str(DOGFOOD_ROOT / "scripts"))

import ctl_ref  # noqa: E402
from prose_policy import (  # noqa: E402
    ALLOWED_LEGACY_ARCHIVE_PATHS,
    ARCHIVE_ID as LEGACY_ARCHIVE_ID,
    PROSE_SUFFIXES,
    archive_member_refs_in_string,
    archive_path,
    is_allowed_loose_prose,
    is_under_generated_cache,
    is_under_git_dir,
    is_under_legacy_archives,
    manifest_path,
    raw_legacy_refs_in_string,
    repo_path,
    validate_archive_member_path,
)


LEGACY_ARCHIVE_DIR = REPO_ROOT / "legacy-archives"
LEGACY_ARCHIVE_PATH = archive_path(REPO_ROOT)
LEGACY_ARCHIVE_MANIFEST_PATH = manifest_path(REPO_ROOT)


def run_git(root: Path, args: list[str]) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


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
        new_cid = objects.get("graph_claim") or objects.get("claim")
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


def verify_manifest_archive_member_path(member_path: str) -> None:
    try:
        validate_archive_member_path(member_path)
    except ValueError as error:
        ctl_ref.die_unless(False, str(error))


def verify_legacy_archive_files() -> None:
    ctl_ref.die_unless(LEGACY_ARCHIVE_DIR.exists(), "legacy archive directory is missing")
    seen = []
    for path in sorted(LEGACY_ARCHIVE_DIR.rglob("*")):
        if not path.is_file():
            continue
        rel = repo_path(REPO_ROOT, path)
        seen.append(rel)
    unexpected = sorted(set(seen) - ALLOWED_LEGACY_ARCHIVE_PATHS)
    ctl_ref.die_unless(
        not unexpected,
        "legacy-archives may contain only the approved tar and manifest files: " + ", ".join(unexpected),
    )
    missing = sorted(ALLOWED_LEGACY_ARCHIVE_PATHS - set(seen))
    ctl_ref.die_unless(not missing, "legacy archive approved files missing: " + ", ".join(missing))

    manifest = load_json(LEGACY_ARCHIVE_MANIFEST_PATH)
    ctl_ref.die_unless(
        manifest.get("schema") == "twisted-yetter/legacy-prose-archive-manifest/1",
        "bad legacy prose archive manifest schema",
    )
    ctl_ref.die_unless(manifest.get("archive_id") == LEGACY_ARCHIVE_ID, "legacy prose archive id mismatch")
    ctl_ref.die_unless(
        manifest.get("archive_path") == LEGACY_ARCHIVE_PATH.relative_to(REPO_ROOT).as_posix(),
        "legacy prose archive path mismatch",
    )
    ctl_ref.die_unless(
        manifest.get("manifest_path") == LEGACY_ARCHIVE_MANIFEST_PATH.relative_to(REPO_ROOT).as_posix(),
        "legacy prose manifest path mismatch",
    )
    ctl_ref.die_unless(
        file_sha256(LEGACY_ARCHIVE_PATH) == manifest.get("archive_sha256"),
        "legacy prose archive sha256 mismatch",
    )
    files = manifest.get("files")
    ctl_ref.die_unless(isinstance(files, list), "legacy prose manifest files must be array")
    ctl_ref.die_unless(manifest.get("file_count") == len(files), "legacy prose manifest file_count mismatch")

    expected = {}
    for item in files:
        ctl_ref.die_unless(isinstance(item, dict), "legacy prose manifest file item must be object")
        member_path = item.get("archive_member_path")
        original_path = item.get("original_repo_path")
        verify_manifest_archive_member_path(member_path)
        verify_manifest_archive_member_path(original_path)
        ctl_ref.die_unless(member_path == original_path, "legacy prose archive member/original path mismatch")
        ctl_ref.die_unless(member_path not in expected, f"duplicate legacy archive member: {member_path}")
        ctl_ref.die_unless(isinstance(item.get("sha256"), str), f"missing legacy archive sha256: {member_path}")
        ctl_ref.die_unless(isinstance(item.get("size_bytes"), int), f"missing legacy archive size: {member_path}")
        expected[member_path] = item

    with tarfile.open(LEGACY_ARCHIVE_PATH, "r") as archive:
        members = sorted(
            (member for member in archive.getmembers() if member.isfile()),
            key=lambda member: member.name,
        )
        names = [member.name for member in members]
        ctl_ref.die_unless(names == sorted(expected), "legacy archive member list does not match manifest")
        for member in members:
            verify_manifest_archive_member_path(member.name)
            ctl_ref.die_unless(member.mode & 0o222 == 0, f"legacy archive member is writable: {member.name}")
            extracted = archive.extractfile(member)
            ctl_ref.die_unless(extracted is not None, f"could not read legacy archive member: {member.name}")
            data = extracted.read()
            item = expected[member.name]
            ctl_ref.die_unless(sha256_bytes(data) == item["sha256"], f"legacy archive member hash mismatch: {member.name}")
            ctl_ref.die_unless(len(data) == item["size_bytes"], f"legacy archive member size mismatch: {member.name}")


def iter_json_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        out: list[str] = []
        for item in value:
            out.extend(iter_json_strings(item))
        return out
    if isinstance(value, dict):
        out = []
        for item in value.values():
            out.extend(iter_json_strings(item))
        return out
    return []


def verify_active_json_has_no_raw_legacy_prose_locators() -> None:
    manifest = load_json(LEGACY_ARCHIVE_MANIFEST_PATH)
    manifest_files = manifest.get("files")
    ctl_ref.die_unless(isinstance(manifest_files, list), "legacy prose manifest files must be array")
    archive_members = {
        validate_archive_member_path(item.get("archive_member_path"))
        for item in manifest_files
        if isinstance(item, dict)
    }
    violations = []
    for root in (REPO_ROOT / "experiments" / "inputs", REPO_ROOT / "experiments" / "results"):
        if not root.exists():
            continue
        for path in sorted(root.rglob("*.json")):
            payload = json.loads(path.read_text())
            raw_locators = sorted(
                {
                    raw_ref
                    for item in iter_json_strings(payload)
                    for raw_ref in raw_legacy_refs_in_string(item)
                }
            )
            archive_refs = sorted(
                {
                    member_ref
                    for item in iter_json_strings(payload)
                    for member_ref in archive_member_refs_in_string(item)
                }
            )
            missing_archive_refs = [
                member_ref for member_ref in archive_refs if member_ref not in archive_members
            ]
            if raw_locators or missing_archive_refs:
                violations.append(
                    {
                        "path": repo_path(REPO_ROOT, path),
                        "missing_archive_refs": missing_archive_refs,
                        "raw_locators": raw_locators,
                    }
                )
    ctl_ref.die_unless(
        not violations,
        "active experiment JSON contains raw legacy prose locators or archive refs "
        "that are missing from the legacy prose manifest; use "
        "legacy-archives/prose-corpus-2026-07-05.manifest.json#archive_member_path=... "
        "with an existing manifest member: "
        + json.dumps(violations, sort_keys=True),
    )


def verify_no_unapproved_prose_files() -> None:
    violations = []
    for path in sorted(REPO_ROOT.rglob("*")):
        if not path.is_file():
            continue
        if is_under_git_dir(REPO_ROOT, path) or is_under_generated_cache(REPO_ROOT, path):
            continue
        if path.suffix.lower() not in PROSE_SUFFIXES:
            continue
        rel = repo_path(REPO_ROOT, path)
        if is_under_legacy_archives(REPO_ROOT, path) and rel in ALLOWED_LEGACY_ARCHIVE_PATHS:
            continue
        if is_allowed_loose_prose(rel):
            continue
        violations.append(rel)
    if violations:
        message = (
            "unapproved prose files found; experiment history, lab notes, wiki, "
            "references, roadmaps, and run transcripts must be CTL/JSON artifacts "
            "or legacy archive members, not loose prose files: "
            + ", ".join(violations)
        )
        ctl_ref.die_unless(False, message)


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
    verify_legacy_archive_files()
    verify_active_json_has_no_raw_legacy_prose_locators()
    verify_no_unapproved_prose_files()
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
