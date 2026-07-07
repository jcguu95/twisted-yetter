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


KERNEL_PROFILE = "ctl-kernel/1"
DEFAULT_ACTOR_ID = "actor:jin"
DEFAULT_SUBMITTED_BY = "actor:codex"


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def write_json(path: Path, value: Any, *, replace: bool = False) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n"
    if path.exists() and not replace:
        old = load_json(path)
        ctl_ref.die_unless(ctl_ref.canonical_bytes(old) == ctl_ref.canonical_bytes(value), f"path exists: {path}")
        return
    path.write_text(text)


def cid_path(dogfood_root: Path, cid: str) -> Path:
    prefix, digest = cid.split(":", 1)
    ctl_ref.die_unless(prefix == "ctlobj-sha256", "unexpected CID prefix")
    return dogfood_root / "objects" / "ctlobj-sha256" / f"{digest}.json"


def load_ref(dogfood_root: Path) -> dict[str, Any]:
    ref = load_json(dogfood_root / "refs" / "main.json")
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
    return ref


def trust_anchor_from_ref(ref: dict[str, Any]) -> dict[str, str]:
    return {
        "project_id": ref["project_id"],
        "kernel_profile": ref["kernel_profile"],
        "genesis_root_cid": ref["genesis_root_cid"],
    }


def load_store_from_roots(dogfood_roots: list[Path]) -> ctl_ref.Store:
    store = ctl_ref.Store()
    seen_roots: set[Path] = set()
    for dogfood_root in dogfood_roots:
        root = dogfood_root.resolve()
        if root in seen_roots:
            continue
        seen_roots.add(root)
        object_dir = root / "objects" / "ctlobj-sha256"
        ctl_ref.die_unless(object_dir.exists(), f"object directory does not exist: {object_dir}")
        for path in sorted(object_dir.glob("*.json")):
            obj = load_json(path)
            cid = store.add(obj)
            expected = "ctlobj-sha256:" + path.stem
            ctl_ref.die_unless(cid == expected, f"object filename CID mismatch: {path}")
    return store


def write_all_objects(dogfood_root: Path, store: ctl_ref.Store) -> None:
    for cid in sorted(store.objects):
        path = cid_path(dogfood_root, cid)
        obj = store.resolve(cid)
        if path.exists():
            old = load_json(path)
            ctl_ref.die_unless(ctl_ref.canonical_bytes(old) == ctl_ref.canonical_bytes(obj), f"object mismatch: {cid}")
            continue
        write_json(path, obj)


def root_lineage(store: ctl_ref.Store, root_cid: str) -> list[str]:
    lineage: list[str] = []
    seen: set[str] = set()
    cursor: str | None = root_cid
    while cursor is not None:
        ctl_ref.die_unless(cursor not in seen, "root parent cycle")
        seen.add(cursor)
        root = store.resolve(cursor)
        ctl_ref.validate_root(root)
        lineage.append(cursor)
        cursor = root["parent"]
    return lineage


def find_lca(store: ctl_ref.Store, left_root: str, right_root: str) -> str:
    right_ancestors = set(root_lineage(store, right_root))
    for cid in root_lineage(store, left_root):
        if cid in right_ancestors:
            return cid
    raise ctl_ref.InvalidHistory("roots do not share an ancestor")


def roots_after_base(store: ctl_ref.Store, base_root: str, head_root: str) -> list[str]:
    lineage = root_lineage(store, head_root)
    ctl_ref.die_unless(base_root in lineage, "base root is not an ancestor of head")
    return list(reversed(lineage[: lineage.index(base_root)]))


def transition_cids_after_base(store: ctl_ref.Store, base_root: str, head_root: str) -> list[str]:
    cids: list[str] = []
    for root_cid in roots_after_base(store, base_root, head_root):
        root = store.resolve(root_cid)
        cids.append(root["transition"])
    return cids


def expected_from_bindings(bindings: dict[str, str], logical_id: str) -> dict[str, str]:
    cid = bindings.get(logical_id)
    if cid is None:
        return {"state": "absent"}
    return {"state": "bound", "cid": cid}


def revision_summary(store: ctl_ref.Store, binding_state: dict[str, str]) -> dict[str, Any]:
    if binding_state["state"] == "absent":
        return {"state": "absent"}
    rev = store.resolve(binding_state["cid"])
    return {
        "state": "bound",
        "cid": binding_state["cid"],
        "logical_id": rev["logical_id"],
        "revision_kind": rev["revision_kind"],
        "payload_profile": rev["payload_profile"],
        "parents": rev["parents"],
    }


def payload_for_state(store: ctl_ref.Store, binding_state: dict[str, str]) -> Any:
    if binding_state["state"] == "absent":
        return None
    return store.resolve(binding_state["cid"])["payload"]


def payload_diff(store: ctl_ref.Store, main_state: dict[str, str], incoming_state: dict[str, str]) -> dict[str, Any]:
    left = payload_for_state(store, main_state)
    right = payload_for_state(store, incoming_state)
    if left == right:
        return {"status": "same"}
    if not isinstance(left, dict) or not isinstance(right, dict):
        return {"status": "changed", "main": left, "incoming": right}
    left_keys = set(left)
    right_keys = set(right)
    changed = {
        key: {"main": left[key], "incoming": right[key]}
        for key in sorted(left_keys & right_keys, key=lambda value: value.encode("utf-8"))
        if left[key] != right[key]
    }
    return {
        "status": "changed",
        "only_main": {key: left[key] for key in sorted(left_keys - right_keys, key=lambda value: value.encode("utf-8"))},
        "only_incoming": {
            key: right[key] for key in sorted(right_keys - left_keys, key=lambda value: value.encode("utf-8"))
        },
        "changed": changed,
    }


def state_key(state: dict[str, str]) -> tuple[str, str | None]:
    if state["state"] == "absent":
        return ("absent", None)
    return ("bound", state["cid"])


def op_result_state(op: dict[str, Any]) -> dict[str, str]:
    if op["op"] == "remove":
        return {"state": "absent"}
    return {"state": "bound", "cid": op["new_cid"]}


def collect_incoming_ops(
    store: ctl_ref.Store,
    base_state: dict[str, Any],
    incoming_transition_cids: list[str],
) -> tuple[list[dict[str, Any]], dict[str, list[dict[str, str]]]]:
    paths: dict[str, list[dict[str, str]]] = {}
    records: list[dict[str, Any]] = []
    for transition_cid in incoming_transition_cids:
        batch = store.resolve(transition_cid)
        for op in batch["binding_ops"]:
            logical_id = op["logical_id"]
            if logical_id not in paths:
                paths[logical_id] = [expected_from_bindings(base_state["bindings"], logical_id)]
            expected = op["expected"]
            ctl_ref.die_unless(
                state_key(paths[logical_id][-1]) == state_key(expected),
                f"incoming branch path mismatch for {logical_id}",
            )
            result = op_result_state(op)
            before_index = len(paths[logical_id]) - 1
            paths[logical_id].append(result)
            records.append(
                {
                    "transition_cid": transition_cid,
                    "logical_id": logical_id,
                    "op": op,
                    "expected": expected,
                    "result": result,
                    "before_index": before_index,
                    "after_index": before_index + 1,
                }
            )
    return records, paths


def state_appears_at_or_after(
    path: list[dict[str, str]],
    state: dict[str, str],
    start_index: int,
) -> bool:
    key = state_key(state)
    return any(state_key(item) == key for item in path[start_index:])


def classify_op(
    bindings: dict[str, str],
    op_record: dict[str, Any],
    paths: dict[str, list[dict[str, str]]],
) -> tuple[str, str, dict[str, str]]:
    logical_id = op_record["logical_id"]
    current = expected_from_bindings(bindings, logical_id)
    expected = op_record["expected"]
    result = op_record["result"]
    if state_key(current) == state_key(expected):
        return "auto-admit", "expected-matches-current", current
    if state_key(current) == state_key(result):
        return "already-present", "op-result-present", current
    if state_appears_at_or_after(paths[logical_id], current, op_record["after_index"]):
        return "already-present", "main-is-ahead-on-incoming-path", current
    return "conflict", "main-current-not-on-incoming-path", current


def conflict_payload_report(store: ctl_ref.Store, current: dict[str, str], incoming: dict[str, str]) -> dict[str, Any] | None:
    if current["state"] != "bound" or incoming["state"] != "bound":
        return None
    if current["cid"] == incoming["cid"]:
        return None
    return payload_diff(store, current, incoming)


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


def admission_batch(
    project_id: str,
    parent_root: str,
    recorded: list[str],
    binding_ops: list[dict[str, Any]],
    evidence: list[dict[str, Any]],
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
        "evidence": ctl_ref.sort_objects(evidence),
        "principal_claim": {"actor_id": actor_id, "role_bindings": ctl_ref.sort_scalars(principal_roles)},
        "submitted_by": {"actor_id": submitted_by},
        "admitted_at": admitted_at,
    }


def filter_evidence(
    batch: dict[str, Any],
    recorded: list[str],
    binding_ops: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    recorded_set = set(recorded)
    binding_ids = {op["logical_id"] for op in binding_ops}
    out = []
    for entry in batch["evidence"]:
        target = entry["target"]
        if target["kind"] == "recorded_revision" and target["cid"] in recorded_set:
            out.append(entry)
        elif target["kind"] == "binding_op" and target["logical_id"] in binding_ids:
            out.append(entry)
    return ctl_ref.sort_objects(out)


def build_merge_context(
    store: ctl_ref.Store,
    main_root: str,
    incoming_root: str,
    trust_anchor: dict[str, str],
    base_root: str | None,
) -> dict[str, Any]:
    main_state = ctl_ref.validate_chain(store, main_root, trust_anchor)
    incoming_state = ctl_ref.validate_chain(store, incoming_root, trust_anchor)
    if base_root is None:
        base_root = find_lca(store, main_root, incoming_root)
    ctl_ref.die_unless(base_root in root_lineage(store, main_root), "base root is not an ancestor of main")
    ctl_ref.die_unless(base_root in root_lineage(store, incoming_root), "base root is not an ancestor of incoming")
    base_state = ctl_ref.validate_chain(store, base_root, trust_anchor)
    incoming_transitions = transition_cids_after_base(store, base_root, incoming_root)
    op_records, paths = collect_incoming_ops(store, base_state, incoming_transitions)
    return {
        "base_root": base_root,
        "base_state": base_state,
        "main_state": main_state,
        "incoming_state": incoming_state,
        "incoming_transition_cids": incoming_transitions,
        "op_records": op_records,
        "paths": paths,
    }


def summarize_logical_ids(
    store: ctl_ref.Store,
    main_state: dict[str, Any],
    paths: dict[str, list[dict[str, str]]],
    items: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    by_logical_id: dict[str, list[dict[str, Any]]] = {}
    for item in items:
        by_logical_id.setdefault(item["logical_id"], []).append(item)

    out: list[dict[str, Any]] = []
    for logical_id in sorted(paths, key=lambda value: value.encode("utf-8")):
        logical_items = by_logical_id.get(logical_id, [])
        statuses = {item["status"] for item in logical_items}
        if "conflict" in statuses:
            status = "conflict"
        elif "auto-admit" in statuses:
            status = "auto-admit"
        else:
            status = "already-present"
        base = paths[logical_id][0]
        incoming = paths[logical_id][-1]
        main_current = expected_from_bindings(main_state["bindings"], logical_id)
        entry: dict[str, Any] = {
            "logical_id": logical_id,
            "status": status,
            "base": revision_summary(store, base),
            "main": revision_summary(store, main_current),
            "incoming": revision_summary(store, incoming),
            "steps": [
                {
                    "status": item["status"],
                    "reason": item["reason"],
                    "transition_cid": item["transition_cid"],
                    "op": item["op"],
                }
                for item in logical_items
            ],
        }
        if status == "conflict":
            entry["payload_diff"] = conflict_payload_report(store, main_current, incoming)
        out.append(entry)
    return out


def report_counts(items: list[dict[str, Any]]) -> dict[str, int]:
    counts = {"auto-admit": 0, "already-present": 0, "conflict": 0}
    for item in items:
        counts[item["status"]] += 1
    return counts


def merge_model_report() -> dict[str, Any]:
    return {
        "status": "dogfood",
        "root_strategy": "single-parent-transplant",
        "refs_main_resolution": "write-new-child-root",
        "multi_parent_roots": "unsupported",
        "payload_dependency_ordering": "unsupported-profile-specific-backlog",
    }


def conflict_entry(
    store: ctl_ref.Store,
    logical_id: str,
    transition_cid: str,
    reason: str,
    incoming_expected: dict[str, str],
    incoming_result: dict[str, str],
    main_current: dict[str, str],
) -> dict[str, Any]:
    out: dict[str, Any] = {
        "logical_id": logical_id,
        "transition_cid": transition_cid,
        "reason": reason,
        "incoming_expected": incoming_expected,
        "incoming_result": incoming_result,
        "main_current": main_current,
        "main_revision": revision_summary(store, main_current),
        "incoming_revision": revision_summary(store, incoming_result),
    }
    payload_report = conflict_payload_report(store, main_current, incoming_result)
    if payload_report is not None:
        out["payload_diff"] = payload_report
    return out


def preflight_conflicts(store: ctl_ref.Store, ctx: dict[str, Any]) -> list[dict[str, Any]]:
    bindings = dict(ctx["main_state"]["bindings"])
    conflicts: list[dict[str, Any]] = []
    for op_record in ctx["op_records"]:
        status, reason, current = classify_op(bindings, op_record, ctx["paths"])
        if status == "conflict":
            conflicts.append(
                conflict_entry(
                    store,
                    op_record["logical_id"],
                    op_record["transition_cid"],
                    reason,
                    op_record["expected"],
                    op_record["result"],
                    current,
                )
            )
        elif status == "auto-admit":
            op = op_record["op"]
            if op["op"] == "set":
                bindings[op["logical_id"]] = op["new_cid"]
            else:
                bindings.pop(op["logical_id"], None)
    return conflicts


def build_merge_preview(
    store: ctl_ref.Store,
    main_root: str,
    incoming_root: str,
    trust_anchor: dict[str, str],
    base_root: str | None = None,
) -> dict[str, Any]:
    ctx = build_merge_context(store, main_root, incoming_root, trust_anchor, base_root)
    preview_bindings = dict(ctx["main_state"]["bindings"])
    items: list[dict[str, Any]] = []

    for op_record in ctx["op_records"]:
        status, reason, current = classify_op(preview_bindings, op_record, ctx["paths"])
        op = op_record["op"]
        item = {
            "status": status,
            "reason": reason,
            "logical_id": op_record["logical_id"],
            "transition_cid": op_record["transition_cid"],
            "op": op["op"],
            "incoming_expected": op["expected"],
            "incoming_result": op_record["result"],
            "main_current": current,
        }
        if op["op"] == "set":
            item["incoming_new_cid"] = op["new_cid"]
        if status == "conflict":
            payload_report = conflict_payload_report(store, current, op_record["result"])
            if payload_report is not None:
                item["payload_diff"] = payload_report
        items.append(item)
        if status == "auto-admit":
            if op["op"] == "set":
                preview_bindings[op["logical_id"]] = op["new_cid"]
            else:
                preview_bindings.pop(op["logical_id"], None)

    recorded_items: list[dict[str, str]] = []
    preview_recorded = set(ctx["main_state"]["recorded"])
    for transition_cid in ctx["incoming_transition_cids"]:
        batch = store.resolve(transition_cid)
        for cid in batch["recorded_revisions"]:
            if cid in preview_recorded:
                recorded_items.append({"status": "already-recorded", "transition_cid": transition_cid, "cid": cid})
            else:
                recorded_items.append({"status": "record", "transition_cid": transition_cid, "cid": cid})
                preview_recorded.add(cid)

    conflicts = [item for item in items if item["status"] == "conflict"]
    return {
        "status": "conflict" if conflicts else "ok",
        "merge_model": merge_model_report(),
        "base_root_cid": ctx["base_root"],
        "main_root_cid": ctx["main_state"]["root_cid"],
        "incoming_root_cid": ctx["incoming_state"]["root_cid"],
        "incoming_transition_cids": ctx["incoming_transition_cids"],
        "summary": report_counts(items),
        "logical_ids": summarize_logical_ids(store, ctx["main_state"], ctx["paths"], items),
        "items": items,
        "recorded_items": recorded_items,
    }


def manifest_reachability_warnings(
    store: ctl_ref.Store,
    target_root: str,
    incoming_store_root: Path,
) -> list[dict[str, Any]]:
    target_reachable = set(root_lineage(store, target_root))
    manifest_dir = incoming_store_root / "manifests"
    warnings: list[dict[str, Any]] = []
    if not manifest_dir.exists():
        return warnings
    for path in sorted(manifest_dir.glob("*.json")):
        rel = path.relative_to(incoming_store_root).as_posix()
        try:
            manifest = load_json(path)
        except Exception as exc:  # noqa: BLE001 - preview should report local sidecar problems.
            warnings.append(
                {
                    "code": "incoming_manifest_unreadable",
                    "path": rel,
                    "message": f"incoming manifest could not be read structurally: {exc}",
                }
            )
            continue
        current_root = manifest.get("current_root_cid") if isinstance(manifest, dict) else None
        if current_root is None:
            continue
        if not ctl_ref.is_cid(current_root):
            warnings.append(
                {
                    "code": "incoming_manifest_bad_current_root",
                    "path": rel,
                    "current_root_cid": current_root,
                    "message": "incoming manifest current_root_cid is not a CTL CID",
                }
            )
            continue
        if current_root not in target_reachable:
            warnings.append(
                {
                    "code": "incoming_manifest_branch_local",
                    "path": rel,
                    "current_root_cid": current_root,
                    "message": (
                        "incoming manifest points at a branch-local root; after transplant the target "
                        "merge manifest is the canonical final sidecar"
                    ),
                    "operator_choices": [
                        "keep as historical incoming-branch metadata outside the target current-manifest set",
                        "archive it outside the target merge commit",
                        "omit it from the target merge commit",
                    ],
                }
            )
    return warnings


def build_store_merge_preview(
    main_store_root: Path,
    incoming_store_root: Path,
    *,
    main_root: str | None = None,
    incoming_root: str | None = None,
    base_root: str | None = None,
) -> dict[str, Any]:
    main_ref = load_ref(main_store_root)
    incoming_ref = load_ref(incoming_store_root)
    resolved_main_root = main_root or main_ref["root_cid"]
    resolved_incoming_root = incoming_root or incoming_ref["root_cid"]
    store = load_store_from_roots([main_store_root, incoming_store_root])
    report = build_merge_preview(
        store,
        resolved_main_root,
        resolved_incoming_root,
        trust_anchor_from_ref(main_ref),
        base_root,
    )
    report["warnings"] = manifest_reachability_warnings(store, resolved_main_root, incoming_store_root)
    return report


def has_transplant_work(report: dict[str, Any]) -> bool:
    summary = report.get("summary", {})
    if summary.get("auto-admit", 0) > 0:
        return True
    return any(item["status"] == "record" for item in report.get("recorded_items", []))


def transplant_command(
    incoming_store_root: Path,
    expected_root: str,
    *,
    auto_only: bool = False,
) -> str:
    parts = [
        "python3 scripts/ctl_merge.py transplant-revisions",
        f"--incoming-store-root {incoming_store_root}",
        f"--expected-root {expected_root}",
        "--admitted-at <UTC>",
    ]
    if auto_only:
        parts.append("--auto-only")
    parts.append("--format text")
    return " ".join(parts)


def build_runbook(
    main_store_root: Path,
    incoming_store_root: Path,
    *,
    main_root: str | None = None,
    incoming_root: str | None = None,
    base_root: str | None = None,
) -> dict[str, Any]:
    preview = build_store_merge_preview(
        main_store_root,
        incoming_store_root,
        main_root=main_root,
        incoming_root=incoming_root,
        base_root=base_root,
    )
    expected_root = preview["main_root_cid"]
    summary = preview.get("summary", {})
    blocked = ctl_ref.sort_scalars(
        [item["logical_id"] for item in preview.get("logical_ids", []) if item["status"] == "conflict"]
    )
    commands: list[str] = []
    if preview["status"] == "ok":
        kind = "full-transplant" if has_transplant_work(preview) else "noop"
        if kind == "full-transplant":
            commands.append(transplant_command(incoming_store_root, expected_root))
    elif summary.get("auto-admit", 0) > 0 and summary.get("conflict", 0) > 0:
        kind = "partial-auto-only"
        commands.append(transplant_command(incoming_store_root, expected_root, auto_only=True))
    else:
        kind = "blocked-conflict"

    return {
        "status": "ok",
        "plan": {
            "kind": kind,
            "writes_state": False,
            "commands": commands,
            "verify_command": "python3 scripts/verify.py",
            "warnings": preview.get("warnings", []),
            "blocked_logical_ids": blocked,
            "commit_checklist": ["refs/main.json", "objects/ctlobj-sha256/*.json", "manifests/*.json"],
        },
        "merge_preview": preview,
    }


def build_manifest_plan(
    main_store_root: Path,
    incoming_store_root: Path,
    *,
    main_root: str | None = None,
) -> dict[str, Any]:
    main_ref = load_ref(main_store_root)
    resolved_main_root = main_root or main_ref["root_cid"]
    store = load_store_from_roots([main_store_root, incoming_store_root])
    target_reachable = set(root_lineage(store, resolved_main_root))
    manifest_dir = incoming_store_root / "manifests"
    items: list[dict[str, Any]] = []
    if manifest_dir.exists():
        for path in sorted(manifest_dir.glob("*.json")):
            rel = path.relative_to(incoming_store_root).as_posix()
            try:
                manifest = load_json(path)
            except Exception as exc:  # noqa: BLE001 - manifest-plan is a sidecar inspection tool.
                items.append(
                    {
                        "path": rel,
                        "classification": "unreadable",
                        "recommended_action": "inspect",
                        "message": f"manifest could not be read structurally: {exc}",
                    }
                )
                continue
            current_root = manifest.get("current_root_cid") if isinstance(manifest, dict) else None
            if current_root is None:
                items.append(
                    {
                        "path": rel,
                        "classification": "reachable-from-target",
                        "recommended_action": "keep-historical",
                        "message": "manifest has no current_root_cid to classify",
                    }
                )
            elif not ctl_ref.is_cid(current_root):
                items.append(
                    {
                        "path": rel,
                        "classification": "bad-current-root",
                        "recommended_action": "inspect",
                        "current_root_cid": current_root,
                        "message": "manifest current_root_cid is not a CTL CID",
                    }
                )
            elif current_root in target_reachable:
                items.append(
                    {
                        "path": rel,
                        "classification": "reachable-from-target",
                        "recommended_action": "keep-historical",
                        "current_root_cid": current_root,
                        "message": "manifest current_root_cid is reachable from target",
                    }
                )
            else:
                items.append(
                    {
                        "path": rel,
                        "classification": "branch-local",
                        "recommended_action": "omit-from-target-merge",
                        "current_root_cid": current_root,
                        "message": (
                            "single-parent transplant does not make this incoming branch-local "
                            "manifest a target-current manifest"
                        ),
                    }
                )
    warning_classes = {"branch-local", "unreadable", "bad-current-root"}
    status = "warning" if any(item["classification"] in warning_classes for item in items) else "ok"
    return {"status": status, "manifest_plan": {"items": items}}


def admit_merge_in_memory(
    store: ctl_ref.Store,
    main_root: str,
    incoming_root: str,
    trust_anchor: dict[str, str],
    *,
    actor_id: str,
    submitted_by: str,
    admitted_at: str,
    base_root: str | None = None,
    auto_only: bool = False,
) -> dict[str, Any]:
    ctl_ref.check_timestamp(admitted_at)
    ctx = build_merge_context(store, main_root, incoming_root, trust_anchor, base_root)
    conflicts = preflight_conflicts(store, ctx)
    if conflicts and not auto_only:
        return {
            "status": "conflict",
            "merge_model": merge_model_report(),
            "base_root_cid": ctx["base_root"],
            "main_root_cid": ctx["main_state"]["root_cid"],
            "incoming_root_cid": ctx["incoming_state"]["root_cid"],
            "conflicts": conflicts,
        }
    current_state = ctx["main_state"]
    op_records_by_transition: dict[str, list[dict[str, Any]]] = {}
    for op_record in ctx["op_records"]:
        op_records_by_transition.setdefault(op_record["transition_cid"], []).append(op_record)

    merge_batches: list[dict[str, Any]] = []
    skipped_conflicts: list[dict[str, Any]] = []
    auto_binding_count = 0
    for transition_cid in ctx["incoming_transition_cids"]:
        incoming_batch = store.resolve(transition_cid)
        binding_ops: list[dict[str, Any]] = []
        for op_record in op_records_by_transition.get(transition_cid, []):
            status, reason, current = classify_op(current_state["bindings"], op_record, ctx["paths"])
            if status == "conflict":
                skipped_conflicts.append(
                    conflict_entry(
                        store,
                        op_record["logical_id"],
                        op_record["transition_cid"],
                        reason,
                        op_record["expected"],
                        op_record["result"],
                        current,
                    )
                )
                continue
            if status == "auto-admit":
                binding_ops.append(op_record["op"])
        if auto_only and not binding_ops:
            continue
        if not auto_only and skipped_conflicts:
            raise ctl_ref.InvalidHistory(f"unexpected conflict after preflight: {skipped_conflicts[-1]['logical_id']}")
        auto_binding_count += len(binding_ops)
        recorded = [cid for cid in incoming_batch["recorded_revisions"] if cid not in current_state["recorded"]]
        if not recorded and not binding_ops:
            continue
        roles = active_role_bindings_for_actor(store, current_state, actor_id)
        ctl_ref.die_unless(roles != [], "no active principal roles for actor")
        batch = admission_batch(
            current_state["project_id"],
            current_state["root_cid"],
            recorded,
            binding_ops,
            filter_evidence(incoming_batch, recorded, binding_ops),
            roles,
            actor_id,
            submitted_by,
            admitted_at,
        )
        batch_cid = store.add(batch)
        child = ctl_ref.validate_transition(store, current_state, batch_cid)
        merge_batches.append(
            {
                "source_transition_cid": transition_cid,
                "merge_batch_cid": batch_cid,
                "root_cid": child["root_cid"],
                "recorded_revisions": ctl_ref.sort_scalars(recorded),
                "binding_logical_ids": ctl_ref.sort_scalars([op["logical_id"] for op in binding_ops]),
            }
        )
        current_state = child

    if auto_only and conflicts and auto_binding_count == 0:
        return {
            "status": "conflict",
            "merge_model": merge_model_report(),
            "base_root_cid": ctx["base_root"],
            "main_root_cid": ctx["main_state"]["root_cid"],
            "incoming_root_cid": ctx["incoming_state"]["root_cid"],
            "conflicts": skipped_conflicts,
            "skipped_conflicts": skipped_conflicts,
        }

    checked = ctl_ref.validate_chain(store, current_state["root_cid"], trust_anchor)
    ctl_ref.die_unless(checked["root_cid"] == current_state["root_cid"], "merge replay mismatch")
    report: dict[str, Any] = {
        "status": "ok",
        "mode": "noop" if not merge_batches else "full",
        "merge_model": merge_model_report(),
        "base_root_cid": ctx["base_root"],
        "previous_root_cid": ctx["main_state"]["root_cid"],
        "incoming_root_cid": ctx["incoming_state"]["root_cid"],
        "current_root_cid": current_state["root_cid"],
        "merge_batches": merge_batches,
        "skipped_conflicts": skipped_conflicts,
    }
    if auto_only:
        report["mode"] = "noop" if not merge_batches else "auto-only"
    return report


def merge_manifest_name(incoming_root: str, admitted_at: str) -> str:
    digest = incoming_root.split(":", 1)[1][:16]
    date = admitted_at[:10]
    return f"merge-{date}-{digest}.json"


def admit_merge_to_store(
    main_store_root: Path,
    incoming_store_root: Path,
    *,
    incoming_root: str,
    expected_root: str,
    admitted_at: str,
    actor_id: str = DEFAULT_ACTOR_ID,
    submitted_by: str = DEFAULT_SUBMITTED_BY,
    base_root: str | None = None,
    auto_only: bool = False,
) -> dict[str, Any]:
    main_ref = load_ref(main_store_root)
    ctl_ref.die_unless(main_ref["root_cid"] == expected_root, "expected root mismatch")
    trust_anchor = trust_anchor_from_ref(main_ref)
    store = load_store_from_roots([main_store_root, incoming_store_root])
    report = admit_merge_in_memory(
        store,
        main_ref["root_cid"],
        incoming_root,
        trust_anchor,
        actor_id=actor_id,
        submitted_by=submitted_by,
        admitted_at=admitted_at,
        base_root=base_root,
        auto_only=auto_only,
    )
    if report["status"] != "ok":
        return report
    if not report["merge_batches"]:
        report["mode"] = "noop"
        return report

    write_all_objects(main_store_root, store)
    last_batch = report["merge_batches"][-1]
    write_json(
        main_store_root / "refs" / "main.json",
        {
            "schema": "ctl-dogfood/ref/1",
            "name": "refs/main",
            "project_id": main_ref["project_id"],
            "kernel_profile": main_ref["kernel_profile"],
            "root_cid": report["current_root_cid"],
            "genesis_root_cid": main_ref["genesis_root_cid"],
            "transition_cid": last_batch["merge_batch_cid"],
            "updated_at": admitted_at,
            "updated_by": submitted_by,
        },
        replace=True,
    )
    manifest_path = main_store_root / "manifests" / merge_manifest_name(incoming_root, admitted_at)
    manifest = {
        "schema": "ctl-dogfood/merge-manifest/1",
        "mode": report.get("mode", "shadow"),
        "project_id": main_ref["project_id"],
        "kernel_profile": main_ref["kernel_profile"],
        "admitted_at": admitted_at,
        "actor_id": actor_id,
        "submitted_by": submitted_by,
        "base_root_cid": report["base_root_cid"],
        "previous_root_cid": report["previous_root_cid"],
        "incoming_root_cid": report["incoming_root_cid"],
        "current_root_cid": report["current_root_cid"],
        "merge_batches": report["merge_batches"],
        "reproduce": [
            "cd ctl-dogfood",
            "uv run python scripts/verify.py",
        ],
    }
    if report.get("skipped_conflicts"):
        manifest["skipped_conflicts"] = report["skipped_conflicts"]
    write_json(manifest_path, manifest)
    report["manifest_path"] = str(manifest_path)
    return report


def resolve_roots_for_cli(args: argparse.Namespace) -> tuple[ctl_ref.Store, dict[str, str], str, str, str | None]:
    main_store_root = args.store_root
    incoming_store_root = args.incoming_store_root or args.store_root
    main_ref = load_ref(main_store_root)
    incoming_ref = load_ref(incoming_store_root)
    main_root = args.main_root or main_ref["root_cid"]
    incoming_root = args.incoming_root or incoming_ref["root_cid"]
    store = load_store_from_roots([main_store_root, incoming_store_root])
    return store, trust_anchor_from_ref(main_ref), main_root, incoming_root, args.base_root


def print_json(value: dict[str, Any]) -> None:
    print(json.dumps(value, sort_keys=True))


def short_cid(cid: str | None) -> str:
    if cid is None:
        return "-"
    if not isinstance(cid, str) or ":" not in cid:
        return str(cid)
    prefix, digest = cid.split(":", 1)
    return f"{prefix}:{digest[:12]}"


def state_text(state: dict[str, Any]) -> str:
    if state["state"] == "absent":
        return "absent"
    return short_cid(state["cid"])


def revision_text(rev: dict[str, Any]) -> str:
    if rev["state"] == "absent":
        return "absent"
    return f"{short_cid(rev['cid'])} {rev['revision_kind']} {rev['payload_profile']}"


def payload_diff_text(diff: dict[str, Any] | None) -> list[str]:
    if diff is None:
        return []
    if diff["status"] == "same":
        return ["    payload: same"]
    lines = ["    payload: changed"]
    changed = diff.get("changed", {})
    for key in sorted(changed, key=lambda value: value.encode("utf-8"))[:8]:
        pair = changed[key]
        lines.append(f"      {key}: main={pair['main']!r} incoming={pair['incoming']!r}")
    only_main = diff.get("only_main", {})
    only_incoming = diff.get("only_incoming", {})
    if only_main:
        lines.append(f"      only_main: {', '.join(sorted(only_main)[:8])}")
    if only_incoming:
        lines.append(f"      only_incoming: {', '.join(sorted(only_incoming)[:8])}")
    return lines


def transplant_command_lines(report: dict[str, Any], *, auto_only: bool = False) -> list[str]:
    lines = [
        "  python3 scripts/ctl_merge.py transplant-revisions \\",
        "    --incoming-store-root <incoming-store-root> \\",
        f"    --expected-root {report['main_root_cid']} \\",
        "    --admitted-at <UTC> \\",
    ]
    if auto_only:
        lines.append("    --auto-only \\")
    lines.append("    --format text")
    return lines


def format_merge_root_text(report: dict[str, Any]) -> str:
    lines = [
        f"status: {report['status']}",
        f"base: {short_cid(report.get('base_root_cid'))}",
        f"target: {short_cid(report.get('main_root_cid'))}",
        f"incoming: {short_cid(report.get('incoming_root_cid'))}",
    ]
    summary = report.get("summary")
    if summary is not None:
        lines.append(
            "summary: "
            f"auto-admit={summary['auto-admit']} "
            f"already-present={summary['already-present']} "
            f"conflict={summary['conflict']}"
        )
    model = report.get("merge_model", {})
    if model:
        lines.append(
            "model: "
            f"{model.get('root_strategy')} refs/main={model.get('refs_main_resolution')} "
            f"multi-parent={model.get('multi_parent_roots')}"
        )
    logical_ids = report.get("logical_ids", [])
    if logical_ids:
        lines.append("logical ids:")
        for item in logical_ids:
            lines.append(f"  - {item['logical_id']}: {item['status']}")
            lines.append(f"    main: {revision_text(item['main'])}")
            lines.append(f"    incoming: {revision_text(item['incoming'])}")
            if item["status"] == "conflict":
                lines.extend(payload_diff_text(item.get("payload_diff")))
    conflicts = report.get("conflicts", [])
    if conflicts:
        lines.append("conflicts:")
        for item in conflicts:
            lines.append(f"  - {item['logical_id']}: {item['reason']}")
            lines.append(f"    main: {revision_text(item['main_revision'])}")
            lines.append(f"    incoming: {revision_text(item['incoming_revision'])}")
            lines.extend(payload_diff_text(item.get("payload_diff")))
    warnings = report.get("warnings", [])
    if warnings:
        lines.append("warnings:")
        for item in warnings:
            lines.append(f"  - {item['code']}: {item['path']}")
            if "current_root_cid" in item:
                lines.append(f"    current_root: {short_cid(item['current_root_cid'])}")
            lines.append(f"    {item['message']}")
    needs_transplant = False
    if summary is not None:
        needs_transplant = summary["auto-admit"] > 0
    needs_transplant = needs_transplant or any(item["status"] == "record" for item in report.get("recorded_items", []))
    if report["status"] == "ok" and not needs_transplant:
        lines.append("next: no CTL root update is needed")
    elif report["status"] == "ok":
        lines.append("next: run this on the target branch if you want to advance refs/main.json:")
        lines.extend(transplant_command_lines(report))
    elif summary is not None and summary["auto-admit"] > 0 and summary["conflict"] > 0:
        lines.append("next: optional partial transplant for auto-admit logical ids only:")
        lines.extend(transplant_command_lines(report, auto_only=True))
        lines.append("then: resolve listed logical-id conflicts by profile-owned rules and rerun merge-root")
    else:
        lines.append("next: resolve listed logical-id conflicts, then rerun merge-root")
    return "\n".join(lines)


def format_transplant_text(report: dict[str, Any]) -> str:
    if report["status"] == "conflict":
        return format_merge_root_text(report)
    lines = [
        f"status: {report['status']}",
        f"previous: {short_cid(report.get('previous_root_cid'))}",
        f"incoming: {short_cid(report.get('incoming_root_cid'))}",
        f"current: {short_cid(report.get('current_root_cid'))}",
    ]
    if report.get("mode") == "noop":
        lines.append("mode: noop")
        lines.append("next: no CTL root update was needed")
        return "\n".join(lines)
    if "mode" in report:
        lines.append(f"mode: {report['mode']}")
    batches = report.get("merge_batches", [])
    lines.append(f"merge batches: {len(batches)}")
    for batch in batches:
        ids = ", ".join(batch["binding_logical_ids"]) if batch["binding_logical_ids"] else "(record-only)"
        lines.append(f"  - {short_cid(batch['merge_batch_cid'])} -> {short_cid(batch['root_cid'])}: {ids}")
    if "manifest_path" in report:
        lines.append(f"manifest: {report['manifest_path']}")
    skipped = report.get("skipped_conflicts", [])
    if skipped:
        lines.append("skipped conflicts:")
        for item in skipped:
            lines.append(f"  - {item['logical_id']}: {item['reason']}")
    lines.append("next: run python3 scripts/verify.py and commit refs/main.json, objects, and manifest together")
    return "\n".join(lines)


def format_runbook_text(report: dict[str, Any]) -> str:
    plan = report["plan"]
    preview = report["merge_preview"]
    summary = preview.get("summary", {})
    lines = [
        "runbook: CTL branch-store merge",
        f"kind: {plan['kind']}",
        "writes_state: false",
        f"target: {short_cid(preview.get('main_root_cid'))}",
        f"incoming: {short_cid(preview.get('incoming_root_cid'))}",
        (
            "summary: "
            f"auto-admit={summary.get('auto-admit', 0)} "
            f"already-present={summary.get('already-present', 0)} "
            f"conflict={summary.get('conflict', 0)}"
        ),
    ]
    blocked = plan.get("blocked_logical_ids", [])
    if blocked:
        lines.append("blocked logical ids:")
        for logical_id in blocked:
            lines.append(f"  - {logical_id}")
    warnings = plan.get("warnings", [])
    if warnings:
        lines.append("warnings:")
        for item in warnings:
            lines.append(f"  - {item['code']}: {item['path']}")
        lines.append("next: inspect manifest sidecars with manifest-plan before committing")
    commands = plan.get("commands", [])
    if commands:
        lines.append("commands:")
        for command in commands:
            lines.append(f"  {command}")
    elif plan["kind"] == "blocked-conflict":
        lines.append("commands: none until profile-owned conflict resolution is admitted")
    else:
        lines.append("commands: none")
    lines.append(f"verify: {plan['verify_command']}")
    lines.append("commit: include generated refs/main.json, objects, and manifests only after verify passes")
    return "\n".join(lines)


def format_manifest_plan_text(report: dict[str, Any]) -> str:
    lines = [f"status: {report['status']}", "manifest plan:"]
    items = report["manifest_plan"]["items"]
    if not items:
        lines.append("  - no incoming manifests found")
        return "\n".join(lines)
    for item in items:
        lines.append(f"  - {item['path']}: {item['classification']}")
        lines.append(f"    action: {item['recommended_action']}")
        lines.append(f"    {item['message']}")
    return "\n".join(lines)


def print_report(value: dict[str, Any], output_format: str, *, command: str) -> None:
    if output_format == "json":
        print_json(value)
        return
    if command in {"merge-root", "preview"}:
        print(format_merge_root_text(value))
    elif command == "runbook":
        print(format_runbook_text(value))
    elif command == "manifest-plan":
        print(format_manifest_plan_text(value))
    else:
        print(format_transplant_text(value))


def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--store-root",
        type=Path,
        default=DOGFOOD_ROOT,
        help="target CTL dogfood store whose refs/main.json is authoritative",
    )
    parser.add_argument(
        "--incoming-store-root",
        type=Path,
        help="incoming branch CTL dogfood store; defaults to --store-root",
    )
    parser.add_argument(
        "--main-root",
        help="target root CID; defaults to target refs/main.json root_cid",
    )
    parser.add_argument(
        "--incoming-root",
        help="incoming root CID; defaults to incoming refs/main.json root_cid",
    )
    parser.add_argument(
        "--base-root",
        help="common base root CID; defaults to computed lowest common ancestor",
    )
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="json",
        help="output format; json is stable for scripts, text is for operators",
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Merge CTL dogfood branch-store roots by logical binding semantics.",
        epilog=(
            "Agents: start with 'runbook --format text' or 'merge-root --format text'. "
            "See ctl-dogfood/protocols/branch-store-merge-agents.org."
        ),
    )
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ["merge-root", "preview", "runbook"]:
        preview = sub.add_parser(
            name,
            help="dry-run semantic merge report or agent runbook; never writes refs/main.json",
        )
        add_common_args(preview)
    manifest_plan = sub.add_parser(
        "manifest-plan",
        help="classify incoming manifest sidecars without writing or deleting files",
    )
    add_common_args(manifest_plan)
    for name in ["transplant-revisions", "admit"]:
        admit = sub.add_parser(
            name,
            help="append no-conflict incoming revisions after the target current root",
        )
        add_common_args(admit)
        admit.add_argument(
            "--expected-root",
            required=True,
            help="required current target root; prevents stale refs/main.json writes",
        )
        admit.add_argument(
            "--admitted-at",
            required=True,
            help="UTC timestamp for generated merge admission batches, e.g. 2026-07-07T01:00:00Z",
        )
        admit.add_argument(
            "--auto-only",
            action="store_true",
            help="transplant only auto-admit binding ops and leave conflicting logical ids untouched",
        )
        admit.add_argument("--actor-id", default=DEFAULT_ACTOR_ID, help="principal actor id")
        admit.add_argument("--submitted-by", default=DEFAULT_SUBMITTED_BY, help="submitting actor id")
    args = parser.parse_args()

    if args.command in {"merge-root", "preview"}:
        incoming_store_root = args.incoming_store_root or args.store_root
        print_report(
            build_store_merge_preview(
                args.store_root,
                incoming_store_root,
                main_root=args.main_root,
                incoming_root=args.incoming_root,
                base_root=args.base_root,
            ),
            args.format,
            command=args.command,
        )
        return 0

    if args.command == "runbook":
        incoming_store_root = args.incoming_store_root or args.store_root
        print_report(
            build_runbook(
                args.store_root,
                incoming_store_root,
                main_root=args.main_root,
                incoming_root=args.incoming_root,
                base_root=args.base_root,
            ),
            args.format,
            command=args.command,
        )
        return 0

    if args.command == "manifest-plan":
        incoming_store_root = args.incoming_store_root or args.store_root
        report = build_manifest_plan(args.store_root, incoming_store_root, main_root=args.main_root)
        print_report(report, args.format, command=args.command)
        return 0 if report["status"] in {"ok", "warning"} else 1

    if args.command in {"transplant-revisions", "admit"}:
        incoming_store_root = args.incoming_store_root or args.store_root
        incoming_ref = load_ref(incoming_store_root)
        incoming_root = args.incoming_root or incoming_ref["root_cid"]
        report = admit_merge_to_store(
            args.store_root,
            incoming_store_root,
            incoming_root=incoming_root,
            expected_root=args.expected_root,
            admitted_at=args.admitted_at,
            actor_id=args.actor_id,
            submitted_by=args.submitted_by,
            base_root=args.base_root,
            auto_only=args.auto_only,
        )
        print_report(report, args.format, command=args.command)
        return 0 if report["status"] == "ok" else 1

    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
