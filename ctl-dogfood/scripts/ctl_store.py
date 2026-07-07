#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any


DOGFOOD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOGFOOD_ROOT.parent
CTL_META_ROOT = Path(os.environ.get("CTL_META_ROOT", REPO_ROOT.parent / "ctl-meta")).resolve()
KERNEL_ROOT = CTL_META_ROOT / "meta" / "ctl-kernel"
sys.path.insert(0, str(KERNEL_ROOT / "reference"))

import ctl_ref  # noqa: E402


def load_json(path: Path) -> Any:
    return ctl_ref.load_json_strict(path)


def issue(code: str, message: str, path: Path | None = None) -> dict[str, str]:
    out = {"code": code, "message": message}
    if path is not None:
        out["path"] = str(path.relative_to(DOGFOOD_ROOT))
    return out


def section_status(errors: list[dict[str, str]]) -> str:
    return "ok" if not errors else "error"


def cid_strings(value: Any) -> list[str]:
    out: list[str] = []
    if isinstance(value, str):
        if ctl_ref.is_cid(value):
            out.append(value)
    elif isinstance(value, list):
        for item in value:
            out.extend(cid_strings(item))
    elif isinstance(value, dict):
        for item in value.values():
            out.extend(cid_strings(item))
    return out


def load_store(dogfood_root: Path = DOGFOOD_ROOT) -> tuple[ctl_ref.Store, dict[str, Any]]:
    store = ctl_ref.Store()
    errors: list[dict[str, str]] = []
    object_dir = dogfood_root / "objects" / "ctlobj-sha256"
    object_paths = sorted(object_dir.glob("*.json"))
    if not object_dir.exists():
        errors.append(issue("missing_object_dir", "object directory does not exist", object_dir))
    for path in object_paths:
        try:
            obj = load_json(path)
            cid = store.add(obj)
            expected = "ctlobj-sha256:" + path.stem
            if cid != expected:
                errors.append(issue("object_filename_cid_mismatch", f"expected {expected}, got {cid}", path))
        except Exception as exc:  # noqa: BLE001 - verifier reports local-store failures.
            errors.append(issue("object_load_failed", str(exc), path))
    return store, {
        "status": section_status(errors),
        "object_count": len(store.objects),
        "checked_object_files": len(object_paths),
        "errors": errors,
    }


def load_ref(dogfood_root: Path = DOGFOOD_ROOT) -> tuple[dict[str, Any] | None, list[dict[str, str]]]:
    ref_path = dogfood_root / "refs" / "main.json"
    errors: list[dict[str, str]] = []
    try:
        ref = load_json(ref_path)
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
        if ref["schema"] != "ctl-dogfood/ref/1":
            errors.append(issue("bad_ref_schema", "refs/main.json has unexpected schema", ref_path))
        if ref["name"] != "refs/main":
            errors.append(issue("bad_ref_name", "refs/main.json has unexpected name", ref_path))
        return ref, errors
    except Exception as exc:  # noqa: BLE001
        errors.append(issue("ref_load_failed", str(exc), ref_path))
        return None, errors


def trust_anchor_from_ref(ref: dict[str, Any]) -> dict[str, str]:
    return {
        "project_id": ref["project_id"],
        "kernel_profile": ref["kernel_profile"],
        "genesis_root_cid": ref["genesis_root_cid"],
    }


def reachable_roots(store: ctl_ref.Store, root_cid: str) -> set[str]:
    roots: set[str] = set()
    cursor = root_cid
    while cursor not in roots:
        roots.add(cursor)
        root = store.resolve(cursor)
        ctl_ref.validate_root(root)
        if root["parent"] is None:
            break
        cursor = root["parent"]
    return roots


def history_report(store: ctl_ref.Store, ref: dict[str, Any] | None, ref_errors: list[dict[str, str]]) -> dict[str, Any]:
    if ref is None or ref_errors:
        return {
            "evaluation_state": "not_evaluated",
            "kernel_result": None,
            "reason": "ref_integrity_failed",
        }
    try:
        state = ctl_ref.validate_chain(store, ref["root_cid"], trust_anchor_from_ref(ref))
        ctl_ref.die_unless(state["root_cid"] == ref["root_cid"], "ref root replay mismatch")
        return {
            "evaluation_state": "evaluated",
            "kernel_result": "Valid",
            "root_cid": state["root_cid"],
        }
    except ctl_ref.UnsupportedProfile as exc:
        return {
            "evaluation_state": "evaluated",
            "kernel_result": "UnsupportedProfile",
            "reason": str(exc),
        }
    except ctl_ref.InvalidHistory as exc:
        return {
            "evaluation_state": "evaluated",
            "kernel_result": "InvalidHistory",
            "reason": str(exc),
        }


def manifest_report(
    store: ctl_ref.Store,
    ref: dict[str, Any] | None,
    dogfood_root: Path = DOGFOOD_ROOT,
) -> dict[str, Any]:
    errors: list[dict[str, str]] = []
    manifests: list[tuple[Path, dict[str, Any]]] = []
    manifest_dir = dogfood_root / "manifests"
    for path in sorted(manifest_dir.glob("*.json")):
        try:
            manifests.append((path, load_json(path)))
        except Exception as exc:  # noqa: BLE001
            errors.append(issue("manifest_load_failed", str(exc), path))

    current_manifests: list[str] = []
    reachable: set[str] = set()
    if ref is not None:
        try:
            reachable = reachable_roots(store, ref["root_cid"])
        except ctl_ref.InvalidHistory as exc:
            errors.append(issue("reachable_roots_failed", str(exc)))

    for path, manifest in manifests:
        for cid in cid_strings(manifest):
            if cid not in store.objects:
                errors.append(issue("manifest_cid_unresolved", f"manifest references missing object {cid}", path))
        current_root = manifest.get("current_root_cid")
        if ref is not None and current_root == ref["root_cid"]:
            current_manifests.append(str(path.relative_to(dogfood_root)))
        if current_root is not None and reachable and current_root not in reachable:
            errors.append(issue("manifest_root_unreachable", f"current_root_cid is not reachable: {current_root}", path))

    bootstrap_path = manifest_dir / "bootstrap-2026-06-26.json"
    if ref is not None:
        try:
            bootstrap_manifest = load_json(bootstrap_path)
            if bootstrap_manifest.get("genesis_root_cid") != ref["genesis_root_cid"]:
                errors.append(issue("bootstrap_genesis_mismatch", "bootstrap manifest genesis does not match ref", bootstrap_path))
        except Exception as exc:  # noqa: BLE001
            errors.append(issue("bootstrap_manifest_load_failed", str(exc), bootstrap_path))
        if not current_manifests:
            errors.append(issue("no_current_manifest", "no manifest points at current ref root"))

    return {
        "status": section_status(errors),
        "manifest_count": len(manifests),
        "current_manifests": current_manifests,
        "errors": errors,
    }


def view_report() -> dict[str, Any]:
    return {
        "evaluation_state": "not_applicable",
        "reason": "ctl-meta dogfood store has no generated view layer yet",
    }


def build_verify_report(dogfood_root: Path = DOGFOOD_ROOT) -> dict[str, Any]:
    store, store_integrity = load_store(dogfood_root)
    ref, ref_errors = load_ref(dogfood_root)
    if ref_errors:
        store_integrity["errors"].extend(ref_errors)
        store_integrity["status"] = section_status(store_integrity["errors"])
    history_validity = history_report(store, ref, ref_errors)
    manifest_integrity = manifest_report(store, ref, dogfood_root)
    status = "ok"
    if store_integrity["status"] != "ok" or manifest_integrity["status"] != "ok":
        status = "error"
    elif history_validity["kernel_result"] == "UnsupportedProfile":
        status = "unsupported"
    elif history_validity["kernel_result"] != "Valid":
        status = "invalid"

    return {
        "status": status,
        "project_id": None if ref is None else ref["project_id"],
        "root_cid": None if ref is None else ref["root_cid"],
        "genesis_root_cid": None if ref is None else ref["genesis_root_cid"],
        "object_count": store_integrity["object_count"],
        "current_manifests": manifest_integrity["current_manifests"],
        "history_validity": history_validity,
        "store_integrity": store_integrity,
        "manifest_integrity": manifest_integrity,
        "view_freshness": view_report(),
    }


def print_report(report: dict[str, Any]) -> int:
    print(json.dumps(report, sort_keys=True))
    return 0 if report["status"] == "ok" else 1


def current_root(dogfood_root: Path = DOGFOOD_ROOT) -> dict[str, Any]:
    ref, errors = load_ref(dogfood_root)
    if ref is None or errors:
        return {"status": "error", "errors": errors}
    return {
        "status": "ok",
        "project_id": ref["project_id"],
        "root_cid": ref["root_cid"],
        "genesis_root_cid": ref["genesis_root_cid"],
        "transition_cid": ref["transition_cid"],
    }


def inspect_binding(logical_id: str, dogfood_root: Path = DOGFOOD_ROOT) -> dict[str, Any]:
    report = build_verify_report(dogfood_root)
    if report["history_validity"]["kernel_result"] != "Valid":
        return {
            "status": "error",
            "reason": "history_not_valid",
            "history_validity": report["history_validity"],
        }
    store, _store_report = load_store(dogfood_root)
    ref, _errors = load_ref(dogfood_root)
    assert ref is not None
    state = ctl_ref.validate_chain(store, ref["root_cid"], trust_anchor_from_ref(ref))
    cid = state["bindings"].get(logical_id)
    if cid is None:
        return {"status": "ok", "logical_id": logical_id, "binding": {"state": "absent"}}
    rev = store.resolve(cid)
    return {
        "status": "ok",
        "logical_id": logical_id,
        "binding": {
            "state": "bound",
            "cid": cid,
            "payload_profile": rev["payload_profile"],
            "revision_kind": rev["revision_kind"],
        },
    }


ABSOLUTE_WORKTREE_PATH_RE = re.compile(r"(/Users/[^\s\"'<>]+|/private/tmp/[^\s\"'<>]+|/var/folders/[^\s\"'<>]+)")
HYGIENE_DIRS = ["manifests", "decisions", "protocols", "profiles", "reviews"]


def path_hygiene_paths(dogfood_root: Path) -> list[Path]:
    paths: list[Path] = []
    for dirname in HYGIENE_DIRS:
        directory = dogfood_root / dirname
        if directory.exists():
            paths.extend(path for path in sorted(directory.rglob("*")) if path.is_file())
    paths.extend(path for path in sorted(dogfood_root.glob("run-*.txt")) if path.is_file())
    return paths


def path_hygiene_report(dogfood_root: Path = DOGFOOD_ROOT) -> dict[str, Any]:
    warnings: list[dict[str, Any]] = []
    checked = 0
    for path in path_hygiene_paths(dogfood_root):
        checked += 1
        try:
            text = path.read_text()
        except UnicodeDecodeError:
            continue
        matches = sorted(set(ABSOLUTE_WORKTREE_PATH_RE.findall(text)))
        if matches:
            warnings.append(
                {
                    "code": "absolute_worktree_path",
                    "path": path.relative_to(dogfood_root).as_posix(),
                    "matches": matches,
                    "message": "canonical CTL-adjacent artifacts should use repo-relative paths or ${REPO_ROOT}",
                }
            )
    return {
        "status": "warning" if warnings else "ok",
        "checked_files": checked,
        "warnings": warnings,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Inspect or verify a CTL dogfood local store.")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("verify")
    sub.add_parser("current-root")
    inspect = sub.add_parser("inspect-binding")
    inspect.add_argument("logical_id")
    sub.add_parser("manifest-check")
    hygiene = sub.add_parser("path-hygiene")
    hygiene.add_argument("--strict", action="store_true", help="exit nonzero when path hygiene warnings are found")
    args = parser.parse_args()

    if args.command == "verify":
        return print_report(build_verify_report())
    if args.command == "current-root":
        return print_report(current_root())
    if args.command == "inspect-binding":
        return print_report(inspect_binding(args.logical_id))
    if args.command == "manifest-check":
        report = build_verify_report()
        return print_report({"status": report["manifest_integrity"]["status"], "manifest_integrity": report["manifest_integrity"]})
    if args.command == "path-hygiene":
        report = path_hygiene_report()
        print(json.dumps(report, sort_keys=True))
        return 1 if args.strict and report["status"] != "ok" else 0
    raise AssertionError(args.command)


if __name__ == "__main__":
    raise SystemExit(main())
