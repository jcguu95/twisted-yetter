#!/usr/bin/env python3
from __future__ import annotations

import copy
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "reference"))

import ctl_ref  # noqa: E402


MALFORMED_VALUES = [[], {}, True, 123, None, "BAD VALUE"]


def classify(fn):
    try:
        fn()
        return ("valid", "")
    except ctl_ref.InvalidHistory as exc:
        return ("invalid", str(exc))
    except ctl_ref.UnsupportedProfile as exc:
        return ("unsupported", str(exc))
    except Exception as exc:  # noqa: BLE001 - this fuzz pass is explicitly looking for host exceptions.
        return ("host:" + type(exc).__name__, str(exc))


def all_paths(value, path, paths):
    paths.append(path)
    if isinstance(value, dict):
        for key, item in value.items():
            all_paths(item, path + [key], paths)
    elif isinstance(value, list):
        for index, item in enumerate(value):
            all_paths(item, path + [index], paths)


def set_path(obj, path, value):
    if not path:
        return value
    cursor = obj
    for part in path[:-1]:
        cursor = cursor[part]
    cursor[path[-1]] = value
    return obj


def valid_transition_batch():
    store, manifest = ctl_ref.build_case("non-genesis")
    genesis = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
    return store, manifest, genesis, store.resolve(manifest["transition_batch"])


def batch_host_exception_issues():
    issues = []
    store, _manifest, _genesis, batch = valid_transition_batch()
    paths = []
    all_paths(batch, [], paths)
    for path in paths:
        if not path:
            continue
        for malformed in MALFORMED_VALUES:
            store, _manifest, genesis, batch = valid_transition_batch()
            try:
                batch = set_path(batch, path, copy.deepcopy(malformed))
            except Exception:
                continue
            try:
                cid = store.add(batch)
            except Exception as exc:  # noqa: BLE001
                if not isinstance(exc, ctl_ref.InvalidHistory):
                    issues.append(("batch", path, malformed, "store-host:" + type(exc).__name__, str(exc)))
                continue
            kind, message = classify(lambda: ctl_ref.validate_transition(store, genesis, cid))
            if kind.startswith("host"):
                issues.append(("batch", path, malformed, kind, message))
    return len(paths), issues


def revision_host_exception_issues(label, revision):
    issues = []
    paths = []
    all_paths(revision, [], paths)
    for path in paths:
        if not path:
            continue
        for malformed in MALFORMED_VALUES:
            mutated = copy.deepcopy(revision)
            try:
                mutated = set_path(mutated, path, copy.deepcopy(malformed))
            except Exception:
                continue
            store = ctl_ref.Store()
            try:
                cid = store.add(mutated)
            except Exception as exc:  # noqa: BLE001
                if not isinstance(exc, ctl_ref.InvalidHistory):
                    issues.append((label, path, malformed, "store-host:" + type(exc).__name__, str(exc)))
                continue
            kind, message = classify(lambda: ctl_ref.validate_revision(store, cid, mutated))
            if kind.startswith("host"):
                issues.append((label, path, malformed, kind, message))
    return len(paths), issues


def valid_mutated_batch_issues():
    issues = []
    _store, _manifest, _genesis, batch = valid_transition_batch()
    paths = []
    all_paths(batch, [], paths)
    for path in paths:
        if not path:
            continue
        for malformed in MALFORMED_VALUES:
            store, _manifest, genesis, batch = valid_transition_batch()
            try:
                batch = set_path(batch, path, copy.deepcopy(malformed))
            except Exception:
                continue
            try:
                cid = store.add(batch)
            except Exception:
                continue
            kind, message = classify(lambda: ctl_ref.validate_transition(store, genesis, cid))
            if kind == "valid":
                issues.append((path, malformed, kind, message))
    return issues


def valid_mutated_revision_issues(revision):
    issues = []
    paths = []
    all_paths(revision, [], paths)
    for path in paths:
        if not path:
            continue
        for malformed in MALFORMED_VALUES:
            mutated = copy.deepcopy(revision)
            try:
                mutated = set_path(mutated, path, copy.deepcopy(malformed))
            except Exception:
                continue
            store = ctl_ref.Store()
            try:
                cid = store.add(mutated)
            except Exception:
                continue
            kind, _message = classify(lambda: ctl_ref.validate_revision(store, cid, mutated))
            if kind == "valid":
                issues.append((path, malformed))
    return issues


def print_issue_list(title, issues):
    print(title, len(issues))
    for issue in issues[:100]:
        print(issue)


def main() -> int:
    batch_paths, batch_issues = batch_host_exception_issues()
    print("batch container+leaf paths", batch_paths, "host issues", len(batch_issues))
    for issue in batch_issues[:100]:
        print(issue)

    revisions = [
        (
            "policy",
            ctl_ref.revision(
                "sys:policy",
                "policy-set",
                "ctl-governance/policy-set/1",
                ctl_ref.policy_payload(),
            ),
        ),
        (
            "role",
            ctl_ref.revision(
                "role-binding:operator",
                "role-binding",
                "ctl-governance/role-binding/1",
                {"actor_id": "actor:jin", "role_id": "role:owner", "scope": {"project_id": "project:demo"}},
            ),
        ),
        (
            "receipt",
            ctl_ref.revision(
                "receipt:one",
                "run-receipt",
                "agent/run-receipt/1",
                {
                    "status": "ok",
                    "command": ["x"],
                    "started_at": "2026-06-25T23:00:00Z",
                    "finished_at": "2026-06-25T23:00:01Z",
                },
            ),
        ),
    ]

    host_issue_count = len(batch_issues)
    for label, revision in revisions:
        path_count, issues = revision_host_exception_issues(label, revision)
        host_issue_count += len(issues)
        print(label, "paths", path_count, "host issues", len(issues))
        for issue in issues[:100]:
            print(issue)

    print_issue_list("valid mutated batch issues", valid_mutated_batch_issues())
    for label, revision in revisions:
        print_issue_list(label + " valid mutations", valid_mutated_revision_issues(revision))

    return 1 if host_issue_count else 0


if __name__ == "__main__":
    raise SystemExit(main())
