#!/usr/bin/env python3
"""Create and verify a fail-closed semantic-review ledger for Lean sources.

The ledger is deliberately independent of ``#print axioms``.  It fingerprints
all project axioms, structures, and classes in the local import closure of the
public final theorem, plus an explicit list of core definitions whose human
meaning matters.  A human approval is current only for the exact declaration
fingerprint that was reviewed.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DECLARATION_RE = re.compile(
    r"^(?:(?:noncomputable|private|protected)\s+)*"
    r"(?P<kind>axiom|structure|class|inductive|def|abbrev|theorem)\s+"
    r"(?P<name>[^\s({:\[]+)"
)
IMPORT_RE = re.compile(r"^import\s+(?P<modules>.+?)\s*$")
FIELD_RE = re.compile(r"^\s{2}(?P<name>[A-Za-z_][A-Za-z0-9_']*)\s*:")
NAMESPACE_RE = re.compile(r"^namespace\s+(?P<name>[^\s]+)\s*$")
SECTION_RE = re.compile(r"^(?:noncomputable\s+)?section(?:\s+[^\s]+)?\s*$")
END_RE = re.compile(r"^end(?:\s+[^\s]+)?\s*$")


@dataclass(frozen=True)
class Declaration:
    file: str
    kind: str
    local_name: str
    qualified_name: str
    start_line: int
    end_line: int
    source: str
    fields: tuple[str, ...]

    @property
    def identifier(self) -> str:
        return f"{self.file}::{self.qualified_name}"

    @property
    def fingerprint(self) -> str:
        normalized = self.source.rstrip() + "\n"
        return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def run_git(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, check=True, capture_output=True, text=True
    )
    return result.stdout.strip()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def module_path(lean_root: Path, module: str) -> Path:
    return lean_root.joinpath(*module.split(".")).with_suffix(".lean")


def local_import_closure(root: Path, entry: str) -> list[str]:
    lean_root = root / "lean"
    pending = [root / entry]
    visited: set[Path] = set()

    while pending:
        path = pending.pop()
        if path in visited:
            continue
        if not path.is_file():
            raise FileNotFoundError(f"missing local Lean source: {path}")
        visited.add(path)
        for line in path.read_text(encoding="utf-8").splitlines():
            match = IMPORT_RE.match(line)
            if match is None:
                continue
            for module in match.group("modules").split():
                imported = module_path(lean_root, module)
                if imported.is_file() and imported not in visited:
                    pending.append(imported)

    return sorted(str(path.relative_to(root)) for path in visited)


def parse_declarations(root: Path, relative_file: str) -> list[Declaration]:
    path = root / relative_file
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    starts: list[tuple[int, re.Match[str], tuple[str, ...]]] = []
    context_stack: list[tuple[str, str | None]] = []
    for index, line in enumerate(lines):
        namespace = NAMESPACE_RE.match(line)
        if namespace is not None:
            context_stack.append(("namespace", namespace.group("name")))
            continue
        if SECTION_RE.match(line) is not None:
            context_stack.append(("section", None))
            continue
        if END_RE.match(line) is not None:
            if context_stack:
                context_stack.pop()
            continue
        match = DECLARATION_RE.match(line)
        if match is not None:
            namespaces = tuple(
                name
                for kind, name in context_stack
                if kind == "namespace" and name is not None
            )
            starts.append((index, match, namespaces))

    declarations: list[Declaration] = []
    for position, (start, match, namespaces) in enumerate(starts):
        end = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        block = "".join(lines[start:end])
        local_name = match.group("name")
        qualified_name = ".".join((*namespaces, local_name))
        fields: list[str] = []
        if match.group("kind") in {"structure", "class"}:
            for line in lines[start + 1 : end]:
                field = FIELD_RE.match(line)
                if field is not None:
                    fields.append(field.group("name"))
        declarations.append(
            Declaration(
                file=relative_file,
                kind=match.group("kind"),
                local_name=local_name,
                qualified_name=qualified_name,
                start_line=start + 1,
                end_line=end,
                source=block,
                fields=tuple(fields),
            )
        )
    return declarations


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def declaration_index(root: Path, closure: list[str]) -> dict[str, Declaration]:
    index: dict[str, Declaration] = {}
    for relative_file in closure:
        for declaration in parse_declarations(root, relative_file):
            if declaration.identifier in index:
                raise ValueError(f"duplicate declaration id: {declaration.identifier}")
            index[declaration.identifier] = declaration
    return index


def field_classification(
    scope: dict[str, Any], declaration: Declaration, field: str
) -> str:
    qualified = f"{declaration.local_name}.{field}"
    overrides = scope.get("field_classifications", {})
    return overrides.get(qualified, "UNCLASSIFIED_STRUCTURE_FIELD")


def declaration_classification(
    scope: dict[str, Any], declaration: Declaration
) -> str:
    overrides = scope.get("declaration_classifications", {})
    if declaration.identifier in overrides:
        return overrides[declaration.identifier]
    short_identifier = f"{declaration.file}::{declaration.local_name}"
    if short_identifier in overrides:
        return overrides[short_identifier]
    if declaration.kind == "axiom":
        return "EXPLICIT_AXIOM_REQUIRES_HUMAN_REVIEW"
    if declaration.kind == "class":
        return "DOMAIN_CLASS_REQUIRES_REFERENCE_REVIEW"
    if declaration.kind == "structure":
        return "STRUCTURE_REQUIRES_FIELD_REVIEW"
    if declaration.kind == "theorem":
        return "CORE_THEOREM_STATEMENT_REVIEW"
    return "CORE_DEFINITION_SEMANTIC_REVIEW"


def selected_declarations(
    scope: dict[str, Any], index: dict[str, Declaration]
) -> list[Declaration]:
    selected: dict[str, Declaration] = {}
    for identifier, declaration in index.items():
        if declaration.kind in {"axiom", "structure", "class"}:
            selected[identifier] = declaration

    for item in scope.get("core_declarations", []):
        matches = [
            declaration
            for declaration in index.values()
            if declaration.file == item["file"]
            and item["name"]
            in {declaration.local_name, declaration.qualified_name}
        ]
        if len(matches) != 1:
            raise KeyError(
                f"core declaration expected one match, found {len(matches)}: "
                f"{item['file']}::{item['name']}"
            )
        selected[matches[0].identifier] = matches[0]

    return [selected[key] for key in sorted(selected)]


def prior_reviews(previous: dict[str, Any] | None) -> dict[str, dict[str, Any]]:
    if previous is None:
        return {}
    return {
        entry["id"]: entry.get("human_review", {})
        for entry in previous.get("entries", [])
    }


def review_for(
    identifier: str, fingerprint: str, reviews: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    review = dict(reviews.get(identifier, {}))
    if not review:
        return {
            "decision": "UNREVIEWED",
            "reviewed_declaration_sha256": None,
            "reviewer": None,
            "reviewed_at_utc": None,
            "evidence": None,
            "freshness": "UNREVIEWED",
        }

    reviewed_hash = review.get("reviewed_declaration_sha256")
    if review.get("decision") == "HUMAN_APPROVED":
        review["freshness"] = "CURRENT" if reviewed_hash == fingerprint else "STALE"
    else:
        review["freshness"] = review.get("decision", "UNREVIEWED")
    return review


def build_ledger(
    root: Path,
    scope_path: Path,
    previous: dict[str, Any] | None,
) -> dict[str, Any]:
    scope = load_json(scope_path)
    closure = local_import_closure(root, scope["entry"])
    index = declaration_index(root, closure)
    selected = selected_declarations(scope, index)
    reviews = prior_reviews(previous)
    kernel_axioms = set(scope.get("recorded_final_kernel_axioms", []))

    entries: list[dict[str, Any]] = []
    for declaration in selected:
        fields = [
            {
                "name": f"{declaration.qualified_name}.{field}",
                "classification": field_classification(scope, declaration, field),
            }
            for field in declaration.fields
        ]
        entries.append(
            {
                "id": declaration.identifier,
                "name": declaration.qualified_name,
                "local_name": declaration.local_name,
                "kind": declaration.kind,
                "classification": declaration_classification(scope, declaration),
                "source": {
                    "file": declaration.file,
                    "start_line": declaration.start_line,
                    "end_line": declaration.end_line,
                    "declaration_sha256": declaration.fingerprint,
                    "file_sha256": sha256_file(root / declaration.file),
                },
                "fields": fields,
                "recorded_final_kernel_dependency":
                    declaration.kind == "axiom"
                    and declaration.local_name in kernel_axioms,
                "human_review": review_for(
                    declaration.identifier, declaration.fingerprint, reviews
                ),
            }
        )

    approved = sum(
        entry["human_review"]["freshness"] == "CURRENT" for entry in entries
    )
    stale = sum(entry["human_review"]["freshness"] == "STALE" for entry in entries)
    unreviewed = sum(
        entry["human_review"]["decision"] == "UNREVIEWED" for entry in entries
    )
    field_classification_counts: dict[str, int] = {}
    for entry in entries:
        for field in entry["fields"]:
            classification = field["classification"]
            field_classification_counts[classification] = (
                field_classification_counts.get(classification, 0) + 1
            )

    return {
        "schema": "twisted-yetter/lean-semantic-review-ledger/1",
        "generated_at_utc": utc_now(),
        "status": "INCONCLUSIVE_HUMAN_REVIEW_REQUIRED",
        "scope": {
            "entry": scope["entry"],
            "scope_file": str(scope_path.relative_to(root)),
            "local_import_closure_file_count": len(closure),
            "local_import_closure": closure,
            "recorded_kernel_axiom_source": scope.get(
                "recorded_kernel_axiom_source"
            ),
        },
        "provenance": {
            "git_commit": run_git(root, "rev-parse", "HEAD"),
            "git_dirty": bool(run_git(root, "status", "--porcelain")),
            "generator": "scripts/lean_semantic_review_ledger.py",
            "scope_sha256": sha256_file(scope_path),
        },
        "policy": {
            "old_chat_or_prose_is_not_approval": True,
            "approval_is_valid_only_for_exact_declaration_sha256": True,
            "changed_declaration_makes_review_stale": True,
            "unclassified_field_fails_closed": True,
        },
        "summary": {
            "entry_count": len(entries),
            "current_human_approvals": approved,
            "stale_human_approvals": stale,
            "unreviewed_entries": unreviewed,
            "field_count": sum(len(entry["fields"]) for entry in entries),
            "unclassified_fields": sum(
                field["classification"] == "UNCLASSIFIED_STRUCTURE_FIELD"
                for entry in entries
                for field in entry["fields"]
            ),
            "field_classification_counts": dict(
                sorted(field_classification_counts.items())
            ),
        },
        "entries": entries,
    }


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


def command_snapshot(args: argparse.Namespace) -> int:
    root = Path(args.root).resolve()
    scope_path = (root / args.scope).resolve()
    output_path = (root / args.output).resolve()
    previous = load_json(output_path) if output_path.exists() else None
    ledger = build_ledger(root, scope_path, previous)
    write_json(output_path, ledger)
    print(json.dumps(ledger["summary"], ensure_ascii=False, indent=2))
    return 0


def current_ledger(root: Path, ledger_path: Path) -> dict[str, Any]:
    saved = load_json(ledger_path)
    scope_relative = saved["scope"]["scope_file"]
    return build_ledger(root, root / scope_relative, saved)


def command_check(args: argparse.Namespace) -> int:
    root = Path(args.root).resolve()
    ledger_path = (root / args.ledger).resolve()
    saved = load_json(ledger_path)
    current = current_ledger(root, ledger_path)

    saved_entries = {entry["id"]: entry for entry in saved["entries"]}
    current_entries = {entry["id"]: entry for entry in current["entries"]}
    added = sorted(set(current_entries) - set(saved_entries))
    removed = sorted(set(saved_entries) - set(current_entries))
    changed = sorted(
        identifier
        for identifier in set(saved_entries) & set(current_entries)
        if saved_entries[identifier]["source"]["declaration_sha256"]
        != current_entries[identifier]["source"]["declaration_sha256"]
    )
    stale = sorted(
        entry["id"]
        for entry in current["entries"]
        if entry["human_review"]["freshness"] == "STALE"
    )

    report = {
        "inventory_added": added,
        "inventory_removed": removed,
        "declarations_changed_since_snapshot": changed,
        "stale_human_reviews": stale,
        "current_summary": current["summary"],
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 1 if added or removed or changed or stale else 0


def command_review(args: argparse.Namespace) -> int:
    root = Path(args.root).resolve()
    ledger_path = (root / args.ledger).resolve()
    saved = load_json(ledger_path)
    current = current_ledger(root, ledger_path)
    current_by_id = {entry["id"]: entry for entry in current["entries"]}
    if args.declaration not in current_by_id:
        raise KeyError(f"declaration is outside the ledger: {args.declaration}")

    entry = current_by_id[args.declaration]
    entry["human_review"] = {
        "decision": args.decision,
        "reviewed_declaration_sha256": entry["source"]["declaration_sha256"],
        "reviewer": args.reviewer,
        "reviewed_at_utc": utc_now(),
        "evidence": args.evidence,
        "freshness": "CURRENT" if args.decision == "HUMAN_APPROVED" else args.decision,
    }
    current["generated_at_utc"] = utc_now()
    current["provenance"]["git_dirty"] = bool(
        run_git(root, "status", "--porcelain")
    )
    current["summary"]["current_human_approvals"] = sum(
        item["human_review"]["freshness"] == "CURRENT"
        for item in current["entries"]
    )
    current["summary"]["stale_human_approvals"] = sum(
        item["human_review"]["freshness"] == "STALE"
        for item in current["entries"]
    )
    current["summary"]["unreviewed_entries"] = sum(
        item["human_review"]["decision"] == "UNREVIEWED"
        for item in current["entries"]
    )
    write_json(ledger_path, current)
    print(f"recorded {args.decision}: {args.declaration}")
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--root", default=".", help="repository root")
    subparsers = result.add_subparsers(dest="command", required=True)

    snapshot = subparsers.add_parser("snapshot")
    snapshot.add_argument("--scope", required=True)
    snapshot.add_argument("--output", required=True)
    snapshot.set_defaults(function=command_snapshot)

    check = subparsers.add_parser("check")
    check.add_argument("--ledger", required=True)
    check.set_defaults(function=command_check)

    review = subparsers.add_parser("review")
    review.add_argument("--ledger", required=True)
    review.add_argument("--declaration", required=True)
    review.add_argument(
        "--decision", choices=["HUMAN_APPROVED", "REJECTED"], required=True
    )
    review.add_argument("--reviewer", required=True)
    review.add_argument("--evidence", required=True)
    review.set_defaults(function=command_review)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        return args.function(args)
    except (FileNotFoundError, KeyError, ValueError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
