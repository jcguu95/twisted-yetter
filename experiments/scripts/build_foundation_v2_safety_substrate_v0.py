"""Build seed artifacts for the foundation-v2 safety substrate.

This generator intentionally does not admit any formal scan evidence.  It
captures the current red-team/manager review inputs, seeds an open blocker
registry, inventories known execution surfaces, and writes an empty formal
admission policy.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
OUT_DIR = REPO_ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SNAPSHOT_DIR = OUT_DIR / "review-input-snapshots"

REVIEW_INPUTS = [
    {
        "id": "foundation-plan-v0",
        "role": "original_foundation_plan",
        "locator": "/tmp/low-rank-ribbon-scan-foundation-plan.md",
        "expected_sha256": "25f8ba073e6a740e3461ca4fe9d6f99f294acaa159f107d98061735cd2892f58",
    },
    {
        "id": "chatgpt-5-6-pro-context-v0",
        "role": "external_reviewer_context",
        "locator": "/tmp/low-rank-ribbon-scan-chatgpt-5-6-pro-context.md",
        "expected_sha256": "d293b6434e8cbb45d269d6ce8921e4cff993df723ccb00ecbeeece4ca99e7dea",
    },
    {
        "id": "red-team-round-1",
        "role": "red_team_review",
        "locator": "/private/tmp/low-rank-ribbon-scan-red-team-round-1.zh-TW.org",
        "expected_sha256": "f47037a4402296f733aa444857db46b0c71130f6896e7469f56ccc8b7eef8f13",
    },
    {
        "id": "manager-round-1",
        "role": "manager_response",
        "locator": "/tmp/low-rank-ribbon-scan-manager-red-team-round-1.zh-TW.org",
        "expected_sha256": "78feead90253161d2394a7e05eecbd1c7eaa1e72e1c33e1ae50eb3fe2e163c43",
    },
    {
        "id": "red-team-round-2",
        "role": "red_team_review",
        "locator": "/private/tmp/low-rank-ribbon-scan-red-team-round-2.zh-TW.org",
        "expected_sha256": "b9f4cc2842174a8fedbf1cf06fb58e99e5f3f484ed87efaa7013fbe93b5fb529",
    },
    {
        "id": "manager-round-2",
        "role": "manager_response",
        "locator": "/tmp/low-rank-ribbon-scan-manager-red-team-round-2.zh-TW.org",
        "expected_sha256": "5ac6f47f6406b70077bc23045f7ea77859f0bd51d86fe0d33b83f547513baea1",
    },
    {
        "id": "red-team-round-3-final",
        "role": "red_team_review",
        "locator": "/private/tmp/low-rank-ribbon-scan-red-team-round-3-final.zh-TW.org",
        "expected_sha256": "cc405ba9b4ddb085ce602d5e27e775219013a45c7da85160f8d19644df31ae0b",
    },
    {
        "id": "manager-round-3-final",
        "role": "manager_response",
        "locator": "/tmp/low-rank-ribbon-scan-manager-red-team-round-3-final.zh-TW.org",
        "expected_sha256": "742095e8072a9b9150b41c67b34733c57c3c8032399726d503aa77f8835c9491",
    },
    {
        "id": "red-team-round-4-final",
        "role": "red_team_review",
        "locator": "/private/tmp/low-rank-ribbon-scan-red-team-round-4-final.zh-TW.org",
        "expected_sha256": "929903fcd621da82bdf70a58c34c00533f30fe3177b8a4595e2d4fab7aa7d9ba",
    },
    {
        "id": "manager-round-4-final",
        "role": "manager_response",
        "locator": "/tmp/low-rank-ribbon-scan-manager-red-team-round-4-final.zh-TW.org",
        "expected_sha256": "23c84bac3bda149266c1dd0c56bbaae9e57d9748535bfbbe86694007a8785e59",
    },
    {
        "id": "red-team-round-5-final",
        "role": "red_team_review",
        "locator": "/private/tmp/low-rank-ribbon-scan-red-team-round-5-final.zh-TW.org",
        "expected_sha256": "33015746b2f5f82422ffa13945d169b79649ec21bc92758b52def05a5bc162cc",
    },
    {
        "id": "manager-round-5-understanding",
        "role": "manager_synthesis",
        "locator": "/tmp/low-rank-ribbon-scan-manager-round-5-understanding.zh-TW.org",
        "expected_sha256": "98c1b9e612ebf65ad1ece30cca1d39f1ce3a882a40c9837f65e5a1badadae13f",
    },
]

RISK_PATTERNS = [
    "FOUNDATION_ESTABLISHED",
    "READY_FOR_SIGNAL_SCAN",
    "complete-no-signal",
    "complete no-signal",
    "rank 2-5",
    "rank 2\u20135",
    "no signal",
    "formal scan",
    "all low-rank",
    "low-rank MTC",
]

P0_RE = re.compile(r"^\*\* +(P0-\d+)[\uff1a:]\s*(.+?)\s*$")


def git_output(args: list[str]) -> str:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT, text=True).strip()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(data, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def artifact_meta(kind: str, started_at: str, git_commit: str, dirty: bool) -> dict[str, Any]:
    return {
        "schema": f"twisted-yetter.foundation_v2.{kind}.v0",
        "status": "SEED_DRAFT_NOT_ADMITTED",
        "generator_script": "experiments/scripts/build_foundation_v2_safety_substrate_v0.py",
        "reproduce_command": "uv run python experiments/scripts/build_foundation_v2_safety_substrate_v0.py",
        "generated_at_utc": started_at,
        "repo_root": str(REPO_ROOT),
        "git_commit": git_commit,
        "git_dirty_at_generation_start": dirty,
        "formal_scan_status": "BLOCKED_FOR_FORMAL_SIGNAL_SCAN",
        "normative_status": "NOT_NORMATIVE_NOT_CTL_ADMITTED",
    }


def capture_review_inputs(started_at: str, git_commit: str, dirty: bool) -> tuple[list[dict[str, Any]], dict[str, str]]:
    SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
    entries: list[dict[str, Any]] = []
    contents: dict[str, str] = {}
    for item in REVIEW_INPUTS:
        source = Path(item["locator"])
        if not source.exists():
            raise FileNotFoundError(f"missing review input: {source}")
        raw = source.read_bytes()
        digest = sha256_bytes(raw)
        if digest != item["expected_sha256"]:
            raise ValueError(f"sha256 mismatch for {source}: {digest} != {item['expected_sha256']}")
        text = raw.decode("utf-8")
        snapshot_name = f"sha256-{digest}.json"
        snapshot_path = SNAPSHOT_DIR / snapshot_name
        snapshot = {
            **artifact_meta("review_input_snapshot", started_at, git_commit, dirty),
            "input_id": item["id"],
            "role": item["role"],
            "source_locator_at_capture": item["locator"],
            "source_locator_is_ephemeral": item["locator"].startswith("/tmp/")
            or item["locator"].startswith("/private/tmp/"),
            "media_type": "text/markdown" if item["locator"].endswith(".md") else "text/org",
            "byte_length": len(raw),
            "sha256": digest,
            "content_encoding": "utf-8",
            "content_utf8": text,
            "safety_note": "Snapshot of non-normative review prose. This is evidence input, not a theorem or CTL claim.",
        }
        write_json(snapshot_path, snapshot)
        entries.append(
            {
                "id": item["id"],
                "role": item["role"],
                "source_locator_at_capture": item["locator"],
                "source_locator_is_ephemeral": snapshot["source_locator_is_ephemeral"],
                "media_type": snapshot["media_type"],
                "byte_length": len(raw),
                "sha256": digest,
                "snapshot_path": str(snapshot_path.relative_to(REPO_ROOT)),
                "snapshot_schema": snapshot["schema"],
                "normative_status": "NON_NORMATIVE_REVIEW_INPUT",
            }
        )
        contents[item["id"]] = text
    return entries, contents


def build_blocker_registry(
    contents: dict[str, str], started_at: str, git_commit: str, dirty: bool
) -> tuple[dict[str, Any], dict[str, Any]]:
    blockers: list[dict[str, Any]] = []
    for source_id, text in contents.items():
        if not source_id.startswith("red-team"):
            continue
        for line_no, line in enumerate(text.splitlines(), start=1):
            match = P0_RE.match(line)
            if not match:
                continue
            source_blocker_id, title = match.groups()
            blockers.append(
                {
                    "blocker_id": f"{source_id}:{source_blocker_id}",
                    "source_input_id": source_id,
                    "source_blocker_id": source_blocker_id,
                    "source_line": line_no,
                    "severity": "P0",
                    "title": title,
                    "status": "OPEN",
                    "closure_source_of_truth": "resolver_derived_not_payload_status",
                    "closure_evidence": [],
                    "notes": [
                        "Seed extraction from red-team prose.",
                        "No blocker is closed by manager acceptance or by inclusion in this registry.",
                    ],
                }
            )
    registry = {
        **artifact_meta("blocker_registry", started_at, git_commit, dirty),
        "registry_id": "low-rank-ribbon-foundation-v2-blocker-registry-v0",
        "closure_semantics": {
            "group_views_are_not_closure_units": True,
            "manager_acceptance_is_not_closure": True,
            "closed_status_must_be_resolver_derived": True,
        },
        "blocker_count": len(blockers),
        "blockers": blockers,
    }
    coverage = {
        **artifact_meta("blocker_coverage_matrix", started_at, git_commit, dirty),
        "matrix_id": "low-rank-ribbon-foundation-v2-blocker-coverage-matrix-v0",
        "coverage_status": "ALL_EXTRACTED_BLOCKERS_OPEN_NO_GUARDS_CLOSED",
        "rows": [
            {
                "blocker_id": item["blocker_id"],
                "attack_preserved": True,
                "guard_status": "MISSING",
                "negative_test_status": "MISSING",
                "artifact_evidence_status": "MISSING",
                "closure_status": "OPEN",
            }
            for item in blockers
        ],
    }
    return registry, coverage


def build_known_execution_surface_inventory(started_at: str, git_commit: str, dirty: bool) -> dict[str, Any]:
    roots = [
        "experiments/scripts",
        "experiments/sage",
        "notebooks",
        "tests",
        "src",
    ]
    candidates: list[dict[str, Any]] = []
    for root in roots:
        root_path = REPO_ROOT / root
        if not root_path.exists():
            continue
        for path in sorted(root_path.rglob("*")):
            if path.is_dir():
                continue
            if path.suffix not in {".py", ".ipynb", ".sage", ".sh"}:
                continue
            rel = str(path.relative_to(REPO_ROOT))
            name = path.name.lower()
            tags = []
            for needle, tag in [
                ("registry", "registry_or_factory"),
                ("formula", "formula_or_preflight"),
                ("evaluator", "evaluator"),
                ("runner", "runner_or_batch"),
                ("workload", "workload"),
                ("report", "report_or_render"),
                ("ribbon", "ribbon"),
                ("morse", "morse"),
                ("yasui", "yasui"),
                ("test_", "test_surface"),
            ]:
                if needle in name or needle in rel.lower():
                    tags.append(tag)
            if not tags:
                continue
            candidates.append(
                {
                    "path": rel,
                    "surface_tags": sorted(set(tags)),
                    "formal_admission_allowed": False,
                    "inventory_completeness": "KNOWN_SURFACE_ONLY_NOT_EXHAUSTIVE",
                }
            )
    return {
        **artifact_meta("known_execution_surface_inventory", started_at, git_commit, dirty),
        "inventory_id": "low-rank-ribbon-foundation-v2-known-execution-surface-inventory-v0",
        "completeness": "NOT_PROVABLE_KNOWN_SURFACES_ONLY",
        "security_boundary": "official_admission_and_publication_consumers_not_execution_prevention",
        "candidate_count": len(candidates),
        "candidates": candidates,
    }


def build_formal_admission_policy(started_at: str, git_commit: str, dirty: bool) -> dict[str, Any]:
    return {
        **artifact_meta("formal_admission_policy", started_at, git_commit, dirty),
        "policy_id": "low-rank-ribbon-foundation-v2-formal-admission-policy-v0",
        "policy_status": "EMPTY_ALLOWLIST_BLOCK_ALL_FORMAL_SCAN_EVIDENCE",
        "formal_result_routes_allowlist": [],
        "ready_targets_allowlist": [],
        "claim_constructors_allowlist": [],
        "legacy_route_policy": "UNADMITTED_LEGACY_ROUTE_ONLY",
        "exploratory_route_policy": "EXPLORATORY_POINT_ESTIMATE_ONLY_FORMAL_CLAIM_FORBIDDEN",
        "formula_route_policy": "FORMULA_PREFLIGHT_ONLY_NOT_EVALUATOR_DENOMINATOR",
        "publication_consumer_rule": "official consumers must require admitted claim manifests; raw results are insufficient",
        "explicit_non_claims": [
            "No READY_FOR_SIGNAL_SCAN target is admitted.",
            "No formal low-rank scan runner is authorized.",
            "No rank-wide denominator is admitted.",
            "No no-signal claim is admitted.",
            "No manager or red-team draft is normative.",
        ],
    }


def build_historical_claim_audit_seed(started_at: str, git_commit: str, dirty: bool) -> dict[str, Any]:
    matches: list[dict[str, Any]] = []
    excluded_prefixes = {
        ".git",
        ".mypy_cache",
        ".pytest_cache",
        ".ruff_cache",
        str(OUT_DIR.relative_to(REPO_ROOT)),
        "ctl-dogfood/objects",
        "ctl-dogfood/generated",
    }
    allowed_suffixes = {".md", ".org", ".txt", ".json", ".py", ".ipynb"}
    for path in sorted(REPO_ROOT.rglob("*")):
        if path.is_dir() or path.suffix not in allowed_suffixes:
            continue
        rel = str(path.relative_to(REPO_ROOT))
        if any(rel == prefix or rel.startswith(prefix + os.sep) for prefix in excluded_prefixes):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        lower = text.lower()
        for pattern in RISK_PATTERNS:
            if pattern.lower() not in lower:
                continue
            line_no = next(
                (idx for idx, line in enumerate(text.splitlines(), start=1) if pattern.lower() in line.lower()),
                None,
            )
            matches.append(
                {
                    "path": rel,
                    "pattern": pattern,
                    "first_line": line_no,
                    "audit_status": "DISCOVERY_ONLY_REQUIRES_HUMAN_REVIEW",
                }
            )
            break
        if len(matches) >= 250:
            break
    return {
        **artifact_meta("historical_claim_audit_seed", started_at, git_commit, dirty),
        "audit_id": "low-rank-ribbon-foundation-v2-historical-claim-audit-seed-v0",
        "audit_status": "SEED_DISCOVERY_ONLY_NOT_COMPLETE_NOT_CURRENT_TRUTH",
        "ctl_current_state_warning": "This artifact is not a CTL current-state lookup and must not be used as normative CTL truth.",
        "patterns": RISK_PATTERNS,
        "excluded_prefixes": sorted(excluded_prefixes),
        "match_count": len(matches),
        "matches_truncated": len(matches) >= 250,
        "matches": matches,
    }


def main() -> None:
    started_at = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    git_commit = git_output(["rev-parse", "HEAD"])
    dirty = bool(git_output(["status", "--porcelain"]))
    entries, contents = capture_review_inputs(started_at, git_commit, dirty)
    bundle = {
        **artifact_meta("review_input_bundle", started_at, git_commit, dirty),
        "bundle_id": "low-rank-ribbon-foundation-v2-review-input-bundle-v0",
        "input_count": len(entries),
        "inputs": entries,
        "bundle_policy": {
            "manager_and_red_team_prose_is_non_normative": True,
            "tmp_paths_are_not_durable_identity": True,
            "snapshots_are_review_inputs_not_ctl_claims": True,
        },
    }
    registry, coverage = build_blocker_registry(contents, started_at, git_commit, dirty)
    artifacts = {
        "review-input-bundle-v0.json": bundle,
        "blocker-registry-v0.json": registry,
        "blocker-coverage-matrix-v0.json": coverage,
        "known-execution-surface-inventory-v0.json": build_known_execution_surface_inventory(
            started_at, git_commit, dirty
        ),
        "formal-admission-policy-v0.json": build_formal_admission_policy(started_at, git_commit, dirty),
        "historical-claim-audit-seed-v0.json": build_historical_claim_audit_seed(
            started_at, git_commit, dirty
        ),
    }
    for filename, payload in artifacts.items():
        write_json(OUT_DIR / filename, payload)


if __name__ == "__main__":
    main()
