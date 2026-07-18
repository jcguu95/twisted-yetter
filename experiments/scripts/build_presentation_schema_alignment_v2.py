#!/usr/bin/env python3
"""Build the fail-closed Python/Lean presentation alignment checkpoint."""

from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-schema-alignment-v2.json"
)
FIXTURE = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-fixture-v1.json"
)
GENERATOR = "experiments/scripts/build_presentation_schema_alignment_v2.py"

SOURCE_FILES = [
    GENERATOR,
    "experiments/inputs/lean-kirby/framed-link-presentation-fixture-v1.json",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "lean/PresentationArtifactReplay.lean",
    "lean/TwistedYetter.lean",
    "lean/TwistedYetter/Kirby/Presentation.lean",
    "lean/TwistedYetter/Kirby/PresentationSchemaRegression.lean",
    (
        "lean/TwistedYetter/Kirby/"
        "PresentationSchemaRegressionAxiomAudit.lean"
    ),
    "scripts/lean_presentation_artifact_replay.sh",
    "src/twisted_yetter/kirby_presentation_v1.py",
    "tests/test_framed_link_presentation_syntax_v1.py",
    "tests/test_kirby_presentation_v1.py",
]


def run(*argv: str, env: dict[str, str] | None = None) -> str:
    result = subprocess.run(
        argv,
        cwd=ROOT,
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    return (result.stdout + result.stderr).strip()


def sha256_bytes(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode()


def add_content_hash(value: dict[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop("content_hash", None)
    result["content_hash"] = sha256_bytes(canonical_bytes(result))
    return result


def file_record(relative: str) -> dict[str, Any]:
    data = (ROOT / relative).read_bytes()
    return {
        "bytes": len(data),
        "sha256": sha256_bytes(data),
    }


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace(
        "+00:00", "Z"
    )


def main() -> None:
    dirty = run("git", "status", "--porcelain")
    if dirty:
        raise SystemExit(
            "refusing to build presentation alignment artifact from dirty tree"
        )

    started_at = utc_now()
    started = time.monotonic()
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["UV_CACHE_DIR"] = str(ROOT / ".uv-cache")
    replay_output = run(
        "./scripts/lean_presentation_artifact_replay.sh",
        env=env,
    )
    if "15 passed" not in replay_output:
        raise RuntimeError("unexpected Python test denominator")
    if "PASS Lean replay + 2 fail-closed mutations" not in replay_output:
        raise RuntimeError("Lean artifact replay did not report terminal pass")

    fixture_bytes = FIXTURE.read_bytes()
    fixture = json.loads(fixture_bytes)
    if fixture["content_hash"] != (
        "sha256:"
        "42eef430c68ffdc02d687958e0e1d702c3cee7ba3638cc15b664985c8e6779aa"
    ):
        raise RuntimeError("fixture content hash drifted")

    payload: dict[str, Any] = {
        "schema": "twisted-yetter.framed-link-presentation-schema-alignment.v2",
        "status": (
            "PASS_PYTHON_LEAN_PRESENTATION_SCHEMA_AND_EXECUTION_ALIGNED"
        ),
        "mathematical_status": (
            "COMBINATORIAL_INPUT_ALIGNMENT_ESTABLISHED_"
            "FOUR_MANIFOLD_INVARIANCE_NOT_ESTABLISHED"
        ),
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "generator_script": GENERATOR,
        "argv": [GENERATOR],
        "reproduce_command": (
            "UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 "
            "uv run python "
            "experiments/scripts/build_presentation_schema_alignment_v2.py"
        ),
        "repo_root": str(ROOT),
        "git": {
            "commit": run("git", "rev-parse", "HEAD"),
            "branch": run("git", "branch", "--show-current"),
            "dirty_before_generation": False,
        },
        "tool_versions": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": run("lake", "env", "lean", "--version"),
            "lake": run("lake", "--version"),
            "uv": run("uv", "--version"),
        },
        "inputs": {
            "fixture": {
                "path": str(FIXTURE.relative_to(ROOT)),
                "file_sha256": sha256_bytes(fixture_bytes),
                "content_hash": fixture["content_hash"],
                "source_snapshot_hash": fixture["source_snapshot_hash"],
                "component_count": len(fixture["components"]),
                "event_count": len(fixture["events"]),
                "slice_count": len(fixture["declared_slices"]),
            },
            "source_files": {
                relative: file_record(relative)
                for relative in SOURCE_FILES
            },
        },
        "checks": {
            "python_and_artifact_tests": {
                "status": "PASS",
                "test_count": 15,
            },
            "lean_runtime_replay": {
                "status": "PASS",
                "event_count": 12,
                "slice_count": 13,
                "fail_closed_mutation_count": 2,
            },
            "lean_kernel_regressions": {
                "status": "PASS_NO_PROJECT_AXIOMS_OR_PROOF_ORACLES",
                "theorem_count": 7,
                "theorems": [
                    "formal_identity_is_content_hash",
                    "provenance_projection_is_source_snapshot_hash",
                    "adjacent_crossing_swaps_boundary_order",
                    "nonadjacent_crossing_rejected",
                    "same_orientation_death_rejected",
                    "planar_reordering_rejected",
                    "unknown_json_field_rejected",
                ],
            },
            "shared_semantics": {
                "strict_snake_case_codec": True,
                "exact_object_keys": True,
                "birth_insert_at": True,
                "adjacent_crossing_swaps_boundary": True,
                "death_requires_adjacency": True,
                "death_requires_opposite_orientations": True,
                "coupon_requires_contiguous_window": True,
                "planar_isotopy_preserves_boundary_order": True,
                "declared_slices_replayed": True,
                "blackboard_writhe_recomputed": True,
                "formal_identity_uses_content_hash": True,
                "provenance_hash_is_not_formal_identity": True,
            },
        },
        "silent_failure_corrections": [
            {
                "old_risk": (
                    "Lean's derived JSON codec used a shape incompatible with "
                    "the repository's snake-case Python artifact schema."
                ),
                "current_guard": (
                    "Lean now has an exact-key manual parser/serializer and "
                    "round-trips the repository fixture bytes."
                ),
            },
            {
                "old_risk": (
                    "Python crossings swapped adjacent strands while Lean "
                    "left the active boundary unchanged."
                ),
                "current_guard": (
                    "Both validators now require adjacency and swap the pair."
                ),
            },
            {
                "old_risk": (
                    "Lean pinned source_snapshot_hash, which is provenance, "
                    "instead of the presentation content_hash."
                ),
                "current_guard": (
                    "FormalPresentation.pinnedSourceHash now projects "
                    "contentHash; provenance has a separate projection."
                ),
            },
            {
                "old_risk": (
                    "Lean did not replay declared slices or recompute writhe."
                ),
                "current_guard": (
                    "Formal admission replays all events, compares all slices, "
                    "and recomputes self-crossing/framing-twist writhe."
                ),
            },
        ],
        "trust_boundary": {
            "lean_kernel_recomputes_sha256": False,
            "canonical_sha256_recomputed_by": (
                "src/twisted_yetter/kirby_presentation_v1.py"
            ),
            "lean_checks": (
                "strict schema, lowercase sha256 shape, event execution, "
                "declared slices, writhe, and the pinned hash string"
            ),
            "status": (
                "CRYPTOGRAPHIC_CONTENT_HASH_VALIDATION_IS_AN_EXPLICIT_"
                "EXTERNAL_ADMISSION_GATE"
            ),
        },
        "target_impact": {
            "presentation_input_alignment": "ESTABLISHED",
            "source_bound_local_move_recipes": "ESTABLISHED_MECHANISM",
            "source_bound_evaluator_compiler_instance": "OPEN",
            "source_bound_geometric_h2_compiler_instance": "OPEN",
            "four_manifold_invariant": "NOT_YET_ESTABLISHED",
        },
        "explicit_nonclaims": [
            "This artifact does not prove Kirby-move completeness.",
            "This artifact does not construct the eight-case evaluator compiler.",
            "This artifact does not construct geometric H2 transport.",
            "This artifact does not establish a four-manifold invariant.",
            "Lean does not recompute canonical SHA-256 inside the kernel.",
            "This artifact does not identify the construction with Crane-Yetter.",
            "This artifact does not admit a CTL theorem claim.",
        ],
        "admission": {
            "status": "REPO_LOCAL_ENGINEERING_CHECKPOINT_ONLY",
            "ctl_manifest_written": False,
            "ctl_theorem_claim_admitted": False,
        },
    }
    payload = add_content_hash(payload)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
    )
    print(OUTPUT.relative_to(ROOT))
    print(payload["content_hash"])


if __name__ == "__main__":
    main()
