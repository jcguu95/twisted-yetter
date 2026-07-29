#!/usr/bin/env python3
"""Build the v3 dotted-puncture implementation bridge evidence."""

from __future__ import annotations

from datetime import UTC, datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from twisted_yetter.kirby_presentation_v1 import validate_presentation


FIXTURE = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "framed-link-presentation-fixture-v1.json"
)
SYNTAX_ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "framed-link-presentation-syntax-v1.json"
)
OUTPUT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dotted-puncture-words-implementation-bridge-v1.json"
)
LEDGER = (
    ROOT
    / "experiments/results/lean-kirby/"
    "independent-combinatorial-semantic-comparison-blocker-v1.json"
)
INDEPENDENT = (
    ROOT / "lean/TwistedYetter/Kirby/Final/Semantics/Independent"
)

FROZEN_HASHES = {
    "Algebra.lean": (
        "00016a4c7e001403745d7977bb6d430bbb601732c69681e2bbef68488bc53959"
    ),
    "Diagram.lean": (
        "00010bb741c9660e60ecde8f673ce3b7b257a52da7dfe2212ba7de202b0c9c16"
    ),
    "Entry.lean": (
        "000ec4a1dc6428a453dbdd949ef0922dee0e2d63657469477c409bffd50bbda8"
    ),
    "Evaluator.lean": (
        "000b5204ae925b864c8a8641a502f33e98293be45070fd86bf18835a5e5238b3"
    ),
    "Graphical.lean": (
        "000fe54f3532524313901518f169db2fdc45b594911d5ddb18b2fa1b9ed5f70c"
    ),
    "Homology.lean": (
        "0005b73b9229f8fe99bd943a17fcf0812ee0439cfa63b28bd033b7efbf283697"
    ),
    "Invariant.lean": (
        "000b0cb95782c5fa91086df9d97431aa950eee74801fcc6839ade620e3421117"
    ),
    "Moves.lean": (
        "0002c475b0e615b838d0d7d1befa5d02077bcc7df9ce428b1d3694073851c0ff"
    ),
}


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_hash(payload: dict[str, Any]) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode()
    return "sha256:" + sha256_bytes(encoded)


def run(argv: list[str]) -> str:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["PYTHONPATH"] = "src"
    result = subprocess.run(
        argv,
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"{argv!r} failed\nstdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result.stdout + result.stderr


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()


def main() -> None:
    started = time.perf_counter()
    started_at = utc_now()
    if git("status", "--porcelain"):
        raise RuntimeError("bridge artifact requires a clean source commit")

    observed_frozen = {
        path.name: sha256_path(path)
        for path in sorted(INDEPENDENT.glob("*.lean"))
    }
    if observed_frozen != FROZEN_HASHES:
        raise AssertionError("frozen Independent semantics changed")

    fixture = json.loads(FIXTURE.read_text())
    validate_presentation(fixture)
    cuts = fixture["dotted_cuts"]
    if len(cuts) != 1 or len(cuts[0]["punctures"]) != 2:
        raise AssertionError("reference fixture did not retain its puncture word")

    pytest_output = run(
        [
            "uv",
            "run",
            "pytest",
            "-q",
            "tests/test_kirby_presentation_v1.py",
            "tests/test_framed_link_presentation_syntax_v1.py",
        ]
    )
    if "33 passed" not in pytest_output:
        raise AssertionError("expected 33 Python checks")

    lean_sources = [
        "lean/TwistedYetter/Kirby/PresentationSchemaRegression.lean",
        (
            "lean/TwistedYetter/Kirby/Final/Semantics/"
            "DottedCutImplementationBridge.lean"
        ),
        (
            "lean/TwistedYetter/Kirby/Final/Semantics/"
            "CombinatorialSemanticComparison.lean"
        ),
    ]
    lean_output = run(["./scripts/lean_local_build.sh", *lean_sources])
    replay_output = run(
        [
            "./scripts/lean_local_check.sh",
            "--run",
            "lean/PresentationArtifactReplay.lean",
            str(FIXTURE.relative_to(ROOT)),
        ]
    )
    if "5 fail-closed mutations" not in replay_output:
        raise AssertionError("Lean runtime mutation replay was incomplete")

    syntax = json.loads(SYNTAX_ARTIFACT.read_text())
    source_commit = git("rev-parse", "HEAD")
    source_hashes = {
        relative: sha256_path(ROOT / relative)
        for relative in [
            "src/twisted_yetter/kirby_presentation_v1.py",
            "lean/TwistedYetter/Kirby/Presentation.lean",
            *lean_sources,
            "lean/PresentationArtifactReplay.lean",
            str(FIXTURE.relative_to(ROOT)),
        ]
    }
    payload: dict[str, Any] = {
        "schema": "twisted-yetter.dotted-puncture-words-bridge.v1",
        "status": "PASS_DOTTED_PUNCTURE_WORDS_IMPLEMENTATION_BRIDGE",
        "started_at_utc": started_at,
        "finished_at_utc": utc_now(),
        "elapsed_milliseconds": round((time.perf_counter() - started) * 1000),
        "git": {
            "branch": git("branch", "--show-current"),
            "commit": source_commit,
            "dirty": False,
        },
        "presentation_schema": fixture["schema"],
        "fixture_content_hash": fixture["content_hash"],
        "syntax_artifact_content_hash": syntax["content_hash"],
        "checks": {
            "python_and_lean_accept_same_canonical_json": "PASS",
            "python_validator_tests": 28,
            "combined_python_tests": 33,
            "lean_runtime_fail_closed_mutations": 5,
            "ordered_positions": [0, 1],
            "direction_sign_convention": {
                "with_disk_orientation": 1,
                "against_disk_orientation": -1,
                "status": "PASS_IMPLEMENTATION_ONLY",
            },
            "topology_certificate_is_proof_bearing": True,
            "aggregated_incidence_used_to_infer_words": False,
            "frozen_semantics_hashes": observed_frozen,
        },
        "source_sha256": source_hashes,
        "resolved_blocker": "DOTTED_PUNCTURE_WORDS_MISSING",
        "remaining_blockers": [
            "PUNCTURE_DIRECTION_SIGN_RELATION_NOT_NORMATIVE",
            "CLOSING_THREE_HANDLE_DATA_MISSING",
            "PRIMAL_DUAL_HOMOLOGY_CONVENTION_MISMATCH",
        ],
        "explicit_non_claims": [
            "No byte under Independent semantics was modified.",
            "No topology proposition is inferred from a JSON hash.",
            "No total CombinatorialSpecialKirbyDiagram bridge is claimed.",
            "No closing three-handle or primal/dual H2 conflict is resolved.",
            "The frozen semantics still does not require direction/sign correspondence.",
        ],
        "reproduce_command": (
            "PYTHONPATH=src UV_CACHE_DIR=.uv-cache LEAN_NUM_THREADS=1 "
            "uv run python "
            "experiments/scripts/build_dotted_puncture_words_bridge_v1.py"
        ),
        "lean_output_sha256": sha256_bytes(lean_output.encode()),
        "replay_output_sha256": sha256_bytes(replay_output.encode()),
        "pytest_output_sha256": sha256_bytes(pytest_output.encode()),
    }
    payload["content_hash"] = canonical_hash(payload)

    ledger = {
        "schema": "independent-combinatorial-semantic-comparison-blocker-v1",
        "recorded_at_utc": utc_now(),
        "branch": git("branch", "--show-current"),
        "frozen_semantic_commit": "8fbbf30",
        "semantic_content_commit": "1cfd7e2",
        "implementation_commit": source_commit,
        "git_dirty_while_recorded": False,
        "frozen_entry": (
            "TwistedYetter.Kirby.Final.Semantics.Independent.Entry"
        ),
        "comparison_status": "BLOCKED_WITH_EXPLICIT_DATA_GAPS",
        "passing_layers": [
            "Independent standalone entry",
            "Component table",
            "Coupon boundary words",
            "Dotted ordered signed puncture words",
            "Proof-bearing dotted-cut topology boundary",
        ],
        "resolved_blockers": [
            "COUPON_INPUT_OUTPUT_WORDS_MISSING",
            "DOTTED_PUNCTURE_WORDS_MISSING",
        ],
        "blockers": [
            {
                "id": "PUNCTURE_DIRECTION_SIGN_RELATION_NOT_NORMATIVE",
                "severity": "NORMATIVE_SEMANTICS_WEAKER_THAN_IMPLEMENTATION",
                "details": (
                    "v3 enforces direction/sign correspondence; frozen "
                    "DottedPuncture only requires the sign to be plus or minus one."
                ),
            },
            {
                "id": "CLOSING_THREE_HANDLE_DATA_MISSING",
                "severity": "SEMANTIC_DATA_MISSING",
            },
            {
                "id": "PRIMAL_DUAL_HOMOLOGY_CONVENTION_MISMATCH",
                "severity": "NONTRIVIAL_SEMANTIC_CONFLICT",
            },
        ],
        "bridge_artifact": {
            "path": str(OUTPUT.relative_to(ROOT)),
            "content_hash": payload["content_hash"],
        },
        "frozen_semantics_sha256": observed_frozen,
        "non_claims": payload["explicit_non_claims"],
    }
    ledger["content_hash"] = canonical_hash(ledger)

    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    LEDGER.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    print(OUTPUT)
    print(LEDGER)
    print(payload["content_hash"])


if __name__ == "__main__":
    main()
