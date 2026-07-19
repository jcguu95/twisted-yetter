from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "egno-modular-kirby-moves-step9-v1.json"
)
ROADMAP = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "egno-canonical-pivotal-roadmap-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_step9_artifact_is_content_addressed_and_clean() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == (
        "PASS_STEP_9_CATEGORY_BOUND_MODULAR_KIRBY_MOVES_RELATIVE_"
        "TO_EXPLICIT_GLOBAL_STANDARD_GRAPHICAL_LAWS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_step9_preserves_theorem_input_boundary() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    historical = json.loads(
        git_bytes(
            artifact["git"]["commit"],
            str(ROADMAP.relative_to(ROOT)),
        )
    )
    statuses = [step["status"] for step in historical["steps"]]
    assert statuses[:6] == ["ESTABLISHED_IN_LEAN"] * 6
    assert statuses[6] == (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_TWO_EXPLICIT_GLOBAL_"
        "STANDARD_TRACE_LAWS"
    )
    assert statuses[7] == "ESTABLISHED_IN_LEAN"
    assert statuses[8] == (
        "ESTABLISHED_IN_LEAN_RELATIVE_TO_EXPLICIT_GLOBAL_"
        "STANDARD_GRAPHICAL_LAWS"
    )
    assert statuses[9] == "NOT_YET_ESTABLISHED"


def test_label_indexed_sum_does_not_collapse_the_colour_early() -> None:
    checks = json.loads(ARTIFACT.read_text())["checks"]
    assert checks["label_coverage"] == "PASS_ALL_SIMPLE_LABELS_QUANTIFIED"
    assert checks["formal_colour_boundary"] == (
        "PASS_TERM_FIRST_THEN_FINITE_SUM_NOT_SINGLETON_OBJECT"
    )


def test_dimensions_are_category_derived() -> None:
    checks = json.loads(ARTIFACT.read_text())["checks"]
    assert checks["dimension_origin"] == (
        "PASS_GLOBAL_AND_TRANSPARENT_DIMENSIONS_DERIVED_FROM_CATEGORY_SUMS"
    )
    derived = json.loads(ARTIFACT.read_text())["lean_derived"]
    assert "transparent-simple dimension equals one in the modular scope" in derived


def test_dual_and_hash_guards_are_active() -> None:
    checks = json.loads(ARTIFACT.read_text())["checks"]
    assert checks["dual_convention"] == (
        "PASS_ONE_SELECTED_RIGHT_DUAL_ACROSS_TRACE_TWIST_AND_CLOSURE"
    )
    assert checks["hash_binding"] == (
        "PASS_CATEGORY_COHERENCE_SLIDE_AND_MOVIE_HASH_SHAPES_REQUIRED"
    )


def test_step9_guards_and_axiom_audit_passed() -> None:
    checks = json.loads(ARTIFACT.read_text())["checks"]
    assert checks["mutations"]["rejected_count"] == 36
    assert checks["axiom_audit"]["audited_declaration_count"] == 127
    assert checks["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )


def test_pinned_sources_replay_from_clean_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]
    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative
