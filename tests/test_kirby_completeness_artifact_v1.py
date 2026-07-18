from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.kirby_completeness_v1 import (
    EXCLUDED_FROM_SPECIAL_MOVIE,
    GENERAL_CERF_MOVE_FAMILIES,
    SPECIAL_MOVE_KINDS,
    canonical_hash,
    validate_topology_movie,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT / "experiments/results/lean-kirby/kirby-completeness-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "kirby-completeness-obligation-matrix-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "kirby-completeness-primary-sources-v1.json"
)
LEAN_SOURCE = (
    ROOT / "lean/TwistedYetter/Kirby/KirbyCompleteness.lean"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_r10_artifact_is_terminal_clean_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["status"] == "PASS_KIRBY_CERF_TOPOLOGY_BOUNDARY"
    assert artifact["mathematical_status"] == (
        "R10_TOPOLOGY_BOUNDARY_ESTABLISHED_AS_TWO_EXPLICIT_"
        "SOURCE_BACKED_INPUTS_NOT_REPROVED_IN_LEAN"
    )
    assert artifact["roadmap_status"] == "R10_TERMINAL_R11_NOT_STARTED"
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_general_cerf_and_table_two_scopes_are_distinct_and_complete() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    boundary = artifact["topology_boundary"]

    assert boundary["status"] == "PASS_TWO_LAYERS_SEPARATELY_VISIBLE"
    assert boundary["general_move_family_count"] == len(
        GENERAL_CERF_MOVE_FAMILIES
    )
    assert boundary["special_directed_constructor_count"] == len(
        SPECIAL_MOVE_KINDS
    )
    assert tuple(boundary["special_excluded_general_moves"]) == (
        EXCLUDED_FROM_SPECIAL_MOVIE
    )
    assert boundary["derived_from_general_cerf_in_lean"] is False
    assert boundary["evaluator_equality_included"] is False


def test_runtime_movie_and_composite_h2_certificate_revalidate() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    runtime = artifact["runtime_certificate"]

    assert runtime["status"] == "PASS_HASHED_MOVIE_AND_H2_TRANSPORT"
    assert runtime["special_move_coverage"] == (
        "PASS_EIGHT_OF_EIGHT_DIRECTED_CONSTRUCTORS"
    )
    validate_topology_movie(runtime["fixture"])
    assert runtime["composite_h2_transport"] == (
        runtime["fixture"]["composite_h2_transport"]
    )


def test_source_capture_limitations_are_not_hidden() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    references = json.loads(REFERENCES.read_text())
    refs = {item["ref_id"]: item for item in references["references"]}
    honesty = artifact["checks"]["source_scope_honesty"]

    assert honesty == {
        "status": "PASS_NO_SCOPE_COLLAPSE",
        "general_cerf_and_table_two_are_distinct_inputs": True,
        "gs_bytes_locally_pinned": False,
        "de_sa_bytes_locally_pinned": False,
        "baerenz_barrett_bytes_locally_pinned": True,
    }
    assert refs[
        "ref:gompf-stipsicz-4-manifolds-kirby-calculus"
    ]["exact_byte_capture"]["status"] == "NO_REPO_LOCAL_PRIMARY_BYTES"
    assert refs[
        "ref:de-sa-link-calculus-1979"
    ]["exact_byte_capture"]["status"] == "METADATA_ONLY_NO_CHAPTER_BYTES"
    assert refs[
        "ref:baerenz-barrett-dichromatic-2018"
    ]["captured_pdf"]["sha256"] == (
        "cf14c9d316c563cbf1bceec0b5309b561083585dc702fd24f579eadb216ff5de"
    )


def test_obligations_are_terminal_and_two_inputs_remain_visible() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    artifact = json.loads(ARTIFACT.read_text())

    assert matrix["status"] == (
        "R10_TERMINAL_AS_EXPLICIT_SOURCE_BACKED_TOPOLOGY_BOUNDARY"
    )
    assert len(matrix["obligations"]) == 31
    assert not any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN"}
        for row in matrix["obligations"]
    )
    assert len(matrix["trusted_inputs"]) == 2
    assert artifact["trusted_topology_inputs"] == matrix["trusted_inputs"]


def test_r9_local_moves_are_hash_pinned_without_scope_upgrade() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    r9_record = artifact["inputs"]["r9_local_move_artifact"]
    r9_path = ROOT / r9_record["path"]
    r9 = json.loads(r9_path.read_text())

    assert r9["content_hash"] == r9_record["content_hash"]
    assert hashlib.sha256(r9_path.read_bytes()).hexdigest() == (
        r9_record["sha256"]
    )
    assert "does not prove evaluator invariance" in " ".join(
        artifact["explicit_non_claims"]
    )


def test_lean_source_has_no_evaluator_escape_hatch() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    whitelist = artifact["checks"]["whitelists"]
    source = LEAN_SOURCE.read_text()

    assert whitelist["general_constructor_count"] == 12
    assert whitelist["special_constructor_count"] == 8
    assert whitelist["evaluator_state_or_equality_included"] is False
    assert "Diagram.eval" not in source
    assert "EvaluationState" not in source
    assert "evaluatorEquality" not in source
    assert "structure TableTwoLinkCompleteness" in source


def test_pinned_sources_replay_from_r10_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]

    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_nonclaims_block_r11_and_crane_yetter_scope_upgrade() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    nonclaims = "\n".join(artifact["explicit_non_claims"])

    assert "does not re-prove Cerf theory" in nonclaims
    assert "does not derive the five-family Table 2" in nonclaims
    assert "does not yet define an invariant of the pair (X, alpha)" in (
        nonclaims
    )
    assert "Crane-Yetter" in nonclaims
    assert "numerical computation artifact" in nonclaims
