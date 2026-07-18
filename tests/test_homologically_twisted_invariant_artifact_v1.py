from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.homologically_twisted_invariant_v1 import (
    ALPHA_DENOMINATOR,
    canonical_hash,
    validate_invariant_runtime,
)
from twisted_yetter.kirby_completeness_v1 import SPECIAL_MOVE_KINDS


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "homologically-twisted-invariant-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "homologically-twisted-invariant-obligation-matrix-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "homologically-twisted-kirby-invariant-sources-v1.json"
)
LEAN_SOURCE = (
    ROOT
    / "lean/TwistedYetter/Kirby/"
    "HomologicallyTwistedInvariant.lean"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_r11_artifact_is_terminal_clean_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["status"] == (
        "PASS_HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT"
    )
    assert artifact["mathematical_status"] == (
        "HOMOLOGICALLY_TWISTED_KIRBY_INVARIANT_"
        "ESTABLISHED_UNDER_LISTED_AXIOMS"
    )
    assert artifact["roadmap_status"] == "R11_TERMINAL_R12_NOT_STARTED"
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_r7_through_r10_predecessors_are_hash_bound() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    predecessors = artifact["inputs"]["predecessor_artifacts"]

    assert set(predecessors) == {
        "r7_framed_link_presentation",
        "r8_handle_moves",
        "r9_cancellation",
        "r10_completeness",
    }
    for record in predecessors.values():
        path = ROOT / record["path"]
        payload = json.loads(path.read_text())
        assert payload["status"] == record["status"]
        assert payload["content_hash"] == record["content_hash"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == (
            record["sha256"]
        )


def test_obligations_are_terminal_and_inputs_remain_visible() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    matrix = json.loads(OBLIGATIONS.read_text())

    assert len(matrix["obligations"]) == 38
    assert len(matrix["trusted_inputs"]) == 4
    assert not any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN", "BLOCKED"}
        for row in matrix["obligations"]
    )
    assert artifact["trusted_inputs"] == matrix["trusted_inputs"]
    assert artifact["inputs"]["obligation_matrix"][
        "obligation_count"
    ] == 38


def test_yetter_scope_is_recorded_without_generalization() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    references = json.loads(REFERENCES.read_text())
    refs = {item["ref_id"]: item for item in references["references"]}
    yetter = refs["ref:yetter-homologically-twisted-1993"]

    assert yetter["captured_pdf"]["sha256"] == (
        "e9e72e8a3ee58f9070c3e3a17d6e60181eaa91249d3265fbf348c590b101b96b"
    )
    assert yetter["captured_pdf"]["repo_local_bytes"] is False
    assert "simply-connected" in yetter["scope_caveat"]
    assert "Z2" in yetter["scope_caveat"]
    assert "Uq(sl2)" in yetter["scope_caveat"]
    assert artifact["checks"]["source_scope_honesty"] == {
        "status": "PASS_YETTER_SCOPE_NOT_UPGRADED",
        "yetter_pdf_hash_recorded": True,
        "yetter_pdf_repo_local": False,
        "yetter_theorem_11_used_as_general_identification": False,
        "arbitrary_category_result_is_conditional": True,
    }


def test_lean_certificate_has_no_holes_and_rejects_all_mutations() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    certificate = artifact["lean_certificate"]

    assert certificate["status"] == (
        "PASS_LEAN_KERNEL_AND_NEGATIVE_MUTATIONS"
    )
    assert certificate["audited_declaration_count"] == 89
    assert certificate["mutation_count"] == 10
    assert len(certificate["mutation_rejections"]) == 10
    assert certificate["proof_hole_scan"]["status"] == (
        "PASS_NO_SORRY_ADMIT_AXIOM_OR_NATIVE_DECIDE"
    )
    assert "sorryAx" not in certificate["axiom_audit"]["output"]


def test_runtime_revalidates_all_moves_and_marked_classes() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    runtime = artifact["runtime_certificate"]

    validate_invariant_runtime(runtime)
    assert runtime["movie_result"]["step_count"] == len(
        SPECIAL_MOVE_KINDS
    )
    assert runtime["movie_result"]["checked_step_alpha_count"] == (
        len(SPECIAL_MOVE_KINDS) * ALPHA_DENOMINATOR
    )
    assert runtime["marked_pair_system"]["geometric_alpha_count"] == (
        ALPHA_DENOMINATOR
    )
    assert runtime["marked_pair_system"]["marked_transport_is_derived"] is True


def test_contract_has_no_equality_or_identification_escape_hatch() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    contract = artifact["invariant_contract"]
    source = LEAN_SOURCE.read_text()

    assert contract["local_directed_constructor_count"] == 8
    assert contract["bare_normalized_equality_constructor"] is False
    assert contract["handwritten_target_alpha_field"] is False
    assert contract["crane_yetter_identification_field"] is False
    assert "fromEquality" not in source
    assert "finalInvariant" not in source
    assert "craneYetterIdentification" not in source
    assert "graphical_kind_sound" in source
    assert "graphical_orientation_sound" in source
    assert "marked_transport_sound" in source


def test_pinned_sources_replay_from_r11_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]

    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_scoped_test_denominator_and_nonclaims_are_exact() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    tests = artifact["checks"]["scoped_pytest"]
    nonclaims = "\n".join(artifact["explicit_non_claims"])

    assert tests["passed_count"] == 76
    assert "76 passed" in tests["output"]
    assert "does not identify" in nonclaims
    assert "Crane-Yetter" in nonclaims
    assert "does not import or validate a concrete category snapshot" in (
        nonclaims
    )
    assert "does not prove Pachner-move invariance" in nonclaims
