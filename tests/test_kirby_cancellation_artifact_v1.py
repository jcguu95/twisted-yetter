from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess

from twisted_yetter.kirby_cancellation_v1 import (
    canonical_hash,
    validate_cancellation_fixture,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT / "experiments/results/lean-kirby/kirby-cancellation-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "kirby-cancellation-obligation-matrix-v1.json"
)
REFERENCES = (
    ROOT
    / "experiments/inputs/references/"
    "kirby-cancellation-primary-sources-v1.json"
)
LEAN_SOURCE = (
    ROOT / "lean/TwistedYetter/Kirby/KirbyCancellation.lean"
)


def git_bytes(commit: str, relative: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{relative}"],
        cwd=ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_r9_artifact_is_terminal_clean_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())

    assert artifact["status"] == (
        "PASS_ALL_BARENZ_BARRETT_TABLE2_LOCAL_KIRBY_MOVES"
    )
    assert artifact["mathematical_status"] == (
        "ALL_REQUIRED_KIRBY_MOVES_EVALUATOR_INVARIANT_RELATIVE_TO_"
        "EXPLICIT_SLIDING_CUTTING_KILLING_TWIST_PIVOTAL_AND_"
        "NORMALIZATION_INPUTS"
    )
    assert artifact["roadmap_status"] == (
        "R8_R9_TERMINAL_RELATIVE_TO_LISTED_STANDARD_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == canonical_hash(artifact)


def test_table2_has_five_of_five_local_move_families() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    coverage = artifact["table2_coverage"]

    assert coverage["status"] == "PASS_FIVE_OF_FIVE_LOCAL_MOVE_FAMILIES"
    assert coverage["r8_slide_family_count"] == 3
    assert coverage["r9_cancellation_family_count"] == 2
    assert coverage["actual_move_family_count"] == 5


def test_all_cancellation_fixtures_revalidate() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    coverage = artifact["cancellation_coverage"]

    assert coverage["expected_count"] == coverage["actual_count"] == 4
    for fixture in coverage["fixtures"]:
        validate_cancellation_fixture(fixture)


def test_normalization_is_derived_not_supplied() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    check = artifact["checks"]["normalization"]
    source = LEAN_SOURCE.read_text()

    assert check["status"] == "PASS_EXACT_SIGNED_EXPONENT_FORMULA"
    assert check["final_normalized_equality_input_allowed"] is False
    assert "Int.ofNat counts.h2 - Int.ofNat counts.h1" in source
    assert "theorem denominator_addOneTwo" in source
    assert "theorem denominator_addTwoThree" in source
    assert "inductive AdmittedCancellation" in source
    assert "fromEquality" not in source


def test_mandatory_graphical_inputs_and_pivotal_warning_remain_visible() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    whitelist = artifact["checks"]["closed_cancellation_whitelist"]
    ledger = json.loads(REFERENCES.read_text())

    assert whitelist["constructor_count"] == 2
    assert whitelist["bare_normalized_equality_constructor"] is False
    assert set(whitelist["mandatory_local_inputs"]) == {
        "killing_identity",
        "transparent_twist_witness",
        "pivotal_dimension_preserved",
    }
    locators = "\n".join(
        item["locator"] for item in ledger["references"][0]["locators"]
    )
    assert "Remark 3.11" in locators
    assert "Lemmas 2.46-2.47" in locators


def test_obligations_are_terminal_and_r8_is_hash_pinned() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    matrix = json.loads(OBLIGATIONS.read_text())
    r8_record = artifact["inputs"]["r8_handle_slide_artifact"]
    r8_path = ROOT / r8_record["path"]
    r8 = json.loads(r8_path.read_text())

    assert matrix["status"] == (
        "R9_TERMINAL_RELATIVE_TO_EXPLICIT_LOCAL_GRAPHICAL_AND_"
        "DIMENSION_INPUTS"
    )
    assert len(matrix["obligations"]) == 22
    assert not any(
        row["status"] in {"NOT_FORMALIZED", "UNKNOWN"}
        for row in matrix["obligations"]
    )
    assert r8["content_hash"] == r8_record["content_hash"]
    assert hashlib.sha256(r8_path.read_bytes()).hexdigest() == (
        r8_record["sha256"]
    )


def test_pinned_sources_replay_from_r9_source_commit() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    commit = artifact["git"]["commit"]

    for relative, metadata in artifact["inputs"]["source_files"].items():
        data = git_bytes(commit, relative)
        assert len(data) == metadata["bytes"], relative
        assert hashlib.sha256(data).hexdigest() == metadata["sha256"], relative


def test_nonclaims_block_r10_and_invariant_scope_upgrade() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    nonclaims = "\n".join(artifact["explicit_non_claims"])

    assert "does not prove Kirby/Cerf completeness" in nonclaims
    assert "pair (X, alpha)" in nonclaims
    assert "Crane-Yetter" in nonclaims
    assert "numerical computation artifact" in nonclaims
    assert "specially-dotted evaluator" in nonclaims
