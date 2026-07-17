from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/generalized-sliding-core-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "generalized-sliding-core-obligation-matrix-v1.json"
)


def _canonical_hash(payload: dict) -> str:
    copy = dict(payload)
    copy.pop("content_hash")
    encoded = json.dumps(copy, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def _sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def test_core_artifact_is_clean_terminal_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == "PASS_GENERALIZED_SLIDING_CORE"
    assert artifact["mathematical_status"] == (
        "GENERALIZED_SLIDING_CORE_ESTABLISHED_RELATIVE_TO_"
        "EXPLICIT_STANDARD_INPUTS"
    )
    assert artifact["git"]["dirty"] is False
    assert artifact["content_hash"] == _canonical_hash(artifact)
    assert artifact["checks"]["fusion_axiom_audit"]["theorem_count"] == 23
    assert artifact["checks"]["kirby_axiom_audit"]["theorem_count"] == 32
    assert artifact["checks"]["fusion_mutation_tests"]["rejected_count"] == 6
    assert artifact["checks"]["kirby_mutation_tests"]["rejected_count"] == 5
    assert artifact["checks"]["resource_guards"]["maximum_allowed_threads"] == 2


def test_every_pinned_source_hash_matches_current_bytes() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    for relative, metadata in artifact["inputs"]["source_files"].items():
        path = ROOT / relative
        assert path.stat().st_size == metadata["bytes"], relative
        assert _sha256_path(path) == metadata["sha256"], relative


def test_obligations_are_terminal_and_trusted_boundary_is_explicit() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    rows = matrix["obligations"]
    assert len(rows) == 20
    assert not any(row["status"] == "NOT_FORMALIZED" for row in rows)
    assert sum(
        row["status"] == "EXPLICIT_SOURCE_BACKED_ASSUMPTION"
        for row in rows
    ) == 3
    statuses = {row["obligation_id"]: row["status"] for row in rows}
    assert statuses["equation-3.1.11-pairing-preservation"] == (
        "LEAN_PROVED_FROM_STANDARD_INPUTS"
    )
    assert statuses["equations-3.1.3-through-3.1.8"] == (
        "LEAN_PROVED_FROM_LOCAL_CERTIFICATES"
    )
    assert statuses["real-functor-valued-sliding-law"] == "LEAN_CONSTRUCTED"
    assert len(matrix["trusted_input_boundary"]) == 5
    assert all(
        item["does_not_assume"] for item in matrix["trusted_input_boundary"]
    )


def test_silent_failure_guards_cover_the_discovered_type_errors() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    guards = "\n".join(matrix["silent_failure_guards"])
    assert "fullness" in guards
    assert "oppositely oriented mate" in guards
    assert "free-module linear combinations" in guards
    assert "not incorrectly of the identity functor" in guards
    assert "Forward and backward identity resolutions" in guards
    assert "final core equality is a theorem" in guards


def test_mutations_cover_every_major_admission_boundary() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    rejections = "\n".join(
        artifact["checks"]["fusion_mutation_tests"]["rejections"]
        + artifact["checks"]["kirby_mutation_tests"]["rejections"]
    )
    for filename in (
        "MissingIdentityResolutionSound.lean",
        "MissingPivotalTraceProof.lean",
        "WrongMateDualOrder.lean",
        "MissingBackwardInsertion.lean",
        "MissingMateMovie.lean",
    ):
        assert filename in rejections


def test_nonclaims_keep_later_roadmap_stages_out_of_lemma_3_3() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    nonclaims = "\n".join(artifact["explicit_non_claims"])
    assert "Lemma 3.4" in nonclaims
    assert "Kirby-calculus completeness" in nonclaims
    assert "four-manifold invariance" in nonclaims
    assert "computation JSON artifacts" in nonclaims
