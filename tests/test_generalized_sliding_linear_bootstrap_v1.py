from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "generalized-sliding-linear-bootstrap-v1.json"
)
OBLIGATIONS = (
    ROOT
    / "experiments/inputs/lean-kirby/"
    "generalized-sliding-linear-obligation-matrix-v1.json"
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


def test_linear_bootstrap_artifact_is_fail_closed_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == "PASS_GENERALIZED_SLIDING_LINEAR_BOOTSTRAP"
    assert artifact["mathematical_status"] == (
        "ESTABLISHED_FINITE_RESOLUTION_AND_CONDITIONAL_PAIRING_TRANSPORT"
    )
    assert artifact["content_hash"] == _canonical_hash(artifact)
    assert artifact["checks"]["axiom_audit"]["status"] == "PASS_NO_SORRY_AX"
    assert artifact["checks"]["axiom_audit"]["theorem_count"] == 13
    assert artifact["checks"]["mutation_tests"]["rejected_count"] == 3
    assert artifact["checks"]["resource_guards"]["default_threads"] == 1
    assert artifact["checks"]["resource_guards"]["maximum_allowed_threads"] == 2
    assert artifact["conditional_boundary"]["status"] == (
        "LINEAR_SKELETON_PROVED_CATEGORY_INSTANCE_NOT_YET_CONSTRUCTED"
    )
    assert len(artifact["explicit_non_claims"]) >= 6


def test_every_pinned_source_hash_matches_the_current_bytes() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    for relative, metadata in artifact["inputs"]["source_files"].items():
        path = ROOT / relative
        assert path.stat().st_size == metadata["bytes"], relative
        assert _sha256_path(path) == metadata["sha256"], relative


def test_obligation_matrix_keeps_future_category_work_visible() -> None:
    matrix = json.loads(OBLIGATIONS.read_text())
    rows = matrix["obligations"]
    assert len(rows) == 16
    assert sum(row["status"] == "NOT_FORMALIZED" for row in rows) == 3
    statuses = {row["obligation_id"]: row["status"] for row in rows}
    assert statuses["finite-insertion-reconstruction"] == "LEAN_PROVED"
    assert statuses["transported-dual-is-canonical"] == (
        "LEAN_PROVED_CONDITIONAL_ON_PAIRING_TRANSPORT"
    )
    assert statuses["categorical-mate-equivalences"] == "NOT_FORMALIZED"
    assert statuses["pivotal-pairing-preservation"] == "NOT_FORMALIZED"
    assert statuses["generalized-sliding-core-diagram-chain"] == "NOT_FORMALIZED"


def test_mutations_cover_the_three_silent_failure_boundaries() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    rejections = "\n".join(
        artifact["checks"]["mutation_tests"]["rejections"]
    )
    assert "MissingDualBasisProof.lean" in rejections
    assert "MissingPairingPreservation.lean" in rejections
    assert "WrongTransportedDualIndex.lean" in rejections
