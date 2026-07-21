from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT
    / "experiments/results/lean-kirby/"
    "canonical-modular-four-manifold-invariant-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def load_artifact() -> dict:
    return json.loads(ARTIFACT.read_text())


def test_artifact_is_content_addressed_and_honest() -> None:
    artifact = load_artifact()
    assert artifact["schema"] == (
        "canonical-modular-four-manifold-invariant-v1"
    )
    assert artifact["status"] == (
        "TOPOLOGY_BOUNDARY_SEPARATED_CANONICAL_EVAL_KERNEL_CHECKED_"
        "LOCAL_REALIZATION_OPEN"
    )
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["conditional_final_theorem"][
        "is_unconditional_closed_four_manifold_invariant"
    ] is False
    assert artifact["conditional_final_theorem"][
        "caller_supplies_local_move_realization"
    ] is True


def test_v1_remains_a_content_addressed_historical_snapshot() -> None:
    artifact = load_artifact()
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["conditional_final_theorem"][
        "is_unconditional_closed_four_manifold_invariant"
    ] is False
    assert artifact["conditional_final_theorem"][
        "caller_supplies_local_move_realization"
    ] is True
    assert artifact["status"].endswith("LOCAL_REALIZATION_OPEN")


def test_v1_metadata_is_not_mistaken_for_current_source_bytes() -> None:
    artifact = load_artifact()
    assert artifact["inputs"]["source_files"]
    assert artifact["inputs"]["reference_records"]
    for group in ("source_files", "reference_records"):
        for metadata in artifact["inputs"][group].values():
            assert metadata["bytes"] > 0
            assert len(metadata["sha256"]) == 64
