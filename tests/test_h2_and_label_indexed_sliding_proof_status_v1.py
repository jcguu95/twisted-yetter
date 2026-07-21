from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
RELATIVE = (
    "experiments/results/lean-kirby/"
    "h2-and-label-indexed-sliding-proof-status-v1.json"
)
ARTIFACT = ROOT / RELATIVE
CORRECTION = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dual-handle-convention-correction-v1.json"
)


def canonical_hash(payload: dict) -> str:
    body = dict(payload)
    body.pop("content_hash", None)
    encoded = json.dumps(
        body, sort_keys=True, separators=(",", ":")
    ).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def stale_inputs(artifact: dict) -> list[str]:
    stale = []
    for group in ("source_files", "reference_records"):
        for relative, metadata in artifact["inputs"][group].items():
            data = (ROOT / relative).read_bytes()
            if (
                len(data) != metadata["bytes"]
                or hashlib.sha256(data).hexdigest()
                != metadata["sha256"]
            ):
                stale.append(relative)
    return stale


def test_historical_snapshot_is_quarantined_after_dual_correction() -> None:
    historical = load(ARTIFACT)
    correction = load(CORRECTION)
    assert historical["content_hash"] == canonical_hash(historical)
    assert correction["content_hash"] == canonical_hash(correction)
    assert stale_inputs(historical)
    assert RELATIVE in correction["resource_safety"][
        "unsafe_prior_artifacts"
    ]
    assert correction["checks"]["source_guards"][
        "dual_handle_chain_forced"
    ] is True
    assert correction["explicit_nonclaims"][0].startswith(
        "This artifact does not yet establish"
    )
