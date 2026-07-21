from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORRECTION = (
    ROOT
    / "experiments/results/lean-kirby/"
    "dual-handle-convention-correction-v1.json"
)
TOMBSTONE = (
    ROOT
    / "experiments/results/lean-kirby/"
    "general-h2-kirby-route-resolution-v1.json"
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


def test_old_route_is_a_fail_closed_tombstone() -> None:
    artifact = load(TOMBSTONE)
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "SUPERSEDED_WRONG_PRIMAL_DUAL_IDENTIFICATION"
    )
    assert artifact["formal_evidence_admissible"] is False


def test_correction_is_content_addressed_and_locally_passes() -> None:
    artifact = load(CORRECTION)
    assert artifact["content_hash"] == canonical_hash(artifact)
    assert artifact["status"] == (
        "PASS_DUAL_HANDLE_CONVENTION_CORRECTED_LOCAL_REGRESSIONS"
    )
    assert artifact["checks"]["lean_build"] == "PASS"
    assert artifact["correct_convention"]["normalization_counts"] == (
        "primal counts, not reversed"
    )


def test_type_level_primal_dual_separation_is_recorded() -> None:
    guards = load(CORRECTION)["checks"]["source_guards"]
    assert guards["primal_counts_preserved"] is True
    assert guards["dual_handle_chain_forced"] is True
    assert guards["transpose_certificate_required"] is True
    assert guards["cancellation_indices_swapped"] is True
    assert guards["wrong_primal_regression_quarantined"] is True


def test_old_no_go_is_retracted_without_overclaiming_completion() -> None:
    artifact = load(CORRECTION)
    assert artifact["checks"]["source_guards"][
        "old_no_go_retracted"
    ] is True
    assert artifact["remaining_global_obligation"]["status"] == (
        "BLOCKED_GLOBAL_DUAL_BOUNDARY_MOVIE_INTEGRATION"
    )
    assert any(
        "does not yet establish" in item
        for item in artifact["explicit_nonclaims"]
    )


def test_unsafe_historical_generators_are_quarantined() -> None:
    generators = load(CORRECTION)["resource_safety"][
        "unsafe_prior_generators"
    ]
    assert len(generators) == 6
    assert all(path.startswith("experiments/scripts/") for path in generators)
