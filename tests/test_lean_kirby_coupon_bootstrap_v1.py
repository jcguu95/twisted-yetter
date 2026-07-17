from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT / "experiments/results/lean-kirby/lean-kirby-coupon-bootstrap-v1.json"
)
OBLIGATIONS = (
    ROOT / "experiments/inputs/lean-kirby/coupon-move-obligation-matrix-v1.json"
)


def _canonical_hash(payload: dict) -> str:
    copy = dict(payload)
    copy.pop("content_hash")
    encoded = json.dumps(copy, sort_keys=True, separators=(",", ":")).encode()
    return f"sha256:{hashlib.sha256(encoded).hexdigest()}"


def test_bootstrap_artifact_is_fail_closed_and_content_addressed() -> None:
    artifact = json.loads(ARTIFACT.read_text())
    assert artifact["status"] == "PASS_KIRBY_COUPON_BOOTSTRAP"
    assert (
        artifact["mathematical_status"]
        == "ESTABLISHED_BOOTSTRAP_WITH_CONDITIONAL_SLIDING_INTERFACE"
    )
    assert artifact["content_hash"] == _canonical_hash(artifact)
    assert artifact["checks"]["axiom_audit"]["status"] == "PASS_NO_SORRY_AX"
    assert artifact["checks"]["axiom_audit"]["theorem_count"] == 18
    assert artifact["checks"]["mutation_tests"]["rejected_count"] == 3
    assert artifact["checks"]["resource_guards"]["default_threads"] == 1
    assert artifact["checks"]["resource_guards"]["maximum_allowed_threads"] == 2
    assert (
        artifact["conditional_boundary"]["status"]
        == "INTERFACE_PROVED_INSTANCE_NOT_YET_CONSTRUCTED"
    )
    assert len(artifact["explicit_non_claims"]) >= 6


def test_every_obligation_has_a_terminal_bootstrap_status() -> None:
    obligations = json.loads(OBLIGATIONS.read_text())
    assert len(obligations["moves"]) == 10
    assert {
        row["status"] for row in obligations["moves"]
    } == {"LEAN_PROVED", "LEAN_PROVED_CONDITIONAL_INTERFACE"}
    assert {
        row["singularity"] for row in obligations["moves"]
    } >= {
        "positive_crossing",
        "negative_crossing",
        "left_coevaluation",
        "left_evaluation",
        "right_coevaluation",
        "right_evaluation",
        "positive_framing_twist",
        "negative_framing_twist",
        "handle_slide_window",
    }
