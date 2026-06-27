import json

import pytest

from twisted_yetter.ordinary_kirby_color import SOURCE_STATUS_BY_SLOT
from twisted_yetter.ordinary_surgery_gate import (
    CLOSED_CLAIM_BLOCKER_ID,
    N22_BLOCKER_ID,
    N23_BLOCKER_ID,
    ORDINARY_SURGERY_GATE_SCHEMA,
    SOURCE_BLOCKER_ID,
    ordinary_surgery_gate_certificate,
    stable_ordinary_surgery_gate_json,
)


def test_ordinary_surgery_gate_returns_blocked_certificate() -> None:
    certificate = ordinary_surgery_gate_certificate()

    assert certificate["schema"] == ORDINARY_SURGERY_GATE_SCHEMA
    assert certificate["status"] == "blocked"
    assert certificate["node_id"] == "n24-ordinary-surgery-gate"
    assert certificate["ordinary_surgery_claim_allowed"] is False
    assert certificate["closed_4_manifold_claim_allowed"] is False
    assert certificate["claim_supporting_closed_invariant_allowed"] is False
    assert certificate["source_status_by_slot"] == SOURCE_STATUS_BY_SLOT
    assert certificate["blocked_source_slots"] == list(SOURCE_STATUS_BY_SLOT)


def test_blocked_reasons_cover_n21_n22_n23_and_closed_claim_refusal() -> None:
    certificate = ordinary_surgery_gate_certificate()
    reasons = {
        reason["reason_id"]: reason for reason in certificate["blocked_reasons"]
    }

    assert list(reasons) == [
        SOURCE_BLOCKER_ID,
        N22_BLOCKER_ID,
        N23_BLOCKER_ID,
        CLOSED_CLAIM_BLOCKER_ID,
    ]

    source_reason = reasons[SOURCE_BLOCKER_ID]
    assert source_reason["source_node"] == "n21-ordinary-kirby-color-source-capture"
    assert source_reason["blocked_source_slots"] == list(SOURCE_STATUS_BY_SLOT)
    assert set(source_reason["source_status_by_slot"].values()) == {"SOURCE NEEDED"}

    n22_reason = reasons[N22_BLOCKER_ID]
    assert n22_reason["n22_claim_level"] == "experimental/local-convention"
    assert n22_reason["n22_normalization_status"] == "SOURCE NEEDED"
    assert "not a sourced surgery formula" in n22_reason["claim_boundary"]

    n23_reason = reasons[N23_BLOCKER_ID]
    assert n23_reason["case_id"] == "S2xS2-hopf"
    assert n23_reason["crossing_count"] == 2
    assert n23_reason["linking_matrix"] == [[0, 1], [1, 0]]
    assert n23_reason["ordinary_scaffold_status"] == "blocked"
    assert "no-crossing" in n23_reason["blocked_reason"]

    assert reasons[CLOSED_CLAIM_BLOCKER_ID][
        "claim_supporting_closed_invariant_allowed"
    ] is False


def test_claim_supporting_closed_invariant_flag_is_refused() -> None:
    with pytest.raises(
        ValueError,
        match="claim_supporting_closed_invariant=True is refused",
    ):
        ordinary_surgery_gate_certificate(claim_supporting_closed_invariant=True)


def test_json_is_stable_and_deterministic() -> None:
    first = ordinary_surgery_gate_certificate()
    second = ordinary_surgery_gate_certificate()

    assert first == second
    assert stable_ordinary_surgery_gate_json(first) == (
        stable_ordinary_surgery_gate_json(second)
    )
    assert json.loads(stable_ordinary_surgery_gate_json(first)) == first


def test_gate_does_not_support_exotic_decorated_or_twisted_claims() -> None:
    certificate = ordinary_surgery_gate_certificate()
    unsupported = certificate["does_not_unblock"]

    assert "decorated formula claim" in unsupported
    assert "twisted formula claim" in unsupported
    assert "exotic smooth-structure detection claim" in unsupported
    assert all("exotic" not in item for item in certificate["unblocks"])
