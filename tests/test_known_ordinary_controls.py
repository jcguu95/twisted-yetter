import pytest

from twisted_yetter.ordinary_control_gate import (
    CLOSED_VALUE_SOURCE_STATUS,
    KNOWN_ORDINARY_CONTROL_SCHEMA,
    SOURCE_NEEDED_SLOTS,
    VALUE_CONVENTION_STATUS,
    VALUE_STATUS,
    known_ordinary_control_ledger,
)
from twisted_yetter.su2_level2 import QuadraticSurd


def test_known_ordinary_controls_classify_n22_supported_local_cases() -> None:
    ledger = known_ordinary_control_ledger()
    cases = {case["case_id"]: case for case in ledger["cases"]}

    assert ledger["schema"] == KNOWN_ORDINARY_CONTROL_SCHEMA
    assert ledger["node_id"] == "n23-known-ordinary-4d-controls"
    assert ledger["closed_4_manifold_claim_allowed"] is False
    assert set(ledger["source_status_by_slot"].values()) == {"SOURCE NEEDED"}
    assert ledger["n24_blocked_slots"] == list(SOURCE_NEEDED_SLOTS)
    assert ledger["value_status_labels"] == {
        "computed_scaffold": VALUE_STATUS,
        "local_convention": VALUE_CONVENTION_STATUS,
        "closed_claim_source_status": CLOSED_VALUE_SOURCE_STATUS,
    }

    for case in cases.values():
        assert case["status"] == VALUE_STATUS
        assert case["value_status"] == VALUE_STATUS
        assert case["value_convention_status"] == VALUE_CONVENTION_STATUS
        assert case["closed_claim_source_status"] == CLOSED_VALUE_SOURCE_STATUS
        assert case["source_audited_ordinary_value_status"] == (
            CLOSED_VALUE_SOURCE_STATUS
        )
        assert case["n22_certificate_summary"]["claim_level"] == (
            VALUE_CONVENTION_STATUS
        )
        assert case["n22_certificate_summary"]["closed_4_manifold_claim_allowed"] is False

    assert cases["S4-empty"]["n22_can_compute"] is True
    assert cases["S4-empty"]["n22_certificate_summary"]["total_value"] == _sparse_sum(
        [(0, QuadraticSurd(1))]
    )

    assert cases["CP2-plus-one-unknot"]["n22_can_compute"] is True
    assert cases["CP2-plus-one-unknot"]["crossing_count"] == 0
    assert cases["CP2-plus-one-unknot"]["n22_certificate_summary"]["total_value"] == (
        _sparse_sum(
            [
                (0, QuadraticSurd(1)),
                (3, QuadraticSurd(2)),
                (8, QuadraticSurd(1)),
            ]
        )
    )

    assert cases["S2xS2-hopf"]["n22_can_compute"] is True
    assert cases["S2xS2-hopf"]["crossing_count"] == 2
    assert cases["S2xS2-hopf"]["linking_matrix"] == [[0, 1], [1, 0]]
    assert cases["S2xS2-hopf"]["n22_certificate_summary"]["sector_count"] == 9
    assert cases["S2xS2-hopf"]["n22_certificate_summary"]["total_value"] == _sparse_sum(
        [(0, QuadraticSurd(4))]
    )


def test_known_ordinary_controls_refuse_closed_claims() -> None:
    with pytest.raises(ValueError, match="closed_4_manifold_claim=True is refused"):
        known_ordinary_control_ledger(closed_4_manifold_claim=True)


def _sparse_sum(entries: list[tuple[int, QuadraticSurd]]) -> dict[str, object]:
    return {
        "kind": "Q(sqrt2)[zeta_16]_sparse_sum",
        "terms": [
            {"exponent": exponent, "coefficient": coefficient.to_jsonable()}
            for exponent, coefficient in entries
        ],
    }
