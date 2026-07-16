import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = (
    ROOT
    / "experiments"
    / "scripts"
    / "build_ising_ribbon_lift_candidate_payloads_v1.py"
)
SPEC = importlib.util.spec_from_file_location(
    "ising_ribbon_lift_candidate_payloads_v1", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_payload_set() -> dict:
    return json.loads(
        (OUT / "ising-ribbon-lift-candidate-payloads-v1.json").read_text(
            encoding="utf-8"
        )
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def assert_candidate_payload_hash(payload: dict) -> None:
    body = dict(payload)
    candidate_hash = body.pop("candidate_payload_hash")
    assert candidate_hash == stable_content_hash(body)


def test_ising_candidate_payloads_materialize_all_sixteen_slots_without_certifying() -> None:
    payload_set = load_payload_set()

    assert_content_hash(payload_set)
    assert payload_set["status"] == (
        "ISING_RIBBON_LIFT_CANDIDATE_PAYLOADS_MATERIALIZED_NOT_CERTIFIED"
    )
    assert payload_set["candidate_payload_count"] == 16
    assert payload_set["formal_snapshot_count"] == 0
    assert payload_set["pending_certificate_count"] == 48
    assert payload_set["row_complete_status"] == "NOT_ROW_COMPLETE"
    assert set(payload_set["checks"].values()) == {True}

    payloads = payload_set["candidate_payloads"]
    assert len(payloads) == 16
    assert len({payload["slot_id"] for payload in payloads}) == 16
    assert len({payload["candidate_payload_hash"] for payload in payloads}) == 16
    assert sorted(len(value) for value in payload_set["payloads_by_braided_class"].values()) == [2] * 8


def test_each_ising_candidate_payload_is_hash_bound_to_source_category_data() -> None:
    payload_set = load_payload_set()

    for payload in payload_set["candidate_payloads"]:
        assert_candidate_payload_hash(payload)
        assert payload["payload_status"] == "CANDIDATE_PAYLOAD_MATERIALIZED_NOT_CERTIFIED"
        assert payload["formal_ribbon_realization_snapshot_produced"] is False
        assert payload["producer_exact_certificate_status"] == "MISSING"
        assert payload["runtime_consumer_certificate_status"] == "MISSING"
        assert payload["ribbon_pivotal_certificate_status"] == "MISSING"
        assert payload["row_complete_status"] == "NOT_ROW_COMPLETE"
        assert payload["source_branch_data_hash"].startswith("sha256:")
        assert payload["candidate_pivotal_data"]["evaluation_coevaluation_status"] == (
            "CANDIDATE_DIMENSIONS_ONLY_NOT_MATERIALIZED"
        )

        category_payload = payload["category_payload"]
        assert category_payload["labels"] == [0, 1, 2]
        assert category_payload["unit"] == 0
        assert category_payload["fusion"]
        assert category_payload["f_symbols"]
        assert category_payload["r_symbols"]
        assert category_payload["twists"]
        assert category_payload["duals"] == {"0": 0, "1": 1, "2": 2}
        assert category_payload["basis_gauge"].startswith("multiplicity-free SU(2)_k")
        assert category_payload["field_embedding"]["branch_status"] == (
            "candidate_galois_power_branch_not_row_certified"
        )


def test_ising_candidate_payloads_keep_scan_gate_closed() -> None:
    payload_set = load_payload_set()

    assert any("not formal evidence" in item for item in payload_set["explicit_non_claims"])
    assert any("does not authorize scan-plan generation" in item for item in payload_set["explicit_non_claims"])
    assert any("check twist/balancing/ribbon compatibility" in item for item in payload_set["remaining_growth"])

    for payload in payload_set["candidate_payloads"]:
        assert any(
            "not formal ribbon_realization_snapshot" in item
            for item in payload["explicit_non_claims"]
        )
        assert any(
            "does not prove twist/balancing/ribbon compatibility" in item
            for item in payload["explicit_non_claims"]
        )


def test_generator_rebuilds_ising_candidate_payload_shape() -> None:
    artifacts = MODULE.build_all()
    payload_set = artifacts["ising-ribbon-lift-candidate-payloads-v1.json"]

    assert payload_set["status"] == (
        "ISING_RIBBON_LIFT_CANDIDATE_PAYLOADS_MATERIALIZED_NOT_CERTIFIED"
    )
    assert payload_set["candidate_payload_count"] == 16
    assert payload_set["formal_snapshot_count"] == 0
    assert payload_set["pending_certificate_count"] == 48
    assert len(payload_set["candidate_payloads"]) == 16
