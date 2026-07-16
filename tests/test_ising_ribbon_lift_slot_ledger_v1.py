import importlib.util
import json
from pathlib import Path

from twisted_yetter.foundation_safety import stable_content_hash


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "experiments" / "results" / "foundation-v2-safety-substrate"
SCRIPT = ROOT / "experiments" / "scripts" / "build_ising_ribbon_lift_slot_ledger_v1.py"
SPEC = importlib.util.spec_from_file_location("ising_ribbon_lift_slot_ledger_v1", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def load_ledger() -> dict:
    return json.loads(
        (OUT / "ising-ribbon-lift-slot-ledger-v1.json").read_text(encoding="utf-8")
    )


def assert_content_hash(payload: dict) -> None:
    body = dict(payload)
    content_hash = body.pop("content_hash")
    assert content_hash == stable_content_hash(body)


def test_ising_ribbon_lift_slot_ledger_enumerates_sixteen_pending_slots() -> None:
    ledger = load_ledger()

    assert_content_hash(ledger)
    assert ledger["status"] == "ISING_RIBBON_LIFT_SLOTS_ENUMERATED_NOT_MATERIALIZED"
    assert ledger["slot_derivation"]["braided_class_count"] == 8
    assert ledger["slot_derivation"]["spherical_structures_per_braided_class"] == 2
    assert ledger["slot_derivation"]["candidate_slot_count"] == 16
    assert ledger["pending_snapshot_count"] == 16
    assert ledger["formal_snapshot_count"] == 0
    assert ledger["row_complete_status"] == "NOT_ROW_COMPLETE"
    assert set(ledger["checks"].values()) == {True}

    slots = ledger["ribbon_lift_slots"]
    assert len(slots) == 16
    assert len({slot["slot_id"] for slot in slots}) == 16
    assert sorted(len(value) for value in ledger["slots_by_braided_class"].values()) == [2] * 8


def test_ising_ribbon_lift_slots_are_not_promoted_to_snapshots() -> None:
    ledger = load_ledger()

    for slot in ledger["ribbon_lift_slots"]:
        assert slot["slot_status"] == "PENDING_RIBBON_LIFT_MATERIALIZATION"
        assert slot["formal_ribbon_realization_snapshot_produced"] is False
        assert slot["producer_exact_certificate_status"] == "MISSING"
        assert slot["runtime_consumer_certificate_status"] == "MISSING"
        assert slot["ribbon_pivotal_certificate_status"] == "MISSING"
        assert slot["spherical_lift_label"] in {"plus", "minus"}

    assert any("does not produce ribbon_realization_snapshot" in item for item in ledger["explicit_non_claims"])
    assert any("does not prove that all sixteen slots survive" in item for item in ledger["explicit_non_claims"])


def test_generator_rebuilds_ising_ribbon_lift_slot_ledger_shape() -> None:
    artifacts = MODULE.build_all()
    ledger = artifacts["ising-ribbon-lift-slot-ledger-v1.json"]

    assert ledger["status"] == "ISING_RIBBON_LIFT_SLOTS_ENUMERATED_NOT_MATERIALIZED"
    assert ledger["pending_snapshot_count"] == 16
    assert ledger["formal_snapshot_count"] == 0
    assert len(ledger["ribbon_lift_slots"]) == 16
