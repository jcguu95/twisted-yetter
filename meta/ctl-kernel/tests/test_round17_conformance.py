from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "reference"))

import ctl_ref  # noqa: E402


def classify(fn):
    try:
        fn()
        return "valid"
    except ctl_ref.InvalidHistory:
        return "invalid"
    except ctl_ref.UnsupportedProfile:
        return "unsupported"
    except Exception as exc:
        return f"host:{type(exc).__name__}"


class Round17ConformanceTests(unittest.TestCase):
    def transition_with_malformed_evidence_target(self, target):
        store, manifest = ctl_ref.build_case("non-genesis")
        genesis = ctl_ref.derive_genesis(store, manifest["objects"]["genesis_batch"])
        role_cid = manifest["objects"]["role"]
        receipt = ctl_ref.revision(
            "run-receipt:one",
            "run-receipt",
            "agent/run-receipt/1",
            {"status": "ok"},
        )
        receipt_cid = store.add(receipt)
        claim = ctl_ref.revision("claim:evidence-target", "claim", "ctl-data/opaque-json/1", {"text": "x"})
        claim_cid = store.add(claim)
        transition = ctl_ref.batch(
            genesis["root_cid"],
            [claim_cid, receipt_cid],
            [ctl_ref.set_op("claim:evidence-target", ctl_ref.absent(), claim_cid)],
            [role_cid],
            evidence=[{"target": target, "basis": "agent/run-receipt/1", "cid": receipt_cid}],
        )
        transition_cid = store.add(transition)
        return classify(lambda: ctl_ref.validate_transition(store, genesis, transition_cid))

    def test_recorded_revision_target_cid_array_is_invalid_not_host_exception(self):
        self.assertEqual(
            self.transition_with_malformed_evidence_target({"kind": "recorded_revision", "cid": []}),
            "invalid",
        )

    def test_recorded_revision_target_cid_object_is_invalid_not_host_exception(self):
        self.assertEqual(
            self.transition_with_malformed_evidence_target({"kind": "recorded_revision", "cid": {}}),
            "invalid",
        )

    def test_binding_op_target_logical_id_array_is_invalid_not_host_exception(self):
        self.assertEqual(
            self.transition_with_malformed_evidence_target({"kind": "binding_op", "logical_id": []}),
            "invalid",
        )

    def test_binding_op_target_logical_id_object_is_invalid_not_host_exception(self):
        self.assertEqual(
            self.transition_with_malformed_evidence_target({"kind": "binding_op", "logical_id": {}}),
            "invalid",
        )


if __name__ == "__main__":
    unittest.main()
