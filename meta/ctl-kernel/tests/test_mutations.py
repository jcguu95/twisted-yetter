from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "reference"))

import ctl_ref  # noqa: E402


class MutationTests(unittest.TestCase):
    def genesis_state(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def non_genesis_state(self):
        store, manifest = ctl_ref.build_case("non-genesis")
        genesis = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        child = ctl_ref.validate_transition(store, genesis, manifest["transition_batch"])
        trust = {
            "project_id": "project:demo",
            "kernel_profile": "ctl-kernel/1",
            "genesis_root_cid": manifest["objects"]["genesis_root"],
        }
        return store, manifest, genesis, child, trust

    def test_object_cid_tamper_is_rejected(self):
        store, manifest, _state = self.genesis_state()
        policy_cid = manifest["objects"]["policy"]
        store.objects[policy_cid]["payload"]["rules"] = []
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.derive_genesis(store, manifest["genesis_batch"])

    def test_transition_set_target_must_be_recorded(self):
        store, manifest, genesis, _child, _trust = self.non_genesis_state()
        transition = store.resolve(manifest["transition_batch"])
        transition["recorded_revisions"] = []
        bad_transition_cid = store.add(transition)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_transition(store, genesis, bad_transition_cid)

    def test_policy_replacement_must_be_atomic(self):
        store, manifest = ctl_ref.build_case("policy-replace-pass")
        genesis = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        transition = store.resolve(manifest["transition_batch"])
        transition["recorded_revisions"] = []
        bad_transition_cid = store.add(transition)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_transition(store, genesis, bad_transition_cid)

    def test_policy_replacement_must_fast_forward(self):
        store, manifest, genesis = self.genesis_state()
        old_policy_cid = manifest["objects"]["policy"]
        role_cid = manifest["objects"]["role"]
        bad_policy = ctl_ref.revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            ctl_ref.policy_payload(),
            parents=[],
        )
        bad_policy["created_at"] = "2026-06-25T23:00:01Z"
        bad_policy_cid = store.add(bad_policy)
        transition = ctl_ref.batch(
            genesis["root_cid"],
            [bad_policy_cid],
            [ctl_ref.set_op("sys:policy", ctl_ref.bound(old_policy_cid), bad_policy_cid)],
            [role_cid],
        )
        transition_cid = store.add(transition)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_transition(store, genesis, transition_cid)

    def test_root_transition_forgery_is_rejected_by_chain_replay(self):
        store, manifest, _genesis, child, trust = self.non_genesis_state()
        forged_root = dict(child["root"])
        forged_root["transition"] = manifest["genesis_batch"]
        forged_root_cid = store.add(forged_root)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_chain(store, forged_root_cid, trust)

    def test_evidence_cannot_target_another_binding_op(self):
        store, manifest, genesis, _child, _trust = self.non_genesis_state()
        role_cid = manifest["objects"]["role"]
        transition = store.resolve(manifest["transition_batch"])
        transition["evidence"] = [
            {
                "target": {"kind": "binding_op", "logical_id": "claim:other"},
                "basis": "agent/run-receipt/1",
                "cid": role_cid,
            }
        ]
        bad_transition_cid = store.add(transition)
        with self.assertRaises(ctl_ref.InvalidHistory):
            ctl_ref.validate_transition(store, genesis, bad_transition_cid)


if __name__ == "__main__":
    unittest.main()

