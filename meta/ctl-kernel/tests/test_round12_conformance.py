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


class Round12ConformanceTests(unittest.TestCase):
    def restricted_lead_state(self):
        store, manifest = ctl_ref.build_case("role-binding-selector-pass")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def owner_state(self):
        store, manifest = ctl_ref.build_case("genesis")
        state = ctl_ref.derive_genesis(store, manifest["genesis_batch"])
        return store, manifest, state

    def test_unsupported_evidence_basis_does_not_mask_policy_denial(self):
        store, manifest, state = self.restricted_lead_state()
        lead_role_cid = manifest["objects"]["lead_role"]
        claim = ctl_ref.revision("claim:unauthorized", "claim", "ctl-data/opaque-json/1", {})
        claim_cid = store.add(claim)
        batch = ctl_ref.batch(
            state["root_cid"],
            [claim_cid],
            [ctl_ref.set_op("claim:unauthorized", ctl_ref.absent(), claim_cid)],
            [lead_role_cid],
            actor_id="actor:lead",
            evidence=[
                {
                    "target": {"kind": "binding_op", "logical_id": "claim:unauthorized"},
                    "basis": "vendor/unknown/1",
                    "cid": lead_role_cid,
                }
            ],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_unsupported_recorded_profile_does_not_mask_policy_denial(self):
        store, manifest, state = self.restricted_lead_state()
        lead_role_cid = manifest["objects"]["lead_role"]
        claim = ctl_ref.revision("claim:unauthorized", "claim", "ctl-data/opaque-json/1", {})
        claim_cid = store.add(claim)
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = ctl_ref.batch(
            state["root_cid"],
            [claim_cid, unknown_cid],
            [ctl_ref.set_op("claim:unauthorized", ctl_ref.absent(), claim_cid)],
            [lead_role_cid],
            actor_id="actor:lead",
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_unsupported_evidence_basis_does_not_mask_policy_liveness_failure(self):
        store, manifest, state = self.owner_state()
        role_cid = manifest["objects"]["role"]
        batch = ctl_ref.batch(
            state["root_cid"],
            [],
            [{"op": "remove", "logical_id": "role-binding:operator", "expected": ctl_ref.bound(role_cid)}],
            [role_cid],
            evidence=[
                {
                    "target": {"kind": "binding_op", "logical_id": "role-binding:operator"},
                    "basis": "vendor/unknown/1",
                    "cid": role_cid,
                }
            ],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )

    def test_unsupported_recorded_profile_does_not_mask_policy_liveness_failure(self):
        store, manifest, state = self.owner_state()
        role_cid = manifest["objects"]["role"]
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        batch = ctl_ref.batch(
            state["root_cid"],
            [unknown_cid],
            [{"op": "remove", "logical_id": "role-binding:operator", "expected": ctl_ref.bound(role_cid)}],
            [role_cid],
        )
        batch_cid = store.add(batch)
        self.assertEqual(
            classify(lambda: ctl_ref.validate_transition(store, state, batch_cid)),
            "invalid",
        )


if __name__ == "__main__":
    unittest.main()
