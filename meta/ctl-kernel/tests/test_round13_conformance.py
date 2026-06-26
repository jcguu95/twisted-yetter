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


class Round13ConformanceTests(unittest.TestCase):
    def test_genesis_unsupported_profile_does_not_mask_liveness_failure(self):
        store = ctl_ref.Store()
        bad_policy = ctl_ref.revision(
            "sys:policy",
            "policy-set",
            "ctl-governance/policy-set/1",
            ctl_ref.policy_payload(allow_owner=False),
        )
        bad_policy_cid = store.add(bad_policy)
        role = ctl_ref.revision(
            "role-binding:operator",
            "role-binding",
            "ctl-governance/role-binding/1",
            {
                "actor_id": "actor:jin",
                "role_id": "role:owner",
                "scope": {"project_id": "project:demo"},
            },
        )
        role_cid = store.add(role)
        unknown = ctl_ref.revision("claim:unknown", "claim", "vendor/profile/1", {})
        unknown_cid = store.add(unknown)
        genesis = ctl_ref.batch(
            None,
            [bad_policy_cid, role_cid, unknown_cid],
            [
                ctl_ref.set_op("role-binding:operator", ctl_ref.absent(), role_cid),
                ctl_ref.set_op("sys:policy", ctl_ref.absent(), bad_policy_cid),
            ],
            [],
        )
        genesis_cid = store.add(genesis)
        self.assertEqual(
            classify(lambda: ctl_ref.derive_genesis(store, genesis_cid)),
            "invalid",
        )


if __name__ == "__main__":
    unittest.main()
